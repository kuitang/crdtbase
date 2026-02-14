# Chapter 6: End-to-End Flow and Tigris Replication

## 1. Architecture Overview

CRDTBase is a CRDT-native database where every replica operates independently
(offline-first), syncs through a shared replicated log stored in S3-compatible
object storage, and converges deterministically via CRDT merge semantics. The
production replication backend is **Tigris**, an S3-compatible object store with
automatic global geo-replication built on top of Fly.io infrastructure.

The key insight: Tigris handles the hard problem of geo-replicating bytes across
regions, while CRDTBase handles the hard problem of merging concurrent writes
deterministically. Together, they achieve multi-region eventual consistency
without any central coordination server.

### High-Level Topology

```
  Region: iad              Region: lhr              Region: nrt
  +-------------+          +-------------+          +-------------+
  | NodeCrdtClient|        | NodeCrdtClient|        | NodeCrdtClient|
  | (site-a)    |          | (site-b)    |          | (site-c)    |
  +------+------+          +------+------+          +------+------+
         |                        |                        |
    push | pull              push | pull              push | pull
         |                        |                        |
  +------v------+          +------v------+          +------v------+
  | S3 SDK      |          | S3 SDK      |          | S3 SDK      |
  +------+------+          +------+------+          +------+------+
         |                        |                        |
         +----------+    +-------+-------+    +-----------+
                    |    |               |    |
                    v    v               v    v
              +------------------------------+
              |     Tigris Object Storage     |
              |  (auto geo-replicated S3)     |
              |                               |
              |  deltas/site-a/0000000001.delta.bin
              |  deltas/site-b/0000000001.delta.bin
              |  deltas/site-c/0000000001.delta.bin
              |  snapshots/manifest.bin       |
              |  snapshots/segments/...       |
              +------------------------------+
```

## 2. The Replicated Log on S3

### 2.1 S3ReplicatedLog: The Core Transport

The replicated log is implemented as a set of S3 objects organized by site ID
and sequence number. This is the foundation for all replication.

**File:** `/home/kuitang/git/crdtbase/src/backend/s3ReplicatedLog.ts`

The key path convention is:

```
deltas/{siteId}/{seq:010}.delta.bin
```

For example:
```
deltas/site-a/0000000001.delta.bin
deltas/site-a/0000000002.delta.bin
deltas/site-b/0000000001.delta.bin
```

The four operations map directly to S3 primitives:

| ReplicatedLog method | S3 operation |
|---|---|
| `append(entry)` | `PutObject` with `IfNoneMatch: '*'` (create-only) |
| `readSince(siteId, since)` | `ListObjectsV2` + `GetObject` for each |
| `listSites()` | `ListObjectsV2` with `Delimiter: '/'` |
| `getHead(siteId)` | `ListObjectsV2`, parse max seq from filenames |

The `append` method is worth examining in detail because it handles concurrent
writers:

```typescript
// s3ReplicatedLog.ts:104-134
async append(entry: AppendLogEntry): Promise<LogPosition> {
  const siteRoot = this.siteRoot(entry.siteId);
  for (let attempt = 0; attempt < 5; attempt += 1) {
    const head = await this.getHead(entry.siteId);
    const nextSeq = head + 1;
    const objectKey = `${siteRoot}${keyForSeq(nextSeq)}`;
    try {
      await this.client.send(
        new PutObjectCommand({
          Bucket: this.bucket,
          Key: objectKey,
          Body: encodeBin({
            siteId: entry.siteId,
            hlc: entry.hlc,
            seq: nextSeq,
            ops: entry.ops,
          } satisfies LogEntry),
          ContentType: 'application/octet-stream',
          IfNoneMatch: '*',      // <-- create-only: fails if object exists
        }),
      );
      return nextSeq;
    } catch (error) {
      if (isRetryableAppendError(error)) {
        continue;               // 409/412 = someone else wrote that seq first
      }
      throw error;
    }
  }
  throw new Error(`failed to append after retries for site '${entry.siteId}'`);
}
```

The `IfNoneMatch: '*'` conditional PUT is critical: it ensures that if two
processes try to write the same sequence number, only one succeeds. The loser
retries with the next sequence number. This provides per-site linearizability
of the log without any external lock.

### 2.2 TigrisReplicatedLog: Thin Wrapper

**File:** `/home/kuitang/git/crdtbase/src/backend/tigrisReplicatedLog.ts`

The Tigris-specific log is just a factory function that configures an
`S3ReplicatedLog` with Tigris-specific defaults:

```typescript
// tigrisReplicatedLog.ts:12-26
export function createTigrisReplicatedLog(options: TigrisReplicatedLogOptions): S3ReplicatedLog {
  return new S3ReplicatedLog({
    bucket: options.bucket,
    prefix: options.prefix ?? 'deltas',
    clientConfig: {
      endpoint: options.endpoint,
      region: options.region ?? 'auto',
      forcePathStyle: false,
      credentials: {
        accessKeyId: options.accessKeyId,
        secretAccessKey: options.secretAccessKey,
      },
    },
  });
}
```

The `region: 'auto'` setting is significant: Tigris automatically routes
requests to the nearest region, so the client does not need to know which
region it is in. The `forcePathStyle: false` uses virtual-hosted-style URLs
which Tigris requires.

### 2.3 Contiguous Cursor Safety

**File:** `/home/kuitang/git/crdtbase/src/core/replication.ts`

Under eventual consistency, S3 LIST operations may return objects out of order
or with gaps (a newly written seq=5 may appear before seq=4 is visible). The
`takeContiguousEntriesSince` function prevents cursor corruption:

```typescript
// replication.ts:28-46
export function takeContiguousEntriesSince(
  entries: readonly LogEntry[],
  since: LogPosition,
): LogEntry[] {
  const ordered = [...entries].sort((left, right) => left.seq - right.seq);
  const contiguous: LogEntry[] = [];
  let expected = since + 1;
  for (const entry of ordered) {
    if (entry.seq < expected) {
      continue;
    }
    if (entry.seq !== expected) {
      break;        // Gap detected - stop here, do NOT skip ahead
    }
    contiguous.push(entry);
    expected += 1;
  }
  return contiguous;
}
```

If seq 3 is visible but seq 2 is not yet visible (Tigris eventual consistency),
this function returns nothing past seq 1. The next pull will pick up seq 2 and 3
together. This prevents the cursor from jumping past entries that have been
written but are not yet visible in the listing.

## 3. The NodeCrdtClient: Push/Pull Cadence

**File:** `/home/kuitang/git/crdtbase/src/platform/node/nodeClient.ts`

The `NodeCrdtClient` is the main client class that mediates between local state
and the replicated log. It maintains:

- `rows`: in-memory CRDT state (`Map<string, RuntimeRowState>`)
- `pendingOps`: ops written locally but not yet pushed
- `syncedSeqBySite`: cursor tracking how far we have pulled from each site
- `syncedHlcBySite`: HLC of the last entry pulled from each site (for integrity)

### 3.1 Push: Flush Local Writes to S3

```typescript
// nodeClient.ts:157-173
async push(): Promise<void> {
  await this.waitReady();
  if (this.pendingOps.length === 0) {
    return;
  }

  const ops = [...this.pendingOps];
  const seq = await this.log.append({
    siteId: this.siteId,
    hlc: ops[ops.length - 1]!.hlc,
    ops,
  });
  this.pendingOps = [];
  this.syncedSeqBySite.set(this.siteId, seq);
  this.syncedHlcBySite.set(this.siteId, ops[ops.length - 1]!.hlc);
  await this.persistStateFiles();
}
```

Push is straightforward: batch all pending ops into a single delta file and
PUT it to S3. The `log.append()` call handles sequence number assignment via
the `IfNoneMatch` conditional.

### 3.2 Pull: Fetch and Merge Remote Deltas

```typescript
// nodeClient.ts:175-222
async pull(): Promise<void> {
  await this.waitReady();
  await this.refreshFromSnapshotManifest();
  const sites = await this.log.listSites();
  for (const siteId of sites) {
    const since = this.syncedSeqBySite.get(siteId) ?? 0;
    // ... cursor validation logic ...
    entries = takeContiguousEntriesSince(probe.slice(1), since);

    for (const entry of entries) {
      for (const op of entry.ops) {
        applyCrdtOpToRows(this.rows, op);    // <-- CRDT merge happens here
      }
      this.syncedSeqBySite.set(siteId, entry.seq);
      this.syncedHlcBySite.set(siteId, entry.hlc);
    }
  }
  await this.persistStateFiles();
}
```

Pull iterates through every known site, fetches new entries since the last
cursor position, and applies each op to local state via CRDT merge. The
cursor validation in pull is notably thorough: it verifies the entry at the
cursor position still exists and has the expected HLC, catching cases where
remote history was rewritten or corrupted.

### 3.3 The Recent Push/Pull Cadence Change

The most recent commit (`b0646e5`) describes the switch to "push/pull cadence":

In the stress test worker loop, every write operation is immediately followed
by a push, and every read operation is preceded by a pull:

```typescript
// flyWorker.ts:776-781  (write operations)
if (wrote) {
  stats.writes += 1;
  await client.push();
  stats.pushes += 1;
}

// flyWorker.ts:761-774  (read operations)
} else {
  await client.pull();
  stats.pulls += 1;
  const rows = normalizeTaskRows(await client.query(TASK_QUERY_SQL));
  // ... validate ...
}
```

This is in contrast to the earlier `sync()` (push-then-pull combined) approach.
The explicit push/pull cadence means:
- Writes are visible to other regions as soon as Tigris replicates the object
- Reads always fetch the latest available state before querying
- No unnecessary pulls after writes (the local state already reflects the write)

## 4. How Tigris Geo-Replication Works

Tigris is an S3-compatible object store built specifically for Fly.io. Its key
property is **automatic geo-replication**: when you PUT an object from one
region, Tigris automatically replicates it to all regions where it has presence.

### 4.1 Consistency Model

From SPEC.md section 12.2:

> **Consistency for manifest:** Use `X-Tigris-Consistent: true` header on GET
> and the If-Match ETag conditional on PUT. This routes through the global
> leader, ensuring the CAS is correct regardless of which region the compaction
> job runs in.
>
> **Consistency for deltas:** Default (eventual) consistency is fine. Worst
> case, a sync pull misses a very recent delta -- it catches up on the next
> pull. CRDTs guarantee convergence.

This two-tier consistency model is elegant:

1. **Deltas (eventual consistency)**: Fast writes, fast reads, eventual
   visibility across regions. Missing a recent delta is harmless because the
   next pull catches it, and CRDT merge is idempotent for state-based types.

2. **Manifest (strong consistency)**: The manifest is the single coordination
   point for compaction. It uses ETags for compare-and-swap to prevent
   concurrent compaction jobs from corrupting each other.

### 4.2 Environment Configuration

**File:** `/home/kuitang/git/crdtbase/deploy/tigris/env.tigris.example`

```bash
export BUCKET_NAME=crdtbase
export AWS_ENDPOINT_URL_S3=https://<your-tigris-s3-endpoint>
export AWS_ACCESS_KEY_ID=<your-access-key-id>
export AWS_SECRET_ACCESS_KEY=<your-secret-access-key>
export AWS_REGION=auto
```

The `AWS_REGION=auto` setting tells the AWS SDK to let Tigris handle region
routing automatically.

**File:** `/home/kuitang/git/crdtbase/deploy/tigris/cors.example.json`

```json
{
  "CORSRules": [
    {
      "AllowedOrigins": ["*"],
      "AllowedMethods": ["GET", "PUT", "POST", "DELETE", "HEAD"],
      "AllowedHeaders": ["*"],
      "ExposeHeaders": ["ETag"],
      "MaxAgeSeconds": 3000
    }
  ]
}
```

The `ExposeHeaders: ["ETag"]` is notable: it allows browser clients to read
the ETag header for the manifest CAS protocol.

## 5. End-to-End Write Flow

Here is the complete path of a write from user SQL to Tigris and back:

### Step 1: Client Executes SQL

```typescript
await client.exec("UPDATE tasks SET title = 'Ship it' WHERE id = 't1';");
```

### Step 2: SQL Parser and Plan

The SQL is parsed into an AST, then compiled into CRDT operations:

```typescript
// nodeClient.ts:120-144
async exec(sql: string): Promise<void> {
  const statement = parseSql(sql);
  const plan = this.buildPlan(statement);
  // For a write plan:
  for (const op of plan.ops) {
    applyCrdtOpToRows(this.rows, op);   // Apply to local state immediately
    this.pendingOps.push(op);           // Buffer for push
  }
  await this.persistStateFiles();
}
```

The generated `EncodedCrdtOp` looks like:

```typescript
{
  tbl: "tasks",
  key: "t1",
  col: "title",
  kind: "cell_lww",
  hlc: "0x18e4a2b3c0010003",    // packed HLC (wallMs << 16 | counter)
  site: "site-a",
  val: "Ship it"
}
```

### Step 3: Push to S3

```typescript
await client.push();
```

This serializes the pending ops into a MessagePack delta file and PUTs it to:

```
deltas/site-a/0000000042.delta.bin
```

The conditional `IfNoneMatch: '*'` ensures uniqueness of the sequence number.

### Step 4: Tigris Geo-Replication

After the PUT succeeds, Tigris automatically replicates the object to all
regions. The replication latency is typically:
- Same continent: 10-50ms
- Cross-continent (e.g., iad to lhr): 50-200ms
- Cross-ocean (e.g., iad to syd): 100-400ms

### Step 5: Remote Client Pulls

```typescript
// On site-b in lhr:
await client.pull();
```

This calls `listSites()` (LIST deltas/ with delimiter), discovers `site-a`,
then calls `readSince('site-a', lastSeq)` which LISTs `deltas/site-a/` and
GETs each new delta file.

### Step 6: CRDT Merge

For each op in the fetched delta, `applyCrdtOpToRows` merges it into local
state. For LWW registers:

```typescript
// lww.ts:23-30
export function mergeLww<T>(a: LwwRegister<T>, b: LwwRegister<T>): LwwRegister<T> {
  assertLwwEventConsistency(a, b);
  const cmp = compareWithSite(a.hlc, a.site, b.hlc, b.site);
  if (cmp >= 0) {
    return a;   // local wins (higher HLC, or same HLC + higher site ID)
  }
  return b;     // remote wins
}
```

The tiebreaker is deterministic: higher HLC wins, and if HLCs are equal,
lexicographically higher site ID wins. This guarantees all replicas converge
to the same value regardless of the order they receive the operations.

## 6. Concurrent Writes: Three Regions Scenario

Consider three clients in iad, lhr, and nrt all updating the same row
concurrently:

```
Time    iad (site-a)           lhr (site-b)           nrt (site-c)
-----   -------------------    -------------------    -------------------
t=0     SET title='Alpha'      SET title='Beta'       SET title='Gamma'
        HLC=0x18e4a2b3c001     HLC=0x18e4a2b3c002     HLC=0x18e4a2b3c000
        push -> deltas/a/42    push -> deltas/b/17    push -> deltas/c/9

t=100ms Tigris replicates...   Tigris replicates...   Tigris replicates...

t=200ms pull()                 pull()                 pull()
        sees b/17, c/9         sees a/42, c/9         sees a/42, b/17
        merge:                 merge:                 merge:
        LWW('Beta' wins:      LWW('Beta' wins:       LWW('Beta' wins:
         0xc002 > 0xc001)      0xc002 > 0xc001)       0xc002 > 0xc001)
```

All three converge to `title='Beta'` because its HLC (0x...c002) is the
highest. The merge is the same regardless of which order the deltas arrive.

### 6.1 How Each CRDT Type Handles Conflicts

| CRDT Type | Conflict Resolution | Concurrent Behavior |
|---|---|---|
| LWW Register | Higher HLC wins; tiebreak by site ID | Last writer wins deterministically |
| PN-Counter | Per-site max for inc/dec maps | All increments accumulate (no conflict) |
| OR-Set | Union elements, union tombstones | All adds preserved; removes only affect observed tags |
| MV-Register | Keep all concurrent values | Application sees all concurrent values |

For PN-Counters, concurrent increments from different sites are naturally
additive. If site-a increments by 3 and site-b increments by 5 concurrently,
the merged counter reflects +8 because each site's count is tracked
independently:

```typescript
// pnCounter merge: for each site key, take max
state.inc = { "site-a": 3, "site-b": 5 }  // total inc = 8
```

## 7. The Snapshot/Compaction Layer

### 7.1 TigrisSnapshotStore

**File:** `/home/kuitang/git/crdtbase/src/backend/tigrisSnapshotStore.ts`

The snapshot store uses a separate S3 prefix (`snapshots/`) and provides:
- `getManifest()` / `putManifest()`: manifest.bin with CAS via ETag
- `getSegment()` / `putSegment()`: segment files
- `getSchema()` / `putSchema()`: schema file

The manifest CAS is the critical coordination primitive:

```typescript
// tigrisSnapshotStore.ts:132-175
async putManifest(manifest: ManifestFile, expectedVersion: number): Promise<boolean> {
  assertManifestPublishable(manifest, expectedVersion);
  const manifestKey = this.keyForPath(this.manifestPath);
  const current = await this.readObject(manifestKey);

  // ... read current version and ETag ...

  if (currentVersion !== expectedVersion) {
    return false;     // Version mismatch: another compactor ran
  }

  const putInput: PutObjectCommandInput = { /* ... */ };
  if (current === null) {
    putInput.IfNoneMatch = '*';       // First manifest ever
  } else if (currentEtag !== null) {
    putInput.IfMatch = currentEtag;   // CAS: only write if ETag matches
  }

  try {
    await this.client.send(new PutObjectCommand(putInput));
    return true;
  } catch (error) {
    if (isCasConflictError(error)) {
      return false;   // Another compactor won the race
    }
    throw error;
  }
}
```

### 7.2 Compaction Flow

**File:** `/home/kuitang/git/crdtbase/src/platform/node/compactor.ts`

```typescript
// compactor.ts:56-114  (simplified)
export async function compactReplicatedLog(options): Promise<NodeCompactionResult> {
  const priorManifest = await options.snapshots.getManifest() ?? makeEmptyManifest();
  const rows = await loadRowsFromManifest(options.snapshots, priorManifest);

  // Read all new deltas from every site since last compaction
  for (const siteId of sites) {
    const since = sitesCompacted[siteId] ?? 0;
    const entries = takeContiguousEntriesSince(
      await options.log.readSince(siteId, since), since
    );
    for (const entry of entries) {
      applyOpsToRuntimeRows(rows, entry.ops);   // CRDT merge
    }
    sitesCompacted[siteId] = nextHead;
  }

  // Build segment files and new manifest
  const builtSegments = buildSegmentsFromRows({ schema, rows, ... });
  for (const built of builtSegments) {
    await options.snapshots.putSegment(built.path, encodeBin(built.segment));
  }

  // CAS manifest update
  const applied = await options.snapshots.putManifest(nextManifest, priorManifest.version);
}
```

### 7.3 Client Snapshot Refresh

When a client pulls, it first checks for an updated manifest:

```typescript
// nodeClient.ts:346-393
private async refreshFromSnapshotManifest(): Promise<void> {
  const manifest = await this.snapshots.getManifest();
  if (manifest === null || manifest.version <= this.localSnapshotManifestVersion) {
    return;
  }

  // Load all segments referenced by the manifest
  const rows = new Map<string, RuntimeRowState>();
  for (const segmentRef of manifest.segments) {
    const bytes = await this.snapshots.getSegment(segmentRef.path);
    const segment = decodeBin<SegmentFile>(bytes);
    const loaded = segmentFileToRuntimeRows(segment);
    mergeRuntimeRowMaps(rows, loaded);
  }

  // Preserve read-your-writes for local unpushed operations
  for (const pending of this.pendingOps) {
    applyCrdtOpToRows(rows, pending);
  }

  this.rows.clear();
  for (const [key, row] of rows.entries()) {
    this.rows.set(key, row);
  }

  // Reset cursors to compaction watermarks
  for (const [siteId, seq] of Object.entries(manifest.sites_compacted)) {
    this.syncedSeqBySite.set(siteId, seq);
    this.syncedHlcBySite.delete(siteId);
  }
}
```

This allows new clients to bootstrap quickly: instead of replaying thousands
of delta files, they load the latest compacted segments and only replay
deltas newer than the compaction watermark.

## 8. The Fly.io Stress Test

The stress test is the most thorough validation of the entire replication
pipeline. It runs three workers in real Fly.io regions against real Tigris.

### 8.1 Architecture

```
  Local machine (coordinator)
  +-------------------------------------------+
  | scripts/stress/fly-coordinator.ts          |
  | - Creates fresh Tigris bucket per run      |
  | - Launches 3 Fly Machines via REST API     |
  | - Orchestrates barriers via S3 objects     |
  | - Validates convergence                    |
  +-------------------+-----------------------+
                      |
         Fly Machines REST API
                      |
    +-----------------+-------------------+
    |                 |                   |
    v                 v                   v
  Fly Machine       Fly Machine         Fly Machine
  region: iad       region: lhr         region: syd
  site-a            site-b              site-c
  (flyWorker.ts)    (flyWorker.ts)      (flyWorker.ts)
    |                 |                   |
    +--------+--------+--------+----------+
             |                 |
             v                 v
        Tigris S3 Bucket (auto-replicated)
```

### 8.2 Worker Image

**File:** `/home/kuitang/git/crdtbase/Dockerfile.stress`

```dockerfile
FROM node:20.19.2-slim AS build
WORKDIR /app
COPY package.json package-lock.json ./
RUN npm ci --ignore-scripts
COPY src ./src
COPY test/stress ./test/stress
RUN npx esbuild test/stress/flyWorker.ts \
  --bundle --platform=node --format=esm --target=node20 \
  --banner:js="import { createRequire } from \"module\"; ..." \
  --outfile=/out/flyWorker.mjs

FROM node:20.19.2-slim AS runtime
WORKDIR /app
COPY --from=build /out/flyWorker.mjs /app/flyWorker.mjs
ENTRYPOINT ["node", "/app/flyWorker.mjs"]
```

The worker is bundled into a single ESM file via esbuild, keeping the Docker
image minimal (just Node.js runtime + one JS file).

### 8.3 Region Configuration

**File:** `/home/kuitang/git/crdtbase/scripts/stress/fly-coordinator.ts`

```typescript
// fly-coordinator.ts:119-133
function parseRegions(raw: string | undefined): Record<SiteId, string> {
  const value = (raw ?? 'iad,lhr,syd').trim();
  // ...
  return {
    'site-a': parts[0]!,    // default: iad (US East, Virginia)
    'site-b': parts[1]!,    // default: lhr (Europe, London)
    'site-c': parts[2]!,    // default: syd (Asia-Pacific, Sydney)
  };
}
```

Default regions span three continents for maximum replication latency stress.

### 8.4 Worker Operation Loop

**File:** `/home/kuitang/git/crdtbase/test/stress/flyWorker.ts`

Each worker executes a configurable number of operations (default 30,000)
with a randomized mix:

```typescript
// flyWorker.ts:727-794
for (let opIndex = 1; opIndex <= config.opsPerClient; opIndex += 1) {
  const rowId = pickRowId(rng, rowIds);
  const opRoll = rng();

  if (opRoll < 0.5) {
    // 50%: Counter increment
    await client.exec(`INC tasks.points BY ${amount} WHERE id = '${rowId}';`);
    await client.push();
  } else if (opRoll < 0.82) {
    // 32%: Set add (unique tag)
    await client.exec(`ADD '${tag}' TO tasks.tags WHERE id = '${rowId}';`);
    await client.push();
  } else if (opRoll < 0.92) {
    // 10%: LWW title update
    await client.exec(`UPDATE tasks SET title = '${title}' WHERE id = '${rowId}';`);
    await client.push();
  } else if (opRoll < 0.97) {
    // 5%: MV-Register status update
    await client.exec(`UPDATE tasks SET status = '${status}' WHERE id = '${rowId}';`);
    await client.push();
  } else {
    // 3%: Read (pull first)
    await client.pull();
    const rows = await client.query(TASK_QUERY_SQL);
    // validate...
  }
}
```

Key design decisions:
- **Hot-row contention**: 72% of operations target the first 8 rows (out of 64),
  creating heavy write contention on a small set of keys
- **Immediate push after write**: Every write is pushed immediately, maximizing
  the chance of concurrent writes from different regions
- **Pull before read**: Reads always pull first to get the latest state

### 8.5 The Barrier Protocol

The barrier protocol is the mechanism for verifying convergence during the
stress test. It runs via S3 control objects (no direct worker-to-worker
communication).

**File:** `/home/kuitang/git/crdtbase/test/stress/PLAN.md`

```
Workers and coordinator rendezvous using S3 control objects under:
- control/<run-id>/barrier-<index>/pre/<site>.json
- control/<run-id>/barrier-<index>/drained/<site>.json
- control/<run-id>/commands/barrier-<index>/entry.json
- control/<run-id>/commands/barrier-<index>/release.json
- control/<run-id>/final/<site>.json
```

There are two types of barriers:

**Soft barriers** (every `STRESS_BARRIER_EVERY_OPS`, default 3000 ops):
1. Workers push all pending ops, then pull
2. Workers publish a "pre" report with their state hash and synced heads
3. Coordinator validates invariants (no regressions, no missing rows)
4. Coordinator publishes "continue" command
5. Workers resume

**Hard barriers** (every `STRESS_HARD_BARRIER_EVERY` soft barriers, default 2):
1. Same as soft barrier through step 2
2. Coordinator computes `targetHeads` from all pre-reports
3. Coordinator publishes "drain" command with target heads
4. Workers perform multiple push/pull rounds until:
   - Local synced heads >= target heads for all sites
   - State hash is stable for `STRESS_DRAIN_QUIESCENCE_ROUNDS` (default 2)
5. Workers publish "drained" report
6. Coordinator validates convergence: **all three state hashes must be identical**
7. Coordinator publishes "release" command
8. Workers resume

The convergence check is the core assertion:

```typescript
// fly-coordinator.ts:461-477
function validateConvergenceHashes(reports: WorkerBarrierReport[]): void {
  let expected = '';
  for (const report of reports) {
    if (!expected) {
      expected = report.stateHash;
    } else if (report.stateHash !== expected) {
      throw new Error(
        `convergence hash mismatch at barrier=${barrierLabel(report.barrierIndex)} ...`,
      );
    }
  }
}
```

### 8.6 Expected Barrier Timing (Real Fly Regions)

From `PLAN.md` and `fly-coordinator.sh`:

| Barrier Type | Typical | p95 | Default Timeout |
|---|---|---|---|
| Soft (invariants only) | 1-4 seconds | 6-8 seconds | 30 seconds |
| Hard (drain + convergence) | 6-20 seconds | 25-40 seconds | 90 seconds |

These numbers reflect real cross-continent Tigris replication latency:
- The soft barrier is fast because it only requires each worker to push
  and report (no cross-region convergence needed)
- The hard barrier must wait for Tigris to replicate objects across all
  three continents (iad <-> lhr <-> syd), which is the dominant latency

### 8.7 Invariant Validation

Workers track local expectations for monotonic CRDT types:

```typescript
// flyWorker.ts:216-253
function validateLocalInvariants(params: {
  rows: NormalizedTaskRow[];
  expectations: MutableExpectations;
}): { ok: boolean; errors: string[] } {
  for (const [rowId, expectedPoints] of params.expectations.points.entries()) {
    const row = byId.get(rowId);
    if (row.points < expectedPoints) {
      errors.push(`row '${rowId}' points regressed below local expectation`);
    }
  }

  for (const [rowId, expectedTags] of params.expectations.tags.entries()) {
    const actual = new Set(row.tags);
    for (const tag of expectedTags) {
      if (!actual.has(tag)) {
        errors.push(`row '${rowId}' missing local tag '${tag}'`);
      }
    }
  }
}
```

This validates two key CRDT properties:
1. **Counter monotonicity**: After convergence, the counter value must be at
   least as large as the local expectation (because other sites may have also
   incremented, making it larger)
2. **Set completeness**: After convergence, all locally added tags must be
   present (OR-Set add is irrevocable unless explicitly removed)

### 8.8 Running the Stress Test

```bash
# Build worker image
docker build -f Dockerfile.stress -t registry.fly.io/YOUR_APP:stress .
docker push registry.fly.io/YOUR_APP:stress

# Run coordinator (launches 3 Fly Machines, orchestrates barriers)
FLY_APP=your-app \
FLY_WORKER_IMAGE=registry.fly.io/YOUR_APP:stress \
FLY_REGIONS=iad,lhr,syd \
AWS_ENDPOINT_URL_S3=https://fly.storage.tigris.dev \
AWS_ACCESS_KEY_ID=... \
AWS_SECRET_ACCESS_KEY=... \
npm run stress:fly:coordinator
```

The coordinator:
1. Creates a fresh bucket per run (`crdtbase-stress-run-...`)
2. Launches 3 Fly Machines via the Machines REST API
3. Orchestrates all barriers
4. Checks final convergence
5. Cleans up machines and bucket

## 9. The E2E Test Suite

### 9.1 Three-Client Chaos Test (In-Process)

**File:** `/home/kuitang/git/crdtbase/test/e2e/three-clients.e2e.test.ts`

The in-process test runs three clients against an HTTP-backed replicated log
server. It uses the same chaos orchestrator but with simulated delays:

```typescript
const result = await runThreeClientChaosScenario({
  clients: { 'site-a': clientA, 'site-b': clientB, 'site-c': clientC },
  observer,
  config: {
    seed,
    stepsPerClient: CHAOS.steps,
    maxDelayMs: CHAOS.maxDelayMs,
    drainRounds: CHAOS.drainRounds,
    quiescenceRounds: CHAOS.quiescenceRounds,
  },
});

// Assert convergence
expect(rowsA).toEqual(rowsB);
expect(rowsB).toEqual(rowsC);
expect(result.observerRows).toEqual(rowsA);
```

### 9.2 S3/MinIO Chaos Test

**File:** `/home/kuitang/git/crdtbase/test/e2e/s3-minio.e2e.test.ts`

Same chaos scenario but running against a local MinIO instance, testing the
actual S3 transport layer. It additionally validates:
- Delta files are present in the bucket with correct prefixes
- Delta files are valid MessagePack and can be dumped with the CLI
- Compaction produces valid segments and manifest
- A fourth client (site-d) can bootstrap from compacted snapshots

## 10. The S3 Integrity Proxy (Planned)

**File:** `/home/kuitang/git/crdtbase/PROXY_PLAN.md`

A planned enhancement adds a proxy server that validates writes before
committing them to S3:

```
Client --> POST /append/:siteId --> Proxy validates --> S3 PUT
```

Key properties:
- Proxy replays operations against mirrored CRDT state to check invariants
- Proxy assigns sequence numbers (prevents client forgery)
- Clients read directly from S3 (reads bypass proxy)
- On rejection, pending ops remain local (no data loss)
- Proxy runs its own sync loop against S3 to stay convergent

This addresses the security gap of direct S3 access: currently any client
with credentials can write arbitrary data to the delta log.

## 11. Summary: Why This Design Works

The crdtbase + Tigris architecture achieves multi-region eventual consistency
through a clean separation of concerns:

1. **Tigris handles bytes**: It stores objects and automatically replicates
   them across regions. It provides eventual consistency for reads and
   conditional PUTs for coordination.

2. **CRDTs handle semantics**: The CRDT merge functions (LWW, PN-Counter,
   OR-Set, MV-Register) ensure that no matter what order operations arrive,
   the result is deterministic and identical across all replicas.

3. **The replicated log handles ordering**: Per-site sequence numbers and
   contiguous cursor safety ensure that operations are applied exactly once
   and in order within each site's log.

4. **Compaction handles efficiency**: Segment files collapse the full delta
   history into a compact snapshot, allowing new clients to bootstrap quickly
   and reducing the number of S3 LIST/GET operations during pull.

5. **The barrier protocol handles verification**: The stress test's soft and
   hard barriers provide empirical proof that the system converges correctly
   under real multi-region conditions with high contention.

The fundamental insight is that Tigris's geo-replication is "good enough" for
the delta log: eventual consistency with a few hundred milliseconds of
cross-region latency. CRDTs tolerate this delay because merge is commutative,
associative, and idempotent. The only place strong consistency is needed is
the manifest CAS, which happens infrequently during compaction.
