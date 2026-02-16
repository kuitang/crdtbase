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
// s3ReplicatedLog.ts:108-138
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

Clients now use the unified `createHlcClock()` API (from `src/core/hlc.ts`)
instead of manual clock management. The factory produces an `HlcClock` with
monotonic wall-clock synthesis, 60-second drift rejection, and explicit
local/remote HLC progression:

```typescript
// hlc.ts:172-186
export function createHlcClock(options: {
  nowWallMs?: () => number;
  driftLimitMs?: number;
} = {}): HlcClock {
  const nowWallMs = options.nowWallMs ?? createMonotonicWallClock();
  const driftLimitMs = normalizeDriftLimitMs(options.driftLimitMs ?? HLC_DRIFT_LIMIT_MS);
  return {
    driftLimitMs,
    nowWallMs,
    next(previous: Hlc | null): Hlc {
      return nextMonotonicHlc(previous, nowWallMs(), driftLimitMs);
    },
    // ...
  };
}
```

Both `NodeCrdtClient` and `BrowserCrdtClient` use `createHlcClock()` at
construction time:

```typescript
// nodeClient.ts:96
this.hlcClock = clock ?? createHlcClock();
```

### 3.1 Push: Flush Local Writes to S3

```typescript
// nodeClient.ts:147-163
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
// nodeClient.ts:165-214
async pull(): Promise<void> {
  await this.waitReady();
  await this.refreshFromSnapshotManifest();
  const sites = await this.log.listSites();
  for (const siteId of sites) {
    const since = this.syncedSeqBySite.get(siteId) ?? 0;
    // ... cursor validation logic ...
    entries = takeContiguousEntriesSince(probe.slice(1), since);

    for (const entry of entries) {
      this.lastLocalHlc = this.hlcClock.recv(this.lastLocalHlc, decodeHlcHex(entry.hlc));
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

### 3.3 Atomic State Persistence

Local persistence now uses an atomic bundle commit pattern to prevent the
PN-Counter double-application bug (P0-1). The client writes state, pending ops,
and sync cursors as a single `state_bundle.bin` file using temp-file + rename:

```typescript
// nodeClient.ts:335-351
const atomicBundle: AtomicStateBundleFile = {
  v: 1,
  state: stateFile,
  pending: pendingFile,
  sync: syncFile,
};

// Commit the authoritative local state as one atomically-renamed bundle.
await this.writeFileAtomically(this.atomicStateBundlePath, encodeBin(atomicBundle));

// Legacy split files remain for backwards compatibility and tooling.
await Promise.all([
  this.writeFileAtomically(this.schemaPath, encodeBin(this.schema)),
  this.writeFileAtomically(this.statePath, encodeBin(stateFile)),
  this.writeFileAtomically(this.pendingPath, encodeBin(pendingFile)),
  this.writeFileAtomically(this.syncPath, encodeBin(syncFile)),
]);
```

The `writeFileAtomically` method itself uses temp-file + `rename`:

```typescript
// nodeClient.ts:367-377
private async writeFileAtomically(path: string, bytes: Uint8Array): Promise<void> {
  const tempPath = `${path}.tmp-${process.pid}-${Date.now()}-${Math.random().toString(16).slice(2)}`;
  await mkdir(dirname(path), { recursive: true });
  await writeFile(tempPath, bytes);
  try {
    await rename(tempPath, path);
  } catch (error) {
    await rm(tempPath, { force: true });
    throw error;
  }
}
```

This guarantees that a crash at any point leaves either the old complete bundle
or the new complete bundle on disk -- never a half-written state.

### 3.4 Push-After-Write / Pull-Before-Read Cadence

The stress test worker loop enforces strict push/pull cadence: every write
operation is immediately followed by a push, and every read operation is
preceded by a pull:

```typescript
// flyWorker.ts:871-875  (write operations)
if (wrote) {
  stats.writes += 1;
  await client.push();
  stats.pushes += 1;
}

// flyWorker.ts:855-869  (read operations)
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
// nodeClient.ts:119-135
async exec(sql: string): Promise<void> {
  await this.waitReady();
  const statement = parseSql(sql);
  const plan = this.buildPlan(statement);
  switch (plan.kind) {
    case 'read':
      throw new Error(`exec does not accept SELECT statements; use query(sql) instead`);
    case 'write': {
      for (const op of plan.ops) {
        applyCrdtOpToRows(this.rows, op);   // Apply to local state immediately
        this.pendingOps.push(op);           // Buffer for push
      }
      this.refreshSchemaFromRows();
      await this.persistStateFiles();
    }
  }
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

The `compactReplicatedLog` function reads the prior manifest, loads existing
segments, replays new deltas from all sites, prunes tombstones, builds fresh
segments, and performs a CAS manifest update:

```typescript
// compactor.ts:62-143
export async function compactReplicatedLog(
  options: SnapshotCompactorOptions,
): Promise<NodeCompactionResult> {
  const schema = options.schema ?? (await options.snapshots.getSchema());
  const priorManifest = (await options.snapshots.getManifest()) ?? makeEmptyManifest();
  const rows = await loadRowsFromManifest(options.snapshots, priorManifest);
  const sitesCompacted: Record<string, number> = { ...priorManifest.sites_compacted };

  let compactionHlc = priorManifest.compaction_hlc;
  let opsRead = 0;

  const sites = await options.log.listSites();
  sites.sort();

  for (const siteId of sites) {
    const since = normalizeSeq(sitesCompacted[siteId] ?? 0);
    const readEntries = await options.log.readSince(siteId, since);
    const entries = takeContiguousEntriesSince(readEntries, since);
    let nextHead = since;
    for (const entry of entries) {
      nextHead = Math.max(nextHead, normalizeSeq(entry.seq));
      compactionHlc = maxHlcHex(compactionHlc, entry.hlc);
      applyOpsToRuntimeRows(rows, entry.ops);
      opsRead += entry.ops.length;
    }
    sitesCompacted[siteId] = nextHead;
  }

  pruneRuntimeRowsForCompaction(rows, {
    nowMs: (options.now ?? (() => Date.now()))(),
    orSetTombstoneTtlMs: options.orSetTombstoneTtlMs ?? DEFAULT_OR_SET_TOMBSTONE_TTL_MS,
    rowTombstoneTtlMs: options.rowTombstoneTtlMs ?? DEFAULT_ROW_TOMBSTONE_TTL_MS,
  });

  const builtSegments = buildSegmentsFromRows({ schema, rows, defaultHlcMax: compactionHlc });
  // ... write segments, CAS manifest ...

  const applied = await options.snapshots.putManifest(nextManifest, priorManifest.version);
}
```

Compaction now includes tombstone pruning for both OR-Set tombstones and
row-level tombstones via configurable TTL (default 7 days each). This resolves
the unbounded tombstone growth problem (P2-1, P2-3).

### 7.3 Snapshot Manifest Coverage Gate (Critical Bug Fix)

**File:** `/home/kuitang/git/crdtbase/src/platform/node/nodeClient.ts`

A critical bug was discovered during stress testing: clients were applying
snapshot manifests that did not cover all previously-synced sites. This caused
rows to be dropped when the snapshot was loaded, while sync cursors stayed
advanced past entries that the snapshot had missed, permanently skipping
required replay for the missing site.

The fix adds a `manifestCoversKnownSites` gate in both `NodeCrdtClient` and
`BrowserCrdtClient`:

```typescript
// nodeClient.ts:388-392
if (!this.manifestCoversKnownSites(manifest)) {
  // Reject incomplete manifests for sites we already track; otherwise we may
  // replace rows with a partial snapshot and skip required log replay.
  return;
}
```

The coverage check iterates every site the client has already synced and
verifies the manifest includes a compaction watermark for it:

```typescript
// nodeClient.ts:434-444
private manifestCoversKnownSites(manifest: ManifestFile): boolean {
  for (const [siteId, seq] of this.syncedSeqBySite.entries()) {
    if (seq <= 0) {
      continue;
    }
    if (!(siteId in manifest.sites_compacted)) {
      return false;
    }
  }
  return true;
}
```

The same gate appears in `BrowserCrdtClient` at line 283/321. Without this
gate, a race between compaction (which may not have seen the latest site) and
a client pull (which has already synced that site) silently drops rows. This
was the root cause of the `run-20260215223738-1-3540465964` stress test
failure.

### 7.4 Client Snapshot Refresh Flow

When a client pulls, it first checks for an updated manifest:

```typescript
// nodeClient.ts:379-432
private async refreshFromSnapshotManifest(): Promise<void> {
  if (!this.snapshots) {
    return;
  }
  await this.hydrateSchemaFromSnapshotsIfMissing();
  const manifest = await this.snapshots.getManifest();
  if (manifest === null || manifest.version <= this.localSnapshotManifestVersion) {
    return;
  }
  if (!this.manifestCoversKnownSites(manifest)) {
    return;   // Coverage gate
  }

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
pipeline. It runs three workers in real Fly.io regions against real Tigris,
now with integrated compaction and snapshot coverage validation.

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
  [compactor?]
    |                 |                   |
    +--------+--------+--------+----------+
             |                 |
             v                 v
        Tigris S3 Bucket (auto-replicated)
```

One worker is designated as the compactor per run (random assignment via
`runSeed % 3`). This worker runs `compactReplicatedLog()` periodically,
exercising the full snapshot/compaction pipeline under real distributed
conditions.

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

### 8.3 Configuration

**File:** `/home/kuitang/git/crdtbase/test/stress/flyWorker.ts`

The stress test configuration is environment-driven with sensible defaults:

```typescript
// flyWorker.ts:339-391
const opsPerClient = parsePositiveIntEnv('STRESS_OPS_PER_CLIENT', 30_000);
const barrierEveryOps = parsePositiveIntEnv('STRESS_BARRIER_EVERY_OPS', 3_000);
const hardBarrierEvery = parsePositiveIntEnv('STRESS_HARD_BARRIER_EVERY', 2);
const compactorSiteId = parseOptionalSiteId(process.env.STRESS_COMPACTOR_SITE);
const compactionEveryOps = parsePositiveIntEnv('STRESS_COMPACTION_EVERY_OPS', 3_000);
const rowCount = parsePositiveIntEnv('STRESS_ROW_COUNT', 64);
const drainRounds = parsePositiveIntEnv('STRESS_DRAIN_ROUNDS', 8);
const drainQuiescenceRounds = parsePositiveIntEnv('STRESS_DRAIN_QUIESCENCE_ROUNDS', 2);
const drainMaxExtraRounds = parsePositiveIntEnv('STRESS_DRAIN_MAX_EXTRA_ROUNDS', 200);
```

For the latest validation batch (2026-02-15), the run shape uses tighter
parameters for faster feedback:

| Parameter | Value |
|---|---|
| `STRESS_OPS_PER_CLIENT` | 120 |
| `STRESS_BARRIER_EVERY_OPS` | 30 |
| `STRESS_HARD_BARRIER_EVERY` | 1 (every barrier is hard) |
| `STRESS_COMPACTION_EVERY_OPS` | 30 |
| Regions | `iad`, `lhr`, `syd` |
| Compactor placement | per-run random (`runSeed % 3`) |

Default regions span three continents for maximum replication latency stress.

### 8.4 Schema Operations in Distributed Test

The stress test now exercises schema operations (`CREATE TABLE`) through the
distributed system. One worker (the `schemaOwner`, determined by seed) creates
the tasks table and seeds initial rows:

```typescript
// flyWorker.ts:766-783
if (config.siteId === schemaOwner) {
  await client.exec(CREATE_TASKS_TABLE_SQL);
  for (const rowId of rowIds) {
    await client.exec(
      [
        'INSERT INTO tasks (id, title, points, tags, status) VALUES (',
        `'${escapeSqlString(rowId)}',`,
        `'seed-${escapeSqlString(rowId)}',`,
        '0,',
        `'seed-${escapeSqlString(rowId)}',`,
        `'open'`,
        ');',
      ].join(' '),
    );
  }
  await client.push();
}
```

Other workers poll until they receive the seeded rows via pull, with a 180-second
startup deadline. This exercises the full schema replication path through Tigris.

### 8.5 Compaction in the Worker Loop

The designated compactor worker runs `compactReplicatedLog()` at multiple
points:

1. **Startup compaction** after initial seed data is available:

```typescript
// flyWorker.ts:815-817
if (isCompactor) {
  await runCompaction('startup');
}
```

2. **Periodic compaction** every `STRESS_COMPACTION_EVERY_OPS` operations
   during the main loop:

```typescript
// flyWorker.ts:877-879
if (isCompactor && opIndex % config.compactionEveryOps === 0) {
  await runCompaction(`op-${opIndex}`);
}
```

3. **Barrier-entry compaction** at the start of hard barrier drain phases:

```typescript
// flyWorker.ts:678-679
if (isCompactor) {
  await runCompaction(`barrier-${barrierIndex}-entry`);
}
```

4. **Barrier-drained compaction** after drain convergence, before publishing
   the drained report:

```typescript
// flyWorker.ts:730-732
if (isCompactor) {
  await runCompaction(`barrier-${barrierIndex}-drained`);
}
```

5. **Final compaction** after all operations complete:

```typescript
// flyWorker.ts:900-902
if (isCompactor) {
  await runCompaction('final');
}
```

The `runCompaction` closure publishes the schema to the snapshot store on first
invocation, then calls `compactReplicatedLog`:

```typescript
// flyWorker.ts:562-585
const runCompaction = async (trigger: string): Promise<void> => {
  if (!snapshots) {
    return;
  }
  if (!snapshotSchemaPublished) {
    await snapshots.putSchema(TASKS_SCHEMA);
    snapshotSchemaPublished = true;
  }
  const result = await compactReplicatedLog({
    log,
    snapshots,
    schema: TASKS_SCHEMA,
  });
  logLine(
    config.siteId,
    config.runId,
    'compaction trigger=' + trigger +
      ' applied=' + String(result.applied ? 1 : 0) +
      ' opsRead=' + String(result.opsRead) +
      ' manifestVersion=' + String(result.manifest.version) +
      ' segments=' + String(result.manifest.segments.length),
  );
};
```

This validates that compaction does not break convergence in a real distributed
setting. The barrier drain phases verify that all workers converge to the same
state hash even after compaction has rewritten the snapshot manifests and
segments.

### 8.6 Worker Operation Loop

**File:** `/home/kuitang/git/crdtbase/test/stress/flyWorker.ts`

Each worker executes a configurable number of operations with a randomized mix:

```typescript
// flyWorker.ts:822-893
for (let opIndex = 1; opIndex <= config.opsPerClient; opIndex += 1) {
  const rowId = pickRowId(rng, rowIds);
  const opRoll = rng();
  let wrote = false;

  if (opRoll < 0.5) {
    // 50%: Counter increment
    const amount = rngInt(rng, 1, 7);
    await client.exec(`INC tasks.points BY ${amount} WHERE id = '${rowId}';`);
    expectations.points.set(rowId, (expectations.points.get(rowId) ?? 0) + amount);
    wrote = true;
  } else if (opRoll < 0.82) {
    // 32%: Set add (unique tag)
    const tag = `${config.siteId}-t-${opIndex}-${rngInt(rng, 10_000, 999_999)}`;
    await client.exec(`ADD '${tag}' TO tasks.tags WHERE id = '${rowId}';`);
    expectations.tags.get(rowId)!.add(tag);
    wrote = true;
  } else if (opRoll < 0.92) {
    // 10%: LWW title update
    await client.exec(`UPDATE tasks SET title = '${title}' WHERE id = '${rowId}';`);
    wrote = true;
  } else if (opRoll < 0.97) {
    // 5%: MV-Register status update
    await client.exec(`UPDATE tasks SET status = '${status}' WHERE id = '${rowId}';`);
    wrote = true;
  } else {
    // 3%: Read (pull first)
    await client.pull();
    stats.pulls += 1;
    const rows = normalizeTaskRows(await client.query(TASK_QUERY_SQL));
    // validate...
  }

  if (wrote) {
    stats.writes += 1;
    await client.push();
    stats.pushes += 1;
  }

  if (isCompactor && opIndex % config.compactionEveryOps === 0) {
    await runCompaction(`op-${opIndex}`);
  }

  if (opIndex % config.barrierEveryOps === 0) {
    barrierIndex += 1;
    await runBarrier(barrierIndex, opIndex);
  }
}
```

Key design decisions:
- **Hot-row contention**: 72% of operations target the first 8 rows (out of 64),
  creating heavy write contention on a small set of keys
- **Immediate push after write**: Every write is pushed immediately, maximizing
  the chance of concurrent writes from different regions
- **Pull before read**: Reads always pull first to get the latest state
- **Interleaved compaction**: The compactor worker runs compaction every N ops,
  exercising snapshot cutover under concurrent writes

### 8.7 The Barrier Protocol

The barrier protocol is the mechanism for verifying convergence during the
stress test. It runs via S3 control objects (no direct worker-to-worker
communication).

**File:** `/home/kuitang/git/crdtbase/test/stress/flyWorker.ts`

```
Workers and coordinator rendezvous using S3 control objects under:
- control/<run-id>/barrier-<index>/pre/<site>.json
- control/<run-id>/barrier-<index>/drained/<site>.json
- control/<run-id>/commands/barrier-<index>/entry.json
- control/<run-id>/commands/barrier-<index>/release.json
- control/<run-id>/final/<site>.json
```

With the latest configuration (`STRESS_HARD_BARRIER_EVERY=1`), every barrier
is a hard barrier. The barrier flow for each is:

1. Workers push all pending ops, then pull to refresh remote cursors
2. Workers publish a "pre" report with state hash, synced heads, and
   local invariant validation results
3. Coordinator computes `targetHeads` from all pre-reports (the union of
   all site heads across all workers)
4. Coordinator publishes "drain" command with target heads
5. Workers perform multiple push/pull rounds until:
   - Local synced heads >= target heads for all sites
   - State hash is stable for `STRESS_DRAIN_QUIESCENCE_ROUNDS` (default 2)
   rounds
6. Workers publish "drained" report
7. Coordinator validates convergence: **all three state hashes must be identical**
8. Coordinator publishes "release" command
9. Workers resume

The drain loop implements target head tracking:

```typescript
// flyWorker.ts:690-724
while (
  (roundsPerformed < requestedRounds ||
    stableRounds < config.drainQuiescenceRounds ||
    !reachedTarget) &&
  roundsPerformed < hardRoundLimit
) {
  await client.push();
  stats.pushes += 1;
  await client.pull();
  stats.pulls += 1;
  roundsPerformed += 1;
  const syncedHeads = client.getSyncedHeads();
  const targetCheck = compareHeadsToTarget(syncedHeads, targetHeads);
  reachedTarget = targetCheck.reached;
  missingTarget = targetCheck.missing;
  const rows = normalizeTaskRows(await client.query(TASK_QUERY_SQL));
  const currentHash = hashRows(rows);
  if (lastHash === currentHash) {
    stableRounds += 1;
  } else {
    stableRounds = 0;
  }
  lastHash = currentHash;
}
```

The `compareHeadsToTarget` function verifies that every site's local synced
cursor is at or past the coordinator-provided target:

```typescript
// flyWorker.ts:414-430
function compareHeadsToTarget(
  syncedHeads: Record<string, number>,
  targetHeads: Record<string, number>,
): { reached: boolean; missing: string[] } {
  const missing: string[] = [];
  for (const [siteId, target] of Object.entries(targetHeads)) {
    const targetSeq = Number.isFinite(target) ? target : 0;
    const actualSeq = syncedHeads[siteId] ?? 0;
    if (actualSeq < targetSeq) {
      missing.push(`${siteId}:${actualSeq}<${targetSeq}`);
    }
  }
  return { reached: missing.length === 0, missing };
}
```

Note that the compactor worker runs compaction both at barrier entry (before
drain) and after drain completes (before publishing the drained report). This
means the drained-phase report reflects state that has been through the full
compaction/snapshot cycle, and the convergence hash check verifies that
compaction preserves correctness.

### 8.8 Invariant Validation

Workers track local expectations for monotonic CRDT types:

```typescript
// flyWorker.ts:237-275
function validateLocalInvariants(params: {
  rows: NormalizedTaskRow[];
  expectations: MutableExpectations;
}): { ok: boolean; errors: string[] } {
  const byId = new Map(params.rows.map((row) => [row.id, row]));
  const errors: string[] = [];

  for (const [rowId, expectedPoints] of params.expectations.points.entries()) {
    const row = byId.get(rowId);
    if (!row) {
      errors.push(`missing row '${rowId}'`);
      continue;
    }
    if (row.points < expectedPoints) {
      errors.push(
        `row '${rowId}' points regressed below local expectation: ` +
        `actual=${row.points} expected>=${expectedPoints}`,
      );
    }
  }

  for (const [rowId, expectedTags] of params.expectations.tags.entries()) {
    const row = byId.get(rowId);
    if (!row) {
      errors.push(`missing row '${rowId}' for tags`);
      continue;
    }
    const actual = new Set(row.tags);
    for (const tag of expectedTags) {
      if (!actual.has(tag)) {
        errors.push(`row '${rowId}' missing local tag '${tag}'`);
      }
    }
  }

  return { ok: errors.length === 0, errors: errors.slice(0, 50) };
}
```

This validates two key CRDT properties:
1. **Counter monotonicity**: After convergence, the counter value must be at
   least as large as the local expectation (because other sites may have also
   incremented, making it larger)
2. **Set completeness**: After convergence, all locally added tags must be
   present (OR-Set add is irrevocable unless explicitly removed)

### 8.9 Timing Results (2026-02-15)

**File:** `/home/kuitang/git/crdtbase/test/stress/TIMING_RESULTS_2026-02-15.md`

The latest 3-run validation batch ran with the snapshot-coverage-gate fix
and compactor-enabled workers:

#### Run-Level Totals

| Run ID | Result | Wall Time (s) |
|---|---|---:|
| `run-20260215224530-1-4067962528` | PASS | 238.4 |
| `run-20260215224933-2-3422796657` | PASS | 271.0 |
| `run-20260215225408-3-2298453710` | PASS | 341.4 |

**Average run wall time: 283.6s** (down 8.6% from 310.3s baseline on 2026-02-14)

#### Barrier Timing Breakdown

| Run ID | Barrier | Pre (s) | Drained (s) | Total (s) |
|---|---:|---:|---:|---:|
| `run-...-1-4067962528` | 1 | 29 | 19 | 48 |
| `run-...-1-4067962528` | 2 | 36 | 19 | 56 |
| `run-...-1-4067962528` | 3 | 29 | 19 | 48 |
| `run-...-1-4067962528` | 4 | 28 | 19 | 47 |
| `run-...-2-3422796657` | 1 | 53 | 21 | 74 |
| `run-...-2-3422796657` | 2 | 54 | 19 | 74 |
| `run-...-2-3422796657` | 3 | 32 | 19 | 51 |
| `run-...-2-3422796657` | 4 | 26 | 19 | 46 |
| `run-...-3-2298453710` | 1 | 58 | 21 | 79 |
| `run-...-3-2298453710` | 2 | 55 | 21 | 76 |
| `run-...-3-2298453710` | 3 | 56 | 21 | 77 |
| `run-...-3-2298453710` | 4 | 56 | 21 | 77 |

#### Cross-Run Averages

| Phase | Time (s) | vs. Baseline |
|---|---:|---|
| Pre phase | 42.67 | -6.75s (-13.7%) |
| Drained phase | 19.83 | +0.08s (+0.4%) |
| Full barrier | 62.75 | -7.00s (-10.0%) |
| Coordinator batch | 864.38 | -80.30s (-8.5%) |

The pre-phase improvement reflects the push-after-write cadence reducing the
number of stale deltas that need to be replicated before barrier entry. The
drained phase is essentially unchanged, which is expected: it is dominated by
cross-continent Tigris replication latency (iad-lhr-syd) rather than local
processing.

#### Failed Run Analysis

One run failed before the coverage gate fix:

- `run-20260215223738-1-3540465964`: snapshot cutover regression when manifest
  omitted a previously-synced site watermark. Clients replaced rows from an
  incomplete snapshot and skipped required log replay, causing convergence
  failure. Root cause: the `refreshFromSnapshotManifest` method accepted any
  manifest with a higher version number without verifying site coverage.
  **Fixed** by adding `manifestCoversKnownSites` in both `nodeClient.ts` and
  `browserClient.ts`.

### 8.10 Running the Stress Test

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
STRESS_COMPACTOR_SITE=site-a \
STRESS_COMPACTION_EVERY_OPS=30 \
npm run stress:fly:coordinator
```

The coordinator:
1. Creates a fresh bucket per run (`crdtbase-stress-run-...`)
2. Launches 3 Fly Machines via the Machines REST API
3. Orchestrates all barriers (all hard with `STRESS_HARD_BARRIER_EVERY=1`)
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

### 9.3 Additional E2E Suites

The test suite also includes:
- **Browser-HTTP E2E** (`browser-http.e2e.test.ts`): Validates the browser
  client against an HTTP-backed log
- **Browser-S3-MinIO E2E** (`browser-s3-minio.e2e.test.ts`): Browser client
  against MinIO S3 transport
- **Cross-backend parity** (`cross-backend-parity.prop.test.ts`): Property-based
  test verifying that all backend combinations produce identical results
- **Crash-restart** (`crash-restart.backends.prop.test.ts`): Property-based test
  for persistence correctness across simulated crashes

## 10. Issue Resolution Summary

All P0 and P1 issues are now resolved. The following table summarizes the
fixes and their verification status:

### P0 (Critical) -- All FIXED

| Issue | Problem | Fix | Verified By |
|---|---|---|---|
| P0-1 | PN-Counter double-application on crash | Atomic `state_bundle.bin` (temp + rename) | Stress test convergence |
| P0-2 | Non-atomic `state.bin`/`pending.bin`/`sync.bin` | Atomic bundle commit first, legacy files second | Crash-restart prop test |
| P0-3 | `FsSnapshotStore` CAS race | Filesystem lock + atomic rename | MinIO E2E compaction test |

### P1 (High) -- All FIXED

| Issue | Problem | Fix | Verified By |
|---|---|---|---|
| P1-1 | Browser HLC not persisted | `localStorage` persistence + HLC restore on open | Browser E2E test |
| P1-2 | Table composition not directly proved | `mergeTableRow_comm/assoc/idem_of_valid` in Lean | `lean/CrdtBase/Crdt/Table/Props.lean` |
| P1-3 | OR-Set idempotence precondition gap | `or_set_merge_canonicalized` + `or_set_merge_idem_general` | `lean/CrdtBase/Crdt/OrSet/Props.lean` |

### P2 (Medium) -- 4 of 8 FIXED

| Issue | Status | Fix |
|---|---|---|
| P2-1: OR-Set tombstone growth | FIXED | TTL pruning in compaction (default 7 days) |
| P2-2: MV-Register stale values | FIXED | `canonicalizeMvRegister` prunes dominated values |
| P2-3: Row tombstone TTL | FIXED | Compaction drops rows past configured TTL |
| P2-4: TS/Lean equivalence | MITIGATED | Unified SQL-script DRT entrypoint |
| P2-5: Network assumptions | Open | Documentation of S3 durability assumptions |
| P2-6: HLC real-time accuracy | FIXED | `createHlcClock()` with monotonic wall-clock + 60s drift rejection |
| P2-7: Orphaned segment cleanup | Open | -- |
| P2-8: Old delta cleanup | Open | -- |

## 11. The S3 Integrity Proxy (Planned)

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

## 12. Summary: Why This Design Works

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
   and reducing the number of S3 LIST/GET operations during pull. The
   compactor runs alongside workers in the stress test, validating that
   snapshot cutover preserves convergence.

5. **The barrier protocol handles verification**: The stress test's hard
   barriers with target head tracking and quiescence detection provide
   empirical proof that the system converges correctly under real
   multi-region conditions with high contention and concurrent compaction.

6. **Atomic persistence handles durability**: The atomic `state_bundle.bin`
   pattern (temp-file + rename) prevents the PN-Counter double-application
   bug and ensures crash recovery is always consistent.

7. **Snapshot coverage gates handle safety**: The `manifestCoversKnownSites`
   check prevents clients from applying partial snapshots that would drop
   rows and skip required log replay.

The fundamental insight is that Tigris's geo-replication is "good enough" for
the delta log: eventual consistency with a few hundred milliseconds of
cross-region latency. CRDTs tolerate this delay because merge is commutative,
associative, and idempotent. The only place strong consistency is needed is
the manifest CAS, which happens infrequently during compaction.

The stress test results confirm this empirically: 3/3 runs pass with average
wall time of 283.6s, barrier pre-phase averaging 42.67s and drained-phase
averaging 19.83s across iad/lhr/syd. The 8.6% improvement over the previous
baseline reflects the push-after-write / pull-before-read cadence reducing
stale-delta propagation time.
