# Testing Strategy

No traditional unit tests. Every test in this project is either a **property-based test**, a **differential test**, or a **model-based test**. If you find yourself writing `expect(add(2, 3)).toBe(5)`, stop — express it as a property instead.

## Tools

- **vitest** — test runner
- **@fast-check/vitest** — property-based testing integration
- **fast-check** — generators, arbitraries, shrinking, model-based testing (`fc.commands()`)
- **Lean 4 executable** — test oracle for differential testing (see LEAN.md)

```bash
npm install -D vitest @fast-check/vitest fast-check
```

## Isolated Checks (Recommended During Concurrent Lean Work)

When multiple agents are editing Lean files, prefer module-level builds and test-file runs over full builds:

```bash
# Build only specific Lean modules (proof files + oracle entrypoint)
cd lean
lake build \
  CrdtBase.Crdt.Lww.Props \
  CrdtBase.Crdt.PnCounter.Props \
  CrdtBase.Crdt.OrSet.Props \
  CrdtBase.Crdt.MvRegister.Props \
  CrdtBase.DiffTest.Main \
  CrdtBaseDRT
```

```bash
# Run only CRDT property tests
npx vitest run \
  test/properties/lww.prop.test.ts \
  test/properties/pnCounter.prop.test.ts \
  test/properties/orSet.prop.test.ts \
  test/properties/mvRegister.prop.test.ts \
  test/properties/invariants.prop.test.ts
```

```bash
# Run only differential oracle tests
npx vitest run \
  test/drt/lww.drt.test.ts \
  test/drt/pnCounter.drt.test.ts \
  test/drt/orSet.drt.test.ts \
  test/drt/mvRegister.drt.test.ts
```

For higher confidence without broad coupling, increase DRT runs:

```bash
DRT_NUM_RUNS=1000 DRT_TIMEOUT_MS=120000 npx vitest run test/drt/*.drt.test.ts

# Replay a specific SQL eval failing seed
DRT_NUM_RUNS=200 DRT_SEED=-1196022201 npx vitest run test/drt/sql-eval.drt.test.ts
```

---

## Testing Levels

### Level 0: Lean Proofs (Mathematical Certainty)

These properties are **theorems in Lean 4**, not tests. They are mechanically verified to hold for ALL inputs, not just sampled ones. See LEAN.md for the full specification.

| Property | Lean Theorem | Verified For |
|----------|-------------|--------------|
| Merge commutativity | `lww_merge_comm_of_consistent`, etc. | LWW (with invariant), PNCounter, ORSet, MVRegister |
| Merge associativity | `lww_merge_assoc_of_consistent`, etc. | LWW (with invariant), PNCounter, ORSet, MVRegister |
| Merge idempotency | `lww_merge_idem`, etc. | LWW, PNCounter, ORSet, MVRegister |
| HLC total order | `hlc_total_order` | All HLC values |
| HLC monotonicity | `hlc_now_monotonic`, `hlc_recv_monotonic` | now(), recv() |
| Convergence | `convergence_*` | All CRDT types under arbitrary network reordering |
| Compaction correctness | `compaction_preserves_state` | Fold-over-ops invariant |
| Tombstone semantics | `delete_wins_if_later`, etc. | Delete/write interaction |

**28 theorems total.** These are checked by `lake build CrdtBase` in CI. If any proof breaks, the build fails. No sampling, no flakiness, no false confidence.

Important note for LWW: commutativity/associativity require the event-consistency invariant. If two states share `(hlc, site)`, they must represent the same logical write (same payload).

### Level 1: Differential Random Testing (Implementation Matches Spec)

The Lean model is the test oracle. fast-check generates random inputs, both Lean and TypeScript process them, outputs must match. This catches bugs where the TypeScript code doesn't match the verified specification.

For LWW, generators should default to invariant-respecting states when testing semilattice properties. Add a separate adversarial suite that intentionally violates invariants to verify rejection/detection paths.

For SQL, differential tests generate **SQL text** and parse it once in TypeScript. The parsed AST is then fed to both implementations with shared context/state. Parser correctness stays covered at Level 2 (`parse/print/parse`), while Lean verifies semantic translation/planning/evaluation.

```typescript
import { test, fc } from '@fast-check/vitest';
import { spawnLeanOracle } from './drt-harness';

// Arbitrary generators for CRDT types
const arbHlc = fc.record({
  wallMs: fc.nat({ max: 2 ** 48 - 1 }),
  counter: fc.nat({ max: 65535 }),
});

// Note: HLC inputs must always respect the 48-bit wallMs and 16-bit counter bounds.

const arbSite = fc.hexaString({ minLength: 8, maxLength: 8 });

const arbLww = fc.record({
  val: fc.oneof(fc.string(), fc.integer(), fc.boolean(), fc.constant(null)),
  hlc: arbHlc,
  site: arbSite,
});

test.prop([arbLww, arbLww])(
  'DRT: LWW merge matches Lean oracle',
  async (a, b) => {
    const tsResult = lwwMerge(a, b);
    const leanResult = await leanOracle.lwwMerge(a, b);
    expect(tsResult).toEqual(leanResult);
  }
);

test.prop([fc.array(arbLww, { minLength: 2, maxLength: 20 })])(
  'DRT: LWW fold-merge matches Lean oracle regardless of order',
  async (states) => {
    const tsResult = states.reduce(lwwMerge);
    const leanResult = await leanOracle.foldMerge('lww', states);
    expect(tsResult).toEqual(leanResult);
  }
);
```

**DRT targets:**

| Target | Input Generator | Comparison |
|--------|----------------|------------|
| LWW merge | Two random LWW states | Merged state equality |
| PNCounter merge | Two random counters (random site maps) | Merged state + materialized value |
| ORSet merge | Two random OR-Sets with overlapping tags + tombstones | Merged elements and tombstones equality |
| MVRegister merge | Two random MV-Registers | Merged values equality |
| HLC compare | Two random HLCs + sites | Ordering equality |
| HLC now | Current state + wall clock | New HLC equality |
| HLC recv | Current state + remote HLC | New HLC equality (or null on drift/bounds rejection) |
| Apply ops sequence | Random op list, random order | Final state equality |
| Conflict guard | Same `(site, hlc, table, key, col)` with differing payloads | Must reject/quarantine |
| SQL write op generation | Random write SQL text + schema/site/HLC context (parsed once to AST) | Lean `sql_generate_ops` equals TS `generateCrdtOps` |
| SQL SELECT planner | Random SELECT SQL text + planner schema (parsed once to AST) | Lean `sql_build_select_plan` equals TS `buildSelectPlan` |
| SQL AST evaluation | Random SQL text + eval state + eval context (parsed once to AST) | Lean `sql_eval` equals TS `evaluateSqlAst` |

**Run configuration:**
- Local dev: 1,000 iterations per target (~10 seconds total)
- CI: 100,000 iterations per target (~5 minutes total)
- Nightly: 1,000,000 iterations per target

### Level 1.5: Invariant Enforcement Tests (Operational Safety)

These tests validate assumptions required by the Lean model but enforced in system code:

- `siteId` uniqueness guard: detect duplicate local `siteId` configuration in multi-replica test harness.
- HLC persistence across restart: after restart, next local HLC must be strictly greater than the persisted last HLC.
- Replay consistency: duplicate `(site, hlc, table, key, col)` with identical payload is accepted as idempotent.
- Conflict rejection: duplicate `(site, hlc, table, key, col)` with different payload is rejected and surfaced.
- Snapshot rollback fence: startup rejects local clock state older than durable high-water mark.

These are property tests and scenario tests, not Lean theorems, because they involve I/O and persistence semantics.

### Level 2: Property-Based Tests (Broader System Properties)

Properties that are NOT in Lean (because they involve I/O, encoding, or system integration) but are still expressed as universal properties over random inputs.

#### Encoding Round-Trips

```typescript
test.prop([arbDeltaFile])(
  'encode then decode is identity for delta files',
  (delta) => {
    const bytes = encodeDelta(delta);
    const decoded = decodeDelta(bytes);
    expect(decoded).toEqual(delta);
  }
);

test.prop([arbSegmentFile])(
  'encode then decode is identity for segment files',
  (segment) => {
    const bytes = encodeSegment(segment);
    const decoded = decodeSegment(bytes);
    expect(decoded).toEqual(segment);
  }
);

test.prop([arbManifest])(
  'encode then decode is identity for manifests',
  (manifest) => {
    const bytes = encodeManifest(manifest);
    const decoded = decodeManifest(bytes);
    expect(decoded).toEqual(manifest);
  }
);
```

#### SQL Parser Round-Trips

```typescript
const arbSelectStmt = fc.record({
  table: arbIdentifier,
  columns: fc.oneof(
    fc.constant('*'),
    fc.array(arbIdentifier, { minLength: 1, maxLength: 10 }),
  ),
  where: fc.option(arbWhereClause),
});

test.prop([arbSelectStmt])(
  'parse(print(ast)) = ast for SELECT statements',
  (stmt) => {
    const sql = printSelect(stmt);
    const parsed = parseSelect(sql);
    expect(parsed).toEqual(stmt);
  }
);
```

Generate arbitraries for each SQL statement type (CREATE TABLE, INSERT, UPDATE, SELECT, DELETE, INC/DEC, ADD/REMOVE). The parser and printer must be inverses.

#### Bloom Filter

```typescript
test.prop([fc.array(fc.string(), { minLength: 1, maxLength: 10000 })])(
  'bloom filter has no false negatives',
  (keys) => {
    const bloom = buildBloomFilter(keys);
    for (const key of keys) {
      expect(bloom.test(key)).toBe(true);
    }
  }
);

test.prop([
  fc.array(fc.string(), { minLength: 100, maxLength: 1000 }),
  fc.array(fc.string(), { minLength: 100, maxLength: 1000 }),
])(
  'bloom filter false positive rate is below 2%',
  (inserted, probes) => {
    const bloom = buildBloomFilter(inserted);
    const insertedSet = new Set(inserted);
    const falsePositives = probes.filter(p => !insertedSet.has(p) && bloom.test(p));
    const nonMembers = probes.filter(p => !insertedSet.has(p));
    if (nonMembers.length > 50) {
      expect(falsePositives.length / nonMembers.length).toBeLessThan(0.02);
    }
  }
);
```

#### Segment Ordering

```typescript
test.prop([fc.array(arbSegmentRow, { minLength: 2, maxLength: 500 })])(
  'segment rows are sorted by primary key after encoding',
  (rows) => {
    const segment = buildSegment('test', '_default', rows);
    const bytes = encodeSegment(segment);
    const decoded = decodeSegment(bytes);
    for (let i = 1; i < decoded.rows.length; i++) {
      expect(compareKeys(decoded.rows[i - 1].key, decoded.rows[i].key)).toBeLessThan(0);
    }
  }
);
```

#### HLC Drift Rejection

```typescript
test.prop([fc.nat(), fc.nat({ min: 61_000 })])(
  'HLC rejects wall clock drift exceeding 60 seconds',
  (localWall, drift) => {
    const remoteWall = localWall + drift;
    const remoteHlc = { wallMs: remoteWall, counter: 0 };
    expect(() => hlcRecv(localState, remoteHlc)).toThrow(/drift/);
  }
);
```

### Level 3: Model-Based Tests (Full System Simulation)

fast-check's `fc.commands()` API: define a simplified model and a set of commands. fast-check generates arbitrary command sequences, runs them against both the model and the real engine, and checks they always agree.

This is the most powerful testing technique for databases. It catches integration bugs that no amount of property testing on individual functions would find.

#### Engine vs. Simple Map Model

```typescript
// The "model" is just a Map<string, Map<string, any>>
// table -> (pk -> { col: value })
type Model = Map<string, Map<string, Record<string, any>>>;

class InsertCommand implements fc.AsyncCommand<Model, CrdtEngine> {
  constructor(
    readonly table: string,
    readonly key: string,
    readonly cols: Record<string, any>,
  ) {}

  check(model: Readonly<Model>) { return true; }

  async run(model: Model, engine: CrdtEngine) {
    // Apply to model
    if (!model.has(this.table)) model.set(this.table, new Map());
    model.get(this.table)!.set(this.key, this.cols);

    // Apply to engine
    await engine.exec(
      `INSERT INTO ${this.table} (id, ${Object.keys(this.cols).join(', ')}) ` +
      `VALUES (${sqlLiteral(this.key)}, ${Object.values(this.cols).map(sqlLiteral).join(', ')})`
    );

    // Compare
    const rows = await engine.query(
      `SELECT * FROM ${this.table} WHERE id = ${sqlLiteral(this.key)}`
    );
    expect(rows.length).toBe(1);
    for (const [col, val] of Object.entries(this.cols)) {
      expect(rows[0][col]).toEqual(val);
    }
  }
}

class UpdateCommand implements fc.AsyncCommand<Model, CrdtEngine> { /* ... */ }
class DeleteCommand implements fc.AsyncCommand<Model, CrdtEngine> { /* ... */ }
class SelectCommand implements fc.AsyncCommand<Model, CrdtEngine> { /* ... */ }

test('engine matches simple model under arbitrary command sequences', async () => {
  await fc.assert(
    fc.asyncProperty(
      fc.commands([
        arbInsertCommand(),
        arbUpdateCommand(),
        arbDeleteCommand(),
        arbSelectCommand(),
      ]),
      async (cmds) => {
        const model: Model = new Map();
        const engine = await createTestEngine();
        await engine.exec(
          'CREATE TABLE t (id STRING PRIMARY KEY, name LWW<STRING>, count COUNTER)'
        );
        await fc.asyncModelRun(() => ({ model, real: engine }), cmds);
      }
    ),
    { numRuns: 500 }
  );
});
```

When fast-check finds a failing command sequence, it **shrinks** it to the minimal reproduction — e.g., "INSERT followed by DELETE followed by SELECT returns wrong result." This is far more useful than a stack trace.

#### Multi-Site Convergence Simulation

The most important model-based test: simulate multiple sites, each performing random operations, syncing in random order, and verifying convergence.

```typescript
class SiteAction {
  constructor(
    readonly siteIndex: number,
    readonly action: 'write' | 'sync_push' | 'sync_pull',
    readonly writeOp?: { key: string; col: string; val: any },
  ) {}
}

test.prop([fc.array(arbSiteAction, { minLength: 10, maxLength: 200 })])(
  'all sites converge after full sync',
  async (actions) => {
    const sites = [createTestEngine(), createTestEngine(), createTestEngine()];
    const log = new MemoryReplicatedLog();

    // Execute random actions
    for (const action of actions) {
      const site = sites[action.siteIndex % sites.length];
      switch (action.action) {
        case 'write':
          await site.exec(
            `UPDATE t SET ${action.writeOp!.col} = ... WHERE ...`
          );
          break;
        case 'sync_push':
          await site.syncPush(log);
          break;
        case 'sync_pull':
          await site.syncPull(log);
          break;
      }
    }

    // Full sync: every site pushes then pulls until stable
    for (const site of sites) await site.syncPush(log);
    for (const site of sites) await site.syncPull(log);
    for (const site of sites) await site.syncPull(log); // second pass

    // All sites must have identical materialized state
    const states = await Promise.all(
      sites.map(s => s.query('SELECT * FROM t'))
    );
    expect(states[0]).toEqual(states[1]);
    expect(states[1]).toEqual(states[2]);
  }
);
```

#### Compaction Equivalence

```typescript
test.prop([fc.array(arbCrdtOp, { minLength: 5, maxLength: 100 })])(
  'state after compaction + remaining deltas equals state from all deltas',
  async (allOps) => {
    // Split ops at a random point
    const splitPoint = Math.floor(allOps.length / 2);
    const prefix = allOps.slice(0, splitPoint);
    const suffix = allOps.slice(splitPoint);

    // Path A: apply all ops directly
    const directState = applyAllOps(allOps);

    // Path B: compact prefix into segment, then apply suffix on top
    const compactedState = applyAllOps(prefix);
    const segmentBytes = encodeSegment(stateToSegment(compactedState));
    const loadedState = segmentToState(decodeSegment(segmentBytes));
    const finalState = applyOpsToState(loadedState, suffix);

    expect(materialize(finalState)).toEqual(materialize(directState));
  }
);
```

This tests the full compaction pipeline including encode/decode, not just the abstract merge.

---

## Test File Organization

```
test/
├── drt/
│   ├── harness.ts            # Spawns Lean executable, manages stdin/stdout
│   ├── lww.drt.test.ts       # DRT: LWW merge
│   ├── pnCounter.drt.test.ts
│   ├── orSet.drt.test.ts
│   ├── mvRegister.drt.test.ts
│   ├── compaction.drt.test.ts
│   ├── sql-generate-ops.drt.test.ts  # DRT: SQL text -> parsed AST -> CRDT ops
│   ├── sql-planner.drt.test.ts       # DRT: SQL text -> parsed AST -> SELECT planner output
│   └── sql-eval.drt.test.ts          # DRT: SQL text -> parsed AST -> eval result + next state
│
├── properties/
│   ├── arbitraries.ts        # All custom fast-check generators
│   ├── encoding.prop.test.ts # Round-trip properties
│   ├── sql-parser.prop.test.ts
│   ├── bloom.prop.test.ts
│   ├── segment.prop.test.ts
│   └── hlc.prop.test.ts
│
├── model/
│   ├── commands.ts           # fc.commands() definitions
│   ├── engine.model.test.ts  # Engine vs simple model
│   ├── convergence.model.test.ts  # Multi-site convergence
│   └── compaction.model.test.ts   # Compaction equivalence
│
└── fixtures/                 # Shared with Lean (JSON test vectors)
    ├── lww_merge_cases.json
    └── ...
```

---

## Generator Library (arbitraries.ts)

A shared file of composable fast-check generators used across all test levels.

```typescript
import fc from 'fast-check';

// Primitives
export const arbHlc = fc.record({
  wallMs: fc.nat({ max: 2 ** 48 - 1 }),
  counter: fc.nat({ max: 65535 }),
});

export const arbSiteId = fc.hexaString({ minLength: 8, maxLength: 8 });

export const arbScalar = fc.oneof(
  fc.string({ maxLength: 50 }),
  fc.integer({ min: -1_000_000, max: 1_000_000 }),
  fc.boolean(),
  fc.constant(null),
);

// CRDT states
export const arbLwwState = fc.record({
  val: arbScalar,
  hlc: arbHlc,
  site: arbSiteId,
});

export const arbPnCounterState = fc.record({
  inc: fc.dictionary(arbSiteId, fc.nat({ max: 10000 })),
  dec: fc.dictionary(arbSiteId, fc.nat({ max: 10000 })),
});

export const arbOrSetElement = fc.record({
  val: arbScalar,
  addHlc: arbHlc,
  addSite: arbSiteId,
});

export const arbOrSetState = fc.record({
  elements: fc.array(arbOrSetElement, { maxLength: 50 }),
});

// Operations
export const arbCrdtOp = fc.oneof(
  fc.record({
    type: fc.constant('lww_set' as const),
    tbl: fc.constant('t'),
    key: fc.string({ maxLength: 10 }),
    col: fc.constantFrom('name', 'status', 'priority'),
    hlc: arbHlc,
    site: arbSiteId,
    val: arbScalar,
  }),
  fc.record({
    type: fc.constant('counter_inc' as const),
    tbl: fc.constant('t'),
    key: fc.string({ maxLength: 10 }),
    col: fc.constant('count'),
    hlc: arbHlc,
    site: arbSiteId,
    val: fc.nat({ max: 100 }),
  }),
);

// SQL AST fragments
export const arbIdentifier = fc.stringMatching(/^[a-z][a-z0-9_]{0,15}$/);

export const arbWhereClause = fc.record({
  column: arbIdentifier,
  op: fc.constantFrom('=', '!=', '<', '>', '<=', '>='),
  value: arbScalar,
});

// File structures
export const arbDeltaFile = fc.record({
  v: fc.constant(1),
  site: arbSiteId,
  seq: fc.nat({ max: 999999 }),
  hlc_min: arbHlc.map(
    h => `0x${(BigInt(h.wallMs) * 65536n + BigInt(h.counter)).toString(16)}`
  ),
  hlc_max: arbHlc.map(
    h => `0x${(BigInt(h.wallMs) * 65536n + BigInt(h.counter)).toString(16)}`
  ),
  ops: fc.array(arbCrdtOp, { minLength: 1, maxLength: 50 }),
});

// Multi-site simulation
export const arbSiteAction = fc.record({
  siteIndex: fc.nat({ max: 2 }),
  action: fc.constantFrom('write', 'sync_push', 'sync_pull'),
  writeOp: fc.option(fc.record({
    key: fc.constantFrom('k1', 'k2', 'k3', 'k4', 'k5'),
    col: fc.constantFrom('name', 'status'),
    val: arbScalar,
  })),
});
```

---

## CI Configuration

```yaml
name: Test
on: [push, pull_request]

jobs:
  lean-proofs:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean4-action@v1
      - run: cd lean && lake build CrdtBase
      # If any proof has `sorry`, this fails

  lean-build-drt:
    runs-on: ubuntu-latest
    needs: lean-proofs
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean4-action@v1
      - run: cd lean && lake build CrdtBaseDRT
      - uses: actions/upload-artifact@v4
        with:
          name: lean-drt-executable
          path: lean/.lake/build/bin/CrdtBaseDRT

  tests:
    runs-on: ubuntu-latest
    needs: lean-build-drt
    steps:
      - uses: actions/checkout@v4
      - uses: oven-sh/setup-bun@v2
      - uses: actions/download-artifact@v4
        with:
          name: lean-drt-executable
          path: bin/
      - run: chmod +x bin/CrdtBaseDRT
      - run: bun install
      - run: bun test
        env:
          LEAN_DRT_BIN: bin/CrdtBaseDRT
          FC_NUM_RUNS: 100000

  nightly-deep-fuzz:
    runs-on: ubuntu-latest
    if: github.event_name == 'schedule'
    steps:
      # Same as tests but with FC_NUM_RUNS=1000000
      # and 6 hour timeout
```

---

## Handling DRT Without Lean Installed

During early development (before the Lean model exists), DRT tests are **skipped** gracefully:

```typescript
import { existsSync } from 'node:fs';

const leanAvailable =
  process.env.LEAN_DRT_BIN && existsSync(process.env.LEAN_DRT_BIN);

const drt = leanAvailable ? test : test.skip;

drt.prop([arbLww, arbLww])(
  'DRT: LWW merge matches Lean oracle',
  async (a, b) => { /* ... */ }
);
```

Property tests (Level 2) and model-based tests (Level 3) run without Lean. DRT tests (Level 1) require the Lean executable. This means you can develop and test the TypeScript implementation immediately, and the Lean verification layer slots in later without changing any test code.

---

## What "Passing" Means at Each Level

| Level | Passing Means | Confidence |
|-------|--------------|------------|
| **Level 0** (Lean proofs) | The *algorithm* is mathematically correct for ALL inputs | Absolute (up to Lean's kernel) |
| **Level 1** (DRT) | The TypeScript *implementation matches* the verified algorithm for 100K+ random inputs | Very high — bugs are in implementation, not algorithm |
| **Level 2** (Properties) | System *invariants hold* (round-trips, ordering, bloom correctness) for 10K+ random inputs | High — covers encoding, parsing, data structures |
| **Level 3** (Model-based) | The *integrated system behaves* like a simple model under arbitrary command sequences | High — catches integration bugs, ordering issues, state corruption |

A release requires all four levels to pass. Level 0 is checked at compile time. Levels 1-3 are checked at test time. A nightly deep-fuzz run at 1M iterations per target provides additional confidence.

---

## Level 4: End-to-End Storage/Replication Tests (Implemented)

This repository now includes end-to-end tests that exercise real persistence and transport paths with `.bin` files:

- `test/e2e/three-clients.e2e.test.ts`
- `test/e2e/s3-minio.e2e.test.ts`

These run in addition to Levels 0-3 and are focused on operational wiring correctness.

### E2E A: Filesystem-backed replication server

**Test file:** `test/e2e/three-clients.e2e.test.ts`

What it validates:

1. Three independent clients execute SQL and converge through the file-backed HTTP replicated log.
2. Clients persist local `schema.bin`, `state.bin`, `pending.bin`, and `sync.bin`.
3. Server persists replicated delta entries as MessagePack `.bin` files.
4. The CLI `dump` command can decode generated `.bin` files.

Core SQL sequence used in test:

```sql
CREATE TABLE tasks (
  id STRING PRIMARY KEY,
  title LWW<STRING>,
  points COUNTER,
  tags SET<STRING>,
  status REGISTER<STRING>
);

INSERT INTO tasks (id, title, points, tags, status)
VALUES ('t1', 'from-a', 0, 'alpha', 'open');

UPDATE tasks SET title = 'from-b', status = 'review' WHERE id = 't1';
INC tasks.points BY 3 WHERE id = 't1';
ADD 'beta' TO tasks.tags WHERE id = 't1';

UPDATE tasks SET title = 'from-c' WHERE id = 't1';
INC tasks.points BY 5 WHERE id = 't1';
ADD 'gamma' TO tasks.tags WHERE id = 't1';

REMOVE 'alpha' FROM tasks.tags WHERE id = 't1';

SELECT * FROM tasks WHERE id = 't1';
```

Expected converged row:

- `title = 'from-c'`
- `points = 8`
- `tags` contains `beta` and `gamma`
- `status` contains both `open` and `review`

### E2E B: Pre-signed S3 replication via MinIO

**Test file:** `test/e2e/s3-minio.e2e.test.ts`

What it validates:

1. Clients replicate through `PresignedS3ReplicatedLog` and fetch pre-signed requests from the pre-sign service.
2. Objects are written to `deltas/<site>/<seq>.delta.bin`.
3. Downloaded S3 objects can be inspected with `node cli.mjs dump`.
4. SQL convergence across three clients remains correct under S3 transport.

The test starts local MinIO + pre-sign services and creates a test bucket automatically.

### Commands: Run Again

Run filesystem e2e only:

```bash
npx vitest run test/e2e/three-clients.e2e.test.ts
```

Run S3/MinIO e2e only:

```bash
npx vitest run test/e2e/s3-minio.e2e.test.ts
```

Run all tests:

```bash
npm test
```

Run CLI dump manually on a `.bin` file:

```bash
npm run cli -- dump /path/to/file.bin
```

### MinIO Notes

On first run, the MinIO harness downloads a MinIO binary to a temp cache directory. Later runs reuse it. If download/startup is slow, run the S3 e2e test alone first.

The S3 e2e test timeout is set higher (`120s`) to tolerate first-run setup cost.
