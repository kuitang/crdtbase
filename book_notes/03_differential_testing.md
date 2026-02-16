# Differential Testing in crdtbase

## Overview

crdtbase employs a multi-level testing strategy where a Lean 4 theorem prover serves as a
mathematically verified oracle against which the TypeScript production implementation is
continuously compared. The project explicitly rejects traditional unit tests in favor of
property-based testing, differential random testing (DRT), and model-based testing
(see `/home/kuitang/git/crdtbase/TESTING.md`, line 3):

> No traditional unit tests. Every test in this project is either a **property-based test**,
> a **differential test**, or a **model-based test**. If you find yourself writing
> `expect(add(2, 3)).toBe(5)`, stop -- express it as a property instead.

The differential testing system compares two independent implementations of CRDT operations:

1. **TypeScript** (production code in `src/core/`)
2. **Lean 4** (verified specification in `lean/CrdtBase/`)

Both receive the same randomly generated inputs. If their outputs ever disagree, the test fails
and fast-check shrinks the failing input to a minimal reproduction.

---

## Architecture

### The Testing Pyramid

| Level | What | Confidence | Location |
|-------|------|-----------|----------|
| Level 0 | Lean proofs (28+ theorems) | Absolute (all inputs) | `lean/CrdtBase/**/Props.lean` |
| Level 1 | Differential Random Testing (DRT) | Very high (100K+ samples) | `test/drt/*.drt.test.ts` |
| Level 2 | Property-based tests (fast-check) | High (10K+ samples) | `test/properties/*.prop.test.ts` |
| Level 3 | Model-based tests (schema consistency, snapshot validation) | High (integration) | `test/properties/multisite-schema.prop.test.ts`, `clientSnapshotPull.prop.test.ts` |
| Level 4 | Stress tests (Fly.io multi-region with compaction) | High (real infra) | `test/stress/` |
| Level 5 | E2E (filesystem + S3/MinIO, three-client chaos) | Operational | `test/e2e/*.e2e.test.ts` |

DRT sits at Level 1 -- it verifies that the TypeScript implementation _matches_ the
mathematically proven Lean specification for a large random sample of inputs. Levels 2-3
cover system aspects beyond Lean's scope: encoding round-trips, SQL parsing, snapshot pull
convergence, schema replication, and TTL-based retention. Level 4 stress tests run on Fly.io
infrastructure with real multi-region replication and compaction.

### Unified Architecture: sql_script_eval

A key architectural decision is the unification of all DRT endpoints. The Lean oracle now
exposes a single `sql_script_eval` endpoint that executes full SQL statement sequences
end-to-end. All CRDT-specific DRT tests (LWW, PN-Counter, OR-Set, MV-Register) generate
SQL scripts that exercise the target CRDT type, rather than sending raw merge structures to
individual Lean handlers:

```
   Test generates SQL scripts
          |
          v
   TypeScript: parseSql -> evaluateSqlScriptTs (statements[])
          |
          v                              Lean: handleSqlScriptEval
   Both receive same AST statements  ->  loops over statements
   Both produce outcomes[] + nextState    applying ops to rows
          |                              tracking HLC consumption
          v
   Normalize both outputs
   Compare for equality
```

The three remaining non-SQL endpoints are the replication log operations (`listSites`,
`getHead`, `readSince`), which model pure log semantics independent of SQL evaluation.

### File Layout

```
test/drt/
  harness.ts                            # IPC client: spawns Lean binary, manages stdin/stdout JSON protocol
  sql-script-utils.ts                   # 322 lines: state conversion, normalization, TS script executor
  lww.drt.test.ts                       # DRT: LWW via SQL UPDATE/SELECT script sequences
  pnCounter.drt.test.ts                 # DRT: PN-Counter via SQL INC/DEC/SELECT script sequences
  orSet.drt.test.ts                     # DRT: OR-Set via SQL ADD/REMOVE/SELECT script sequences
  mvRegister.drt.test.ts                # DRT: MV-Register via SQL UPDATE/SELECT script sequences
  compaction.drt.test.ts                # DRT: SQL script split law (all split points)
  sql-generate-ops.drt.test.ts          # DRT: SQL write -> CRDT ops generation via sql_script_eval
  sql-planner.drt.test.ts              # DRT: SQL SELECT -> query plan via sql_script_eval
  sql-eval.drt.test.ts                 # DRT: full SQL AST evaluation (single + multi-statement)
  replication-log-endpoints.drt.test.ts # DRT: S3 log listSites/getHead/readSince
```

The 11 DRT test files exercise 10 differential targets:

1. LWW merge (via SQL script pipeline)
2. PN-Counter merge (via SQL script pipeline)
3. OR-Set merge (via SQL script pipeline)
4. MV-Register merge (via SQL script pipeline)
5. SQL script split law (compaction correctness)
6. SQL write op generation
7. SQL SELECT query planner
8. SQL single-statement evaluation
9. SQL multi-statement sequence evaluation
10. Replication log `listSites`/`getHead`/`readSince`

---

## How the Lean Oracle Works

### Lean Binary Compilation

The Lean project is at `/home/kuitang/git/crdtbase/lean/`. The lake configuration
(`/home/kuitang/git/crdtbase/lean/lakefile.toml`) defines two build targets:

```toml
[[lean_lib]]
name = "CrdtBase"

[[lean_exe]]
name = "CrdtBaseDRT"
root = "CrdtBase.DiffTest.Main"
```

- `CrdtBase` -- the library containing all CRDT definitions, proofs, SQL semantics, and
  replication definitions. Building this type-checks all theorems.
- `CrdtBaseDRT` -- a standalone executable whose entry point is
  `/home/kuitang/git/crdtbase/lean/CrdtBase/DiffTest/Main.lean`. This is the test oracle.

The build: `cd lean && lake build CrdtBase CrdtBaseDRT` (or `npm run lean:build`).
Binary lands at `lean/.lake/build/bin/CrdtBaseDRT`.

### The Lean Oracle Protocol (stdin/stdout JSON-line IPC)

The oracle is a long-running process that reads one JSON object per line from stdin and writes
one JSON object per line to stdout. From Main.lean, lines 1019-1037:

```lean
partial def loop (stdin : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then pure ()
  else
    let trimmed := line.trimAscii
    if trimmed.isEmpty then loop stdin
    else
      match handleLine trimmed.copy with
      | Except.ok out => emitLine out
      | Except.error err =>
          emitLine <| (Json.mkObj [("error", toJson err)]).compress
      loop stdin
```

The `handleLine` dispatcher (lines 1003-1011) is consolidated to four endpoints:

```lean
def handleLine (line : String) : Except String String := do
  let json ← Json.parse line
  let typ ← json.getObjValAs? String "type"
  match typ with
  | "sql_script_eval"        => handleSqlScriptEval json
  | "replication_list_sites" => handleReplicationListSites json
  | "replication_get_head"   => handleReplicationGetHead json
  | "replication_read_since" => handleReplicationReadSince json
  | _                        => throw s!"unsupported command: {typ}"
```

The previous architecture had separate endpoints for each CRDT merge type (`lww_merge`,
`pn_merge`, `or_set_merge`, `mv_merge`), plus separate `sql_eval`, `sql_generate_ops`, and
`sql_build_select_plan` handlers. All have been unified into `sql_script_eval`.

### The sql_script_eval Endpoint

The heart of the oracle (`/home/kuitang/git/crdtbase/lean/CrdtBase/DiffTest/Main.lean`,
lines 940-973):

```lean
def handleSqlScriptEval (json : Json) : Except String String := do
  let cmd : SqlScriptEvalCmd ← fromJson? json
  let schema := cmd.context.schema
  let rows ← normalizeEvalRows cmd.state.rows
  let rec loop
      (currentRows : List EvalRow)
      (remainingHlc : Option (List String))
      (statements : List Json)
      (acc : List Json)
      : Except String (List Json × List EvalRow) := do
    match statements with
    | [] => pure (acc.reverse, currentRows)
    | statement :: tail =>
        let (result, nextRows, consumedHlc) ← runSqlEvalStatement
          statement schema cmd.context.site remainingHlc cmd.context.removeTags currentRows
        let nextHlc := match remainingHlc with
          | some values => some (values.drop consumedHlc)
          | none => none
        loop nextRows nextHlc tail (result :: acc)
  let (outcomes, nextRows) ← loop rows cmd.context.hlcSequence cmd.statements []
  -- ...returns {outcomes, nextState: {schema, rows}}
```

Key design aspects:
- **Sequential execution:** Each statement runs against accumulated state from prior statements
- **HLC consumption tracking:** Write statements advance the HLC cursor by `consumedHlc`
- **Unified SELECT/write dispatch:** `runSqlEvalStatement` routes on `kind` field
- **Input:** `SqlScriptEvalCmd` takes `statements: List Json`, `context: SqlEvalContextCmd`,
  `state: SqlEvalStateCmd`

---

## The TypeScript Harness

### LeanDrtClient

`/home/kuitang/git/crdtbase/test/drt/harness.ts` (109 lines) implements the IPC client.

**Binary discovery** (lines 34-41):

```typescript
static findBinary(): string | null {
  const explicit = process.env.LEAN_DRT_BIN;
  if (explicit && existsSync(explicit)) {
    return explicit;
  }
  const fallback = 'lean/.lake/build/bin/CrdtBaseDRT';
  return existsSync(fallback) ? fallback : null;
}
```

**Process spawning** (lines 14-32): The Lean process is spawned once per `describe` block
(in `beforeAll`) and killed in `afterAll`. A FIFO queue of pending promises maps each
request to its response line.

**Request/Response** (lines 43-62):

```typescript
async send<T>(payload: unknown): Promise<T> {
  return new Promise((resolve, reject) => {
    this.pending.push({
      resolve: (line) => {
        const parsed = JSON.parse(line) as T & { error?: string };
        if (typeof parsed.error === 'string') {
          reject(new Error(parsed.error));
          return;
        }
        resolve(parsed);
      },
      reject,
    });
    this.proc.stdin.write(`${JSON.stringify(payload)}\n`);
  });
}
```

**Convenience methods** (lines 64-95):

```typescript
async sqlScriptEval<T>(statements: unknown, context: unknown, state: unknown): Promise<T> {
  return this.send<T>({ type: 'sql_script_eval', statements, context, state });
}
async replicationListSites<T>(entries: unknown): Promise<T> { ... }
async replicationGetHead<T>(entries: unknown, siteId: string): Promise<T> { ... }
async replicationReadSince<T>(entries: unknown, siteId: string, since: number): Promise<T> { ... }
```

Every DRT test file uses the graceful skip pattern:

```typescript
const leanBin = LeanDrtClient.findBinary();
const drt = leanBin ? test : test.skip;
```

---

## SQL Script Utilities

`/home/kuitang/git/crdtbase/test/drt/sql-script-utils.ts` (322 lines) provides the shared
infrastructure for all SQL-based DRT tests.

### Wire Format Types

Defines `LeanSchema`, `LeanEvalState`, and `LeanScriptEvalOutcome` types that mirror the
Lean-side structures. The CRDT column state uses numeric type tags:

| Tag | CRDT Type | Fields |
|-----|-----------|--------|
| 1 | LWW | `val: unknown`, `hlc: string`, `site: string` |
| 2 | PN-Counter | `inc: Array<{site, n}>`, `dec: Array<{site, n}>` |
| 3 | OR-Set | `elements: Array<{val, hlc, site}>`, `tombstones: Array<{hlc, site}>` |
| 4 | MV-Register | `values: Array<{val, hlc, site}>` |

### State Conversion

- `toLeanSchema` (lines 204-214): converts TS nested Records to Lean's List-based format
- `toLeanState` (lines 234-259): converts PN-Counter `Record<string, number>` to
  `List {site, n}` for Lean
- `fromLeanState` (lines 261-284): reverse conversion from Lean response to TS format

### Normalization

Extensive normalization handles non-deterministic output:
- `normalizeJsonObject` -- recursive deep sort of all object keys
- `normalizeColumnState` -- per-CRDT-type element/value sorting
- `normalizeState` -- full schema + row normalization
- `normalizeResult` -- read result row sorting
- `normalizeScriptExecution` -- wraps everything for multi-statement sequences

### TypeScript Script Executor

`evaluateSqlScriptTs` (lines 286-321) mirrors the Lean `handleSqlScriptEval`:

```typescript
export function evaluateSqlScriptTs(
  statements: SqlStatement[],
  input: { state: SqlEvalState; context: SqlEvalContext },
): { outcomes: SqlEvalOutcome['result'][]; nextState: SqlEvalState } {
  let state = input.state;
  let consumedHlc = 0;
  const outcomes: SqlEvalOutcome['result'][] = [];
  for (const statement of statements) {
    const outcome = evaluateSqlAst(statement, {
      state,
      context: { schema: state.schema, site: input.context.site,
                 hlcSequence: input.context.hlcSequence?.slice(consumedHlc),
                 removeTags: input.context.removeTags },
    });
    outcomes.push(outcome.result);
    if (outcome.result.kind === 'write') consumedHlc += outcome.result.ops.length;
    state = outcome.nextState;
  }
  return { outcomes, nextState: state };
}
```

---

## Test Case Generation

All random data is generated by `fast-check` with `@fast-check/vitest`. Test cases are
randomly sampled and automatically shrunk on failure.

### Core Arbitraries

From `/home/kuitang/git/crdtbase/test/properties/arbitraries.ts`:

```typescript
export const arbHlc = (): fc.Arbitrary<Hlc> =>
  fc.record({
    wallMs: fc.nat({ max: HLC_LIMITS.wallMsMax - 1 }),  // max 2^48 - 1
    counter: fc.nat({ max: HLC_LIMITS.counterMax - 1 }), // max 2^16 - 1
  });

export const arbSiteId = (): fc.Arbitrary<string> =>
  fc.hexaString({ minLength: 8, maxLength: 8 });
```

### SQL Script Arbitraries

Each CRDT-focused DRT test generates SQL scripts specific to its type. The LWW test
(`/home/kuitang/git/crdtbase/test/drt/lww.drt.test.ts`, lines 23-26) generates UPDATE
sequences; the PN-Counter test generates INC/DEC steps; the OR-Set test generates ADD/REMOVE
steps; the MV-Register test generates UPDATE steps with mv_register columns.

### SQL Eval and Trace Generators

1. `/home/kuitang/git/crdtbase/test/properties/sql.generators.ts` -- generates
   `GeneratedWriteOpsCase` with `sql`, `schema`, `site`, `hlcSequence`, `removeTags`,
   and `expectedOps`.

2. `/home/kuitang/git/crdtbase/test/properties/sql-eval.generators.ts` -- generates
   `GeneratedSqlEvalCase` (single statement) and `GeneratedSqlEvalTraceCase`
   (multi-statement sequence).

All SQL generators produce syntactically valid SQL by construction.

---

## What Each DRT Test Compares

### 1-4. CRDT-Specific SQL Script Tests

**Files:** `lww.drt.test.ts`, `pnCounter.drt.test.ts`, `orSet.drt.test.ts`,
`mvRegister.drt.test.ts`

Each generates a CRDT-specific SQL script (e.g., UPDATE for LWW, INC/DEC for PN-Counter,
ADD/REMOVE for OR-Set, UPDATE for MV-Register), ending with a SELECT. Both TS
`evaluateSqlScriptTs` and Lean `sql_script_eval` receive the same parsed AST statements,
schema, site, and HLC sequence. Normalized outcomes + nextState are compared.

```typescript
drt
  .prop([arbLwwSqlCase], { numRuns: drtRuns })
  ('LWW-focused SQL scripts match Lean and TypeScript', async (input) => {
    const sqlStatements = input.values.map(
      (value) => `UPDATE tasks SET title = ${renderLiteral(value)} WHERE id = 'task-1'`,
    );
    sqlStatements.push("SELECT title FROM tasks WHERE id = 'task-1'");
    // ... parse, evaluate in both, normalize, compare
  }, drtTimeoutMs);
```

### 5. SQL Script Split Law (Compaction)

**File:** `/home/kuitang/git/crdtbase/test/drt/compaction.drt.test.ts`

For any sequence of SQL statements and any split point `k`:

> Executing the full list equals executing prefix `[0..k)` then suffix `[k..]` from
> the prefix's resulting state. Must hold in BOTH TypeScript and Lean.

```typescript
for (const splitIndex of splitPoints(statements.length)) {
  const prefix = statements.slice(0, splitIndex);
  const suffix = statements.slice(splitIndex);
  const tsPrefix = evaluateSqlScriptTs(prefix, { state, context });
  const tsSuffix = evaluateSqlScriptTs(suffix, {
    state: tsPrefix.nextState,
    context: { ...context, hlcSequence: context.hlcSequence?.slice(consumedHlc(tsPrefix.outcomes)) },
  });
  expect(normalizeExecution(mergeExecutions(tsPrefix, tsSuffix))).toEqual(normalizeExecution(directTs));
  // same for Lean
}
```

The split law verification checks ALL `n+1` split points for a list of length `n`
(lines 34-36):

```typescript
function splitPoints(length: number): number[] {
  return Array.from({ length: length + 1 }, (_, index) => index);
}
```

HLC sequence consumption is tracked across the split boundary -- the suffix receives only
the unconsumed portion, mirroring how compaction boundaries work in production.

### 6. SQL Write Op Generation

**File:** `/home/kuitang/git/crdtbase/test/drt/sql-generate-ops.drt.test.ts`

Three-way comparison: `tsOps == expectedOps`, `lean.result.outcomes[0].ops == expectedOps`,
`lean.result.outcomes[0].ops == tsOps`. The `expectedOps` are pre-computed by the generator,
making this a _triple_ differential test.

### 7. SQL SELECT Query Planner

**File:** `/home/kuitang/git/crdtbase/test/drt/sql-planner.drt.test.ts`

Sends parsed SELECT via `sql_script_eval` with empty state. Compares TypeScript
`buildSelectPlan` with Lean's plan (from `outcome.select`) and pre-computed `expectedPlan`.

### 8-9. SQL Full Evaluation (Single + Multi-Statement)

**File:** `/home/kuitang/git/crdtbase/test/drt/sql-eval.drt.test.ts`

Two sub-tests:

- **Single-statement** (lines 35-89): Random SQL + random initial state + eval context.
  Wraps in single-element array for `sql_script_eval`.
- **Multi-statement** (lines 91-147): Generates a trace of statements executed sequentially.
  Exercises full pipeline with HLC consumption tracking.

**Error agreement**: If TypeScript throws, Lean must also throw:

```typescript
if (tsError) {
  await expect(client!.sqlScriptEval<...>(...)).rejects.toThrow();
  return;
}
```

**Seed replay**: `DRT_NUM_RUNS=200 DRT_SEED=-1196022201 npx vitest run test/drt/sql-eval.drt.test.ts`

### 10. Replication Log Endpoints

**File:** `/home/kuitang/git/crdtbase/test/drt/replication-log-endpoints.drt.test.ts`

- **Input:** Random entries (site-a/b/c, seq 1-30), random query site, random `since`, random
  S3 page size (1-4)
- **Uses:** `InMemoryS3ReaderClient` (lines 34-106) simulating S3 pagination in-process
- **Comparison:** `listSites()`, `getHead(siteId)`, `readSince(siteId, since)` against Lean

---

## Wire Format and Data Marshaling

### HLC Hex Canonicalization

Both sides canonicalize HLC hex strings to strip leading zeros. From
`/home/kuitang/git/crdtbase/lean/CrdtBase/Sql/Defs.lean`, lines 253-261:

```lean
def canonicalizeHlcHex (raw : String) : String :=
  let withoutPrefix :=
    if raw.startsWith "0x" || raw.startsWith "0X" then raw.drop 2 else raw
  let trimmed := (withoutPrefix.dropWhile (fun ch => ch = '0')).toString
  let body := if trimmed.isEmpty then "0" else trimmed
  s!"0x{body}"
```

Used pervasively in the Lean oracle -- `EvalOrElement`, `EvalMvValue`, `EvalColumnState.lww`,
and OR-Set tombstones all canonicalize on ingest (Main.lean, lines 111-116, 135-140,
163-167, 174-175). Ensures `0x00ff`, `0x0ff`, `0xff`, and `0xFF` all normalize to `0xff`.

### PN-Counter Map/List Conversion

TypeScript uses `Record<string, number>` (JS object); Lean uses `List PnEntryJson` (sorted
list of `{site, n}` pairs). `toLeanState` and `fromLeanState` in `sql-script-utils.ts`
handle the bidirectional conversion.

### SQL Eval Context Wire Format

The `SqlScriptEvalCmd` (Main.lean, lines 231-236):

```lean
structure SqlScriptEvalCmd where
  type : String
  statements : List Json
  context : SqlEvalContextCmd    -- schema, site?, hlcSequence?, removeTags?
  state : SqlEvalStateCmd        -- rows with full CRDT column states
  deriving FromJson
```

---

## Property-Based and Model-Based Tests

### Compaction Retention

**File:** `/home/kuitang/git/crdtbase/test/properties/compactionRetention.prop.test.ts`
(100 lines)

Two properties validating TTL-based pruning:
1. Row tombstones older than `rowTombstoneTtlMs` are dropped; recent ones retained
2. OR-Set tombstones older than `orSetTombstoneTtlMs` are pruned independently

```typescript
test.prop(
  [fc.integer({ min: 10_000, max: 1_000_000 }), fc.integer({ min: 1, max: 10_000 })],
  { numRuns: 40 },
)('row tombstones older than TTL are dropped during compaction', (nowMs, ttlMs) => {
  // ... pruneRuntimeRowsForCompaction, verify old gone / recent kept
});
```

### Client Snapshot Pull

**File:** `/home/kuitang/git/crdtbase/test/properties/clientSnapshotPull.prop.test.ts`
(465 lines)

Tests the manifest coverage gate for both Node and Browser clients. Five properties:

1. **Node client compacted prefix + tail deltas** -- compacts a random prefix, then verifies
   a fresh client loading snapshot + remaining log equals full-log replay
2. **Browser client compacted prefix + tail deltas** -- same for BrowserCrdtClient
3. **Node client ignores manifest missing previously synced site watermark** -- corrupt
   manifest with missing site is rejected; client continues from prior state
4. **Browser client ignores manifest missing previously synced site watermark** -- same
5. **Node pull preserves pending local writes across snapshot refresh** -- local writes
   survive a snapshot refresh during pull

Uses `InMemorySnapshotStore` (with read counters) and `InMemoryReplicatedLog`.

### Multi-Site Schema Replication

**File:** `/home/kuitang/git/crdtbase/test/properties/multisite-schema.prop.test.ts`
(238 lines)

Tests distributed schema consistency with deterministic conflict rejection. A single
property test with 20 runs:

1. A randomly chosen schema owner creates a table
2. A non-owner inserts a row (verifying schema propagation without local CREATE)
3. Multiple sites concurrently add unique columns
4. Two sites attempt conflicting `ADD COLUMN` with different CRDT types
5. After all syncs, all three sites must have identical `information_schema.columns`
6. The conflicting column resolves to the first definition (first-write-wins)
7. SELECT results are identical across all sites

```typescript
test.prop([fc.integer()], { numRuns: 20 })(
  'schema propagates without local CREATE and concurrent ADD COLUMN converges',
  async (rawSeed) => {
    // ... creates 3 NodeCrdtClient instances on a shared InMemoryReplicatedLog
    // ... exercises CREATE TABLE, INSERT, ADD COLUMN, concurrent conflict
    // ... verifies all 3 sites converge to identical schema and data
  },
);
```

---

## Run Configuration

### Environment Variables

| Variable | Default | Purpose |
|----------|---------|---------|
| `LEAN_DRT_BIN` | `lean/.lake/build/bin/CrdtBaseDRT` | Path to oracle binary |
| `DRT_NUM_RUNS` | 50 (basic), 15 (compaction) | Iterations per property |
| `DRT_TIMEOUT_MS` | 30000 (basic), 45000 (compaction) | Per-property timeout |
| `DRT_SEED` | undefined | Replay a specific fast-check seed |

### Commands

```bash
# Quick local run (50 iterations per target)
npx vitest run test/drt/*.drt.test.ts

# Higher confidence
DRT_NUM_RUNS=1000 DRT_TIMEOUT_MS=120000 npx vitest run test/drt/*.drt.test.ts

# Full build + all tests
npm run test:all

# Replay a failing seed
DRT_NUM_RUNS=200 DRT_SEED=-1196022201 npx vitest run test/drt/sql-eval.drt.test.ts
```

---

## CI Pipeline

**File:** `/home/kuitang/git/crdtbase/.github/workflows/ci.yml`

A single job on `ubuntu-latest` (120-minute timeout):

1. **Checkout + Node 22 + npm ci**
2. **Build Lean proofs and DRT oracle** via `leanprover/lean-action@v1` with Mathlib cache
3. **Verify binary** -- `test -x lean/.lake/build/bin/CrdtBaseDRT`
4. **Resolve Chromium** for Playwright e2e tests
5. **Run test suite** -- `npm test` with `LEAN_DRT_BIN` env var set

---

## Edge Cases and Failure Modes

### Lean-Side Op Application

The Lean oracle applies CRDT ops to a full row state via `applyOpToRows`
(Main.lean, lines 608-715), handling all four CRDT types:

- **LWW (typ 1):** `mergeLwwValue` validates event consistency and keeps the winner
- **PN-Counter (typ 2):** Parses `{d, n}` and calls `setPnNat` to increment site counter
- **OR-Set (typ 3):** Handles `add`/`rmv`; both go through `normalizeOrSetState`
- **MV-Register (typ 4):** Appends value; `normalizeMvState` dedupes and filters dominated

### HLC Bounds

The Lean `Hlc` structure carries proof obligations (from
`/home/kuitang/git/crdtbase/lean/CrdtBase/Hlc/Defs.lean`):

```lean
structure Hlc where
  wallMs : Nat
  counter : Nat
  wallMs_lt : wallMs < wallMsMax    -- proof that wallMs < 2^48
  counter_lt : counter < counterMax -- proof that counter < 2^16
```

The DRT oracle validates these bounds when converting from JSON (Main.lean, lines 249-252):

```lean
def toHlc (h : HlcJson) : Except String Hlc := do
  match Hlc.mk? h.wallMs h.counter with
  | some hlc => pure hlc
  | none => throw s!"invalid HLC bounds: {h.wallMs} {h.counter}"
```

The TypeScript arbitrary generates within bounds by construction:

```typescript
wallMs: fc.nat({ max: HLC_LIMITS.wallMsMax - 1 }),
counter: fc.nat({ max: HLC_LIMITS.counterMax - 1 }),
```

### SQL Eval Error Agreement

The SQL eval DRT handles the case where TypeScript throws an error by verifying that Lean
also throws (sql-eval.drt.test.ts, lines 54-68). This ensures both implementations reject
the same invalid inputs (e.g., column type mismatches, missing primary keys, write statements
without site context).

### Normalization for Non-Deterministic Output

Both implementations may produce structurally equivalent but differently ordered output.
The `sql-script-utils.ts` file has approximately 200 lines of normalization code to handle:

- JSON object key ordering
- PN-Counter map-vs-list representation
- OR-Set element and tombstone ordering
- MV-Register value ordering
- HLC hex canonicalization (e.g., `0x00ff` vs `0xff`)
- Read result row ordering
- Multi-statement outcome ordering

This normalization is applied symmetrically to both TS and Lean outputs before comparison.

### S3 Pagination Simulation

The replication log DRT test includes a full `InMemoryS3ReaderClient` (106 lines) that
simulates S3's `ListObjectsV2` pagination behavior, including:
- Page size limiting with continuation tokens
- Delimiter-based prefix grouping (for `listSites`)
- `GetObjectCommand` with 404 error simulation
- Random page sizes (1-4) to stress pagination boundary handling

---

## Lean-side Implementation Details

### State Row Operations

The Lean oracle maintains a `List EvalRow` where each row has a table name, key, and
list of `EvalColumn` entries. `upsertColumnState` (Main.lean, lines 516-525) replaces or
appends a column; `upsertRow` (lines 527-537) replaces or appends a row in the list.

### SELECT Materialization

`materializeRow` (Main.lean, lines 717-736) converts CRDT column states to user-visible JSON:
- LWW: returns the current value
- PN-Counter: `sum(inc) - sum(dec)` (as integer)
- OR-Set: array of visible (non-tombstoned) element values, deduplicated
- MV-Register: single value if one entry, array if multiple concurrent values

### Replication Log Model

From `/home/kuitang/git/crdtbase/lean/CrdtBase/Replication/Defs.lean`:

Pure functional model. `readSince` filters entries for a site, then takes only the
_contiguous_ sequence starting from `since + 1`:

```lean
def readSince (entries : List LogEntry) (siteId : String) (since : Nat) : List Nat :=
  let seqs := (canonicalSeqs entries siteId).filter (fun seq => seq > since)
  takeContiguousFrom (since + 1) seqs
```

---

## Summary

The crdtbase testing system is a six-layer architecture:

1. **Lean 4 proofs** guarantee mathematical correctness for ALL inputs
2. **DRT tests** verify TypeScript matches the Lean specification for large random samples
3. **Property-based tests** cover encoding, SQL parsing, CRDT properties, TTL retention
4. **Model-based tests** validate snapshot pull convergence, manifest coverage gates,
   distributed schema replication with conflict resolution
5. **Stress tests** exercise multi-region replication with compaction on Fly.io
6. **E2E tests** run the full client lifecycle with filesystem, S3, and three-client chaos

The DRT system is unified around `sql_script_eval`, which executes full SQL statement
sequences against the Lean oracle. This means the oracle tests the SAME integrated code path
as production -- SQL parsing, CRDT op generation, state application, HLC consumption tracking,
and SELECT materialization. The system exercises 11 DRT test files spanning CRDT-specific SQL
scripts, compaction split law, write op generation, query planning, single and multi-statement
evaluation, and replication log semantics. All test cases are randomly generated by `fast-check`,
with automatic shrinking on failure and seed replay support for debugging.
