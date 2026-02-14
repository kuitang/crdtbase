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
| Level 0 | Lean proofs (28 theorems) | Absolute (all inputs) | `lean/CrdtBase/**/Props.lean` |
| Level 1 | Differential Random Testing (DRT) | Very high (100K+ samples) | `test/drt/*.drt.test.ts` |
| Level 1.5 | Invariant enforcement | High | `test/properties/invariants.prop.test.ts` |
| Level 2 | Property-based tests | High (10K+ samples) | `test/properties/*.prop.test.ts` |
| Level 3 | Model-based tests (fc.commands) | High (integration) | Described in TESTING.md |
| Level 4 | E2E (filesystem + S3/MinIO) | Operational | `test/e2e/*.e2e.test.ts` |

DRT sits at Level 1 -- it verifies that the TypeScript implementation _matches_ the
mathematically proven Lean specification for a large random sample of inputs.

### File Layout

```
test/drt/
  harness.ts                          # IPC client: spawns Lean binary, manages stdin/stdout JSON protocol
  lww.drt.test.ts                     # DRT: LWW merge
  pnCounter.drt.test.ts               # DRT: PN-Counter merge
  orSet.drt.test.ts                   # DRT: OR-Set merge
  mvRegister.drt.test.ts              # DRT: MV-Register merge
  compaction.drt.test.ts              # DRT: compaction split-law (all 4 CRDT types)
  sql-generate-ops.drt.test.ts        # DRT: SQL write -> CRDT ops generation
  sql-planner.drt.test.ts             # DRT: SQL SELECT -> query plan
  sql-eval.drt.test.ts                # DRT: full SQL AST evaluation with state
  replication-log-endpoints.drt.test.ts # DRT: S3 log listSites/getHead/readSince
```

---

## How the Lean Oracle Works

### Lean Binary Compilation

The Lean project is at `/home/kuitang/git/crdtbase/lean/`. The lake configuration
(`/home/kuitang/git/crdtbase/lean/lakefile.toml`, lines 18-24) defines two build targets:

```toml
[[lean_lib]]
name = "CrdtBase"

[[lean_exe]]
name = "CrdtBaseDRT"
root = "CrdtBase.DiffTest.Main"
```

- `CrdtBase` -- the library containing all CRDT definitions, proofs, SQL semantics, and
  replication definitions. Building this type-checks all 28 theorems.
- `CrdtBaseDRT` -- a standalone executable whose entry point is
  `/home/kuitang/git/crdtbase/lean/CrdtBase/DiffTest/Main.lean`. This is the test oracle.

The build command is:

```bash
cd lean && lake build CrdtBase CrdtBaseDRT
```

Or via npm:

```bash
npm run lean:build
# which expands to: cd lean && lake build CrdtBase CrdtBaseDRT
```

The resulting binary lands at `lean/.lake/build/bin/CrdtBaseDRT`.

### The Lean Oracle Protocol (stdin/stdout JSON-line IPC)

The oracle is a long-running process that reads one JSON object per line from stdin and writes
one JSON object per line to stdout. This avoids the overhead of spawning a new process per test
case.

From `/home/kuitang/git/crdtbase/lean/CrdtBase/DiffTest/Main.lean`, lines 892-909:

```lean
partial def loop (stdin : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then
    pure ()
  else
    let trimmed := line.trimAscii
    if trimmed.isEmpty then
      loop stdin
    else
      match handleLine trimmed.copy with
      | Except.ok out => emitLine out
      | Except.error err =>
          emitLine <| (Json.mkObj [("error", toJson err)]).compress
      loop stdin

def main : IO Unit := do
  let stdin ← IO.getStdin
  loop stdin
```

The `handleLine` dispatcher (lines 862-884) routes on the `type` field:

```lean
def handleLine (line : String) : Except String String := do
  let json ← Json.parse line
  let typ ← json.getObjValAs? String "type"
  match typ with
  | "lww_merge"              => handleLwwMerge cmd.a cmd.b
  | "pn_merge"               => handlePnMerge cmd.a cmd.b
  | "or_set_merge"           => handleOrSetMerge cmd.a cmd.b
  | "mv_merge"               => handleMvMerge cmd.a cmd.b
  | "sql_generate_ops"       => handleSqlGenerateOps json
  | "sql_build_select_plan"  => handleSqlBuildSelectPlan json
  | "sql_eval"               => handleSqlEval json
  | "replication_list_sites" => handleReplicationListSites json
  | "replication_get_head"   => handleReplicationGetHead json
  | "replication_read_since" => handleReplicationReadSince json
  | _                        => throw s!"unsupported command: {typ}"
```

Success responses are wrapped as `{"result": ...}`. Errors are `{"error": "message"}`.

---

## The TypeScript Harness

### LeanDrtClient

`/home/kuitang/git/crdtbase/test/drt/harness.ts` implements the IPC client.

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

The binary is found via `LEAN_DRT_BIN` env var (set in CI), or by falling back to the local
build path. If neither exists, DRT tests are skipped.

**Process spawning** (lines 14-32):

```typescript
constructor(private readonly binPath: string) {
  this.proc = spawn(this.binPath, [], { stdio: ['pipe', 'pipe', 'inherit'] });
  const rl = createInterface({ input: this.proc.stdout });
  rl.on('line', (line) => {
    const next = this.pending.shift();
    if (next) {
      next.resolve(line);
    }
  });
  // ...
}
```

The Lean process is spawned once per `describe` block (in `beforeAll`) and killed in
`afterAll`. A FIFO queue of pending promises maps each request to its response line.

**Request/Response protocol** (lines 43-61):

```typescript
async send<T>(payload: unknown): Promise<T> {
  return new Promise((resolve, reject) => {
    this.pending.push({
      resolve: (line) => {
        try {
          const parsed = JSON.parse(line) as T & { error?: string };
          if (typeof parsed.error === 'string') {
            reject(new Error(parsed.error));
            return;
          }
          resolve(parsed);
        } catch (error) {
          reject(error instanceof Error ? error : new Error(String(error)));
        }
      },
      reject,
    });
    this.proc.stdin.write(`${JSON.stringify(payload)}\n`);
  });
}
```

### Graceful Skip When Lean Is Unavailable

Every DRT test file follows this pattern (e.g. `/home/kuitang/git/crdtbase/test/drt/lww.drt.test.ts`, lines 8-9):

```typescript
const leanBin = LeanDrtClient.findBinary();
const drt = leanBin ? test : test.skip;
```

If the Lean binary is not built, all DRT tests are skipped without failure.

---

## Test Case Generation

All random data is generated by `fast-check` (version ^3.16.0) with the `@fast-check/vitest`
integration (version ^0.1.4). Test cases are NOT manually written or exhaustively enumerated --
they are randomly sampled and automatically shrunk on failure.

### Core CRDT Arbitraries

From `/home/kuitang/git/crdtbase/test/properties/arbitraries.ts`:

**HLC** (lines 12-16):

```typescript
export const arbHlc = (): fc.Arbitrary<Hlc> =>
  fc.record({
    wallMs: fc.nat({ max: HLC_LIMITS.wallMsMax - 1 }),  // max 2^48 - 1
    counter: fc.nat({ max: HLC_LIMITS.counterMax - 1 }), // max 2^16 - 1
  });
```

**Site ID** (lines 18-19):

```typescript
export const arbSiteId = (): fc.Arbitrary<string> =>
  fc.hexaString({ minLength: 8, maxLength: 8 });
```

**LWW Register** (lines 29-34):

```typescript
export const arbLwwState = (): fc.Arbitrary<LwwRegister<...>> =>
  fc.record({
    val: arbScalar(),
    hlc: arbHlc(),
    site: arbSiteId(),
  });
```

**PN-Counter** (lines 42-48): uses `fc.dictionary` to generate `{site: count}` maps:

```typescript
export const arbPnCounter = (): fc.Arbitrary<PnCounter> =>
  fc.record({
    inc: fc.dictionary(arbSiteId(), fc.nat({ max: 1_000_000 })),
    dec: fc.dictionary(arbSiteId(), fc.nat({ max: 1_000_000 })),
  }).map(normalizePnCounter);
```

**OR-Set** (lines 62-74): unique elements by tag key, separate tombstones:

```typescript
export const arbOrSetState = (): fc.Arbitrary<OrSet<...>> =>
  fc.record({
    elements: fc.uniqueArray(arbOrSetElement(), {
      maxLength: 40,
      selector: (element) => tagKey(element.tag),
    }),
    tombstones: fc.uniqueArray(arbOrSetTag(), {
      maxLength: 40,
      selector: tagKey,
    }),
  }).map(canonicalizeOrSet);
```

**MV-Register** (lines 83-92): unique values by `(hlc, site)` key:

```typescript
export const arbMvRegister = (): fc.Arbitrary<MvRegister<...>> =>
  fc.record({
    values: fc.uniqueArray(arbMvValue(), {
      maxLength: 40,
      selector: mvEventKey,
    }),
  }).map(canonicalizeMvRegister);
```

### SQL Arbitraries

SQL test case generators build actual SQL text plus expected results. There are three
generator files:

1. `/home/kuitang/git/crdtbase/test/properties/sql.generators.ts` -- generates SQL text
   for parser round-trip tests and write-op DRT cases. Constructs `GeneratedWriteOpsCase`
   with `sql`, `schema`, `site`, `hlcSequence`, `removeTags`, and `expectedOps`.

2. `/home/kuitang/git/crdtbase/test/properties/sql-eval.generators.ts` -- generates
   `GeneratedSqlEvalCase` with `sql`, `context` (site + HLC sequence), and `state` (existing
   rows with full CRDT column states).

3. The SELECT planner generator produces `GeneratedSelectPlanCase` with partition routing.

All SQL generators produce syntactically valid SQL strings by construction (they build the
string from structured components, not by randomly concatenating tokens).

---

## What Each DRT Test Compares

### 1. LWW Merge

**File:** `/home/kuitang/git/crdtbase/test/drt/lww.drt.test.ts`

- **Input:** Two random `LwwRegister` states
- **Precondition:** `fc.pre(!isConflictingLwwEvent(a, b))` -- filters out cases where `(hlc, site)` match but payloads differ (those are tested separately in invariant tests)
- **Comparison:** TypeScript `mergeLww(a, b)` equals Lean's `LwwRegister.merge` result
- **Lean handler:** `handleLwwMerge` (Main.lean:307-314) -- validates consistency, converts JSON to `LwwRegister Json`, calls `LwwRegister.merge`, converts back

```typescript
drt.prop([arbLwwState(), arbLwwState()], { numRuns: drtRuns })
  ('merge matches Lean oracle', async (a, b) => {
    fc.pre(!isConflictingLwwEvent(a, b));
    const tsResult = mergeLww(a, b);
    const leanResult = await client!.send<{ result: typeof tsResult }>({
      type: 'lww_merge', a, b,
    });
    expect(tsResult).toEqual(leanResult.result);
  }, drtTimeoutMs);
```

### 2. PN-Counter Merge

**File:** `/home/kuitang/git/crdtbase/test/drt/pnCounter.drt.test.ts`

- **Input:** Two random `PnCounter` states (inc/dec maps per site)
- **Wire format conversion:** TypeScript uses `Record<string, number>`, Lean uses `List {site, n}`. The `toWire` function (lines 17-32) converts before sending and comparison
- **Comparison:** `toWire(tsResult)` equals `leanResult.result`
- **Lean handler:** `handlePnMerge` (Main.lean:336-345) -- uses `PnCounter.merge` which takes max per-site count

### 3. OR-Set Merge

**File:** `/home/kuitang/git/crdtbase/test/drt/orSet.drt.test.ts`

- **Input:** Two random OR-Set states (elements + tombstones)
- **Precondition:** `fc.pre(!hasConflictingOrSetEvents(a, b))` -- same tag, different payload
- **Comparison:** TypeScript `mergeOrSet(a, b)` equals Lean's `mergeOrSetJson`
- **Lean implementation:** Merges elements by union, deduplicates by tag key, filters out tombstoned elements, sorts by canonical key

### 4. MV-Register Merge

**File:** `/home/kuitang/git/crdtbase/test/drt/mvRegister.drt.test.ts`

- **Input:** Two random MV-Register states
- **Precondition:** `fc.pre(!hasConflictingMvEvents(a, b))`
- **Comparison:** TypeScript `mergeMvRegister(a, b)` equals Lean's `mergeMvJson`
- **Lean implementation:** Union of values, deduplicated by `(hlc, site)` key, sorted

### 5. Compaction Split Law

**File:** `/home/kuitang/git/crdtbase/test/drt/compaction.drt.test.ts`

This is the most interesting DRT test. For each CRDT type, it verifies:

> For any list of states and any split point `k`, folding the full list equals folding the
> prefix `[0..k)` then folding the suffix `[k..]` on top. This must hold in BOTH TypeScript
> and Lean.

```typescript
// Lines 137-161 (LWW example):
drt.prop([fc.array(arbLwwState(), { maxLength: 12 })], { numRuns: drtRuns })
  ('LWW: every prefix/suffix split matches direct fold and Lean', async (states) => {
    fc.pre(!hasConflictingLwwList(states, isConflictingLwwEvent));
    const directTs = foldTs(states, mergeLww);
    const directLean = await foldLean(states, mergeLean);
    expect(directTs).toEqual(directLean);
    for (const splitIndex of splitPoints(states.length)) {
      const splitTs = applyCompactionSplitTs(states, splitIndex, mergeLww);
      const splitLean = await applyCompactionSplitLean(states, splitIndex, mergeLean);
      expect(splitTs).toEqual(directTs);
      expect(splitLean).toEqual(directLean);
    }
  }, drtTimeoutMs);
```

This test exercises ALL split points (0 through `states.length`), checking:
1. `directTs == directLean` (basic DRT agreement)
2. `splitTs == directTs` (TS compaction correctness)
3. `splitLean == directLean` (Lean compaction correctness)

The same test is repeated for PN-Counter, OR-Set, and MV-Register.

### 6. SQL Write Op Generation

**File:** `/home/kuitang/git/crdtbase/test/drt/sql-generate-ops.drt.test.ts`

- **Input:** Random SQL write statement (INSERT, UPDATE, INC, DEC, ADD, REMOVE, DELETE) + schema + site + HLC sequence
- **Flow:** SQL text is parsed ONCE by TypeScript. The parsed AST is sent to both implementations.
- **Comparison:** Three-way -- `tsOps == expectedOps`, `lean.result == expectedOps`, `lean.result == tsOps`
- **Notable:** The `expectedOps` are pre-computed by the generator using the model, so this is actually a _triple_ differential test

### 7. SQL SELECT Query Planner

**File:** `/home/kuitang/git/crdtbase/test/drt/sql-planner.drt.test.ts`

- **Input:** Random SELECT SQL + schema with optional `partitionBy`
- **Comparison:** TypeScript `buildSelectPlan` equals Lean `buildSelectPlan` equals pre-computed `expectedPlan`
- **Tests:** Partition routing logic (single_partition vs all_partitions), filter extraction

### 8. SQL Full Evaluation

**File:** `/home/kuitang/git/crdtbase/test/drt/sql-eval.drt.test.ts`

The most complex DRT test. It generates:
- Random SQL statement (any type: SELECT, INSERT, UPDATE, DELETE, INC, DEC, ADD, REMOVE)
- Random initial database state (rows with full CRDT column states: LWW, PN-Counter, OR-Set, MV-Register)
- Random eval context (site ID, HLC sequence)

The test:
1. Parses the SQL text in TypeScript
2. Runs `evaluateSqlAst` in TypeScript to get `(result, nextState)`
3. Sends the parsed AST + context + state to Lean's `handleSqlEval`
4. Normalizes both outputs (sorts keys, canonicalizes HLC hex, sorts set elements)
5. Compares

**Error agreement** (lines 311-336): If TypeScript throws, Lean must also throw:

```typescript
if (tsError) {
  await expect(
    client!.sqlEval<{ result: LeanEvalOutcome }>( ... ),
  ).rejects.toThrow();
  return;
}
```

**Normalization** (lines 62-206): Extensive normalization is needed because:
- JSON object key order is non-deterministic
- PN-Counter uses `Record<string, number>` in TS but `List {site, n}` in Lean
- OR-Set elements and tombstones may appear in different orders
- HLC hex values need canonical form (`0x0` vs `0x00000000`)

**Seed replay** (from TESTING.md):

```bash
DRT_NUM_RUNS=200 DRT_SEED=-1196022201 npx vitest run test/drt/sql-eval.drt.test.ts
```

The `DRT_SEED` env var is read at line 22:

```typescript
const drtSeed = process.env.DRT_SEED === undefined ? undefined : Number(process.env.DRT_SEED);
```

And passed to fast-check at line 306:

```typescript
drtSeed === undefined ? { numRuns: drtRuns } : { numRuns: drtRuns, seed: drtSeed },
```

### 9. Replication Log Endpoints

**File:** `/home/kuitang/git/crdtbase/test/drt/replication-log-endpoints.drt.test.ts`

- **Input:** Random log entries (site-a/b/c, seq 1-30), random query site, random `since` cursor, random S3 page size
- **Uses:** An `InMemoryS3ReaderClient` that simulates S3 pagination in-process
- **Comparison:** Three operations against Lean's pure model vs TS's `S3ReplicatedLog`:
  - `listSites()` -- sorted unique site IDs
  - `getHead(siteId)` -- max sequence number for a site
  - `readSince(siteId, since)` -- contiguous sequence numbers after `since`

---

## Wire Format and Data Marshaling

### PN-Counter Serialization

The most interesting marshaling challenge. TypeScript uses `Record<string, number>` (JS object),
but Lean uses `List PnEntryJson` (sorted list of `{site, n}` pairs).

From `/home/kuitang/git/crdtbase/test/drt/pnCounter.drt.test.ts`, lines 17-32:

```typescript
function toWire(counter: PnCounter): PnWire {
  const encode = (entries: Record<string, number>): PnWireEntry[] =>
    Object.entries(entries)
      .filter(([, n]) => n !== 0)     // skip zero entries
      .sort(([left], [right]) => ...) // deterministic order
      .map(([site, n]) => ({ site, n }));
  return { inc: encode(counter.inc), dec: encode(counter.dec) };
}
```

### HLC Hex Canonicalization

Both sides canonicalize HLC hex strings to strip leading zeros. From Lean
(`/home/kuitang/git/crdtbase/lean/CrdtBase/Sql/Defs.lean`, lines 253-261):

```lean
def canonicalizeHlcHex (raw : String) : String :=
  let withoutPrefix :=
    if raw.startsWith "0x" || raw.startsWith "0X" then raw.drop 2 else raw
  let trimmed := (withoutPrefix.dropWhile (fun ch => ch = '0')).toString
  let body := if trimmed.isEmpty then "0" else trimmed
  s!"0x{body}"
```

### SQL Eval State Conversion

The SQL eval DRT has elaborate conversion functions to/from Lean's array-of-records format.
`toLeanSchema` converts TS's nested `Record<table, {pk, columns: Record<col, {crdt}>}>` to
Lean's `List {table, pk, partitionBy, columns: List {name, crdt}}`.

`toLeanState` and `fromLeanState` handle the PN-Counter map vs list conversion for column
states embedded in rows.

---

## Run Configuration

### Environment Variables

| Variable | Default | Purpose |
|----------|---------|---------|
| `LEAN_DRT_BIN` | `lean/.lake/build/bin/CrdtBaseDRT` | Path to oracle binary |
| `DRT_NUM_RUNS` | 50 (basic), 25 (compaction) | Iterations per property |
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

# Coverage run with tuned parameters
npm run test:coverage
```

---

## CI Pipeline

**File:** `/home/kuitang/git/crdtbase/.github/workflows/ci.yml`

A single job that runs on `ubuntu-latest` with a 120-minute timeout:

1. **Checkout + Node 22 + npm ci**

2. **Build Lean proofs and DRT oracle** (lines 37-46):
   ```yaml
   - name: Build Lean proofs and DRT oracle
     uses: leanprover/lean-action@v1
     with:
       auto-config: false
       build: true
       build-args: CrdtBase CrdtBaseDRT
       lake-package-directory: lean
       use-github-cache: true
       use-mathlib-cache: true
   ```
   This builds both the proof library AND the DRT executable. If any Lean proof contains
   `sorry`, this step fails. Mathlib cache is used to avoid rebuilding the dependency.

3. **Verify Lean DRT oracle binary** (line 50):
   ```yaml
   - run: test -x lean/.lake/build/bin/CrdtBaseDRT
   ```

4. **Resolve Chromium for Playwright** (for browser e2e tests)

5. **Run TypeScript test suite** (lines 69-72):
   ```yaml
   - name: Run TypeScript test suite
     env:
       LEAN_DRT_BIN: lean/.lake/build/bin/CrdtBaseDRT
     run: npm test
   ```
   `npm test` expands to `vitest run`, which runs ALL test files including DRT.

---

## Edge Cases and Failure Modes

### Event Consistency Invariant

The LWW CRDT has a critical invariant: if two states share the same `(hlc, site)` pair, they
MUST have the same payload. This invariant is required for commutativity and associativity
proofs in Lean.

DRT tests use `fc.pre()` to filter out conflicting events:

```typescript
fc.pre(!isConflictingLwwEvent(a, b));
```

Separate invariant tests (`/home/kuitang/git/crdtbase/test/properties/invariants.prop.test.ts`)
verify that `mergeLww` throws on conflicting events (line 14-21):

```typescript
test.prop([arbHlc(), arbSiteId(), fc.tuple(arbScalar(), arbScalar())])(
  'merge rejects conflicting payloads for same (hlc, site)',
  (hlc, site, [leftVal, rightVal]) => {
    fc.pre(!Object.is(leftVal, rightVal));
    const a = { val: leftVal, hlc, site };
    const b = { val: rightVal, hlc, site };
    expect(() => mergeLww(a, b)).toThrow(/conflicting LWW event identity/);
  },
);
```

The Lean oracle also validates this (Main.lean:296-298):

```lean
def assertLwwConsistent (a b : LwwJson) : Except String Unit := do
  if (a.hlc == b.hlc) && (a.site == b.site) && a.val != b.val then
    throw "conflicting LWW event identity: same (hlc, site) with different payloads"
```

### OR-Set and MV-Register Tag Conflicts

Same pattern -- `hasConflictingOrSetEvents` and `hasConflictingMvEvents` filter DRT inputs,
while separate invariant tests verify rejection.

### HLC Bounds

The Lean `Hlc` structure carries proof obligations (from
`/home/kuitang/git/crdtbase/lean/CrdtBase/Hlc/Defs.lean`, lines 16-21):

```lean
structure Hlc where
  wallMs : Nat
  counter : Nat
  wallMs_lt : wallMs < wallMsMax    -- proof that wallMs < 2^48
  counter_lt : counter < counterMax -- proof that counter < 2^16
```

The DRT oracle validates these bounds when converting from JSON (Main.lean:242-245):

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
also throws (sql-eval.drt.test.ts, lines 311-336). This ensures both implementations reject
the same invalid inputs (e.g., column type mismatches, missing primary keys).

### Normalization for Non-Deterministic Output

Both implementations may produce structurally equivalent but differently ordered output.
The SQL eval test has approximately 150 lines of normalization code to handle:

- JSON object key ordering
- PN-Counter map-vs-list representation
- OR-Set element and tombstone ordering
- MV-Register value ordering
- HLC hex canonicalization (e.g., `0x00ff` vs `0xff`)
- Read result row ordering

This normalization is applied symmetrically to both TS and Lean outputs before comparison.

### Compaction Split Exhaustiveness

The compaction test checks ALL `n+1` split points for a list of length `n` (lines 120-122):

```typescript
function splitPoints(length: number): number[] {
  return Array.from({ length: length + 1 }, (_, index) => index);
}
```

This means for a 12-element list, it checks 13 splits (including empty prefix and empty
suffix). Combined with 25 random inputs, this gives 25 * 13 * 2 = 650 Lean oracle calls
per CRDT type.

---

## Lean-side Implementation Details

### LWW Merge in Lean

From `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/Lww/Defs.lean`, lines 14-18:

```lean
def merge {a : Type} (a b : LwwRegister a) : LwwRegister a :=
  if Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .lt then b else a
```

This is the _same_ logic as the TypeScript version
(`/home/kuitang/git/crdtbase/src/core/crdt/lww.ts`, lines 23-30):

```typescript
export function mergeLww<T>(a: LwwRegister<T>, b: LwwRegister<T>): LwwRegister<T> {
  assertLwwEventConsistency(a, b);
  const cmp = compareWithSite(a.hlc, a.site, b.hlc, b.site);
  if (cmp >= 0) return a;
  return b;
}
```

The DRT test verifies these produce identical results for 50+ random input pairs.

### Replication Log Model in Lean

From `/home/kuitang/git/crdtbase/lean/CrdtBase/Replication/Defs.lean`:

Pure functional model with `listSites`, `getHead`, and `readSince`. The `readSince` function
(lines 56-58) filters entries for a site, then takes only the _contiguous_ sequence starting
from `since + 1`:

```lean
def readSince (entries : List LogEntry) (siteId : String) (since : Nat) : List Nat :=
  let seqs := (canonicalSeqs entries siteId).filter (fun seq => seq > since)
  takeContiguousFrom (since + 1) seqs
```

This is compared against the actual S3 log implementation with an in-memory S3 mock that
simulates pagination (page size is also random).

---

## Summary

The crdtbase differential testing system is a three-layer architecture:

1. **Lean 4 proofs** guarantee mathematical correctness of CRDT merge, HLC ordering,
   convergence, and compaction for ALL inputs
2. **DRT tests** verify that the TypeScript production code matches the Lean specification
   for large random samples, using a long-running Lean process as an oracle via JSON-line IPC
3. **Property and model-based tests** cover system aspects outside Lean's scope (encoding
   round-trips, SQL parsing, multi-site convergence simulation, bloom filters)

The system tests 10 differential targets spanning primitive CRDT merges, compaction correctness,
SQL write-op generation, SQL query planning, full SQL evaluation with state, and replication
log endpoint semantics. All test cases are randomly generated by `fast-check`, with automatic
shrinking on failure and seed replay support for debugging.
