# CRDTBase

CRDT-native SQL sync engine in TypeScript, with pluggable replication backends.

This repository includes:
- Node client runtime
- Browser client runtime
- HTTP replicated-log backend (`FileReplicatedLogServer`)
- S3 replicated-log backend
- Chaos E2E tests for Node and browser
- REPLs for Node CLI and browser

## Install

```bash
npm install
```

## Test Matrix

Run TypeScript tests:

```bash
npm test
```

Run Node E2E chaos tests only:

```bash
npm run test:e2e:node
```

Run browser E2E chaos tests only (Playwright + Chromium):

```bash
npm run test:e2e:browser
```

Run full suite (Lean + TS):

```bash
npm run test:all
```

## TypeScript Test Architecture

TypeScript tests are organized into three layers:
- `test/properties/*.prop.test.ts`: fast-check property tests for CRDT algebra, invariants, SQL parsing/planning, compaction, and snapshot stores.
- `test/drt/*.drt.test.ts`: differential random tests (DRT) that compare TypeScript behavior against the Lean oracle (`CrdtBaseDRT`).
- `test/e2e/*.e2e.test.ts`: multi-client chaos end-to-end flows (HTTP and S3/MinIO for Node and browser adapters).

This project intentionally favors property/model/differential testing over one-off example unit tests.

## Coverage (Vitest + Property Tests)

Coverage is collected with `c8` (Node V8 coverage) wrapped around Vitest. This is fast and stable for this ESM + fast-check suite, including property and chaos tests.

Run coverage on the current Node CI matrix plus property and DRT suites:

```bash
npm run test:coverage
```

Run coverage on the full suite (includes browser E2E when Playwright/Chromium is available):

```bash
npm run test:coverage:all
```

Reports are written to:
- `coverage/index.html`
- `coverage/lcov.info`
- `coverage/coverage-summary.json`

`test:coverage` lowers chaos/DRT run counts and forces single-worker execution to avoid MinIO port races while still exercising end-to-end merge/sync paths.

## Backend: HTTP (File Replicated Log)

Start HTTP backend:

```bash
npm run backend:http -- --host 0.0.0.0 --port 8788 --root-dir ./.crdtbase-http-server
```

This server exposes `GET/POST/PUT` endpoints for logs and snapshots and now includes CORS headers for browser use.

## Backend: S3 with Pre-Signed URLs

For REPL S3 mode, clients use a pre-sign service that returns short-lived signed URLs for:
- `ListObjectsV2`
- `GetObject`
- `PutObject`

Start pre-sign service:

```bash
npm run presign:server -- \
  --host 0.0.0.0 \
  --port 8787 \
  --endpoint http://127.0.0.1:9000 \
  --region us-east-1 \
  --force-path-style true \
  --access-key-id minioadmin \
  --secret-access-key minioadmin
```

### How pre-signed flow works

1. Client asks pre-sign service for a signed request (`/v1/presign/*`).
2. Service signs S3 operation using server-side credentials.
3. Client executes returned signed URL directly via `fetch`.

### Browser note for S3

Browser direct-to-S3 requests require bucket CORS to allow your REPL origin.

Example with `mc`:

```bash
cat > cors.json <<'JSON'
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
JSON

mc alias set local http://127.0.0.1:9000 minioadmin minioadmin
mc cors set local/crdtbase cors.json
```

## Node REPL

Default behavior:
- each REPL process uses a fresh ephemeral local state dir under `/tmp` (avoids stale cursor errors after backend resets)
- pass `--data-dir <path>` if you want persistent state across sessions
- pass `--reset-state` to wipe `--data-dir` on startup

Start Node REPL (HTTP backend):

```bash
npm run repl:node -- \
  --backend http \
  --site-id site-a \
  --http-base-url http://127.0.0.1:8788
```

Start Node REPL (S3 pre-sign backend):

```bash
npm run repl:node -- \
  --backend s3-presign \
  --site-id site-a \
  --bucket crdtbase \
  --prefix deltas \
  --presign-base-url http://127.0.0.1:8787
```

Start Node REPL with persistent local state (opt-in):

```bash
npm run repl:node -- \
  --backend s3-presign \
  --site-id site-a \
  --bucket crdtbase \
  --prefix deltas \
  --presign-base-url http://127.0.0.1:8787 \
  --data-dir ./.crdtbase-cli/site-a
```

### REPL commands

- `.help`
- `.examples`
- `.push`
- `.pull`
- `.sync`
- `.quit`

SQL input supports DDL/write/select. `SELECT` results are rendered as plain text tables.

## Browser REPL

Start browser REPL server:

```bash
npm run repl:browser -- --host 0.0.0.0 --port 4173
```

Open:

```text
http://0.0.0.0:4173
```

The browser REPL uses a black-and-white ChatGPT-like style and supports:
- backend switch (`HTTP` or `S3 (Pre-Signed URLs)`)
- `.push` / `.pull` / `.sync` buttons
- SQL execution (Ctrl/Cmd + Enter)
- plain table output formatting
- clickable example queries

Browser REPL state safety:
- local client state is in-memory only (no browser persistence across page reload)
- changing backend or connection settings auto-disconnects the active session
- reconnect always starts a fresh local session

## Example SQL (works in both REPLs)

```sql
CREATE TABLE tasks (
  id STRING PRIMARY KEY,
  title LWW<STRING>,
  points COUNTER,
  tags SET<STRING>,
  status REGISTER<STRING>
);

INSERT INTO tasks (id, title, points, tags, status)
VALUES ('t1', 'hello', 0, 'alpha', 'open');

INC tasks.points BY 3 WHERE id = 't1';
ADD 'beta' TO tasks.tags WHERE id = 't1';
UPDATE tasks SET title = 'from-repl' WHERE id = 't1';
SELECT * FROM tasks;
```

## Manual Consistency Check

1. Start backend (`backend:http` or S3+presign).
2. Open two clients (two Node REPLs, or Node + browser) with different `site-id`s.
3. On client A: run DDL + insert + `INC` + `ADD`, then `.push`.
4. On client B: `.pull`, run concurrent writes, `.push`.
5. On both: `.sync`.
6. Run `SELECT * FROM tasks;` on both clients.

Expected: both clients converge to identical rows after sync rounds, matching chaos E2E guarantees.
