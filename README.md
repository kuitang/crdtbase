# CRDTBase

CRDT-native SQL sync engine in TypeScript with pluggable replication backends (HTTP and direct S3).

## Command Source of Truth

Shell commands for setup, tests, runtime, and Tigris operations are in `AGENTS.md`.
This README focuses on manual validation expectations and operator notes.

## Components

- Node REPL client
- Browser REPL client
- HTTP replicated log backend (`FileReplicatedLogServer`)
- Direct S3 replicated log backend (`S3ReplicatedLog`)
- Property tests, differential random tests (Lean parity), and chaos E2E suites

## Lean DRT SQL Interface

Lean SQL parity tests use a single DRT command, `sql_script_eval`, which accepts
a list of SQL AST statements plus eval context/state, executes the sequence
end-to-end, and returns per-statement outcomes and final state.

Individual DRT suites (`lww`, `pnCounter`, `orSet`, `mvRegister`, SQL planner,
SQL op generation, SQL eval, and split-law checks) are preserved and now route
through this same SQL-script pipeline.

## Table CRDT Model

Table state is modeled as a key-to-row map where each row has mixed CRDT columns plus an
explicit row-visibility register. Wire ops use discriminated forms:

- `row_exists` (row tombstone / resurrection marker)
- `cell_lww`
- `cell_counter`
- `cell_or_set_add`
- `cell_or_set_remove`
- `cell_mv_register`

## Canonical S3 Environment Variables

The codebase now uses canonical AWS names:

- `BUCKET_NAME`
- `AWS_ENDPOINT_URL_S3` (or `AWS_ENDPOINT_URL`)
- `AWS_REGION` (or `AWS_DEFAULT_REGION`)
- `AWS_ACCESS_KEY_ID`
- `AWS_SECRET_ACCESS_KEY`
- `AWS_SESSION_TOKEN` (optional)
- `S3_PREFIX` (optional, default `deltas`)
- `S3_FORCE_PATH_STYLE` (optional)

Project-specific `CRDTBASE_*` S3 env aliases are intentionally removed.

## Manual Runtime Notes

- Run long-lived services (`crdtbase-http`, `crdtbase-browser`) in tmux sessions (see `AGENTS.md`).
- Attach to existing sessions using the tmux commands in `AGENTS.md`.
- Open browser REPL at `http://<host>:4183/`, where `<host>` is the machine running tmux.
- Node REPL defaults to ephemeral local state under `/tmp` unless `DATA_DIR` is set.

## Browser S3 Auth Input

Browser REPL S3 config accepts either:
- JSON object
- whitespace/newline-separated `KEY=value` tokens

Recognized keys include both plain names and AWS env-style names (`bucket` or `BUCKET_NAME`, `endpoint` or `AWS_ENDPOINT_URL_S3`, etc.).
Unknown keys are ignored, so pasting a larger env block is safe.

## Manual Convergence Scenario (3 Sites)

Use three site IDs (`site-a`, `site-b`, `site-c`) against the same backend.

1. On `site-a`, create schema and insert the initial row, then push.
2. On `site-b`, pull, apply concurrent edits (title/status/increment/tag), then push.
3. On `site-c`, pull, apply another concurrent title/increment/tag, then push and pull again.
4. Sync all three sites and compare final row values.

Expected converged row for the standard walkthrough:
- `id = 't1'`
- `title = 'from-c'`
- `points = 8`
- `tags = [alpha, beta, gamma]`
- `status = [open, review]`

## Verifying Writes Are Going to Tigris (Not MinIO)

When validating manually:
- Confirm the active S3 endpoint is your Tigris endpoint, not `localhost` or `0.0.0.0:9000`.
- Confirm expected delta keys exist under `deltas/<site-id>/...` in the configured bucket.
- Decode one delta object using the pipe-based decode command in `AGENTS.md` and verify fields such as `siteId`, `seq`, and `ops`.

## Tigris Setup Artifacts

- `deploy/tigris/README.md`
- `deploy/tigris/env.tigris.example`
- `deploy/tigris/cors.example.json`

## Fly Multi-Region Stress Coordinator

For true multi-region stress (real Tigris endpoint, per-run bucket lifecycle), use:

- `scripts/stress/fly-coordinator.sh`
- `test/stress/flyWorker.ts`
- `test/stress/PLAN.md`

Coordinator behavior:
- creates a fresh bucket for each run
- launches three Fly workers (`iad,lhr,syd` by default)
- drives soft/hard S3 control-object barriers
- enforces invariants + convergence digests
- deletes the bucket at the end of each run (success and failure paths)

Basic usage:

```bash
export FLY_APP=<your-fly-app>
export FLY_WORKER_IMAGE=<registry/image:tag-built-with-Dockerfile.stress>
export AWS_ENDPOINT_URL_S3=<tigris-endpoint>
export AWS_ACCESS_KEY_ID=<key>
export AWS_SECRET_ACCESS_KEY=<secret>
export AWS_REGION=auto

npm run stress:fly:coordinator
```

Optional knobs:
- `STRESS_RUNS` (default `10`)
- `STRESS_OPS_PER_CLIENT` (default `30000`)
- `STRESS_BARRIER_EVERY_OPS` (default `3000`)
- `STRESS_HARD_BARRIER_EVERY` (default `2`)
- `STRESS_DRAIN_ROUNDS` (default `8`)
- `STRESS_SOFT_BARRIER_TIMEOUT_S` (default `30`)
- `STRESS_HARD_BARRIER_TIMEOUT_S` (default `90`)
