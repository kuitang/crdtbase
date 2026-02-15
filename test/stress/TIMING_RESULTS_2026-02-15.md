# Fly Stress Timing Results (2026-02-15)

## Scope

This file captures:

- end-to-end Fly multi-region stress outcomes observed on 2026-02-15
- barrier timing distributions
- correctness outcomes by run id
- coordinator batch wall-clock timings

Test topology:

- app: `crdtbase-stress-260209055135`
- regions: `iad`, `lhr`, `syd`
- worker image (final validated): `registry.fly.io/crdtbase-stress-260209055135:stress-20260215-snapshot-coverage-224446`
- run shape: `STRESS_RUNS=3`, `STRESS_OPS_PER_CLIENT=120`, `STRESS_BARRIER_EVERY_OPS=30`, `STRESS_HARD_BARRIER_EVERY=1`, `STRESS_COMPACTION_EVERY_OPS=30`
- compactor placement: per-run random assignment (`runSeed % 3`)

Batch executions:

- batch A log: `test/stress/STRESS_RUN_20260215T223737Z_snapshot_auto.log` (wall time `79.55s`, stopped in run 1 due application bug; fixed)
- batch B log: `test/stress/STRESS_RUN_20260215T224529Z_snapshot_coverage.log` (wall time `864.382s`, all 3 runs passed)

## Correctness Summary (All Finished Runs So Far)

Passed:

- `run-20260215224530-1-4067962528` (batch B)
- `run-20260215224933-2-3422796657` (batch B)
- `run-20260215225408-3-2298453710` (batch B)

Failed:

- `run-20260215223738-1-3540465964`: snapshot cutover regression when manifest omitted a previously-synced site watermark; clients could replace rows from an incomplete snapshot and skip required replay. Fixed in Node+Browser snapshot manifest coverage gate. See `STRESS_TEST_BUGS.md`.

## Final 3-Run Validation Timing (push-after-write / pull-before-read)

### Run-level totals

| Run ID | Result | Wall Time (s) |
| --- | --- | ---: |
| `run-20260215224530-1-4067962528` | PASS | 238.4 |
| `run-20260215224933-2-3422796657` | PASS | 271.0 |
| `run-20260215225408-3-2298453710` | PASS | 341.4 |

Average run wall time: **283.6s**

### Barrier timings by run

| Run ID | Barrier | Pre (s) | Drained (s) | Total (s) |
| --- | ---: | ---: | ---: | ---: |
| `run-20260215224530-1-4067962528` | 1 | 29 | 19 | 48 |
| `run-20260215224530-1-4067962528` | 2 | 36 | 19 | 56 |
| `run-20260215224530-1-4067962528` | 3 | 29 | 19 | 48 |
| `run-20260215224530-1-4067962528` | 4 | 28 | 19 | 47 |
| `run-20260215224933-2-3422796657` | 1 | 53 | 21 | 74 |
| `run-20260215224933-2-3422796657` | 2 | 54 | 19 | 74 |
| `run-20260215224933-2-3422796657` | 3 | 32 | 19 | 51 |
| `run-20260215224933-2-3422796657` | 4 | 26 | 19 | 46 |
| `run-20260215225408-3-2298453710` | 1 | 58 | 21 | 79 |
| `run-20260215225408-3-2298453710` | 2 | 55 | 21 | 76 |
| `run-20260215225408-3-2298453710` | 3 | 56 | 21 | 77 |
| `run-20260215225408-3-2298453710` | 4 | 56 | 21 | 77 |

Cross-run averages:

- pre phase: **42.67s**
- drained phase: **19.83s**
- full barrier: **62.75s**

## Timing Delta vs 2026-02-14 Final Validation

Baseline: `test/stress/TIMING_RESULTS_2026-02-14.md` (final 3-run batch B)

- average run wall time: `310.3s -> 283.6s` (**-26.7s**, `-8.6%`)
- average pre phase: `49.42s -> 42.67s` (**-6.75s**, `-13.7%`)
- average drained phase: `19.75s -> 19.83s` (**+0.08s**, `+0.4%`)
- average full barrier: `69.75s -> 62.75s` (**-7.00s**, `-10.0%`)
- coordinator batch wall time: `944.68s -> 864.382s` (**-80.298s**, `-8.5%`)

## Profiling Breakdown

### Raw object-store latency baseline (Tigris endpoint from local host)

- Not re-measured in this execution.
- Reference baseline remains in `test/stress/TIMING_RESULTS_2026-02-09.md`.

### CRDT profile on real Tigris

- Not re-profiled in this execution.
- This run focused on end-to-end multi-region stress timing with compactor-enabled workers and snapshot-first client cutover safety.

### Why multi-second op latencies appeared

Hard barriers include cross-region replication delay and explicit drain convergence rounds across `iad`, `lhr`, and `syd`; total barrier time is determined by the slowest site in each phase.
