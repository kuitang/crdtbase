# Fly Stress Timing Results (2026-02-14)

## Scope

This file captures:

- end-to-end Fly multi-region stress outcomes observed on 2026-02-14
- barrier timing distributions
- correctness outcomes by run id
- coordinator batch wall-clock timings

Test topology:

- app: `crdtbase-stress-260209055135`
- regions: `iad`, `lhr`, `syd`
- worker image (final validated): `registry.fly.io/crdtbase-stress-260209055135:stress-20260214-compactor-230750`
- run shape: `STRESS_RUNS=3`, `STRESS_OPS_PER_CLIENT=120`, `STRESS_BARRIER_EVERY_OPS=30`, `STRESS_HARD_BARRIER_EVERY=1`, `STRESS_COMPACTION_EVERY_OPS=30`
- compactor placement: per-run random assignment (`runSeed % 3`)

Batch executions:

- batch A log: `test/stress/STRESS_RUN_20260214T230827Z.log` (wall time `668.04s`, stopped in run 3)
- batch B log: `test/stress/STRESS_RUN_20260214T231957Z_retry.log` (wall time `944.68s`, all 3 runs passed)

## Correctness Summary (All Finished Runs So Far)

Passed:

- `run-20260214230828-1-3163995505` (batch A)
- `run-20260214231326-2-963658103` (batch A)
- `run-20260214231958-1-842732356` (batch B)
- `run-20260214232446-2-3707725326` (batch B)
- `run-20260214232934-3-3681729989` (batch B)

Failed:

- `run-20260214231929-3-1000358062`: Fly Machines API `403 unauthorized` on machine create after token expiry while refresh command was disabled in that invocation (`FLY_API_TOKEN_COMMAND=''`); fixed for batch B by setting `FLY_API_TOKEN_COMMAND='flyctl auth token --quiet'`.

## Final 3-Run Validation Timing (push-after-write / pull-before-read)

### Run-level totals

| Run ID | Result | Wall Time (s) |
| --- | --- | ---: |
| `run-20260214231958-1-842732356` | PASS | 283.9 |
| `run-20260214232446-2-3707725326` | PASS | 284.0 |
| `run-20260214232934-3-3681729989` | PASS | 363.0 |

Average run wall time: **310.3s**

### Barrier timings by run

| Run ID | Barrier | Pre (s) | Drained (s) | Total (s) |
| --- | ---: | ---: | ---: | ---: |
| `run-20260214231958-1-842732356` | 1 | 49 | 17 | 66 |
| `run-20260214231958-1-842732356` | 2 | 43 | 17 | 61 |
| `run-20260214231958-1-842732356` | 3 | 43 | 17 | 60 |
| `run-20260214231958-1-842732356` | 4 | 45 | 17 | 62 |
| `run-20260214232446-2-3707725326` | 1 | 50 | 17 | 67 |
| `run-20260214232446-2-3707725326` | 2 | 44 | 18 | 62 |
| `run-20260214232446-2-3707725326` | 3 | 45 | 18 | 64 |
| `run-20260214232446-2-3707725326` | 4 | 44 | 18 | 61 |
| `run-20260214232934-3-3681729989` | 1 | 63 | 24 | 89 |
| `run-20260214232934-3-3681729989` | 2 | 53 | 25 | 79 |
| `run-20260214232934-3-3681729989` | 3 | 57 | 24 | 82 |
| `run-20260214232934-3-3681729989` | 4 | 57 | 25 | 84 |

Cross-run averages:

- pre phase: **49.42s**
- drained phase: **19.75s**
- full barrier: **69.75s**

## Profiling Breakdown

### Raw object-store latency baseline (Tigris endpoint from local host)

- Not re-measured in this execution.
- Reference baseline remains in `test/stress/TIMING_RESULTS_2026-02-09.md`.

### CRDT profile on real Tigris

- Not re-profiled in this execution.
- This run focused on end-to-end multi-region stress timing with compactor-enabled workers.

### Why multi-second op latencies appeared

Hard barriers include cross-region replication delay and explicit drain convergence rounds across `iad`, `lhr`, and `syd`; total barrier time is determined by the slowest site in each phase.
