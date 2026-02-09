# Fly Stress Timing Results (2026-02-09)

## Scope

This file captures:

- end-to-end Fly multi-region stress outcomes observed on 2026-02-09
- barrier timing distributions
- correctness outcomes by run id
- profiling breakdown for the replicated-log request path

Test topology:

- app: `crdtbase-stress-260209055135`
- regions: `iad`, `lhr`, `syd`
- worker image (final validated): `registry.fly.io/crdtbase-stress-260209055135:stress-20260209-pushpull-2`
- run shape: `STRESS_RUNS=3`, `STRESS_OPS_PER_CLIENT=120`, `STRESS_BARRIER_EVERY_OPS=30`, `STRESS_HARD_BARRIER_EVERY=1`

## Correctness Summary (All Finished Runs So Far)

Passed:

- `run-20260209065950-1-1265189473` (legacy sync-each-op config)
- `run-20260209071504-1-48948680` (legacy sync-each-op config)
- `run-20260209072229-2-2861297512` (legacy sync-each-op config)
- `run-20260209072947-3-1742581533` (legacy sync-each-op config)
- `run-20260209075321-1-347386762` (push-after-write / pull-before-read)
- `run-20260209075731-2-2090248377` (push-after-write / pull-before-read)
- `run-20260209080132-3-2936197411` (push-after-write / pull-before-read)

Failed:

- `run-20260209071017-2-3413263296`: Fly Machines API `403 unauthorized` while creating machines (fixed by token-refresh logic in coordinator).
- `run-20260209074554-1-1213804810`: barrier 4 drain target not reached with `STRESS_DRAIN_MAX_EXTRA_ROUNDS=40` (fixed by raising default to `200`).

## Final 3-Run Validation Timing (push-after-write / pull-before-read)

### Run-level totals

| Run ID | Result | Wall Time (s) |
| --- | --- | ---: |
| `run-20260209075321-1-347386762` | PASS | 245.7 |
| `run-20260209075731-2-2090248377` | PASS | 237.9 |
| `run-20260209080132-3-2936197411` | PASS | 233.0 |

Average run wall time: **238.9s**

### Barrier timings by run

| Run ID | Barrier | Pre (s) | Drained (s) | Total (s) |
| --- | ---: | ---: | ---: | ---: |
| `run-20260209075321-1-347386762` | 1 | 43 | 16 | 59 |
| `run-20260209075321-1-347386762` | 2 | 40 | 14 | 54 |
| `run-20260209075321-1-347386762` | 3 | 37 | 14 | 52 |
| `run-20260209075321-1-347386762` | 4 | 37 | 14 | 51 |
| `run-20260209075731-2-2090248377` | 1 | 44 | 13 | 57 |
| `run-20260209075731-2-2090248377` | 2 | 37 | 14 | 52 |
| `run-20260209075731-2-2090248377` | 3 | 38 | 14 | 52 |
| `run-20260209075731-2-2090248377` | 4 | 40 | 14 | 54 |
| `run-20260209080132-3-2936197411` | 1 | 43 | 14 | 56 |
| `run-20260209080132-3-2936197411` | 2 | 37 | 14 | 51 |
| `run-20260209080132-3-2936197411` | 3 | 37 | 14 | 51 |
| `run-20260209080132-3-2936197411` | 4 | 36 | 14 | 51 |

Cross-run averages:

- pre phase: **39.08s**
- drained phase: **14.08s**
- full barrier: **53.33s**

## Profiling Breakdown

### Raw object-store latency baseline (Tigris endpoint from local host)

- `PUT`: mean `83ms` (p50 `72ms`)
- `HEAD`: mean `62ms` (p50 `60ms`)
- `GET`: mean `63ms` (p50 `61ms`)
- `LIST`: mean `143ms` (p50 `96ms`)
- `DELETE`: mean `92ms` (p50 `74ms`)

### CRDT profile on real Tigris

`syncEvery=1` (old behavior):

- throughput: `0.88 ops/s` (`180 ops` in `203.9s`)
- log calls: `append=181`, `listSites=185`, `getHead=542`, `readSince=548`
- calls per op:
  - `append`: `1.01/op`
  - `listSites`: `1.03/op`
  - `getHead`: `3.01/op`
  - `readSince`: `3.04/op`
  - total log calls: **`8.09/op`**

`syncEvery=5` (reference profile):

- throughput: `4.62 ops/s` (`180 ops` in `38.95s`)
- log calls: `append=37`, `listSites=41`, `getHead=110`, `readSince=116`
- total log calls: **`1.69/op`**

### Why multi-second op latencies appeared

Even with individual object ops in ~`50-150ms`, old sync-each-op behavior multiplied request volume and serialized many of those requests per operation (`getHead` + `readSince` fanout across sites). Cross-region tail latency (especially at barriers waiting for the slowest site) amplified this further.

