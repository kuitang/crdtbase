# Fly Multi-Region Stress Plan

## Goal

Run true multi-region stress against real Tigris S3 with one fresh bucket per randomized execution, then delete the bucket on completion.

## Topology

- Single Fly app (`FLY_APP`)
- Three region-pinned workers:
  - `site-a` in `iad`
  - `site-b` in `lhr`
  - `site-c` in `syd`
- One bucket per execution (`BUCKET_PREFIX` + run id)
- Coordinator runs as TypeScript (`scripts/stress/fly-coordinator.ts`) and calls
  Fly Machines REST API directly using OpenAPI-generated TS types
  (`scripts/stress/fly-machines-openapi.d.ts`).
- Coordinator authentication uses `FLY_API_TOKEN` (or `FLY_ACCESS_TOKEN`) with
  base URL `FLY_API_HOSTNAME` (default `https://api.machines.dev/v1`).

## Barrier Protocol

Workers and coordinator rendezvous using S3 control objects under:

- `control/<run-id>/barrier-<index>/pre/<site>.json`
- `control/<run-id>/barrier-<index>/drained/<site>.json`
- `control/<run-id>/commands/barrier-<index>/entry.json`
- `control/<run-id>/commands/barrier-<index>/release.json`
- `control/<run-id>/final/<site>.json`

Soft barriers validate invariants only.
Hard barriers force drain rounds and require identical state digests across all sites before release.
Commands are immutable by phase to avoid cross-region stale-read hazards from overwriting one command object.
Each worker syncs before pre-barrier publication. Coordinator computes a target head vector from
`pre/<site>.json` (`syncedHeads[site]` for each site) and includes it in hard-barrier drain commands.
Workers must report `pendingOps=0` at pre barrier and drain until local synced heads reach that vector.

## Throughput/Randomness

- Long sequences per site (`STRESS_OPS_PER_CLIENT`, default 30,000)
- Hot-row contention + randomized operation mix
- Very high throughput by default (no artificial sleep in operation loop)
- Every operation ends with `sync()` (explicitly push+pull each op)

## Barrier Time Expectations (iad + lhr + syd)

- Soft barrier:
  - Typical: 1-4 seconds
  - p95: 6-8 seconds
  - Timeout default: 30 seconds
- Hard barrier:
  - Typical: 6-20 seconds
  - p95: 25-40 seconds
  - Timeout default: 90 seconds

## Default SLO Knobs

- `STRESS_SOFT_BARRIER_TIMEOUT_S=30`
- `STRESS_HARD_BARRIER_TIMEOUT_S=90`
- `STRESS_POLL_INTERVAL_MS=250`
- `STRESS_DRAIN_ROUNDS=8`
- `STRESS_DRAIN_QUIESCENCE_ROUNDS=2`
- `STRESS_DRAIN_MAX_EXTRA_ROUNDS=40`
