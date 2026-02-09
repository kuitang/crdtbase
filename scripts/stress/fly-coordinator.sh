#!/usr/bin/env bash
set -euo pipefail

# Multi-region barrier timing expectations for iad+lhr+syd:
# - Soft barrier (invariants-only, no forced drain):
#   typical 1-4s, p95 ~6-8s. Default timeout: 30s.
# - Hard barrier (head-target drain + convergence digest check):
#   typical 6-20s, p95 ~25-40s. Default timeout: 90s.
#
# Barrier protocol summary:
# - Workers publish pre/drained reports under control/<run>/barrier-XXXX/{pre|drained}/<site>.json
# - Coordinator publishes immutable command objects under:
#     control/<run>/commands/barrier-XXXX/entry.json
#     control/<run>/commands/barrier-XXXX/release.json
# - Hard barriers compute targetHeads from pre reports and require workers to drain until
#   syncedHeads >= targetHeads, then verify convergence hash equality.
#
# Implementation note:
# This shell entrypoint is intentionally thin. Coordinator logic lives in
# scripts/stress/fly-coordinator.ts using Fly Machines REST API with OpenAPI-generated types.

exec npx tsx scripts/stress/fly-coordinator.ts "$@"
