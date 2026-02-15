# Stress Test Application Bugs

## 2026-02-15 - Snapshot Manifest Site-Coverage Regression (Application Bug)

### Observed in stress

- Batch: `test/stress/STRESS_RUN_20260215T223737Z_snapshot_auto.log`
- Failure point: barrier `0001` pre phase
- Symptom: local invariants failed with regressions such as:
  - `row 't4' points regressed below local expectation`
  - `row 't1' missing local tag ...`

### Root cause

Clients applied newer snapshot manifests even when `manifest.sites_compacted` omitted a site the client had already synced (`seq > 0`).

In that case, snapshot row replacement could drop state for the omitted site while the existing sync cursor for that site stayed advanced, so required replay was skipped.

### Fix

- Added a manifest coverage gate in **all clients** that consume snapshots:
  - `src/platform/node/nodeClient.ts`
  - `src/platform/browser/browserClient.ts`
- New rule: apply a newer manifest only if it includes `sites_compacted` entries for every site currently tracked by that client with `seq > 0`.
- If coverage is incomplete, skip that manifest and keep current local state/cursors.

### Why this is an application bug

The failure was in production client snapshot cutover logic (state/cursor correctness), not in stress orchestration or reporting.

### Validation added

- New property tests in `test/properties/clientSnapshotPull.prop.test.ts`:
  - node client ignores newer manifest missing previously synced site watermark
  - browser client ignores newer manifest missing previously synced site watermark
