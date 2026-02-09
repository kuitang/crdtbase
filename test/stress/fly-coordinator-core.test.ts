import { describe, expect, it } from 'vitest';
import {
  computeTargetHeadsFromPreReports,
  resolveFlyApiBaseUrl,
  sanitizeBucketName,
  validatePreBarrierSyncState,
  type WorkerBarrierReport,
} from '../../scripts/stress/flyCoordinatorCore';

function makeReport(siteId: 'site-a' | 'site-b' | 'site-c', selfSeq: number): WorkerBarrierReport {
  return {
    runId: 'run-1',
    siteId,
    region: 'test',
    barrierIndex: 1,
    barrierType: 'hard',
    phase: 'pre',
    opIndex: 10,
    stateHash: 'abc',
    rowCount: 1,
    heads: { 'site-a': 1, 'site-b': 1, 'site-c': 1 },
    syncedHeads: {
      'site-a': siteId === 'site-a' ? selfSeq : 0,
      'site-b': siteId === 'site-b' ? selfSeq : 0,
      'site-c': siteId === 'site-c' ? selfSeq : 0,
    },
    pendingOps: 0,
    invariantOk: true,
    invariantErrors: [],
    expectedLocalPointsByRow: {},
    expectedLocalTagsByRow: {},
    stats: { writes: 0, pushes: 0, pulls: 0, syncs: 0 },
    generatedAt: new Date().toISOString(),
  };
}

describe('fly coordinator core helpers', () => {
  it('normalizes fly API base URL to include /v1', () => {
    expect(resolveFlyApiBaseUrl(undefined)).toBe('https://api.machines.dev/v1');
    expect(resolveFlyApiBaseUrl('https://api.machines.dev')).toBe('https://api.machines.dev/v1');
    expect(resolveFlyApiBaseUrl('https://api.machines.dev/v1')).toBe('https://api.machines.dev/v1');
    expect(resolveFlyApiBaseUrl('https://api.machines.dev/v1/')).toBe('https://api.machines.dev/v1');
  });

  it('sanitizes bucket names into valid lowercase forms', () => {
    const bucket = sanitizeBucketName('CRDTBASE_STRESS__RUN#ABC');
    expect(bucket).toMatch(/^[a-z0-9.-]{3,63}$/);
    expect(bucket).toContain('crdtbase-stress');
  });

  it('validates pre-barrier sync state and computes target heads', () => {
    const reports = [makeReport('site-a', 11), makeReport('site-b', 13), makeReport('site-c', 17)];
    expect(() => validatePreBarrierSyncState(reports)).not.toThrow();
    expect(computeTargetHeadsFromPreReports(reports)).toEqual({
      'site-a': 11,
      'site-b': 13,
      'site-c': 17,
    });
  });

  it('fails validation when pending ops remain at pre barrier', () => {
    const reports = [makeReport('site-a', 1), makeReport('site-b', 2), makeReport('site-c', 3)];
    reports[1].pendingOps = 2;
    expect(() => validatePreBarrierSyncState(reports)).toThrow(/pendingOps/);
  });
});
