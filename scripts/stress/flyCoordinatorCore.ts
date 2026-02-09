export const SITE_IDS = ['site-a', 'site-b', 'site-c'] as const;

export type SiteId = (typeof SITE_IDS)[number];

export type WorkerBarrierReport = {
  runId: string;
  siteId: SiteId;
  region: string;
  barrierIndex: number;
  barrierType: 'soft' | 'hard';
  phase: 'pre' | 'drained';
  opIndex: number;
  stateHash: string;
  rowCount: number;
  heads: Record<string, number>;
  syncedHeads: Record<string, number>;
  pendingOps: number;
  invariantOk: boolean;
  invariantErrors: string[];
  expectedLocalPointsByRow: Record<string, number>;
  expectedLocalTagsByRow: Record<string, string[]>;
  stats: {
    writes: number;
    pushes: number;
    pulls: number;
    syncs: number;
  };
  generatedAt: string;
};

export function sanitizeBucketName(raw: string): string {
  let value = raw
    .toLowerCase()
    .replace(/_/g, '-')
    .replace(/[^a-z0-9.-]+/g, '-')
    .replace(/^-+/, '')
    .replace(/-+$/, '')
    .replace(/\.{2,}/g, '.');
  value = value.replace(/^-+/, '').replace(/-+$/, '').replace(/^\.+/, '').replace(/\.+$/, '');
  if (value.length < 3) {
    value = `crdtbase-stress-${Date.now()}`;
  }
  if (value.length > 63) {
    value = value.slice(0, 63);
  }
  return value;
}

export function resolveFlyApiBaseUrl(raw: string | undefined): string {
  const trimmed = (raw ?? 'https://api.machines.dev').trim().replace(/\/+$/, '');
  if (trimmed.endsWith('/v1')) {
    return trimmed;
  }
  return `${trimmed}/v1`;
}

export function validatePreBarrierSyncState(reports: WorkerBarrierReport[]): void {
  const bySite = new Map(reports.map((report) => [report.siteId, report]));
  for (const site of SITE_IDS) {
    const report = bySite.get(site);
    if (!report) {
      throw new Error(`missing pre-barrier report for ${site}`);
    }
    if (!Number.isInteger(report.pendingOps) || report.pendingOps !== 0) {
      throw new Error(
        `invalid pre-barrier pendingOps for ${site}: expected=0 actual=${String(report.pendingOps)}`,
      );
    }
    const selfSynced = report.syncedHeads[site];
    if (!Number.isInteger(selfSynced) || selfSynced < 0) {
      throw new Error(`invalid pre-barrier syncedHeads[${site}] for ${site}: ${String(selfSynced)}`);
    }
  }
}

export function computeTargetHeadsFromPreReports(
  reports: WorkerBarrierReport[],
): Record<SiteId, number> {
  validatePreBarrierSyncState(reports);
  const bySite = new Map(reports.map((report) => [report.siteId, report]));
  const out = {} as Record<SiteId, number>;
  for (const site of SITE_IDS) {
    out[site] = bySite.get(site)!.syncedHeads[site]!;
  }
  return out;
}
