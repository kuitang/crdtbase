import { Hlc, packHlc } from '../hlc';

export type LwwEventIdentity = {
  table: string;
  key: string | number;
  col: string;
  site: string;
  hlc: Hlc;
};

function encodeIdentity(id: LwwEventIdentity): string {
  return [
    id.table,
    String(id.key),
    id.col,
    id.site,
    packHlc(id.hlc).toString(16),
  ].join('\u001f');
}

function fingerprintValue(value: unknown): string {
  const kind = typeof value;
  if (value === null || kind === 'string' || kind === 'number' || kind === 'boolean') {
    return `${kind}:${String(value)}`;
  }
  return `json:${JSON.stringify(value)}`;
}

export class LwwConflictGuard {
  private readonly seen = new Map<string, string>();

  observe(identity: LwwEventIdentity, value: unknown): void {
    const key = encodeIdentity(identity);
    const nextFingerprint = fingerprintValue(value);
    const priorFingerprint = this.seen.get(key);
    if (priorFingerprint !== undefined && priorFingerprint !== nextFingerprint) {
      throw new Error(
        `conflicting LWW payload for identity ${identity.table}.${identity.col} key=${identity.key} site=${identity.site}`,
      );
    }
    this.seen.set(key, nextFingerprint);
  }
}
