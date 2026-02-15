import { AppendLogEntry, LogEntry, LogPosition, ReplicatedLog } from '../../core/replication';
import { HttpSnapshotStore } from './httpSnapshotStore';

function normalizeBaseUrl(baseUrl: string): string {
  return baseUrl.replace(/\/+$/u, '');
}

async function readJsonResponse<T>(response: Response): Promise<T> {
  const raw = await response.text();
  let body: unknown = null;
  if (raw.length > 0) {
    try {
      body = JSON.parse(raw) as unknown;
    } catch {
      throw new Error(`expected JSON response, got: ${raw}`);
    }
  }

  if (!response.ok) {
    const message =
      body && typeof body === 'object' && 'error' in body
        ? String((body as Record<string, unknown>).error)
        : `${response.status} ${response.statusText}`;
    throw new Error(`replicated log request failed: ${message}`);
  }

  return body as T;
}

export class HttpReplicatedLog implements ReplicatedLog {
  private readonly baseUrl: string;

  constructor(baseUrl: string) {
    this.baseUrl = normalizeBaseUrl(baseUrl);
  }

  async append(entry: AppendLogEntry): Promise<LogPosition> {
    const response = await fetch(
      `${this.baseUrl}/logs/${encodeURIComponent(entry.siteId)}`,
      {
        method: 'POST',
        headers: { 'content-type': 'application/json' },
        body: JSON.stringify(entry),
      },
    );
    const body = await readJsonResponse<{ seq: LogPosition }>(response);
    return body.seq;
  }

  async readSince(siteId: string, since: LogPosition): Promise<LogEntry[]> {
    const response = await fetch(
      `${this.baseUrl}/logs/${encodeURIComponent(siteId)}?since=${encodeURIComponent(
        String(since),
      )}`,
    );
    const body = await readJsonResponse<{ entries: LogEntry[] }>(response);
    return body.entries;
  }

  async listSites(): Promise<string[]> {
    const response = await fetch(`${this.baseUrl}/logs`);
    const body = await readJsonResponse<{ sites: string[] }>(response);
    return body.sites;
  }

  async getHead(siteId: string): Promise<LogPosition> {
    const response = await fetch(`${this.baseUrl}/logs/${encodeURIComponent(siteId)}/head`);
    const body = await readJsonResponse<{ seq: LogPosition }>(response);
    return body.seq;
  }

  getSnapshotStore(): HttpSnapshotStore {
    return new HttpSnapshotStore(this.baseUrl);
  }
}
