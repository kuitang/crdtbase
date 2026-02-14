import { describe, expect, it } from 'vitest';
import { createHlcClock } from '../../src/core/hlc';
import { BrowserCrdtClient, BrowserHlcStorage } from '../../src/platform/browser/browserClient';
import { AppendLogEntry, LogEntry, LogPosition, ReplicatedLog } from '../../src/core/replication';

class InMemoryReplicatedLog implements ReplicatedLog {
  private readonly entriesBySite = new Map<string, LogEntry[]>();

  async append(entry: AppendLogEntry): Promise<LogPosition> {
    const entries = this.entriesBySite.get(entry.siteId) ?? [];
    const nextSeq = entries.length === 0 ? 1 : entries[entries.length - 1]!.seq + 1;
    entries.push({
      siteId: entry.siteId,
      hlc: entry.hlc,
      seq: nextSeq,
      ops: [...entry.ops],
    });
    this.entriesBySite.set(entry.siteId, entries);
    return nextSeq;
  }

  async readSince(siteId: string, since: LogPosition): Promise<LogEntry[]> {
    return (this.entriesBySite.get(siteId) ?? []).filter((entry) => entry.seq > since);
  }

  async listSites(): Promise<string[]> {
    return [...this.entriesBySite.keys()].sort();
  }

  async getHead(siteId: string): Promise<LogPosition> {
    const entries = this.entriesBySite.get(siteId) ?? [];
    return entries.length === 0 ? 0 : entries[entries.length - 1]!.seq;
  }
}

class MemoryStorage implements BrowserHlcStorage {
  private readonly values = new Map<string, string>();

  getItem(key: string): string | null {
    return this.values.get(key) ?? null;
  }

  setItem(key: string, value: string): void {
    this.values.set(key, value);
  }
}

describe('Browser client HLC persistence', () => {
  it('persists HLC high-water mark across restart when storage is available', async () => {
    const log = new InMemoryReplicatedLog();
    const storage = new MemoryStorage();
    const now = () => 1_000;

    const first = await BrowserCrdtClient.open({
      siteId: 'site-a',
      log,
      clock: createHlcClock({ nowWallMs: now }),
      storage,
    });
    await first.exec('CREATE TABLE tasks (id PRIMARY KEY, title LWW<STRING>);');
    await first.exec("INSERT INTO tasks (id, title) VALUES ('t1', 'a');");
    await first.push();

    const restarted = await BrowserCrdtClient.open({
      siteId: 'site-a',
      log,
      clock: createHlcClock({ nowWallMs: now }),
      storage,
    });
    await restarted.exec('CREATE TABLE tasks (id PRIMARY KEY, title LWW<STRING>);');
    await restarted.pull();

    await expect(
      restarted.exec("UPDATE tasks SET title = 'b' WHERE id = 't1';"),
    ).resolves.toBeUndefined();
  });

  it('advances local HLC from pull after restart even when persistence is unavailable', async () => {
    const log = new InMemoryReplicatedLog();
    const now = () => 1_000;

    const first = await BrowserCrdtClient.open({
      siteId: 'site-a',
      log,
      clock: createHlcClock({ nowWallMs: now }),
      storage: null,
    });
    await first.exec('CREATE TABLE tasks (id PRIMARY KEY, title LWW<STRING>);');
    await first.exec("INSERT INTO tasks (id, title) VALUES ('t1', 'a');");
    await first.push();

    const restarted = await BrowserCrdtClient.open({
      siteId: 'site-a',
      log,
      clock: createHlcClock({ nowWallMs: now }),
      storage: null,
    });
    await restarted.exec('CREATE TABLE tasks (id PRIMARY KEY, title LWW<STRING>);');
    await restarted.pull();

    await expect(restarted.exec("UPDATE tasks SET title = 'b' WHERE id = 't1';")).resolves.toBeUndefined();
  });
});
