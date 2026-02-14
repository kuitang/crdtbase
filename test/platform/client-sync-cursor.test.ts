import { mkdtemp, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import { encodeBin } from '../../src/core/encoding';
import { createHlcClock } from '../../src/core/hlc';
import { AppendLogEntry, LogEntry, LogPosition, ReplicatedLog } from '../../src/core/replication';
import { EncodedCrdtOp } from '../../src/core/sql';
import { BrowserCrdtClient } from '../../src/platform/browser/browserClient';
import { NodeCrdtClient } from '../../src/platform/node/nodeClient';

class StubReplicatedLog implements ReplicatedLog {
  private readonly entriesBySite = new Map<string, LogEntry[]>();
  readSinceCalls = 0;

  constructor(entriesBySite: Record<string, LogEntry[]>) {
    for (const [siteId, entries] of Object.entries(entriesBySite)) {
      this.entriesBySite.set(
        siteId,
        [...entries].sort((left, right) => left.seq - right.seq),
      );
    }
  }

  async append(entry: AppendLogEntry): Promise<LogPosition> {
    const entries = this.entriesBySite.get(entry.siteId) ?? [];
    const next = entries.length === 0 ? 1 : entries[entries.length - 1]!.seq + 1;
    entries.push({
      siteId: entry.siteId,
      hlc: entry.hlc,
      seq: next,
      ops: [...entry.ops],
    });
    this.entriesBySite.set(entry.siteId, entries);
    return next;
  }

  async readSince(siteId: string, since: LogPosition): Promise<LogEntry[]> {
    this.readSinceCalls += 1;
    return (this.entriesBySite.get(siteId) ?? []).filter((entry) => entry.seq > since);
  }

  async listSites(): Promise<string[]> {
    return [...this.entriesBySite.keys()].sort();
  }

  async getHead(siteId: string): Promise<LogPosition> {
    const entries = this.entriesBySite.get(siteId) ?? [];
    return entries.length === 0 ? 0 : entries[entries.length - 1]!.seq;
  }

  getEntries(siteId: string): LogEntry[] {
    return [...(this.entriesBySite.get(siteId) ?? [])];
  }
}

class GapFirstReadReplicatedLog implements ReplicatedLog {
  private readonly entriesBySite = new Map<string, LogEntry[]>();
  private gapInjected = false;

  constructor(entriesBySite: Record<string, LogEntry[]>) {
    for (const [siteId, entries] of Object.entries(entriesBySite)) {
      this.entriesBySite.set(
        siteId,
        [...entries].sort((left, right) => left.seq - right.seq),
      );
    }
  }

  async append(entry: AppendLogEntry): Promise<LogPosition> {
    const entries = this.entriesBySite.get(entry.siteId) ?? [];
    const next = entries.length === 0 ? 1 : entries[entries.length - 1]!.seq + 1;
    entries.push({
      siteId: entry.siteId,
      hlc: entry.hlc,
      seq: next,
      ops: [...entry.ops],
    });
    this.entriesBySite.set(entry.siteId, entries);
    return next;
  }

  async readSince(siteId: string, since: LogPosition): Promise<LogEntry[]> {
    const all = (this.entriesBySite.get(siteId) ?? []).filter((entry) => entry.seq > since);
    if (!this.gapInjected && since === 0) {
      this.gapInjected = true;
      return all.filter((entry) => entry.seq !== 2);
    }
    return all;
  }

  async listSites(): Promise<string[]> {
    return [...this.entriesBySite.keys()].sort();
  }

  async getHead(siteId: string): Promise<LogPosition> {
    const entries = this.entriesBySite.get(siteId) ?? [];
    return entries.length === 0 ? 0 : entries[entries.length - 1]!.seq;
  }
}

async function writeNodeSyncFileV1(
  dataDir: string,
  syncedSeqBySite: Record<string, LogPosition>,
): Promise<void> {
  await writeFile(
    join(dataDir, 'sync.bin'),
    encodeBin({
      v: 1 as const,
      syncedSeqBySite,
    }),
  );
}

async function writeNodeSyncFileV2(
  dataDir: string,
  syncedBySite: Record<string, { seq: LogPosition; hlc: string | null }>,
): Promise<void> {
  await writeFile(
    join(dataDir, 'sync.bin'),
    encodeBin({
      v: 2 as const,
      syncedBySite,
    }),
  );
}

function makeCounterEntry(seq: number, amount: number): LogEntry {
  const existsOp: EncodedCrdtOp = {
    tbl: 'tasks',
    key: 't1',
    hlc: `0x1000${seq}`,
    site: 'site-a',
    kind: 'row_exists',
    exists: true,
  };
  const op: EncodedCrdtOp = {
    tbl: 'tasks',
    key: 't1',
    col: 'points',
    hlc: `0x1000${seq}`,
    site: 'site-a',
    kind: 'cell_counter',
    d: 'inc',
    n: amount,
  };
  return {
    siteId: 'site-a',
    hlc: op.hlc,
    seq,
    ops: [existsOp, op],
  };
}

function packHlcHex(wallMs: number, counter: number): string {
  return `0x${((BigInt(wallMs) << 16n) | BigInt(counter)).toString(16)}`;
}

describe('client sync cursor safety', () => {
  const tempDirs: string[] = [];

  afterEach(async () => {
    await Promise.all(
      tempDirs.splice(0, tempDirs.length).map((dir) => rm(dir, { recursive: true, force: true })),
    );
  });

  it('throws in node client when local cursor is ahead of remote head', async () => {
    const dataDir = await mkdtemp(join(tmpdir(), 'crdtbase-node-sync-cursor-'));
    tempDirs.push(dataDir);
    await writeNodeSyncFileV1(dataDir, {
      'site-a': 4,
    });

    const log = new StubReplicatedLog({
      'site-a': [
        {
          siteId: 'site-a',
          hlc: '0x10001',
          seq: 1,
          ops: [],
        },
      ],
    });
    const client = await NodeCrdtClient.open({
      siteId: 'site-b',
      log,
      dataDir,
      clock: createHlcClock({ nowWallMs: () => 1_000 }),
    });

    await expect(client.pull()).rejects.toThrow("local sync cursor for site 'site-a' (4) is ahead");
    expect(log.readSinceCalls).toBe(0);
  });

  it('throws in node client when cursor seq exists but HLC does not match', async () => {
    const dataDir = await mkdtemp(join(tmpdir(), 'crdtbase-node-sync-cursor-hlc-'));
    tempDirs.push(dataDir);
    await writeNodeSyncFileV2(dataDir, {
      'site-a': {
        seq: 1,
        hlc: '0x10001',
      },
    });

    const log = new StubReplicatedLog({
      'site-a': [
        {
          siteId: 'site-a',
          hlc: '0x20001',
          seq: 1,
          ops: [],
        },
      ],
    });
    const client = await NodeCrdtClient.open({
      siteId: 'site-b',
      log,
      dataDir,
      clock: createHlcClock({ nowWallMs: () => 2_000 }),
    });

    await expect(client.pull()).rejects.toThrow("sync cursor mismatch for site 'site-a' at seq 1");
    expect(log.readSinceCalls).toBe(1);
  });

  it('throws in browser client when local cursor is ahead of remote head', async () => {
    const log = new StubReplicatedLog({
      'site-a': [
        {
          siteId: 'site-a',
          hlc: '0x10001',
          seq: 2,
          ops: [],
        },
      ],
    });
    const client = await BrowserCrdtClient.open({
      siteId: 'site-b',
      log,
      clock: createHlcClock({ nowWallMs: () => 2_000 }),
    });
    client.hydrateForTest({
      syncedSeqBySite: {
        'site-a': 7,
      },
    });

    await expect(client.pull()).rejects.toThrow("local sync cursor for site 'site-a' (7) is ahead");
    expect(log.readSinceCalls).toBe(0);
  });

  it('throws in browser client when cursor seq exists but HLC does not match', async () => {
    const log = new StubReplicatedLog({
      'site-a': [
        {
          siteId: 'site-a',
          hlc: '0x30001',
          seq: 1,
          ops: [],
        },
      ],
    });
    const client = await BrowserCrdtClient.open({
      siteId: 'site-b',
      log,
      clock: createHlcClock({ nowWallMs: () => 4_000 }),
    });
    client.hydrateForTest({
      syncedSeqBySite: {
        'site-a': 1,
      },
      syncedHlcBySite: {
        'site-a': '0x10001',
      },
    });

    await expect(client.pull()).rejects.toThrow("sync cursor mismatch for site 'site-a' at seq 1");
    expect(log.readSinceCalls).toBe(1);
  });

  it('node client does not skip missing seq when first listing is gappy', async () => {
    const dataDir = await mkdtemp(join(tmpdir(), 'crdtbase-node-gap-readsince-'));
    tempDirs.push(dataDir);
    const log = new GapFirstReadReplicatedLog({
      'site-a': [
        makeCounterEntry(1, 1),
        makeCounterEntry(2, 2),
        makeCounterEntry(3, 3),
      ],
    });
    const client = await NodeCrdtClient.open({
      siteId: 'site-b',
      log,
      dataDir,
      clock: createHlcClock({ nowWallMs: () => 5_000 }),
    });
    await client.exec('CREATE TABLE tasks (id PRIMARY KEY, points COUNTER);');

    await client.pull();
    expect(client.getSyncedHeads()['site-a']).toBe(1);

    await client.pull();
    expect(client.getSyncedHeads()['site-a']).toBe(3);
  });

  it('browser client does not skip missing seq when first listing is gappy', async () => {
    const log = new GapFirstReadReplicatedLog({
      'site-a': [
        makeCounterEntry(1, 1),
        makeCounterEntry(2, 2),
        makeCounterEntry(3, 3),
      ],
    });
    const client = await BrowserCrdtClient.open({
      siteId: 'site-b',
      log,
      clock: createHlcClock({ nowWallMs: () => 6_000 }),
    });
    await client.exec('CREATE TABLE tasks (id PRIMARY KEY, points COUNTER);');

    await client.pull();
    expect(client.getSyncedHeads()['site-a']).toBe(1);

    await client.pull();
    expect(client.getSyncedHeads()['site-a']).toBe(3);
  });

  it('rejects drifted remote HLCs in node client pull', async () => {
    const dataDir = await mkdtemp(join(tmpdir(), 'crdtbase-node-drift-pull-'));
    tempDirs.push(dataDir);
    const driftedRemote = packHlcHex(100_000, 0);
    const log = new StubReplicatedLog({
      'site-a': [
        {
          siteId: 'site-a',
          hlc: driftedRemote,
          seq: 1,
          ops: [],
        },
      ],
    });
    const client = await NodeCrdtClient.open({
      siteId: 'site-b',
      log,
      dataDir,
      clock: createHlcClock({ nowWallMs: () => 1_000 }),
    });

    await expect(client.pull()).rejects.toThrow(/drift/i);
  });

  it('rejects drifted remote HLCs in browser client pull', async () => {
    const driftedRemote = packHlcHex(100_000, 0);
    const log = new StubReplicatedLog({
      'site-a': [
        {
          siteId: 'site-a',
          hlc: driftedRemote,
          seq: 1,
          ops: [],
        },
      ],
    });
    const client = await BrowserCrdtClient.open({
      siteId: 'site-b',
      log,
      clock: createHlcClock({ nowWallMs: () => 1_000 }),
    });

    await expect(client.pull()).rejects.toThrow(/drift/i);
  });

  it('advances local HLC from pulled remote timestamps before next local write', async () => {
    const dataDir = await mkdtemp(join(tmpdir(), 'crdtbase-node-hlc-recv-'));
    tempDirs.push(dataDir);
    const remoteHlc = packHlcHex(50_000, 0);
    const log = new StubReplicatedLog({
      'site-a': [
        {
          siteId: 'site-a',
          hlc: remoteHlc,
          seq: 1,
          ops: [],
        },
      ],
    });

    const client = await NodeCrdtClient.open({
      siteId: 'site-b',
      log,
      dataDir,
      clock: createHlcClock({ nowWallMs: () => 1_000 }),
    });
    await client.exec('CREATE TABLE tasks (id PRIMARY KEY, title LWW<STRING>);');
    await client.pull();
    await client.exec("INSERT INTO tasks (id, title) VALUES ('t1', 'hello');");
    await client.push();

    const siteBEntries = log.getEntries('site-b');
    expect(siteBEntries.length).toBe(1);
    expect(BigInt(siteBEntries[0]!.hlc)).toBeGreaterThan(BigInt(remoteHlc));
  });
});
