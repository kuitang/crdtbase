import { mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { describe, expect } from 'vitest';
import { compactReplicatedLog } from '../../src/platform/node/compactor';
import { BrowserCrdtClient } from '../../src/platform/browser/browserClient';
import { NodeCrdtClient } from '../../src/platform/node/nodeClient';
import { createHlcClock } from '../../src/core/hlc';
import { AppendLogEntry, LogEntry, LogPosition, ReplicatedLog } from '../../src/core/replication';
import type { SnapshotStore } from '../../src/core/snapshotStore';
import type { SqlSchema, EncodedCrdtOp } from '../../src/core/sql';
import type { ManifestFile } from '../../src/core/compaction';
import { decodeBin, encodeBin } from '../../src/core/encoding';

const TASKS_SCHEMA: SqlSchema = {
  tasks: {
    pk: 'id',
    partitionBy: null,
    columns: {
      id: { crdt: 'scalar' },
      points: { crdt: 'pn_counter' },
    },
  },
};

type SiteId = 'site-a' | 'site-b' | 'site-c';

type Event = {
  siteId: SiteId;
  rowId: 't1' | 't2' | 't3';
  amount: number;
};

class InMemorySnapshotStore implements SnapshotStore {
  private manifest: ManifestFile | null = null;
  private readonly segments = new Map<string, Uint8Array>();
  private schema: SqlSchema | null = null;

  manifestReads = 0;
  segmentReads = 0;

  async getManifest(): Promise<ManifestFile | null> {
    this.manifestReads += 1;
    return this.manifest ? decodeBin<ManifestFile>(encodeBin(this.manifest)) : null;
  }

  async putManifest(manifest: ManifestFile, expectedVersion: number): Promise<boolean> {
    const currentVersion = this.manifest?.version ?? 0;
    if (currentVersion !== expectedVersion) {
      return false;
    }
    this.manifest = decodeBin<ManifestFile>(encodeBin(manifest));
    return true;
  }

  async getSegment(path: string): Promise<Uint8Array | null> {
    this.segmentReads += 1;
    const value = this.segments.get(path);
    return value ? new Uint8Array(value) : null;
  }

  async putSegment(path: string, data: Uint8Array): Promise<void> {
    this.segments.set(path, new Uint8Array(data));
  }

  async getSchema(): Promise<SqlSchema | null> {
    return this.schema ? decodeBin<SqlSchema>(encodeBin(this.schema)) : null;
  }

  async putSchema(schema: SqlSchema): Promise<void> {
    this.schema = decodeBin<SqlSchema>(encodeBin(schema));
  }
}

class InMemoryReplicatedLog implements ReplicatedLog {
  private readonly entriesBySite = new Map<string, LogEntry[]>();

  constructor(
    entriesBySite: Record<string, LogEntry[]>,
    private readonly snapshotStore: SnapshotStore | null,
  ) {
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
    return (this.entriesBySite.get(siteId) ?? []).filter((entry) => entry.seq > since);
  }

  async listSites(): Promise<string[]> {
    return [...this.entriesBySite.keys()].sort();
  }

  async getHead(siteId: string): Promise<LogPosition> {
    const entries = this.entriesBySite.get(siteId) ?? [];
    return entries.length === 0 ? 0 : entries[entries.length - 1]!.seq;
  }

  getSnapshotStore(): SnapshotStore | null {
    return this.snapshotStore;
  }
}

function makeEventEntries(events: readonly Event[]): Record<string, LogEntry[]> {
  const out: Record<string, LogEntry[]> = {
    'site-a': [],
    'site-b': [],
    'site-c': [],
  };
  const nextSeq: Record<SiteId, number> = {
    'site-a': 1,
    'site-b': 1,
    'site-c': 1,
  };

  for (let index = 0; index < events.length; index += 1) {
    const event = events[index]!;
    const seq = nextSeq[event.siteId];
    nextSeq[event.siteId] += 1;
    const hlc = `0x${((0x1000n + BigInt(index + 1)) << 16n).toString(16)}`;
    const ops: EncodedCrdtOp[] = [
      {
        tbl: 'tasks',
        key: event.rowId,
        hlc,
        site: event.siteId,
        kind: 'row_exists',
        exists: true,
      },
      {
        tbl: 'tasks',
        key: event.rowId,
        col: 'points',
        hlc,
        site: event.siteId,
        kind: 'cell_counter',
        d: 'inc',
        n: event.amount,
      },
    ];

    out[event.siteId].push({
      siteId: event.siteId,
      hlc,
      seq,
      ops,
    });
  }

  return out;
}

function normalizeTaskRows(rows: Record<string, unknown>[]): Array<{ id: string; points: number }> {
  return [...rows]
    .map((row) => ({
      id: String(row.id),
      points: typeof row.points === 'number' ? row.points : 0,
    }))
    .sort((left, right) => left.id.localeCompare(right.id));
}

const arbEvent: fc.Arbitrary<Event> = fc.record({
  siteId: fc.constantFrom<SiteId>('site-a', 'site-b', 'site-c'),
  rowId: fc.constantFrom<'t1' | 't2' | 't3'>('t1', 't2', 't3'),
  amount: fc.integer({ min: 1, max: 9 }),
});

const arbScenario = fc
  .array(arbEvent, { minLength: 2, maxLength: 40 })
  .chain((events) =>
    fc.integer({ min: 1, max: events.length - 1 }).map((split) => ({ events, split })),
  );

const arbSiteAScenario = fc
  .array(
    fc.record({
      rowId: fc.constantFrom<'t1' | 't2' | 't3'>('t1', 't2', 't3'),
      amount: fc.integer({ min: 1, max: 9 }),
    }),
    { minLength: 3, maxLength: 40 },
  )
  .chain((events) =>
    fc.integer({ min: 1, max: events.length - 1 }).map((split) => ({
      events: events.map((event) => ({
        siteId: 'site-a' as const,
        rowId: event.rowId,
        amount: event.amount,
      })),
      split,
    })),
  );

const CREATE_TASKS_SQL = `CREATE TABLE tasks (id PRIMARY KEY, points COUNTER);`;

describe('Snapshot-first pull properties', () => {
  test.prop([arbScenario], { numRuns: 20 })(
    'node client state equals full-log replay when loading compacted prefix + tail deltas',
    async ({ events, split }) => {
      const prefixEntries = makeEventEntries(events.slice(0, split));
      const fullEntries = makeEventEntries(events);

      const store = new InMemorySnapshotStore();
      await store.putSchema(TASKS_SCHEMA);
      const prefixLog = new InMemoryReplicatedLog(prefixEntries, store);
      const compaction = await compactReplicatedLog({
        log: prefixLog,
        snapshots: store,
        schema: TASKS_SCHEMA,
      });
      expect(compaction.applied).toBe(true);

      const withSnapshots = new InMemoryReplicatedLog(fullEntries, store);
      const plain = new InMemoryReplicatedLog(fullEntries, null);

      const dataDirWithSnapshots = await mkdtemp(join(tmpdir(), 'crdtbase-snapshot-node-a-'));
      const dataDirPlain = await mkdtemp(join(tmpdir(), 'crdtbase-snapshot-node-b-'));
      try {
        const fromSnapshots = await NodeCrdtClient.open({
          siteId: 'site-z',
          log: withSnapshots,
          dataDir: dataDirWithSnapshots,
          clock: createHlcClock({ nowWallMs: () => 10_000 }),
        });
        const fullReplay = await NodeCrdtClient.open({
          siteId: 'site-y',
          log: plain,
          dataDir: dataDirPlain,
          clock: createHlcClock({ nowWallMs: () => 20_000 }),
        });

        await fromSnapshots.exec(CREATE_TASKS_SQL);
        await fullReplay.exec(CREATE_TASKS_SQL);

        await fromSnapshots.pull();
        await fullReplay.pull();

        const rowsSnapshot = normalizeTaskRows(await fromSnapshots.query('SELECT id, points FROM tasks;'));
        const rowsReplay = normalizeTaskRows(await fullReplay.query('SELECT id, points FROM tasks;'));
        expect(rowsSnapshot).toEqual(rowsReplay);
        expect(store.manifestReads).toBeGreaterThan(0);
        expect(store.segmentReads).toBeGreaterThan(0);
      } finally {
        await rm(dataDirWithSnapshots, { recursive: true, force: true });
        await rm(dataDirPlain, { recursive: true, force: true });
      }
    },
  );

  test.prop([arbScenario], { numRuns: 20 })(
    'browser client state equals full-log replay when loading compacted prefix + tail deltas',
    async ({ events, split }) => {
      const prefixEntries = makeEventEntries(events.slice(0, split));
      const fullEntries = makeEventEntries(events);

      const store = new InMemorySnapshotStore();
      await store.putSchema(TASKS_SCHEMA);
      const prefixLog = new InMemoryReplicatedLog(prefixEntries, store);
      const compaction = await compactReplicatedLog({
        log: prefixLog,
        snapshots: store,
        schema: TASKS_SCHEMA,
      });
      expect(compaction.applied).toBe(true);

      const withSnapshots = new InMemoryReplicatedLog(fullEntries, store);
      const plain = new InMemoryReplicatedLog(fullEntries, null);

      const fromSnapshots = await BrowserCrdtClient.open({
        siteId: 'site-z',
        log: withSnapshots,
        clock: createHlcClock({ nowWallMs: () => 10_000 }),
        storage: null,
      });
      const fullReplay = await BrowserCrdtClient.open({
        siteId: 'site-y',
        log: plain,
        clock: createHlcClock({ nowWallMs: () => 20_000 }),
        storage: null,
      });

      await fromSnapshots.exec(CREATE_TASKS_SQL);
      await fullReplay.exec(CREATE_TASKS_SQL);

      await fromSnapshots.pull();
      await fullReplay.pull();

      const rowsSnapshot = normalizeTaskRows(await fromSnapshots.query('SELECT id, points FROM tasks;'));
      const rowsReplay = normalizeTaskRows(await fullReplay.query('SELECT id, points FROM tasks;'));
      expect(rowsSnapshot).toEqual(rowsReplay);
      expect(store.manifestReads).toBeGreaterThan(0);
      expect(store.segmentReads).toBeGreaterThan(0);
    },
  );

  test.prop([arbSiteAScenario], { numRuns: 20 })(
    'node client ignores newer manifest missing previously synced site watermark',
    async ({ events, split }) => {
      const prefixEntries = makeEventEntries(events.slice(0, split));
      const fullEntries = makeEventEntries(events);

      const store = new InMemorySnapshotStore();
      await store.putSchema(TASKS_SCHEMA);
      const prefixLog = new InMemoryReplicatedLog(prefixEntries, store);
      const compaction = await compactReplicatedLog({
        log: prefixLog,
        snapshots: store,
        schema: TASKS_SCHEMA,
      });
      expect(compaction.applied).toBe(true);

      const fullLog = new InMemoryReplicatedLog(fullEntries, store);
      const dataDir = await mkdtemp(join(tmpdir(), 'crdtbase-snapshot-node-coverage-'));
      try {
        const client = await NodeCrdtClient.open({
          siteId: 'site-local',
          log: fullLog,
          dataDir,
          clock: createHlcClock({ nowWallMs: () => 10_000 }),
        });

        await client.exec(CREATE_TASKS_SQL);
        await client.pull();
        const before = normalizeTaskRows(await client.query('SELECT id, points FROM tasks;'));

        const priorManifest = await store.getManifest();
        expect(priorManifest).not.toBeNull();
        const buggySitesCompacted = {
          ...(priorManifest?.sites_compacted ?? {}),
        } as Record<string, number>;
        delete buggySitesCompacted['site-a'];

        const applied = await store.putManifest(
          {
            ...(priorManifest as ManifestFile),
            version: (priorManifest as ManifestFile).version + 1,
            sites_compacted: buggySitesCompacted,
          },
          (priorManifest as ManifestFile).version,
        );
        expect(applied).toBe(true);

        await client.pull();
        const after = normalizeTaskRows(await client.query('SELECT id, points FROM tasks;'));
        expect(after).toEqual(before);
      } finally {
        await rm(dataDir, { recursive: true, force: true });
      }
    },
  );

  test.prop([arbSiteAScenario], { numRuns: 20 })(
    'browser client ignores newer manifest missing previously synced site watermark',
    async ({ events, split }) => {
      const prefixEntries = makeEventEntries(events.slice(0, split));
      const fullEntries = makeEventEntries(events);

      const store = new InMemorySnapshotStore();
      await store.putSchema(TASKS_SCHEMA);
      const prefixLog = new InMemoryReplicatedLog(prefixEntries, store);
      const compaction = await compactReplicatedLog({
        log: prefixLog,
        snapshots: store,
        schema: TASKS_SCHEMA,
      });
      expect(compaction.applied).toBe(true);

      const fullLog = new InMemoryReplicatedLog(fullEntries, store);
      const client = await BrowserCrdtClient.open({
        siteId: 'site-local',
        log: fullLog,
        clock: createHlcClock({ nowWallMs: () => 10_000 }),
        storage: null,
      });

      await client.exec(CREATE_TASKS_SQL);
      await client.pull();
      const before = normalizeTaskRows(await client.query('SELECT id, points FROM tasks;'));

      const priorManifest = await store.getManifest();
      expect(priorManifest).not.toBeNull();
      const buggySitesCompacted = {
        ...(priorManifest?.sites_compacted ?? {}),
      } as Record<string, number>;
      delete buggySitesCompacted['site-a'];

      const applied = await store.putManifest(
        {
          ...(priorManifest as ManifestFile),
          version: (priorManifest as ManifestFile).version + 1,
          sites_compacted: buggySitesCompacted,
        },
        (priorManifest as ManifestFile).version,
      );
      expect(applied).toBe(true);

      await client.pull();
      const after = normalizeTaskRows(await client.query('SELECT id, points FROM tasks;'));
      expect(after).toEqual(before);
    },
  );

  test.prop([arbScenario, fc.integer({ min: 1, max: 9 })], { numRuns: 15 })(
    'node pull preserves pending local writes across snapshot refresh',
    async ({ events, split }, pendingAmount) => {
      const prefixEntries = makeEventEntries(events.slice(0, split));
      const fullEntries = makeEventEntries(events);

      const store = new InMemorySnapshotStore();
      await store.putSchema(TASKS_SCHEMA);
      const prefixLog = new InMemoryReplicatedLog(prefixEntries, store);
      await compactReplicatedLog({
        log: prefixLog,
        snapshots: store,
        schema: TASKS_SCHEMA,
      });

      const fullLog = new InMemoryReplicatedLog(fullEntries, store);
      const dataDir = await mkdtemp(join(tmpdir(), 'crdtbase-snapshot-node-pending-'));
      try {
        const client = await NodeCrdtClient.open({
          siteId: 'site-local',
          log: fullLog,
          dataDir,
          clock: createHlcClock({ nowWallMs: () => 10_000 }),
        });

        await client.pull();
        await client.exec(`INC tasks.points BY ${pendingAmount} WHERE id = 't1';`);

        // Bump manifest version without new log ops; pull should keep local pending write.
        await compactReplicatedLog({
          log: fullLog,
          snapshots: store,
          schema: TASKS_SCHEMA,
        });

        const before = normalizeTaskRows(await client.query("SELECT id, points FROM tasks WHERE id = 't1';"));
        await client.pull();
        const after = normalizeTaskRows(await client.query("SELECT id, points FROM tasks WHERE id = 't1';"));
        expect(after).toEqual(before);
      } finally {
        await rm(dataDir, { recursive: true, force: true });
      }
    },
  );
});
