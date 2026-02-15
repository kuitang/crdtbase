import { mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { describe, expect } from 'vitest';
import { createHlcClock } from '../../src/core/hlc';
import { AppendLogEntry, LogEntry, LogPosition, ReplicatedLog } from '../../src/core/replication';
import { NodeCrdtClient } from '../../src/platform/node/nodeClient';
import {
  buildAddColumnSql,
  CREATE_TASKS_TABLE_SQL,
  DDL_SITE_IDS,
  DdlSiteId,
  schemaOwnerForSeed,
} from '../shared/tasksSchema';

class InMemoryReplicatedLog implements ReplicatedLog {
  private readonly entriesBySite = new Map<string, LogEntry[]>();

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
}

function createSeededRng(seed: number): () => number {
  let state = (seed >>> 0) || 0x6d2b79f5;
  return () => {
    state ^= state << 13;
    state ^= state >>> 17;
    state ^= state << 5;
    return (state >>> 0) / 0x1_0000_0000;
  };
}

function pickSite(rng: () => number): DdlSiteId {
  return DDL_SITE_IDS[Math.min(DDL_SITE_IDS.length - 1, Math.floor(rng() * DDL_SITE_IDS.length))]!;
}

function otherSite(siteId: DdlSiteId): DdlSiteId {
  return DDL_SITE_IDS.find((candidate) => candidate !== siteId)!;
}

async function syncAll(clients: Record<DdlSiteId, NodeCrdtClient>): Promise<void> {
  await Promise.all(DDL_SITE_IDS.map((siteId) => clients[siteId].sync()));
}

function stableRowJson(rows: Record<string, unknown>[]): string {
  const normalized = rows
    .map((row) =>
      Object.fromEntries(
        Object.keys(row)
          .sort((left, right) => left.localeCompare(right))
          .map((key) => [key, row[key]]),
      ))
    .sort((left, right) => String(left.id).localeCompare(String(right.id)));
  return JSON.stringify(normalized);
}

function crdtFromDefinition(definition: 'LWW<STRING>' | 'COUNTER'): 'lww' | 'pn_counter' {
  return definition === 'COUNTER' ? 'pn_counter' : 'lww';
}

describe('Multi-site schema replication properties', () => {
  test.prop([fc.integer()], { numRuns: 20 })(
    'schema propagates without local CREATE and concurrent ADD COLUMN converges with deterministic conflict rejection',
    async (rawSeed) => {
      const seed = rawSeed | 0;
      const rng = createSeededRng(seed);
      const owner = schemaOwnerForSeed(seed);
      const tempRoot = await mkdtemp(join(tmpdir(), 'crdtbase-multisite-schema-prop-'));
      try {
        const log = new InMemoryReplicatedLog();
        const clocks: Record<DdlSiteId, () => number> = {
          'site-a': (() => {
            let tick = 1_000;
            return () => {
              tick += 1;
              return tick;
            };
          })(),
          'site-b': (() => {
            let tick = 2_000;
            return () => {
              tick += 1;
              return tick;
            };
          })(),
          'site-c': (() => {
            let tick = 3_000;
            return () => {
              tick += 1;
              return tick;
            };
          })(),
        };
        const clients: Record<DdlSiteId, NodeCrdtClient> = {
          'site-a': await NodeCrdtClient.open({
            siteId: 'site-a',
            log,
            dataDir: join(tempRoot, 'site-a'),
            clock: createHlcClock({ nowWallMs: clocks['site-a'] }),
          }),
          'site-b': await NodeCrdtClient.open({
            siteId: 'site-b',
            log,
            dataDir: join(tempRoot, 'site-b'),
            clock: createHlcClock({ nowWallMs: clocks['site-b'] }),
          }),
          'site-c': await NodeCrdtClient.open({
            siteId: 'site-c',
            log,
            dataDir: join(tempRoot, 'site-c'),
            clock: createHlcClock({ nowWallMs: clocks['site-c'] }),
          }),
        };

        await clients[owner].exec(CREATE_TASKS_TABLE_SQL);
        await syncAll(clients);

        const nonOwner = otherSite(owner);
        await expect(
          clients[nonOwner].exec(
            "INSERT INTO tasks (id, title, points, tags, status) VALUES ('t1', 'seed', 0, 'seed', 'open');",
          ),
        ).resolves.toBeUndefined();
        await syncAll(clients);

        const uniqueAdds: Array<{ siteId: DdlSiteId; column: string }> = [];
        for (const siteId of DDL_SITE_IDS) {
          if (rng() < 0.7) {
            uniqueAdds.push({
              siteId,
              column: `extra_${siteId.replaceAll('-', '_')}_${Math.floor(rng() * 10_000)}`,
            });
          }
        }
        if (uniqueAdds.length === 0) {
          uniqueAdds.push({
            siteId: owner,
            column: `extra_${owner.replaceAll('-', '_')}_${Math.floor(rng() * 10_000)}`,
          });
        }

        for (const add of uniqueAdds) {
          await clients[add.siteId].exec(buildAddColumnSql(add.column, 'LWW<STRING>'));
        }
        await syncAll(clients);

        for (const add of uniqueAdds) {
          await clients[add.siteId].exec(
            `UPDATE tasks SET ${add.column} = '${add.siteId}' WHERE id = 't1';`,
          );
        }
        await syncAll(clients);

        const conflictColumn = `conflict_${Math.floor(rng() * 10_000)}`;
        const firstSite = pickSite(rng);
        const secondSite = otherSite(firstSite);
        const firstDefinition: 'LWW<STRING>' | 'COUNTER' = rng() < 0.5 ? 'LWW<STRING>' : 'COUNTER';
        const secondDefinition: 'LWW<STRING>' | 'COUNTER' =
          firstDefinition === 'LWW<STRING>' ? 'COUNTER' : 'LWW<STRING>';

        await clients[firstSite].exec(buildAddColumnSql(conflictColumn, firstDefinition));
        await syncAll(clients);
        await expect(
          clients[secondSite].exec(buildAddColumnSql(conflictColumn, secondDefinition)),
        ).rejects.toThrow(/conflict|existing/i);
        await syncAll(clients);

        const infoSchemas = await Promise.all(
          DDL_SITE_IDS.map((siteId) =>
            clients[siteId].query(
              "SELECT column_name, crdt_kind FROM information_schema.columns WHERE table_name = 'tasks';",
            )),
        );
        const normalizedInfo = infoSchemas.map((rows) =>
          rows
            .map((row) => ({
              column_name: String(row.column_name),
              crdt_kind: String(row.crdt_kind),
            }))
            .sort((left, right) => left.column_name.localeCompare(right.column_name)),
        );
        expect(normalizedInfo[0]).toEqual(normalizedInfo[1]);
        expect(normalizedInfo[1]).toEqual(normalizedInfo[2]);

        const expectedColumns = new Map<string, string>([
          ['id', 'scalar'],
          ['title', 'lww'],
          ['points', 'pn_counter'],
          ['tags', 'or_set'],
          ['status', 'mv_register'],
        ]);
        for (const add of uniqueAdds) {
          expectedColumns.set(add.column, 'lww');
        }
        expectedColumns.set(conflictColumn, crdtFromDefinition(firstDefinition));
        for (const [column, crdt] of expectedColumns.entries()) {
          expect(normalizedInfo[0].some((entry) => entry.column_name === column && entry.crdt_kind === crdt)).toBe(true);
        }

        const snapshots = await Promise.all(
          DDL_SITE_IDS.map((siteId) =>
            clients[siteId].query("SELECT * FROM tasks WHERE id = 't1';"),
          ),
        );
        const [first, second, third] = snapshots.map(stableRowJson);
        expect(first).toBe(second);
        expect(second).toBe(third);
      } finally {
        await rm(tempRoot, { recursive: true, force: true });
      }
    },
  );
});
