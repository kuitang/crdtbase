import { mkdtemp, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { describe, expect } from 'vitest';
import { encodeBin } from '../../src/core/encoding';
import { createHlcClock } from '../../src/core/hlc';
import { AppendLogEntry, LogEntry, LogPosition, ReplicatedLog } from '../../src/core/replication';
import { EncodedCrdtOp } from '../../src/core/sql';
import { NodeCrdtClient } from '../../src/platform/node/nodeClient';

class InMemoryReplicatedLog implements ReplicatedLog {
  private readonly entriesBySite = new Map<string, LogEntry[]>();

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

function counterHlcHex(seq: number): string {
  return `0x${((0x1000n + BigInt(seq)) << 16n).toString(16)}`;
}

function makeCounterEntries(amounts: readonly number[]): LogEntry[] {
  return amounts.map((amount, index) => {
    const seq = index + 1;
    const hlc = counterHlcHex(seq);
    const ops: EncodedCrdtOp[] = [];
    if (seq === 1) {
      ops.push({
        tbl: 'tasks',
        key: 't1',
        hlc,
        site: 'site-a',
        kind: 'row_exists',
        exists: true,
      });
    }
    ops.push({
      tbl: 'tasks',
      key: 't1',
      col: 'points',
      hlc,
      site: 'site-a',
      kind: 'cell_counter',
      d: 'inc',
      n: amount,
    });
    return {
      siteId: 'site-a',
      hlc,
      seq,
      ops,
    };
  });
}

describe('Node client persistence properties', () => {
  test.prop(
    [fc.array(fc.integer({ min: 1, max: 100 }), { minLength: 1, maxLength: 20 })],
    { numRuns: 40 },
  )(
    'atomic state bundle prevents PN-counter replay when legacy sync file is stale',
    async (amounts) => {
      const dataDir = await mkdtemp(join(tmpdir(), 'crdtbase-node-persist-prop-'));
      try {
        const expected = amounts.reduce((sum, value) => sum + value, 0);
        const log = new InMemoryReplicatedLog({
          'site-a': makeCounterEntries(amounts),
        });

        const initial = await NodeCrdtClient.open({
          siteId: 'site-b',
          log,
          dataDir,
          clock: createHlcClock({ nowWallMs: () => 5_000 }),
        });
        await initial.exec('CREATE TABLE tasks (id PRIMARY KEY, points COUNTER);');
        await initial.pull();

        const beforeRestart = await initial.query("SELECT points FROM tasks WHERE id = 't1';");
        expect(beforeRestart).toHaveLength(1);
        expect(beforeRestart[0]!.points).toBe(expected);
        expect(initial.getSyncedHeads()['site-a']).toBe(amounts.length);

        // Simulate a torn legacy write where sync.bin rolls back but state.bin is newer.
        await writeFile(
          join(dataDir, 'sync.bin'),
          encodeBin({
            v: 2 as const,
            syncedBySite: {},
          }),
        );

        const reopened = await NodeCrdtClient.open({
          siteId: 'site-b',
          log,
          dataDir,
          clock: createHlcClock({ nowWallMs: () => 5_000 }),
        });
        await reopened.pull();

        const afterRestart = await reopened.query("SELECT points FROM tasks WHERE id = 't1';");
        expect(afterRestart).toHaveLength(1);
        expect(afterRestart[0]!.points).toBe(expected);
        expect(reopened.getSyncedHeads()['site-a']).toBe(amounts.length);
      } finally {
        await rm(dataDir, { recursive: true, force: true });
      }
    },
  );
});
