import { describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import {
  DEFAULT_OR_SET_TOMBSTONE_TTL_MS,
  DEFAULT_ROW_TOMBSTONE_TTL_MS,
  pruneRuntimeRowsForCompaction,
} from '../../src/core/compaction';
import { RuntimeRowState } from '../../src/core/sqlEval';

function makeDeletedRow(key: string, tombstoneWallMs: number): RuntimeRowState {
  return {
    table: 'tasks',
    key,
    columns: new Map([
      [
        '_exists',
        {
          typ: 1 as const,
          state: {
            val: false,
            hlc: {
              wallMs: tombstoneWallMs,
              counter: 0,
            },
            site: 'site-a',
          },
        },
      ],
    ]),
  };
}

describe('Compaction retention properties', () => {
  test.prop(
    [fc.integer({ min: 10_000, max: 1_000_000 }), fc.integer({ min: 1, max: 10_000 })],
    { numRuns: 40 },
  )('row tombstones older than TTL are dropped during compaction', (nowMs, ttlMs) => {
    const oldWallMs = nowMs - ttlMs - 1;
    const recentWallMs = nowMs - ttlMs + 1;
    const rows = new Map<string, RuntimeRowState>([
      ['old', makeDeletedRow('old', oldWallMs)],
      ['recent', makeDeletedRow('recent', recentWallMs)],
    ]);

    pruneRuntimeRowsForCompaction(rows, {
      nowMs,
      orSetTombstoneTtlMs: DEFAULT_OR_SET_TOMBSTONE_TTL_MS,
      rowTombstoneTtlMs: ttlMs,
    });

    expect(rows.has('old')).toBe(false);
    expect(rows.has('recent')).toBe(true);
  });

  test.prop(
    [fc.integer({ min: 10_000, max: 1_000_000 }), fc.integer({ min: 1, max: 10_000 })],
    { numRuns: 40 },
  )('OR-Set tombstones older than TTL are pruned during compaction', (nowMs, ttlMs) => {
    const oldWallMs = nowMs - ttlMs - 1;
    const recentWallMs = nowMs - ttlMs + 1;
    const row: RuntimeRowState = {
      table: 'tasks',
      key: 't1',
      columns: new Map([
        [
          'tags',
          {
            typ: 3 as const,
            state: {
              elements: [],
              tombstones: [
                {
                  addHlc: { wallMs: oldWallMs, counter: 0 },
                  addSite: 'site-a',
                },
                {
                  addHlc: { wallMs: recentWallMs, counter: 0 },
                  addSite: 'site-b',
                },
              ],
            },
          },
        ],
      ]),
    };
    const rows = new Map<string, RuntimeRowState>([['row', row]]);

    pruneRuntimeRowsForCompaction(rows, {
      nowMs,
      orSetTombstoneTtlMs: ttlMs,
      rowTombstoneTtlMs: DEFAULT_ROW_TOMBSTONE_TTL_MS,
    });

    const tags = rows.get('row')!.columns.get('tags');
    expect(tags?.typ).toBe(3);
    expect(tags?.typ === 3 ? tags.state.tombstones.length : 0).toBe(1);
    expect(tags?.typ === 3 ? tags.state.tombstones[0]!.addSite : '').toBe('site-b');
  });
});
