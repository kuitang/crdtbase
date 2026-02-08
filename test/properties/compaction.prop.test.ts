import { describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import {
  SegmentFile,
  bloomMayContain,
  buildSegmentFile,
  compareSqlPrimaryKeys,
  segmentFileToRuntimeRows,
} from '../../src/core/compaction';
import { decodeBin, encodeBin } from '../../src/core/encoding';
import { EncodedCrdtOp } from '../../src/core/sql';
import { RuntimeRowState, applyCrdtOpToRows, runtimeRowsToEval } from '../../src/core/sqlEval';
import { arbScalar, arbSiteId } from './arbitraries';

type OpTemplate = {
  typ: 1 | 2 | 3 | 4;
  key: string | number;
  site: string;
  scalar: string | number | boolean | null;
  counterDirection: 'inc' | 'dec';
  counterAmount: number;
  setAction: 'add' | 'rmv';
  removeTags: Array<{ wallMs: number; counter: number; site: string }>;
};

function opHlc(index: number): string {
  const packed = (BigInt(10_000 + index) << 16n) | BigInt(index % 65_536);
  return `0x${packed.toString(16)}`;
}

function tagHlc(wallMs: number, counter: number): string {
  const packed = (BigInt(wallMs) << 16n) | BigInt(counter % 65_536);
  return `0x${packed.toString(16)}`;
}

function toOp(template: OpTemplate, index: number): EncodedCrdtOp {
  const hlc = opHlc(index);
  switch (template.typ) {
    case 1:
      return {
        tbl: 't',
        key: template.key,
        col: 'lww',
        typ: 1,
        hlc,
        site: template.site,
        val: template.scalar,
      };
    case 2:
      return {
        tbl: 't',
        key: template.key,
        col: 'counter',
        typ: 2,
        hlc,
        site: template.site,
        val: {
          d: template.counterDirection,
          n: template.counterAmount,
        },
      };
    case 3:
      return {
        tbl: 't',
        key: template.key,
        col: 'set',
        typ: 3,
        hlc,
        site: template.site,
        val:
          template.setAction === 'add'
            ? { a: 'add', val: template.scalar }
            : {
                a: 'rmv',
                tags: template.removeTags.map((tag) => ({
                  hlc: tagHlc(tag.wallMs, tag.counter),
                  site: tag.site,
                })),
              },
      };
    case 4:
      return {
        tbl: 't',
        key: template.key,
        col: 'reg',
        typ: 4,
        hlc,
        site: template.site,
        val: template.scalar,
      };
  }
}

const arbCompactionOps = fc
  .array(
    fc.record({
      typ: fc.constantFrom<1 | 2 | 3 | 4>(1, 2, 3, 4),
      key: fc.oneof(
        fc.string({ minLength: 1, maxLength: 8 }),
        fc.integer({ min: -20, max: 20 }),
      ),
      site: arbSiteId(),
      scalar: arbScalar(),
      counterDirection: fc.constantFrom<'inc' | 'dec'>('inc', 'dec'),
      counterAmount: fc.nat({ max: 200 }),
      setAction: fc.constantFrom<'add' | 'rmv'>('add', 'rmv'),
      removeTags: fc.array(
        fc.record({
          wallMs: fc.nat({ max: 100_000 }),
          counter: fc.nat({ max: 65_535 }),
          site: arbSiteId(),
        }),
        { maxLength: 3 },
      ),
    }),
    { minLength: 1, maxLength: 100 },
  )
  .map((templates) => templates.map((template, index) => toOp(template, index)));

function applyOps(ops: EncodedCrdtOp[]): Map<string, RuntimeRowState> {
  const rows = new Map<string, RuntimeRowState>();
  for (const op of ops) {
    applyCrdtOpToRows(rows, op);
  }
  return rows;
}

function segmentForRows(rows: Map<string, RuntimeRowState>): SegmentFile {
  const tableRows = [...rows.values()].filter((row) => row.table === 't');
  return buildSegmentFile({
    table: 't',
    partition: '_default',
    rows: tableRows,
    defaultHlcMax: '0x0',
  });
}

describe('Compaction properties', () => {
  test.prop([arbCompactionOps])(
    'compaction prefix + remaining suffix preserves final state',
    (ops) => {
      const split = Math.floor(ops.length / 2);
      const prefix = ops.slice(0, split);
      const suffix = ops.slice(split);

      const direct = applyOps(ops);
      const compactedPrefix = segmentForRows(applyOps(prefix));
      const loadedPrefix = segmentFileToRuntimeRows(
        decodeBin<SegmentFile>(encodeBin(compactedPrefix)),
      );
      for (const op of suffix) {
        applyCrdtOpToRows(loadedPrefix, op);
      }

      expect(runtimeRowsToEval(loadedPrefix)).toEqual(runtimeRowsToEval(direct));
    },
  );

  test.prop([arbCompactionOps])('compaction is idempotent when no new ops arrive', (ops) => {
    const first = segmentForRows(applyOps(ops));
    const reloaded = decodeBin<SegmentFile>(encodeBin(first));
    const second = segmentForRows(segmentFileToRuntimeRows(reloaded));
    expect(second).toEqual(reloaded);
  });

  test.prop([arbCompactionOps])('segment rows are sorted by primary key', (ops) => {
    const segment = segmentForRows(applyOps(ops));
    for (let index = 1; index < segment.rows.length; index += 1) {
      const previous = segment.rows[index - 1]!;
      const next = segment.rows[index]!;
      expect(compareSqlPrimaryKeys(previous.key, next.key)).toBeLessThanOrEqual(0);
    }
  });

  test.prop([arbCompactionOps])('segment bloom filter has no false negatives', (ops) => {
    const segment = segmentForRows(applyOps(ops));
    for (const row of segment.rows) {
      expect(bloomMayContain(segment.bloom, segment.bloom_k, row.key)).toBe(true);
    }
  });
});
