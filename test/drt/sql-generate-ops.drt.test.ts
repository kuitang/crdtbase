import { afterAll, beforeAll, describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { LeanDrtClient } from './harness';
import {
  generateCrdtOps,
  parseSql,
  type SqlSchema,
} from '../../src/core/sql';
import { arbGeneratedWriteOpsCase, type ModelSqlSchema } from '../properties/sql.generators';

const leanBin = LeanDrtClient.findBinary();
const drt = leanBin ? test : test.skip;
const drtRuns = Number(process.env.DRT_NUM_RUNS ?? 50);
const drtTimeoutMs = Number(process.env.DRT_TIMEOUT_MS ?? 30_000);

function toLeanSchema(schema: ModelSqlSchema): Array<{
  table: string;
  pk: string;
  partitionBy: string | null;
  columns: Array<{ name: string; crdt: string }>;
}> {
  return Object.entries(schema).map(([table, tableSchema]) => ({
    table,
    pk: tableSchema.pk,
    partitionBy: tableSchema.partitionBy ?? null,
    columns: Object.entries(tableSchema.columns).map(([name, column]) => ({
      name,
      crdt: column.crdt,
    })),
  }));
}

describe('DRT: SQL write op generation', () => {
  let client: LeanDrtClient | null = null;

  beforeAll(() => {
    if (leanBin) {
      client = new LeanDrtClient(leanBin);
    }
  });

  afterAll(() => {
    client?.close();
  });

  drt
    .prop([arbGeneratedWriteOpsCase], { numRuns: drtRuns })
    ('Lean sql_generate_ops matches TypeScript generateCrdtOps', async (input) => {
      const parsed = parseSql(input.sql);
      fc.pre(
        parsed.kind !== 'select' &&
          parsed.kind !== 'create_table' &&
          parsed.kind !== 'drop_table',
      );
      const statement = parsed as Parameters<typeof generateCrdtOps>[0];

      let hlcIndex = 0;
      const tsOps = generateCrdtOps(statement, {
        schema: input.schema as SqlSchema,
        site: input.site,
        nextHlc: () => {
          if (hlcIndex >= input.hlcSequence.length) {
            throw new Error('nextHlc called too many times');
          }
          const value = input.hlcSequence[hlcIndex]!;
          hlcIndex += 1;
          return value;
        },
        resolveSetRemoveTags: () => input.removeTags ?? [],
      });

      const lean = await client!.sqlGenerateOps<{ result: typeof tsOps }>(statement, {
        schema: toLeanSchema(input.schema),
        site: input.site,
        hlcSequence: input.hlcSequence,
        removeTags: input.removeTags ?? null,
      });

      expect(tsOps).toEqual(input.expectedOps);
      expect(lean.result).toEqual(input.expectedOps);
      expect(lean.result).toEqual(tsOps);
    }, drtTimeoutMs);
});
