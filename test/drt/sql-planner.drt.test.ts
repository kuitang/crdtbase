import { afterAll, beforeAll, describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { LeanDrtClient } from './harness';
import {
  buildSelectPlan,
  parseSql,
  type SelectPlannerSchema,
  type SelectStatement,
} from '../../src/core/sql';
import { arbGeneratedSelectPlanCase } from '../properties/sql.generators';

const leanBin = LeanDrtClient.findBinary();
const drt = leanBin ? test : test.skip;
const drtRuns = Number(process.env.DRT_NUM_RUNS ?? 50);
const drtTimeoutMs = Number(process.env.DRT_TIMEOUT_MS ?? 30_000);

describe('DRT: SQL planner', () => {
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
    .prop([arbGeneratedSelectPlanCase], { numRuns: drtRuns })
    ('Lean sql_build_select_plan matches TypeScript buildSelectPlan', async (input) => {
      const parsed = parseSql(input.sql);
      fc.pre(parsed.kind === 'select');
      const statement = parsed as SelectStatement;

      const schema: SelectPlannerSchema = {
        partitionBy: input.partitionBy ?? null,
      };
      const tsPlan = buildSelectPlan(statement, schema);
      const lean = await client!.sqlBuildSelectPlan<{ result: typeof tsPlan }>(statement, schema);

      expect(tsPlan).toEqual(input.expectedPlan);
      expect(lean.result).toEqual(input.expectedPlan);
      expect(lean.result).toEqual(tsPlan);
    }, drtTimeoutMs);
});
