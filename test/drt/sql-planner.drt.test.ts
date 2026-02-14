import { afterAll, beforeAll, describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { LeanDrtClient } from './harness';
import {
  buildSelectPlan,
  parseSql,
  type SelectPlannerSchema,
  type SelectStatement,
  type SqlSchema,
} from '../../src/core/sql';
import { type SqlEvalState } from '../../src/core/sqlEval';
import { arbGeneratedSelectPlanCase } from '../properties/sql.generators';
import { toLeanSchema, toLeanState, type LeanScriptEvalOutcome } from './sql-script-utils';

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
    ('Lean sql_script_eval select plan matches TypeScript buildSelectPlan', async (input) => {
      const parsed = parseSql(input.sql);
      fc.pre(parsed.kind === 'select');
      const statement = parsed as SelectStatement;

      const schema: SelectPlannerSchema = {
        partitionBy: input.partitionBy ?? null,
      };
      const tsPlan = buildSelectPlan(statement, schema);

      const tableSchema: SqlSchema = {
        [statement.table]: {
          pk: 'id',
          partitionBy: input.partitionBy ?? null,
          columns: {},
        },
      };

      const initialState: SqlEvalState = {
        schema: tableSchema,
        rows: [],
      };

      const lean = await client!.sqlScriptEval<{ result: LeanScriptEvalOutcome }>(
        [statement],
        {
          schema: toLeanSchema(tableSchema),
          hlcSequence: [],
          removeTags: null,
        },
        toLeanState(initialState),
      );

      expect(lean.result.outcomes).toHaveLength(1);
      const outcome = lean.result.outcomes[0]!;
      expect(outcome.kind).toBe('read');
      expect(outcome.kind === 'read' ? outcome.select : null).toEqual(input.expectedPlan);
      expect(tsPlan).toEqual(input.expectedPlan);
      expect(outcome.kind === 'read' ? outcome.select : null).toEqual(tsPlan);
    }, drtTimeoutMs);
});
