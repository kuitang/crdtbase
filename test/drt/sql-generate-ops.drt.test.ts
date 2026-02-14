import { afterAll, beforeAll, describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { LeanDrtClient } from './harness';
import { generateCrdtOps, parseSql, type SqlSchema } from '../../src/core/sql';
import { type SqlEvalState } from '../../src/core/sqlEval';
import { arbGeneratedWriteOpsCase } from '../properties/sql.generators';
import { toLeanSchema, toLeanState, type LeanScriptEvalOutcome } from './sql-script-utils';

const leanBin = LeanDrtClient.findBinary();
const drt = leanBin ? test : test.skip;
const drtRuns = Number(process.env.DRT_NUM_RUNS ?? 50);
const drtTimeoutMs = Number(process.env.DRT_TIMEOUT_MS ?? 30_000);

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
    ('Lean sql_script_eval write ops match TypeScript generateCrdtOps', async (input) => {
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

      const initialState: SqlEvalState = {
        schema: input.schema as SqlSchema,
        rows: [],
      };

      const lean = await client!.sqlScriptEval<{ result: LeanScriptEvalOutcome }>(
        [statement],
        {
          schema: toLeanSchema(input.schema as SqlSchema),
          site: input.site,
          hlcSequence: input.hlcSequence,
          removeTags: input.removeTags ?? null,
        },
        toLeanState(initialState),
      );

      expect(lean.result.outcomes).toHaveLength(1);
      const outcome = lean.result.outcomes[0]!;
      expect(outcome.kind).toBe('write');
      expect(outcome.kind === 'write' ? outcome.ops : []).toEqual(input.expectedOps);
      expect(tsOps).toEqual(input.expectedOps);
      expect(outcome.kind === 'write' ? outcome.ops : []).toEqual(tsOps);
    }, drtTimeoutMs);
});
