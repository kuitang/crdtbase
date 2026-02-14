import { afterAll, beforeAll, describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import { LeanDrtClient } from './harness';
import { parseSql } from '../../src/core/sql';
import { arbSqlEvalCase, arbSqlEvalTraceCase } from '../properties/sql-eval.generators';
import {
  evaluateSqlScriptTs,
  fromLeanState,
  normalizeJsonObject,
  normalizeScriptExecution,
  toLeanSchema,
  toLeanState,
  type LeanScriptEvalOutcome,
} from './sql-script-utils';

const leanBin = LeanDrtClient.findBinary();
const drt = leanBin ? test : test.skip;
const drtRuns = Number(process.env.DRT_NUM_RUNS ?? 50);
const drtSeed = process.env.DRT_SEED === undefined ? undefined : Number(process.env.DRT_SEED);
const drtTimeoutMs = Number(process.env.DRT_TIMEOUT_MS ?? 30_000);

describe('DRT: SQL AST evaluation', () => {
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
    .prop(
      [arbSqlEvalCase],
      drtSeed === undefined ? { numRuns: drtRuns } : { numRuns: drtRuns, seed: drtSeed },
    )
    ('Lean sql_script_eval matches TypeScript evaluateSqlAst for single statements', async (input) => {
      const statement = parseSql(input.sql);

      let tsExecution: ReturnType<typeof evaluateSqlScriptTs> | null = null;
      let tsError: string | null = null;
      try {
        tsExecution = evaluateSqlScriptTs([statement], {
          state: input.state,
          context: input.context,
        });
      } catch (error) {
        tsError = error instanceof Error ? error.message : String(error);
      }

      if (tsError) {
        await expect(
          client!.sqlScriptEval<{ result: LeanScriptEvalOutcome }>(
            [statement],
            {
              schema: toLeanSchema(input.context.schema ?? input.state.schema),
              site: input.context.site,
              hlcSequence: input.context.hlcSequence,
              removeTags: input.context.removeTags ?? null,
            },
            toLeanState(input.state),
          ),
        ).rejects.toThrow();
        return;
      }

      const lean = await client!.sqlScriptEval<{ result: LeanScriptEvalOutcome }>(
        [statement],
        {
          schema: toLeanSchema(input.context.schema ?? input.state.schema),
          site: input.context.site,
          hlcSequence: input.context.hlcSequence,
          removeTags: input.context.removeTags ?? null,
        },
        toLeanState(input.state),
      );

      const leanExecution = {
        outcomes: lean.result.outcomes,
        nextState: fromLeanState(lean.result.nextState),
      };

      const normalizedLean = normalizeJsonObject(normalizeScriptExecution(leanExecution));
      const normalizedTs = normalizeJsonObject(normalizeScriptExecution(tsExecution!));
      expect(normalizedLean).toEqual(normalizedTs);
    }, drtTimeoutMs);

  drt
    .prop(
      [arbSqlEvalTraceCase],
      drtSeed === undefined
        ? { numRuns: Math.max(10, Math.floor(drtRuns / 2)) }
        : { numRuns: Math.max(10, Math.floor(drtRuns / 2)), seed: drtSeed },
    )
    ('Lean sql_script_eval matches TypeScript evaluateSqlAst across statement sequences', async (input) => {
      const statements = input.statements.map((sql) => parseSql(sql));

      let tsExecution: ReturnType<typeof evaluateSqlScriptTs> | null = null;
      let tsError: string | null = null;
      try {
        tsExecution = evaluateSqlScriptTs(statements, {
          state: input.state,
          context: input.context,
        });
      } catch (error) {
        tsError = error instanceof Error ? error.message : String(error);
      }

      if (tsError) {
        await expect(
          client!.sqlScriptEval<{ result: LeanScriptEvalOutcome }>(
            statements,
            {
              schema: toLeanSchema(input.context.schema ?? input.state.schema),
              site: input.context.site,
              hlcSequence: input.context.hlcSequence,
              removeTags: input.context.removeTags ?? null,
            },
            toLeanState(input.state),
          ),
        ).rejects.toThrow();
        return;
      }

      const lean = await client!.sqlScriptEval<{ result: LeanScriptEvalOutcome }>(
        statements,
        {
          schema: toLeanSchema(input.context.schema ?? input.state.schema),
          site: input.context.site,
          hlcSequence: input.context.hlcSequence,
          removeTags: input.context.removeTags ?? null,
        },
        toLeanState(input.state),
      );

      const leanExecution = {
        outcomes: lean.result.outcomes,
        nextState: fromLeanState(lean.result.nextState),
      };

      const normalizedLean = normalizeJsonObject(normalizeScriptExecution(leanExecution));
      const normalizedTs = normalizeJsonObject(normalizeScriptExecution(tsExecution!));
      expect(normalizedLean).toEqual(normalizedTs);
    }, drtTimeoutMs);
});
