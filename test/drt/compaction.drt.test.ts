import { afterAll, beforeAll, describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import { LeanDrtClient } from './harness';
import { parseSql, type SqlStatement } from '../../src/core/sql';
import { type SqlEvalContext, type SqlEvalOutcome, type SqlEvalState } from '../../src/core/sqlEval';
import { arbSqlEvalTraceCase } from '../properties/sql-eval.generators';
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
const drtRuns = Number(process.env.DRT_NUM_RUNS ?? 15);
const drtTimeoutMs = Number(process.env.DRT_TIMEOUT_MS ?? 45_000);

type ScriptExecution = {
  outcomes: SqlEvalOutcome['result'][];
  nextState: SqlEvalState;
};

function consumedHlc(outcomes: SqlEvalOutcome['result'][]): number {
  return outcomes.reduce(
    (acc, outcome) => acc + (outcome.kind === 'write' ? outcome.ops.length : 0),
    0,
  );
}

function splitPoints(length: number): number[] {
  return Array.from({ length: length + 1 }, (_, index) => index);
}

function normalizeExecution(execution: ScriptExecution): unknown {
  return normalizeJsonObject(normalizeScriptExecution(execution));
}

function mergeExecutions(prefix: ScriptExecution, suffix: ScriptExecution): ScriptExecution {
  return {
    outcomes: [...prefix.outcomes, ...suffix.outcomes],
    nextState: suffix.nextState,
  };
}

describe('DRT: SQL script split law', () => {
  let client: LeanDrtClient | null = null;

  beforeAll(() => {
    if (leanBin) {
      client = new LeanDrtClient(leanBin);
    }
  });

  afterAll(() => {
    client?.close();
  });

  const runLean = async (
    statements: SqlStatement[],
    state: SqlEvalState,
    context: SqlEvalContext,
  ): Promise<ScriptExecution> => {
    const lean = await client!.sqlScriptEval<{ result: LeanScriptEvalOutcome }>(
      statements,
      {
        schema: toLeanSchema(state.schema),
        site: context.site,
        hlcSequence: context.hlcSequence,
        removeTags: context.removeTags ?? null,
      },
      toLeanState(state),
    );
    return {
      outcomes: lean.result.outcomes,
      nextState: fromLeanState(lean.result.nextState),
    };
  };

  drt
    .prop([arbSqlEvalTraceCase], { numRuns: drtRuns })
    ('every prefix/suffix split matches direct execution in TS and Lean', async (input) => {
      const statements = input.statements.map((sql) => parseSql(sql));

      const directTs = evaluateSqlScriptTs(statements, {
        state: input.state,
        context: input.context,
      });
      const directLean = await runLean(statements, input.state, input.context);

      expect(normalizeExecution(directLean)).toEqual(normalizeExecution(directTs));

      for (const splitIndex of splitPoints(statements.length)) {
        const prefix = statements.slice(0, splitIndex);
        const suffix = statements.slice(splitIndex);

        const tsPrefix = evaluateSqlScriptTs(prefix, {
          state: input.state,
          context: input.context,
        });
        const tsSuffix = evaluateSqlScriptTs(suffix, {
          state: tsPrefix.nextState,
          context: {
            ...input.context,
            hlcSequence: input.context.hlcSequence?.slice(consumedHlc(tsPrefix.outcomes)),
          },
        });
        const splitTs = mergeExecutions(tsPrefix, tsSuffix);

        const leanPrefix = await runLean(prefix, input.state, input.context);
        const leanSuffix = await runLean(suffix, leanPrefix.nextState, {
          ...input.context,
          hlcSequence: input.context.hlcSequence?.slice(consumedHlc(leanPrefix.outcomes)),
        });
        const splitLean = mergeExecutions(leanPrefix, leanSuffix);

        expect(normalizeExecution(splitTs)).toEqual(normalizeExecution(directTs));
        expect(normalizeExecution(splitLean)).toEqual(normalizeExecution(directLean));
      }
    }, drtTimeoutMs);
});
