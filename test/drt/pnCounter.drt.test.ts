import { afterAll, beforeAll, describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { LeanDrtClient } from './harness';
import { parseSql, type SqlSchema } from '../../src/core/sql';
import { type SqlEvalState } from '../../src/core/sqlEval';
import { arbSiteId } from '../properties/arbitraries';
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
const drtTimeoutMs = Number(process.env.DRT_TIMEOUT_MS ?? 30_000);

const arbPnSqlCase = fc.record({
  steps: fc.array(
    fc.record({
      dir: fc.constantFrom<'inc' | 'dec'>('inc', 'dec'),
      amount: fc.integer({ min: 0, max: 10_000 }),
    }),
    { minLength: 1, maxLength: 12 },
  ),
  site: arbSiteId(),
});

function makeInitialState(): SqlEvalState {
  const schema: SqlSchema = {
    tasks: {
      pk: 'id',
      partitionBy: null,
      columns: {
        id: { crdt: 'scalar' },
        points: { crdt: 'pn_counter' },
      },
    },
  };
  return {
    schema,
    rows: [],
  };
}

function makeHlcSequence(length: number): string[] {
  return Array.from({ length }, (_, index) => `0x${(index + 1).toString(16)}`);
}

describe('DRT: PN-Counter via SQL script pipeline', () => {
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
    .prop([arbPnSqlCase], { numRuns: drtRuns })
    ('counter-focused SQL scripts match Lean and TypeScript', async (input) => {
      const sqlStatements = input.steps.map((step) =>
        step.dir === 'inc'
          ? `INC tasks.points BY ${step.amount} WHERE id = 'task-1'`
          : `DEC tasks.points BY ${step.amount} WHERE id = 'task-1'`,
      );
      sqlStatements.push("SELECT points FROM tasks WHERE id = 'task-1'");
      const statements = sqlStatements.map((sql) => parseSql(sql));
      const hlcSequence = makeHlcSequence(input.steps.length * 2);

      const initialState = makeInitialState();
      const tsExecution = evaluateSqlScriptTs(statements, {
        state: initialState,
        context: {
          site: input.site,
          hlcSequence,
        },
      });

      const lean = await client!.sqlScriptEval<{ result: LeanScriptEvalOutcome }>(
        statements,
        {
          schema: toLeanSchema(initialState.schema),
          site: input.site,
          hlcSequence,
          removeTags: null,
        },
        toLeanState(initialState),
      );

      const leanExecution = {
        outcomes: lean.result.outcomes,
        nextState: fromLeanState(lean.result.nextState),
      };

      const normalizedLean = normalizeJsonObject(normalizeScriptExecution(leanExecution));
      const normalizedTs = normalizeJsonObject(normalizeScriptExecution(tsExecution));
      expect(normalizedLean).toEqual(normalizedTs);
    }, drtTimeoutMs);
});
