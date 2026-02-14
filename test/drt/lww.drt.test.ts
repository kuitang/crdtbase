import { afterAll, beforeAll, describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { LeanDrtClient } from './harness';
import { parseSql, type SqlSchema } from '../../src/core/sql';
import { type SqlEvalState } from '../../src/core/sqlEval';
import { arbScalar, arbSiteId } from '../properties/arbitraries';
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

const arbLwwSqlCase = fc.record({
  values: fc.array(arbScalar(), { minLength: 1, maxLength: 12 }),
  site: arbSiteId(),
});

function renderLiteral(value: string | number | boolean | null): string {
  if (value === null) return 'NULL';
  if (typeof value === 'string') return `'${value.replace(/'/g, "''")}'`;
  if (typeof value === 'boolean') return value ? 'TRUE' : 'FALSE';
  return String(value);
}

function makeInitialState(): SqlEvalState {
  const schema: SqlSchema = {
    tasks: {
      pk: 'id',
      partitionBy: null,
      columns: {
        id: { crdt: 'scalar' },
        title: { crdt: 'lww' },
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

describe('DRT: LWW via SQL script pipeline', () => {
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
    .prop([arbLwwSqlCase], { numRuns: drtRuns })
    ('LWW-focused SQL scripts match Lean and TypeScript', async (input) => {
      const sqlStatements = input.values.map(
        (value) => `UPDATE tasks SET title = ${renderLiteral(value)} WHERE id = 'task-1'`,
      );
      sqlStatements.push("SELECT title FROM tasks WHERE id = 'task-1'");
      const statements = sqlStatements.map((sql) => parseSql(sql));
      const hlcSequence = makeHlcSequence(input.values.length * 2);

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
