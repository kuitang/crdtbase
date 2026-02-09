import {
  CREATE_TASKS_TABLE_SQL,
  TASK_QUERY_SQL,
  E2eClientAdapter,
  E2eClientMap,
  E2eChaosScenarioResult,
  E2eSiteId,
  NormalizedTaskRow,
  normalizeTaskRows,
} from './orchestrator';

type MutableExpectations = {
  points: Map<string, number>;
  tags: Map<string, Set<string>>;
};

type SiteScriptStep =
  | {
      delayMs: number;
      kind: 'write';
      sql: string;
      track:
        | { kind: 'inc'; rowId: string; amount: number }
        | { kind: 'tag'; rowId: string; value: string }
        | { kind: 'none' };
    }
  | {
      delayMs: number;
      kind: 'push' | 'pull' | 'sync';
    };

export type DeterministicTraceStep =
  | {
      siteId: E2eSiteId;
      delayMs: number;
      kind: 'write';
      sql: string;
      track:
        | { kind: 'inc'; rowId: string; amount: number }
        | { kind: 'tag'; rowId: string; value: string }
        | { kind: 'none' };
    }
  | {
      siteId: E2eSiteId;
      delayMs: number;
      kind: 'push' | 'pull' | 'sync';
    };

export type DeterministicTraceConfig = {
  seed: number;
  stepsPerClient: number;
  maxDelayMs: number;
  rowIds: string[];
};

export type DeterministicReplayConfig = {
  rowIds: string[];
  drainRounds: number;
  quiescenceRounds: number;
};

export type DeterministicReplayOptions = {
  clients: E2eClientMap;
  observer?: E2eClientAdapter;
  trace: DeterministicTraceStep[];
  config: DeterministicReplayConfig;
  sleepFn?: (ms: number) => Promise<void>;
  afterStep?: (context: {
    stepIndex: number;
    step: DeterministicTraceStep;
    clients: E2eClientMap;
  }) => Promise<void>;
};

const SITE_IDS: E2eSiteId[] = ['site-a', 'site-b', 'site-c'];

export function createSeededRng(seed: number): () => number {
  let state = (seed >>> 0) || 0x6d2b79f5;
  return () => {
    state ^= state << 13;
    state ^= state >>> 17;
    state ^= state << 5;
    return (state >>> 0) / 0x1_0000_0000;
  };
}

function rngInt(rng: () => number, minInclusive: number, maxInclusive: number): number {
  const span = maxInclusive - minInclusive + 1;
  return minInclusive + Math.floor(rng() * span);
}

function rngPick<T>(rng: () => number, values: readonly T[]): T {
  if (values.length === 0) {
    throw new Error('rngPick requires non-empty values');
  }
  return values[Math.min(values.length - 1, Math.floor(rng() * values.length))]!;
}

function escapeSqlString(value: string): string {
  return value.replaceAll("'", "''");
}

function writeStepFor(
  siteId: E2eSiteId,
  rowIds: readonly string[],
  rng: () => number,
  index: number,
  maxDelayMs: number,
): SiteScriptStep {
  const rowId = rngPick(rng, rowIds);
  if (typeof rowId !== 'string') {
    throw new Error(`row generator produced non-string id for site ${siteId}`);
  }

  const roll = rng();
  if (roll < 0.35) {
    const amount = rngInt(rng, 1, 5);
    return {
      delayMs: rngInt(rng, 0, maxDelayMs),
      kind: 'write',
      sql: `INC tasks.points BY ${amount} WHERE id = '${escapeSqlString(rowId)}';`,
      track: { kind: 'inc', rowId, amount },
    };
  }

  if (roll < 0.7) {
    const tag = `${siteId}-${index}-${rngInt(rng, 10_000, 999_999)}`;
    return {
      delayMs: rngInt(rng, 0, maxDelayMs),
      kind: 'write',
      sql: `ADD '${escapeSqlString(tag)}' TO tasks.tags WHERE id = '${escapeSqlString(rowId)}';`,
      track: { kind: 'tag', rowId, value: tag },
    };
  }

  if (roll < 0.85) {
    const title = `${siteId}-title-${rngInt(rng, 1, 10_000)}`;
    return {
      delayMs: rngInt(rng, 0, maxDelayMs),
      kind: 'write',
      sql: `UPDATE tasks SET title = '${escapeSqlString(title)}' WHERE id = '${escapeSqlString(rowId)}';`,
      track: { kind: 'none' },
    };
  }

  const status = rngPick(rng, ['open', 'review', 'blocked', 'done']);
  return {
    delayMs: rngInt(rng, 0, maxDelayMs),
    kind: 'write',
    sql: `UPDATE tasks SET status = '${escapeSqlString(status)}' WHERE id = '${escapeSqlString(rowId)}';`,
    track: { kind: 'none' },
  };
}

function randomSyncStep(rng: () => number, maxDelayMs: number): SiteScriptStep {
  const roll = rng();
  if (roll < 0.45) {
    return { delayMs: rngInt(rng, 0, maxDelayMs), kind: 'push' };
  }
  if (roll < 0.8) {
    return { delayMs: rngInt(rng, 0, maxDelayMs), kind: 'pull' };
  }
  return { delayMs: rngInt(rng, 0, maxDelayMs), kind: 'sync' };
}

function buildSiteScript(params: {
  siteId: E2eSiteId;
  rowIds: readonly string[];
  seed: number;
  stepsPerClient: number;
  maxDelayMs: number;
}): SiteScriptStep[] {
  const rng = createSeededRng(params.seed);
  const steps: SiteScriptStep[] = [];

  steps.push(writeStepFor(params.siteId, params.rowIds, rng, 0, params.maxDelayMs));
  for (let index = 1; index < params.stepsPerClient; index += 1) {
    if (rng() < 0.55) {
      steps.push(writeStepFor(params.siteId, params.rowIds, rng, index, params.maxDelayMs));
    } else {
      steps.push(randomSyncStep(rng, params.maxDelayMs));
    }
  }

  return steps;
}

function createExpectations(rowIds: string[]): MutableExpectations {
  const points = new Map<string, number>();
  const tags = new Map<string, Set<string>>();
  for (const rowId of rowIds) {
    points.set(rowId, 0);
    tags.set(rowId, new Set([`seed-${rowId}`]));
  }
  return { points, tags };
}

function materializeExpectations(expectations: MutableExpectations): {
  expectedPointsByRow: Record<string, number>;
  expectedTagsByRow: Record<string, string[]>;
} {
  return {
    expectedPointsByRow: Object.fromEntries(expectations.points.entries()),
    expectedTagsByRow: Object.fromEntries(
      [...expectations.tags.entries()].map(([rowId, tags]) => [rowId, [...tags].sort()]),
    ),
  };
}

async function syncAll(clients: E2eClientMap): Promise<void> {
  await Promise.all(SITE_IDS.map((siteId) => clients[siteId].sync()));
}

async function readNormalizedRows(clients: E2eClientMap): Promise<Record<E2eSiteId, NormalizedTaskRow[]>> {
  const [rowsA, rowsB, rowsC] = await Promise.all([
    clients['site-a'].query(TASK_QUERY_SQL),
    clients['site-b'].query(TASK_QUERY_SQL),
    clients['site-c'].query(TASK_QUERY_SQL),
  ]);

  return {
    'site-a': normalizeTaskRows(rowsA),
    'site-b': normalizeTaskRows(rowsB),
    'site-c': normalizeTaskRows(rowsC),
  };
}

async function readObserverRows(observer: E2eClientAdapter | undefined): Promise<NormalizedTaskRow[] | null> {
  if (!observer) {
    return null;
  }
  await observer.pull();
  return normalizeTaskRows(await observer.query(TASK_QUERY_SQL));
}

function allSitesEqual(rowsBySite: Record<E2eSiteId, NormalizedTaskRow[]>): boolean {
  const serializedA = JSON.stringify(rowsBySite['site-a']);
  return serializedA === JSON.stringify(rowsBySite['site-b'])
    && serializedA === JSON.stringify(rowsBySite['site-c']);
}

async function initializeRows(params: {
  clients: E2eClientMap;
  observer?: E2eClientAdapter;
  rowIds: readonly string[];
}): Promise<void> {
  await Promise.all(SITE_IDS.map((siteId) => params.clients[siteId].exec(CREATE_TASKS_TABLE_SQL)));
  if (params.observer) {
    await params.observer.exec(CREATE_TASKS_TABLE_SQL);
  }

  for (const rowId of params.rowIds) {
    await params.clients['site-a'].exec(
      [
        'INSERT INTO tasks (id, title, points, tags, status) VALUES (',
        `'${escapeSqlString(rowId)}',`,
        `'seed-${escapeSqlString(rowId)}',`,
        '0,',
        `'seed-${escapeSqlString(rowId)}',`,
        `'open'`,
        ');',
      ].join(' '),
    );
  }

  await syncAll(params.clients);
}

function defaultSleep(ms: number): Promise<void> {
  if (ms <= 0) {
    return Promise.resolve();
  }
  return new Promise((resolve) => setTimeout(resolve, ms));
}

export function buildDeterministicTrace(config: DeterministicTraceConfig): DeterministicTraceStep[] {
  if (!Number.isInteger(config.seed)) {
    throw new Error(`seed must be an integer, got ${String(config.seed)}`);
  }
  if (config.stepsPerClient <= 0) {
    throw new Error(`stepsPerClient must be positive, got ${String(config.stepsPerClient)}`);
  }
  if (config.rowIds.length === 0) {
    throw new Error('rowIds must not be empty');
  }

  const scripts: Record<E2eSiteId, SiteScriptStep[]> = {
    'site-a': buildSiteScript({
      siteId: 'site-a',
      rowIds: config.rowIds,
      seed: (config.seed ^ 0x9e3779b9) >>> 0,
      stepsPerClient: config.stepsPerClient,
      maxDelayMs: config.maxDelayMs,
    }),
    'site-b': buildSiteScript({
      siteId: 'site-b',
      rowIds: config.rowIds,
      seed: (config.seed ^ 0x85ebca6b) >>> 0,
      stepsPerClient: config.stepsPerClient,
      maxDelayMs: config.maxDelayMs,
    }),
    'site-c': buildSiteScript({
      siteId: 'site-c',
      rowIds: config.rowIds,
      seed: (config.seed ^ 0xc2b2ae35) >>> 0,
      stepsPerClient: config.stepsPerClient,
      maxDelayMs: config.maxDelayMs,
    }),
  };

  const trace: DeterministicTraceStep[] = [];
  for (let index = 0; index < config.stepsPerClient; index += 1) {
    for (const siteId of SITE_IDS) {
      const step = scripts[siteId][index]!;
      trace.push({ siteId, ...step });
    }
  }
  return trace;
}

export async function replayDeterministicTraceScenario(
  options: DeterministicReplayOptions,
): Promise<E2eChaosScenarioResult> {
  const expectations = createExpectations(options.config.rowIds);
  const stats: E2eChaosScenarioResult['stats'] = {
    writes: 0,
    pushes: 0,
    pulls: 0,
    syncs: 0,
  };

  const sleepFn = options.sleepFn ?? defaultSleep;

  await initializeRows({
    clients: options.clients,
    observer: options.observer,
    rowIds: options.config.rowIds,
  });

  for (let index = 0; index < options.trace.length; index += 1) {
    const step = options.trace[index]!;
    await sleepFn(step.delayMs);

    const client = options.clients[step.siteId];
    if (step.kind === 'write') {
      await client.exec(step.sql);
      stats.writes += 1;

      if (step.track.kind === 'inc') {
        expectations.points.set(
          step.track.rowId,
          (expectations.points.get(step.track.rowId) ?? 0) + step.track.amount,
        );
      } else if (step.track.kind === 'tag') {
        const set = expectations.tags.get(step.track.rowId);
        if (!set) {
          throw new Error(`unknown row in expectations: ${step.track.rowId}`);
        }
        set.add(step.track.value);
      }
    } else if (step.kind === 'push') {
      await client.push();
      stats.pushes += 1;
    } else if (step.kind === 'pull') {
      await client.pull();
      stats.pulls += 1;
    } else {
      await client.sync();
      stats.syncs += 1;
    }

    if (options.afterStep) {
      await options.afterStep({
        stepIndex: index,
        step,
        clients: options.clients,
      });
    }
  }

  let convergenceRound = -1;
  let normalizedRowsBySite: Record<E2eSiteId, NormalizedTaskRow[]> | null = null;
  let observerRows: NormalizedTaskRow[] | null = null;
  for (let round = 1; round <= options.config.drainRounds; round += 1) {
    await syncAll(options.clients);
    const snapshot = await readNormalizedRows(options.clients);
    const observerSnapshot = await readObserverRows(options.observer);
    if (
      allSitesEqual(snapshot)
      && (observerSnapshot === null
        || JSON.stringify(observerSnapshot) === JSON.stringify(snapshot['site-a']))
    ) {
      convergenceRound = round;
      normalizedRowsBySite = snapshot;
      observerRows = observerSnapshot;
      break;
    }
  }

  if (normalizedRowsBySite === null) {
    const snapshot = await readNormalizedRows(options.clients);
    throw new Error(
      `clients did not converge after ${options.config.drainRounds} drain rounds; final snapshot=${JSON.stringify(snapshot)}`,
    );
  }

  for (let round = 0; round < options.config.quiescenceRounds; round += 1) {
    await syncAll(options.clients);
    const snapshot = await readNormalizedRows(options.clients);
    const observerSnapshot = await readObserverRows(options.observer);
    if (!allSitesEqual(snapshot)) {
      throw new Error(
        `clients diverged during quiescence (round ${round}); snapshot=${JSON.stringify(snapshot)}`,
      );
    }
    if (
      observerSnapshot !== null
      && JSON.stringify(observerSnapshot) !== JSON.stringify(snapshot['site-a'])
    ) {
      throw new Error(
        `observer diverged during quiescence (round ${round}); observer=${JSON.stringify(observerSnapshot)} clients=${JSON.stringify(snapshot['site-a'])}`,
      );
    }
    if (JSON.stringify(snapshot['site-a']) !== JSON.stringify(normalizedRowsBySite['site-a'])) {
      throw new Error(`state changed after convergence during quiescence (round ${round})`);
    }
  }

  const materialized = materializeExpectations(expectations);
  return {
    normalizedRowsBySite,
    observerRows,
    expectedPointsByRow: materialized.expectedPointsByRow,
    expectedTagsByRow: materialized.expectedTagsByRow,
    convergenceRound,
    stats,
  };
}
