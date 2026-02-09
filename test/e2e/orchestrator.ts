export type E2eSiteId = 'site-a' | 'site-b' | 'site-c';

export type E2eClientAdapter = {
  siteId: string;
  exec(sql: string): Promise<void>;
  query(sql: string): Promise<Record<string, unknown>[]>;
  push(): Promise<void>;
  pull(): Promise<void>;
  sync(): Promise<void>;
};

export type E2eClientMap = Record<E2eSiteId, E2eClientAdapter>;

export type NormalizedTaskRow = {
  id: string;
  title: unknown;
  points: number;
  tags: string[];
  status: string[];
};

export type E2eChaosScenarioConfig = {
  seed: number;
  stepsPerClient: number;
  maxDelayMs: number;
  rowIds: string[];
  drainRounds: number;
  quiescenceRounds: number;
};

export type E2eChaosScenarioResult = {
  normalizedRowsBySite: Record<E2eSiteId, NormalizedTaskRow[]>;
  observerRows: NormalizedTaskRow[] | null;
  expectedPointsByRow: Record<string, number>;
  expectedTagsByRow: Record<string, string[]>;
  convergenceRound: number;
  stats: {
    writes: number;
    pushes: number;
    pulls: number;
    syncs: number;
  };
};

export const CREATE_TASKS_TABLE_SQL = [
  'CREATE TABLE tasks (',
  'id PRIMARY KEY,',
  'title LWW<STRING>,',
  'points COUNTER,',
  'tags SET<STRING>,',
  'status REGISTER<STRING>',
  ')',
].join(' ');

export const TASK_QUERY_SQL = 'SELECT * FROM tasks;';

const SITE_IDS: E2eSiteId[] = ['site-a', 'site-b', 'site-c'];

const DEFAULT_CONFIG: Omit<E2eChaosScenarioConfig, 'seed'> = {
  stepsPerClient: 140,
  maxDelayMs: 8,
  rowIds: ['t1', 't2', 't3', 't4', 't5'],
  drainRounds: 20,
  quiescenceRounds: 3,
};

type MutableExpectations = {
  points: Map<string, number>;
  tags: Map<string, Set<string>>;
};

type ScriptStep =
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

function createRng(seed: number): () => number {
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

function sleep(ms: number): Promise<void> {
  if (ms <= 0) {
    return Promise.resolve();
  }
  return new Promise((resolve) => setTimeout(resolve, ms));
}

function escapeSqlString(value: string): string {
  return value.replaceAll("'", "''");
}

function rowKey(raw: unknown): string {
  if (typeof raw === 'string') {
    return raw;
  }
  if (typeof raw === 'number') {
    return String(raw);
  }
  throw new Error(`expected SQL row id to be string|number, got ${typeof raw}`);
}

function normalizeStringArray(value: unknown): string[] {
  if (!Array.isArray(value)) {
    return [];
  }
  const out = value
    .map((item) => String(item))
    .sort((left, right) => left.localeCompare(right));
  return [...new Set(out)];
}

export function normalizeTaskRows(rows: Record<string, unknown>[]): NormalizedTaskRow[] {
  return [...rows]
    .map((row) => {
      const id = rowKey(row.id);
      const pointsRaw = row.points;
      const points = typeof pointsRaw === 'number' ? pointsRaw : 0;
      return {
        id,
        title: row.title,
        points,
        tags: normalizeStringArray(row.tags),
        status: normalizeStringArray(row.status),
      } satisfies NormalizedTaskRow;
    })
    .sort((left, right) => left.id.localeCompare(right.id));
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

function writeStepFor(
  siteId: E2eSiteId,
  rowIds: readonly string[],
  rng: () => number,
  index: number,
  maxDelayMs: number,
): ScriptStep {
  const rowId = rngPick(rng, rowIds);
  if (typeof rowId !== 'string') {
    throw new Error(
      `row generator produced non-string id for site ${siteId}: ${String(rowId)} from rowIds=${JSON.stringify(rowIds)}`,
    );
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

function randomSyncStep(rng: () => number, maxDelayMs: number): ScriptStep {
  const roll = rng();
  if (roll < 0.45) {
    return { delayMs: rngInt(rng, 0, maxDelayMs), kind: 'push' };
  }
  if (roll < 0.8) {
    return { delayMs: rngInt(rng, 0, maxDelayMs), kind: 'pull' };
  }
  return { delayMs: rngInt(rng, 0, maxDelayMs), kind: 'sync' };
}

function buildScript(params: {
  siteId: E2eSiteId;
  rowIds: readonly string[];
  seed: number;
  stepsPerClient: number;
  maxDelayMs: number;
}): ScriptStep[] {
  const rng = createRng(params.seed);
  const steps: ScriptStep[] = [];

  // Force at least one local write so every site contributes deltas.
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

async function runScript(params: {
  client: E2eClientAdapter;
  script: ScriptStep[];
  expectations: MutableExpectations;
  stats: E2eChaosScenarioResult['stats'];
}): Promise<void> {
  for (const step of params.script) {
    await sleep(step.delayMs);

    if (step.kind === 'write') {
      await params.client.exec(step.sql);
      params.stats.writes += 1;

      if (step.track.kind === 'inc') {
        params.expectations.points.set(
          step.track.rowId,
          (params.expectations.points.get(step.track.rowId) ?? 0) + step.track.amount,
        );
      } else if (step.track.kind === 'tag') {
        const set = params.expectations.tags.get(step.track.rowId);
        if (!set) {
          throw new Error(`unknown row in expectations: ${step.track.rowId}`);
        }
        set.add(step.track.value);
      }
      continue;
    }

    if (step.kind === 'push') {
      await params.client.push();
      params.stats.pushes += 1;
      continue;
    }

    if (step.kind === 'pull') {
      await params.client.pull();
      params.stats.pulls += 1;
      continue;
    }

    await params.client.sync();
    params.stats.syncs += 1;
  }
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
  return serializedA === JSON.stringify(rowsBySite['site-b']) &&
    serializedA === JSON.stringify(rowsBySite['site-c']);
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

export async function runThreeClientChaosScenario(params: {
  clients: E2eClientMap;
  observer?: E2eClientAdapter;
  config: Partial<E2eChaosScenarioConfig> & { seed: number };
}): Promise<E2eChaosScenarioResult> {
  const config: E2eChaosScenarioConfig = {
    ...DEFAULT_CONFIG,
    ...params.config,
  };

  if (!Number.isInteger(config.seed)) {
    throw new Error(`seed must be an integer, got ${String(config.seed)}`);
  }
  if (config.stepsPerClient <= 0) {
    throw new Error(`stepsPerClient must be positive, got ${String(config.stepsPerClient)}`);
  }
  if (config.rowIds.length === 0) {
    throw new Error('rowIds must not be empty');
  }

  const expectations = createExpectations(config.rowIds);
  const stats: E2eChaosScenarioResult['stats'] = {
    writes: 0,
    pushes: 0,
    pulls: 0,
    syncs: 0,
  };

  await initializeRows({
    clients: params.clients,
    observer: params.observer,
    rowIds: config.rowIds,
  });

  const scripts: Record<E2eSiteId, ScriptStep[]> = {
    'site-a': buildScript({
      siteId: 'site-a',
      rowIds: config.rowIds,
      seed: (config.seed ^ 0x9e3779b9) >>> 0,
      stepsPerClient: config.stepsPerClient,
      maxDelayMs: config.maxDelayMs,
    }),
    'site-b': buildScript({
      siteId: 'site-b',
      rowIds: config.rowIds,
      seed: (config.seed ^ 0x85ebca6b) >>> 0,
      stepsPerClient: config.stepsPerClient,
      maxDelayMs: config.maxDelayMs,
    }),
    'site-c': buildScript({
      siteId: 'site-c',
      rowIds: config.rowIds,
      seed: (config.seed ^ 0xc2b2ae35) >>> 0,
      stepsPerClient: config.stepsPerClient,
      maxDelayMs: config.maxDelayMs,
    }),
  };

  await Promise.all(
    SITE_IDS.map((siteId) =>
      runScript({
        client: params.clients[siteId],
        script: scripts[siteId],
        expectations,
        stats,
      }),
    ),
  );

  let convergenceRound = -1;
  let normalizedRowsBySite: Record<E2eSiteId, NormalizedTaskRow[]> | null = null;
  let observerRows: NormalizedTaskRow[] | null = null;
  for (let round = 1; round <= config.drainRounds; round += 1) {
    await syncAll(params.clients);
    const snapshot = await readNormalizedRows(params.clients);
    const observerSnapshot = await readObserverRows(params.observer);
    if (
      allSitesEqual(snapshot) &&
      (observerSnapshot === null ||
        JSON.stringify(observerSnapshot) === JSON.stringify(snapshot['site-a']))
    ) {
      convergenceRound = round;
      normalizedRowsBySite = snapshot;
      observerRows = observerSnapshot;
      break;
    }
  }

  if (normalizedRowsBySite === null) {
    const snapshot = await readNormalizedRows(params.clients);
    throw new Error(
      `clients did not converge for seed ${config.seed} after ${config.drainRounds} drain rounds; final snapshot=${JSON.stringify(snapshot)}`,
    );
  }

  for (let round = 0; round < config.quiescenceRounds; round += 1) {
    await syncAll(params.clients);
    const snapshot = await readNormalizedRows(params.clients);
    const observerSnapshot = await readObserverRows(params.observer);
    if (!allSitesEqual(snapshot)) {
      throw new Error(
        `clients diverged during quiescence (seed ${config.seed}, round ${round}); snapshot=${JSON.stringify(snapshot)}`,
      );
    }
    if (
      observerSnapshot !== null &&
      JSON.stringify(observerSnapshot) !== JSON.stringify(snapshot['site-a'])
    ) {
      throw new Error(
        `observer diverged during quiescence (seed ${config.seed}, round ${round}); observer=${JSON.stringify(observerSnapshot)} clients=${JSON.stringify(snapshot['site-a'])}`,
      );
    }
    if (JSON.stringify(snapshot['site-a']) !== JSON.stringify(normalizedRowsBySite['site-a'])) {
      throw new Error(
        `state changed after convergence during quiescence (seed ${config.seed}, round ${round})`,
      );
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

export function parseE2eSeeds(raw: string | undefined, fallback: number[]): number[] {
  if (!raw || raw.trim().length === 0) {
    return fallback;
  }

  const values = raw
    .split(',')
    .map((part) => part.trim())
    .filter((part) => part.length > 0)
    .map((part) => Number.parseInt(part, 10))
    .filter((value) => Number.isFinite(value));

  if (values.length === 0) {
    return fallback;
  }

  return [...new Set(values.map((value) => value | 0))];
}
