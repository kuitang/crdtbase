export type E2eSiteId = 'site-a' | 'site-b' | 'site-c';

export type E2eClientAdapter = {
  siteId: E2eSiteId;
  exec(sql: string): Promise<void>;
  query(sql: string): Promise<Record<string, unknown>[]>;
  push(): Promise<void>;
  pull(): Promise<void>;
  sync(): Promise<void>;
};

export type E2eClientMap = Record<E2eSiteId, E2eClientAdapter>;

export type E2eSchedule = {
  name: string;
  writerOrder: ['site-b', 'site-c'] | ['site-c', 'site-b'];
  pullOrderAfterConcurrent: E2eSiteId[];
  pullOrderAfterRemove: E2eSiteId[];
};

export type E2eScenarioResult = {
  rowsBySite: Record<E2eSiteId, Record<string, unknown>[]>;
};

export const CREATE_TASKS_TABLE_SQL = [
  'CREATE TABLE tasks (',
  'id STRING PRIMARY KEY,',
  'title LWW<STRING>,',
  'points COUNTER,',
  'tags SET<STRING>,',
  'status REGISTER<STRING>',
  ')',
].join(' ');

export const TASK_QUERY_SQL = "SELECT * FROM tasks WHERE id = 't1';";

export const E2E_SCHEDULES: E2eSchedule[] = [
  {
    name: 'writers-b-then-c',
    writerOrder: ['site-b', 'site-c'],
    pullOrderAfterConcurrent: ['site-c', 'site-a', 'site-b'],
    pullOrderAfterRemove: ['site-a', 'site-c', 'site-b'],
  },
  {
    name: 'writers-c-then-b',
    writerOrder: ['site-c', 'site-b'],
    pullOrderAfterConcurrent: ['site-b', 'site-c', 'site-a'],
    pullOrderAfterRemove: ['site-c', 'site-a', 'site-b'],
  },
];

function uniqueOrder(order: E2eSiteId[]): E2eSiteId[] {
  const out: E2eSiteId[] = [];
  for (const siteId of order) {
    if (!out.includes(siteId)) {
      out.push(siteId);
    }
  }
  for (const siteId of ['site-a', 'site-b', 'site-c'] as const) {
    if (!out.includes(siteId)) {
      out.push(siteId);
    }
  }
  return out;
}

async function runWriterBatch(client: E2eClientAdapter): Promise<void> {
  if (client.siteId === 'site-b') {
    await client.exec("UPDATE tasks SET title = 'from-b', status = 'review' WHERE id = 't1';");
    await client.exec("INC tasks.points BY 3 WHERE id = 't1';");
    await client.exec("ADD 'beta' TO tasks.tags WHERE id = 't1';");
    return;
  }
  if (client.siteId === 'site-c') {
    await client.exec("UPDATE tasks SET title = 'from-c' WHERE id = 't1';");
    await client.exec("INC tasks.points BY 5 WHERE id = 't1';");
    await client.exec("ADD 'gamma' TO tasks.tags WHERE id = 't1';");
    return;
  }
  throw new Error(`unsupported writer batch site: ${client.siteId}`);
}

export async function runThreeClientConvergenceScenario(params: {
  clients: E2eClientMap;
  schedule: E2eSchedule;
}): Promise<E2eScenarioResult> {
  const { clients, schedule } = params;

  await Promise.all([
    clients['site-a'].exec(CREATE_TASKS_TABLE_SQL),
    clients['site-b'].exec(CREATE_TASKS_TABLE_SQL),
    clients['site-c'].exec(CREATE_TASKS_TABLE_SQL),
  ]);

  await clients['site-a'].exec(
    "INSERT INTO tasks (id, title, points, tags, status) VALUES ('t1', 'from-a', 0, 'alpha', 'open');",
  );
  await clients['site-a'].sync();
  await clients['site-b'].pull();
  await clients['site-c'].pull();

  for (const writerSite of schedule.writerOrder) {
    await runWriterBatch(clients[writerSite]);
  }

  await clients[schedule.writerOrder[0]].push();
  await clients[schedule.writerOrder[1]].push();

  for (const siteId of uniqueOrder(schedule.pullOrderAfterConcurrent)) {
    await clients[siteId].pull();
  }

  await clients['site-b'].exec("REMOVE 'alpha' FROM tasks.tags WHERE id = 't1';");
  await clients['site-b'].push();

  for (const siteId of uniqueOrder(schedule.pullOrderAfterRemove)) {
    if (siteId === 'site-b') {
      continue;
    }
    await clients[siteId].pull();
  }

  const rowsBySite: E2eScenarioResult['rowsBySite'] = {
    'site-a': await clients['site-a'].query(TASK_QUERY_SQL),
    'site-b': await clients['site-b'].query(TASK_QUERY_SQL),
    'site-c': await clients['site-c'].query(TASK_QUERY_SQL),
  };
  return { rowsBySite };
}
