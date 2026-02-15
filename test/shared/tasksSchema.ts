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

export const DDL_SITE_IDS = ['site-a', 'site-b', 'site-c'] as const;

export type DdlSiteId = (typeof DDL_SITE_IDS)[number];

export function schemaOwnerForSeed(seed: number): DdlSiteId {
  const normalized = seed >>> 0;
  return DDL_SITE_IDS[normalized % DDL_SITE_IDS.length]!;
}

export function buildAddColumnSql(
  column: string,
  definition: 'LWW<STRING>' | 'LWW<NUMBER>' | 'LWW<BOOLEAN>' | 'COUNTER' | 'SET<STRING>' | 'REGISTER<STRING>',
): string {
  return `ALTER TABLE tasks ADD COLUMN ${column} ${definition};`;
}
