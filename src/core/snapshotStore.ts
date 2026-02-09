import { ManifestFile, ManifestSegmentRef, SegmentFile, compareSqlPrimaryKeys, isValidPackedHlcHex } from './compaction';
import { SqlSchema, SqlValue } from './sql';

export const DEFAULT_MANIFEST_PATH = 'manifest.bin';
export const DEFAULT_SCHEMA_PATH = 'schema.bin';

export interface SnapshotStore {
  getManifest(): Promise<ManifestFile | null>;
  putManifest(manifest: ManifestFile, expectedVersion: number): Promise<boolean>;
  getSegment(path: string): Promise<Uint8Array | null>;
  putSegment(path: string, data: Uint8Array): Promise<void>;
  getSchema(): Promise<SqlSchema | null>;
  putSchema(schema: SqlSchema): Promise<void>;
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

function assertNonNegativeInteger(value: number, label: string): void {
  if (!Number.isInteger(value) || value < 0) {
    throw new Error(`invalid ${label}: ${String(value)}`);
  }
}

function assertPositiveInteger(value: number, label: string): void {
  if (!Number.isInteger(value) || value <= 0) {
    throw new Error(`invalid ${label}: ${String(value)}`);
  }
}

function assertSqlScalar(value: unknown, label: string): asserts value is SqlValue {
  if (
    value !== null &&
    typeof value !== 'string' &&
    typeof value !== 'number' &&
    typeof value !== 'boolean'
  ) {
    throw new Error(`invalid ${label}: expected SQL scalar`);
  }
}

function assertSqlPrimaryKey(value: unknown, label: string): asserts value is string | number {
  if (typeof value !== 'string' && typeof value !== 'number') {
    throw new Error(`invalid ${label}: expected string|number`);
  }
}

function assertSiteMap(value: unknown, label: string): void {
  if (!isRecord(value)) {
    throw new Error(`invalid ${label}: expected object`);
  }
  for (const [siteId, n] of Object.entries(value)) {
    if (siteId.length === 0) {
      throw new Error(`invalid ${label}: empty site id`);
    }
    if (typeof n !== 'number') {
      throw new Error(`invalid ${label}: expected numeric values`);
    }
    assertNonNegativeInteger(n, `${label}.${siteId}`);
  }
}

export function assertSafeSnapshotRelativePath(path: string, label = 'snapshot path'): void {
  const normalized = path.replace(/\\/gu, '/');
  if (normalized.length === 0) {
    throw new Error(`invalid ${label}: empty path`);
  }
  if (normalized.startsWith('/')) {
    throw new Error(`invalid ${label}: absolute path is not allowed`);
  }
  if (/^[A-Za-z]:\//u.test(normalized)) {
    throw new Error(`invalid ${label}: drive path is not allowed`);
  }
  if (normalized.includes('\0')) {
    throw new Error(`invalid ${label}: NUL byte is not allowed`);
  }

  const parts = normalized.split('/');
  if (parts.some((part) => part.length === 0 || part === '.' || part === '..')) {
    throw new Error(`invalid ${label}: contains unsafe path segment`);
  }
}

function assertManifestSegmentRef(segment: ManifestSegmentRef, index: number): void {
  assertSafeSnapshotRelativePath(segment.path, `manifest.segments[${index}].path`);
  if (segment.table.length === 0) {
    throw new Error(`invalid manifest.segments[${index}].table: empty`);
  }
  if (segment.partition.length === 0) {
    throw new Error(`invalid manifest.segments[${index}].partition: empty`);
  }
  assertPositiveInteger(segment.row_count, `manifest.segments[${index}].row_count`);
  assertPositiveInteger(segment.size_bytes, `manifest.segments[${index}].size_bytes`);
  if (!isValidPackedHlcHex(segment.hlc_max)) {
    throw new Error(`invalid manifest.segments[${index}].hlc_max: ${segment.hlc_max}`);
  }
  assertSqlPrimaryKey(segment.key_min, `manifest.segments[${index}].key_min`);
  assertSqlPrimaryKey(segment.key_max, `manifest.segments[${index}].key_max`);
  if (compareSqlPrimaryKeys(segment.key_min, segment.key_max) > 0) {
    throw new Error(`invalid manifest.segments[${index}]: key_min > key_max`);
  }
}

export function validateManifestFile(manifest: ManifestFile): void {
  if (manifest.v !== 1) {
    throw new Error(`unsupported manifest version tag: ${manifest.v}`);
  }
  assertNonNegativeInteger(manifest.version, 'manifest.version');
  if (!isValidPackedHlcHex(manifest.compaction_hlc)) {
    throw new Error(`invalid manifest.compaction_hlc: ${manifest.compaction_hlc}`);
  }
  if (!Array.isArray(manifest.segments)) {
    throw new Error('invalid manifest.segments: expected array');
  }

  const seenPaths = new Set<string>();
  for (let index = 0; index < manifest.segments.length; index += 1) {
    const segment = manifest.segments[index]!;
    assertManifestSegmentRef(segment, index);
    if (seenPaths.has(segment.path)) {
      throw new Error(`invalid manifest.segments: duplicate path '${segment.path}'`);
    }
    seenPaths.add(segment.path);
  }

  assertSiteMap(manifest.sites_compacted, 'manifest.sites_compacted');
}

function assertSqlTableSchema(table: string, schema: SqlSchema[string]): void {
  if (schema.pk.length === 0) {
    throw new Error(`invalid schema.${table}.pk: empty`);
  }
  if (!isRecord(schema.columns)) {
    throw new Error(`invalid schema.${table}.columns: expected object`);
  }
  const primaryColumn = schema.columns[schema.pk];
  if (!primaryColumn) {
    throw new Error(`invalid schema.${table}: primary key column '${schema.pk}' is missing`);
  }
  if (primaryColumn.crdt !== 'scalar') {
    throw new Error(`invalid schema.${table}.${schema.pk}: primary key column must be scalar`);
  }
  for (const [column, definition] of Object.entries(schema.columns)) {
    if (column.length === 0) {
      throw new Error(`invalid schema.${table}.columns: empty column name`);
    }
    if (
      definition.crdt !== 'scalar' &&
      definition.crdt !== 'lww' &&
      definition.crdt !== 'pn_counter' &&
      definition.crdt !== 'or_set' &&
      definition.crdt !== 'mv_register'
    ) {
      throw new Error(`invalid schema.${table}.${column}.crdt: ${String(definition.crdt)}`);
    }
  }

  const partitionBy = schema.partitionBy ?? null;
  if (partitionBy !== null && !schema.columns[partitionBy]) {
    throw new Error(`invalid schema.${table}.partitionBy: '${partitionBy}' is not a column`);
  }
}

export function validateSqlSchema(schema: SqlSchema): void {
  if (!isRecord(schema)) {
    throw new Error('invalid schema: expected object');
  }
  for (const [table, tableSchema] of Object.entries(schema)) {
    if (table.length === 0) {
      throw new Error('invalid schema: empty table name');
    }
    assertSqlTableSchema(table, tableSchema);
  }
}

function assertSegmentColumnState(
  state: SegmentFile['rows'][number]['cols'][string],
  rowIndex: number,
  column: string,
): void {
  if (state.typ === 1) {
    assertSqlScalar(state.val, `segment.rows[${rowIndex}].cols.${column}.val`);
    if (!isValidPackedHlcHex(state.hlc)) {
      throw new Error(`invalid segment.rows[${rowIndex}].cols.${column}.hlc: ${state.hlc}`);
    }
    if (state.site.length === 0) {
      throw new Error(`invalid segment.rows[${rowIndex}].cols.${column}.site: empty`);
    }
    return;
  }
  if (state.typ === 2) {
    assertSiteMap(state.inc, `segment.rows[${rowIndex}].cols.${column}.inc`);
    assertSiteMap(state.dec, `segment.rows[${rowIndex}].cols.${column}.dec`);
    return;
  }
  if (state.typ === 3) {
    for (let index = 0; index < state.elements.length; index += 1) {
      const element = state.elements[index]!;
      assertSqlScalar(
        element.val,
        `segment.rows[${rowIndex}].cols.${column}.elements[${index}].val`,
      );
      if (!isValidPackedHlcHex(element.hlc)) {
        throw new Error(
          `invalid segment.rows[${rowIndex}].cols.${column}.elements[${index}].hlc: ${element.hlc}`,
        );
      }
      if (element.site.length === 0) {
        throw new Error(
          `invalid segment.rows[${rowIndex}].cols.${column}.elements[${index}].site: empty`,
        );
      }
    }
    for (let index = 0; index < state.tombstones.length; index += 1) {
      const tombstone = state.tombstones[index]!;
      if (!isValidPackedHlcHex(tombstone.hlc)) {
        throw new Error(
          `invalid segment.rows[${rowIndex}].cols.${column}.tombstones[${index}].hlc: ${tombstone.hlc}`,
        );
      }
      if (tombstone.site.length === 0) {
        throw new Error(
          `invalid segment.rows[${rowIndex}].cols.${column}.tombstones[${index}].site: empty`,
        );
      }
    }
    return;
  }
  if (state.typ === 4) {
    for (let index = 0; index < state.values.length; index += 1) {
      const value = state.values[index]!;
      assertSqlScalar(
        value.val,
        `segment.rows[${rowIndex}].cols.${column}.values[${index}].val`,
      );
      if (!isValidPackedHlcHex(value.hlc)) {
        throw new Error(
          `invalid segment.rows[${rowIndex}].cols.${column}.values[${index}].hlc: ${value.hlc}`,
        );
      }
      if (value.site.length === 0) {
        throw new Error(
          `invalid segment.rows[${rowIndex}].cols.${column}.values[${index}].site: empty`,
        );
      }
    }
    return;
  }
  throw new Error(`invalid segment.rows[${rowIndex}].cols.${column}.typ: ${String((state as { typ?: unknown }).typ)}`);
}

export function validateSegmentFile(segment: SegmentFile): void {
  if (segment.v !== 1) {
    throw new Error(`unsupported segment version tag: ${segment.v}`);
  }
  if (segment.table.length === 0) {
    throw new Error('invalid segment.table: empty');
  }
  if (segment.partition.length === 0) {
    throw new Error('invalid segment.partition: empty');
  }
  if (!isValidPackedHlcHex(segment.hlc_max)) {
    throw new Error(`invalid segment.hlc_max: ${segment.hlc_max}`);
  }
  assertNonNegativeInteger(segment.bloom_k, 'segment.bloom_k');
  if (segment.row_count !== segment.rows.length) {
    throw new Error(
      `invalid segment.row_count: expected ${segment.rows.length} got ${segment.row_count}`,
    );
  }
  for (let index = 0; index < segment.rows.length; index += 1) {
    const row = segment.rows[index]!;
    assertSqlPrimaryKey(row.key, `segment.rows[${index}].key`);
    if (index > 0) {
      const prev = segment.rows[index - 1]!;
      if (compareSqlPrimaryKeys(prev.key, row.key) > 0) {
        throw new Error(`invalid segment.rows: row ${index - 1} key > row ${index} key`);
      }
    }
    for (const [column, state] of Object.entries(row.cols)) {
      if (column.length === 0) {
        throw new Error(`invalid segment.rows[${index}].cols: empty column name`);
      }
      assertSegmentColumnState(state, index, column);
    }
  }
}

export function assertManifestPublishable(manifest: ManifestFile, expectedVersion: number): void {
  assertNonNegativeInteger(expectedVersion, 'expectedVersion');
  validateManifestFile(manifest);
  const requiredVersion = expectedVersion + 1;
  if (manifest.version !== requiredVersion) {
    throw new Error(
      `manifest.version must be exactly expectedVersion + 1 (expected ${requiredVersion}, got ${manifest.version})`,
    );
  }
}
