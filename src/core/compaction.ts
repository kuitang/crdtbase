import { packHlc } from './hlc';
import { EncodedCrdtOp, SqlPrimaryKey, SqlSchema, SqlTableSchema } from './sql';
import {
  RuntimeRowState,
  SqlEvalColumnState,
  SqlEvalRowState,
  applyCrdtOpToRows,
  evalRowsToRuntime,
  materializeRow,
  runtimeColumnStateToEval,
} from './sqlEval';

export type SegmentRow = {
  key: SqlPrimaryKey;
  cols: Record<string, SqlEvalColumnState>;
};

export type SegmentFile = {
  v: 1;
  table: string;
  partition: string;
  hlc_max: string;
  row_count: number;
  bloom: Uint8Array;
  bloom_k: number;
  rows: SegmentRow[];
};

export type ManifestSegmentRef = {
  path: string;
  table: string;
  partition: string;
  row_count: number;
  size_bytes: number;
  hlc_max: string;
  key_min: SqlPrimaryKey;
  key_max: SqlPrimaryKey;
};

export type ManifestFile = {
  v: 1;
  version: number;
  compaction_hlc: string;
  segments: ManifestSegmentRef[];
  sites_compacted: Record<string, number>;
};

export type BuiltSegment = {
  path: string;
  segment: SegmentFile;
};

type PartitionGroup = {
  table: string;
  partition: string;
  rows: RuntimeRowState[];
};

const textEncoder = new TextEncoder();

function compareText(left: string, right: string): number {
  if (left < right) return -1;
  if (left > right) return 1;
  return 0;
}

function normalizeHlcHex(value: string): string {
  if (value.startsWith('0x') || value.startsWith('0X')) {
    return `0x${value.slice(2).toLowerCase()}`;
  }
  return `0x${value.toLowerCase()}`;
}

function parseHlcHex(value: string): bigint {
  return BigInt(normalizeHlcHex(value));
}

function sortObjectByKey<T>(record: Record<string, T>): Record<string, T> {
  return Object.fromEntries(
    Object.entries(record).sort(([left], [right]) => compareText(left, right)),
  );
}

function rowToSegmentRow(row: RuntimeRowState): SegmentRow {
  const cols: Record<string, SqlEvalColumnState> = {};
  for (const [column, state] of [...row.columns.entries()].sort(([left], [right]) =>
    compareText(left, right),
  )) {
    cols[column] = runtimeColumnStateToEval(state);
  }
  return {
    key: row.key,
    cols: sortObjectByKey(cols),
  };
}

function hlcCandidatesFromColumnState(state: SqlEvalColumnState): string[] {
  switch (state.typ) {
    case 1:
      return [state.hlc];
    case 2:
      return [];
    case 3:
      return [
        ...state.elements.map((element) => element.hlc),
        ...state.tombstones.map((tombstone) => tombstone.hlc),
      ];
    case 4:
      return state.values.map((entry) => entry.hlc);
  }
}

function computeSegmentHlcMax(rows: SegmentRow[], fallback: string): string {
  let out = normalizeHlcHex(fallback);
  for (const row of rows) {
    for (const state of Object.values(row.cols)) {
      for (const candidate of hlcCandidatesFromColumnState(state)) {
        out = maxHlcHex(out, candidate);
      }
    }
  }
  return out;
}

function hashFNV1a(bytes: Uint8Array, seed: number): number {
  let hash = (0x811c9dc5 ^ seed) >>> 0;
  for (let index = 0; index < bytes.length; index += 1) {
    hash ^= bytes[index]!;
    hash = Math.imul(hash, 0x01000193) >>> 0;
  }
  return hash >>> 0;
}

function hashIndex(text: string, seed: number, bitCount: number): number {
  const bytes = textEncoder.encode(text);
  return hashFNV1a(bytes, seed) % bitCount;
}

function setBit(bits: Uint8Array, index: number): void {
  const byteIndex = Math.floor(index / 8);
  const bitIndex = index % 8;
  bits[byteIndex] = bits[byteIndex]! | (1 << bitIndex);
}

function getBit(bits: Uint8Array, index: number): boolean {
  const byteIndex = Math.floor(index / 8);
  const bitIndex = index % 8;
  return (bits[byteIndex]! & (1 << bitIndex)) !== 0;
}

export function compareSqlPrimaryKeys(left: SqlPrimaryKey, right: SqlPrimaryKey): number {
  if (typeof left === 'number' && typeof right === 'number') {
    if (left < right) return -1;
    if (left > right) return 1;
    return 0;
  }
  if (typeof left === 'string' && typeof right === 'string') {
    return compareText(left, right);
  }
  return compareText(String(left), String(right));
}

export function maxHlcHex(left: string, right: string): string {
  const leftPacked = parseHlcHex(left);
  const rightPacked = parseHlcHex(right);
  return leftPacked >= rightPacked
    ? normalizeHlcHex(left)
    : normalizeHlcHex(right);
}

export function maxHlcHexAcrossOps(ops: EncodedCrdtOp[], fallback = '0x0'): string {
  let out = normalizeHlcHex(fallback);
  for (const op of ops) {
    out = maxHlcHex(out, op.hlc);
  }
  return out;
}

export function buildBloomFilter(
  keys: SqlPrimaryKey[],
  bitsPerElement = 10,
): { bloom: Uint8Array; bloomK: number } {
  if (keys.length === 0) {
    return {
      bloom: new Uint8Array(0),
      bloomK: 0,
    };
  }

  const requestedBitCount = Math.max(8, Math.ceil(keys.length * bitsPerElement));
  const byteCount = Math.ceil(requestedBitCount / 8);
  const bitCount = byteCount * 8;
  const bloom = new Uint8Array(byteCount);
  const bloomK = Math.max(1, Math.round((bitCount / keys.length) * Math.log(2)));
  const seeds = Array.from({ length: bloomK }, (_, index) => (index + 1) * 0x9e3779b1);

  for (const key of keys) {
    const serialized = String(key);
    for (const seed of seeds) {
      setBit(bloom, hashIndex(serialized, seed, bitCount));
    }
  }

  return { bloom, bloomK };
}

export function bloomMayContain(
  bloom: Uint8Array,
  bloomK: number,
  key: SqlPrimaryKey,
): boolean {
  if (bloom.length === 0 || bloomK === 0) {
    return false;
  }
  const bitCount = bloom.length * 8;
  for (let index = 0; index < bloomK; index += 1) {
    const seed = (index + 1) * 0x9e3779b1;
    const slot = hashIndex(String(key), seed, bitCount);
    if (!getBit(bloom, slot)) {
      return false;
    }
  }
  return true;
}

export function applyOpsToRuntimeRows(
  rows: Map<string, RuntimeRowState>,
  ops: EncodedCrdtOp[],
): void {
  for (const op of ops) {
    applyCrdtOpToRows(rows, op);
  }
}

export function segmentFileToRuntimeRows(segment: SegmentFile): Map<string, RuntimeRowState> {
  const evalRows: SqlEvalRowState[] = segment.rows.map((row) => ({
    table: segment.table,
    key: row.key,
    columns: row.cols,
  }));
  return evalRowsToRuntime(evalRows);
}

export function mergeRuntimeRowMaps(
  target: Map<string, RuntimeRowState>,
  source: Map<string, RuntimeRowState>,
): void {
  for (const [key, row] of source.entries()) {
    target.set(key, row);
  }
}

export function resolveRowPartition(row: RuntimeRowState, tableSchema: SqlTableSchema): string {
  const partitionBy = tableSchema.partitionBy ?? null;
  if (partitionBy === null) {
    return '_default';
  }
  if (partitionBy === tableSchema.pk) {
    return String(row.key);
  }
  const materialized = materializeRow(row)[partitionBy];
  if (
    typeof materialized === 'string' ||
    typeof materialized === 'number' ||
    typeof materialized === 'boolean'
  ) {
    return String(materialized);
  }
  return '_default';
}

export function groupRowsByTableAndPartition(
  schema: SqlSchema,
  rows: Map<string, RuntimeRowState>,
): PartitionGroup[] {
  const groups = new Map<string, PartitionGroup>();
  for (const row of rows.values()) {
    const tableSchema = schema[row.table];
    if (!tableSchema) {
      continue;
    }
    const partition = resolveRowPartition(row, tableSchema);
    const groupKey = `${row.table}\u001f${partition}`;
    const existing =
      groups.get(groupKey) ??
      {
        table: row.table,
        partition,
        rows: [],
      };
    existing.rows.push(row);
    groups.set(groupKey, existing);
  }
  return [...groups.values()].sort((left, right) => {
    const tableCmp = compareText(left.table, right.table);
    if (tableCmp !== 0) {
      return tableCmp;
    }
    return compareText(left.partition, right.partition);
  });
}

function sanitizePathToken(value: string): string {
  const sanitized = value.replace(/[^a-zA-Z0-9._-]/gu, '_');
  return sanitized.length === 0 ? '_' : sanitized;
}

function compactionHlcSuffix(value: string): string {
  const raw = normalizeHlcHex(value).slice(2);
  return raw.padStart(8, '0').slice(0, 8);
}

export function defaultSegmentPath(table: string, partition: string, hlcMax: string): string {
  return `segments/${sanitizePathToken(table)}_${sanitizePathToken(partition)}_${compactionHlcSuffix(hlcMax)}.seg.bin`;
}

export function buildSegmentFile(params: {
  table: string;
  partition: string;
  rows: RuntimeRowState[];
  defaultHlcMax: string;
}): SegmentFile {
  const sortedRows = [...params.rows].sort((left, right) =>
    compareSqlPrimaryKeys(left.key, right.key),
  );
  const segmentRows = sortedRows.map((row) => {
    if (row.table !== params.table) {
      throw new Error(`row table mismatch in segment build: ${row.table} != ${params.table}`);
    }
    return rowToSegmentRow(row);
  });
  const { bloom, bloomK } = buildBloomFilter(segmentRows.map((row) => row.key));
  const hlcMax = computeSegmentHlcMax(segmentRows, params.defaultHlcMax);
  return {
    v: 1,
    table: params.table,
    partition: params.partition,
    hlc_max: hlcMax,
    row_count: segmentRows.length,
    bloom,
    bloom_k: bloomK,
    rows: segmentRows,
  };
}

export function buildSegmentsFromRows(params: {
  schema: SqlSchema;
  rows: Map<string, RuntimeRowState>;
  defaultHlcMax: string;
  segmentPathFor?: (table: string, partition: string, hlcMax: string) => string;
}): BuiltSegment[] {
  const groups = groupRowsByTableAndPartition(params.schema, params.rows);
  const segmentPathFor = params.segmentPathFor ?? defaultSegmentPath;
  const out: BuiltSegment[] = [];
  for (const group of groups) {
    if (group.rows.length === 0) {
      continue;
    }
    const segment = buildSegmentFile({
      table: group.table,
      partition: group.partition,
      rows: group.rows,
      defaultHlcMax: params.defaultHlcMax,
    });
    out.push({
      path: segmentPathFor(segment.table, segment.partition, segment.hlc_max),
      segment,
    });
  }
  return out.sort((left, right) => compareText(left.path, right.path));
}

export function buildManifestSegmentRef(
  path: string,
  segment: SegmentFile,
  sizeBytes: number,
): ManifestSegmentRef {
  if (segment.rows.length === 0) {
    throw new Error(`cannot create manifest ref for empty segment '${path}'`);
  }
  return {
    path,
    table: segment.table,
    partition: segment.partition,
    row_count: segment.row_count,
    size_bytes: sizeBytes,
    hlc_max: normalizeHlcHex(segment.hlc_max),
    key_min: segment.rows[0]!.key,
    key_max: segment.rows[segment.rows.length - 1]!.key,
  };
}

export function makeEmptyManifest(): ManifestFile {
  return {
    v: 1,
    version: 0,
    compaction_hlc: '0x0',
    segments: [],
    sites_compacted: {},
  };
}

export function isValidPackedHlcHex(value: string): boolean {
  try {
    const packed = parseHlcHex(value);
    const wallMs = Number(packed >> 16n);
    const counter = Number(packed & 0xffffn);
    packHlc({ wallMs, counter });
    return true;
  } catch {
    return false;
  }
}
