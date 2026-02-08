import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { decodeBin, encodeBin } from '../../core/encoding';
import { HLC_LIMITS, Hlc, packHlc } from '../../core/hlc';
import { LwwRegister, mergeLww } from '../../core/crdt/lww';
import { MvRegister, MvRegisterValue, canonicalizeMvRegister, mergeMvRegister } from '../../core/crdt/mvRegister';
import { OrSet, OrSetElement, OrSetTag, canonicalizeOrSet, mergeOrSet } from '../../core/crdt/orSet';
import { PnCounter, applyPnCounterDelta, pnCounterValue } from '../../core/crdt/pnCounter';
import { LogPosition, ReplicatedLog } from '../../core/replication';
import {
  CrdtOpPayload,
  EncodedCrdtOp,
  SetRemoveOpPayload,
  SetRemoveTag,
  SqlComparisonOp,
  SqlExecutionPlan,
  SqlPrimaryKey,
  SqlSchema,
  SqlValue,
  buildSqlExecutionPlanFromStatement,
  parseSql,
} from '../../core/sql';

type ColumnState =
  | { typ: 1; state: LwwRegister<SqlValue> }
  | { typ: 2; state: PnCounter }
  | { typ: 3; state: OrSet<SqlValue> }
  | { typ: 4; state: MvRegister<SqlValue> };

type RowState = {
  table: string;
  key: SqlPrimaryKey;
  columns: Map<string, ColumnState>;
};

type SerializedTag = {
  hlc: string;
  site: string;
};

type SerializedColumnState =
  | { typ: 1; val: SqlValue; hlc: string; site: string }
  | { typ: 2; inc: Record<string, number>; dec: Record<string, number> }
  | {
      typ: 3;
      elements: Array<{ val: SqlValue; hlc: string; site: string }>;
      tombstones: SerializedTag[];
    }
  | {
      typ: 4;
      values: Array<{ val: SqlValue; hlc: string; site: string }>;
    };

type SerializedRow = {
  table: string;
  key: SqlPrimaryKey;
  columns: Record<string, SerializedColumnState>;
};

type StateFile = {
  v: 1;
  rows: SerializedRow[];
  lastLocalHlc: string | null;
};

type SyncFile = {
  v: 1;
  syncedSeqBySite: Record<string, LogPosition>;
};

type PendingFile = {
  v: 1;
  pendingOps: EncodedCrdtOp[];
};

function rowStorageKey(table: string, key: SqlPrimaryKey): string {
  return `${table}\u001f${String(key)}`;
}

function encodeHlcHex(hlc: Hlc): string {
  return `0x${packHlc(hlc).toString(16)}`;
}

function decodeHlcHex(encoded: string): Hlc {
  const normalized = encoded.startsWith('0x') ? encoded : `0x${encoded}`;
  const packed = BigInt(normalized);
  const wallMs = Number(packed >> 16n);
  const counter = Number(packed & 0xFFFFn);
  return { wallMs, counter };
}

function valueEquals(left: SqlValue, right: SqlValue): boolean {
  return Object.is(left, right);
}

function compareSqlScalars(left: SqlValue, right: SqlValue): number | null {
  if (typeof left === 'number' && typeof right === 'number') {
    return left === right ? 0 : left < right ? -1 : 1;
  }
  if (typeof left === 'string' && typeof right === 'string') {
    const cmp = left.localeCompare(right);
    return cmp === 0 ? 0 : cmp < 0 ? -1 : 1;
  }
  if (typeof left === 'boolean' && typeof right === 'boolean') {
    if (left === right) {
      return 0;
    }
    return left ? 1 : -1;
  }
  if (left === null && right === null) {
    return 0;
  }
  return null;
}

function evalCondition(actual: unknown, op: SqlComparisonOp, expected: SqlValue): boolean {
  if (
    actual === null ||
    typeof actual === 'string' ||
    typeof actual === 'number' ||
    typeof actual === 'boolean'
  ) {
    const scalar = actual as SqlValue;
    const cmp = compareSqlScalars(scalar, expected);
    if (cmp === null) {
      return op === '!=';
    }
    switch (op) {
      case '=':
        return cmp === 0;
      case '!=':
        return cmp !== 0;
      case '<':
        return cmp < 0;
      case '>':
        return cmp > 0;
      case '<=':
        return cmp <= 0;
      case '>=':
        return cmp >= 0;
    }
  }

  if (Array.isArray(actual)) {
    if (op === '=') {
      return actual.some((value) => value === expected);
    }
    if (op === '!=') {
      return actual.every((value) => value !== expected);
    }
  }
  return false;
}

function nextMonotonicHlc(previous: Hlc | null, nowMs: number): Hlc {
  const wallMs = previous === null ? nowMs : Math.max(nowMs, previous.wallMs);
  const counter = previous !== null && wallMs === previous.wallMs ? previous.counter + 1 : 0;
  if (wallMs >= HLC_LIMITS.wallMsMax || counter >= HLC_LIMITS.counterMax) {
    throw new Error('unable to allocate monotonic HLC within bounds');
  }
  return { wallMs, counter };
}

function assertCounterPayload(payload: CrdtOpPayload): payload is { d: 'inc' | 'dec'; n: number } {
  return (
    typeof payload === 'object' &&
    payload !== null &&
    'd' in payload &&
    'n' in payload &&
    (payload.d === 'inc' || payload.d === 'dec') &&
    typeof payload.n === 'number'
  );
}

function assertSetAddPayload(payload: CrdtOpPayload): payload is { a: 'add'; val: SqlValue } {
  return typeof payload === 'object' && payload !== null && 'a' in payload && payload.a === 'add' && 'val' in payload;
}

function assertSetRemovePayload(payload: CrdtOpPayload): payload is SetRemoveOpPayload {
  return (
    typeof payload === 'object' &&
    payload !== null &&
    'a' in payload &&
    payload.a === 'rmv' &&
    'tags' in payload &&
    Array.isArray(payload.tags)
  );
}

function isSqlScalar(value: unknown): value is SqlValue {
  return (
    value === null ||
    typeof value === 'string' ||
    typeof value === 'number' ||
    typeof value === 'boolean'
  );
}

function serializeTag(tag: OrSetTag): SerializedTag {
  return { hlc: encodeHlcHex(tag.addHlc), site: tag.addSite };
}

function deserializeTag(tag: SerializedTag): OrSetTag {
  return { addHlc: decodeHlcHex(tag.hlc), addSite: tag.site };
}

function serializeColumnState(state: ColumnState): SerializedColumnState {
  switch (state.typ) {
    case 1:
      return {
        typ: 1,
        val: state.state.val,
        hlc: encodeHlcHex(state.state.hlc),
        site: state.state.site,
      };
    case 2:
      return {
        typ: 2,
        inc: state.state.inc,
        dec: state.state.dec,
      };
    case 3:
      return {
        typ: 3,
        elements: state.state.elements.map((element) => ({
          val: element.val,
          hlc: encodeHlcHex(element.tag.addHlc),
          site: element.tag.addSite,
        })),
        tombstones: state.state.tombstones.map(serializeTag),
      };
    case 4:
      return {
        typ: 4,
        values: state.state.values.map((value) => ({
          val: value.val,
          hlc: encodeHlcHex(value.hlc),
          site: value.site,
        })),
      };
  }
}

function deserializeColumnState(state: SerializedColumnState): ColumnState {
  switch (state.typ) {
    case 1:
      return {
        typ: 1,
        state: {
          val: state.val,
          hlc: decodeHlcHex(state.hlc),
          site: state.site,
        },
      };
    case 2:
      return {
        typ: 2,
        state: {
          inc: state.inc,
          dec: state.dec,
        },
      };
    case 3:
      return {
        typ: 3,
        state: canonicalizeOrSet({
          elements: state.elements.map(
            (element): OrSetElement<SqlValue> => ({
              val: element.val,
              tag: { addHlc: decodeHlcHex(element.hlc), addSite: element.site },
            }),
          ),
          tombstones: state.tombstones.map(deserializeTag),
        }),
      };
    case 4:
      return {
        typ: 4,
        state: canonicalizeMvRegister({
          values: state.values.map(
            (value): MvRegisterValue<SqlValue> => ({
              val: value.val,
              hlc: decodeHlcHex(value.hlc),
              site: value.site,
            }),
          ),
        }),
      };
  }
}

export type NodeCrdtClientOptions = {
  siteId: string;
  log: ReplicatedLog;
  dataDir: string;
  now?: () => number;
};

export class NodeCrdtClient {
  private readonly rows = new Map<string, RowState>();
  private readonly syncedSeqBySite = new Map<string, LogPosition>();
  private pendingOps: EncodedCrdtOp[] = [];
  private lastLocalHlc: Hlc | null = null;
  private schema: SqlSchema = {};
  private readonly ready: Promise<void>;
  private readonly now: () => number;

  private readonly schemaPath: string;
  private readonly statePath: string;
  private readonly pendingPath: string;
  private readonly syncPath: string;

  constructor(
    public readonly siteId: string,
    private readonly log: ReplicatedLog,
    private readonly dataDir: string,
    now?: () => number,
  ) {
    this.now = now ?? (() => Date.now());
    this.schemaPath = join(this.dataDir, 'schema.bin');
    this.statePath = join(this.dataDir, 'state.bin');
    this.pendingPath = join(this.dataDir, 'pending.bin');
    this.syncPath = join(this.dataDir, 'sync.bin');
    this.ready = this.loadFromDisk();
  }

  static async open(options: NodeCrdtClientOptions): Promise<NodeCrdtClient> {
    const client = new NodeCrdtClient(options.siteId, options.log, options.dataDir, options.now);
    await client.waitReady();
    return client;
  }

  async exec(sql: string): Promise<void> {
    await this.waitReady();
    const statement = parseSql(sql);
    const plan = this.buildPlan(statement);
    switch (plan.kind) {
      case 'ddl_create_table': {
        this.schema[plan.table] = plan.schema;
        await this.persistSchema();
        return;
      }
      case 'ddl_drop_table': {
        delete this.schema[plan.table];
        await this.persistSchema();
        return;
      }
      case 'read':
        throw new Error(`exec does not accept SELECT statements; use query(sql) instead`);
      case 'write': {
        for (const op of plan.ops) {
          this.applyOp(op);
          this.pendingOps.push(op);
        }
        await this.persistStateFiles();
      }
    }
  }

  async query(sql: string): Promise<Record<string, unknown>[]> {
    await this.waitReady();
    const statement = parseSql(sql);
    const plan = this.buildPlan(statement);
    if (plan.kind !== 'read') {
      throw new Error(`query requires SELECT statement, got ${plan.kind}`);
    }

    const tableSchema = this.schema[plan.select.table];
    if (!tableSchema) {
      throw new Error(`unknown table '${plan.select.table}'`);
    }

    const rows: Record<string, unknown>[] = [];
    for (const row of this.rows.values()) {
      if (row.table !== plan.select.table) {
        continue;
      }

      const materialized = this.materializeRow(row);
      materialized[tableSchema.pk] = row.key;
      if (!plan.select.filters.every((condition) => evalCondition(materialized[condition.column], condition.op, condition.value))) {
        continue;
      }

      if (plan.select.columns === '*') {
        rows.push(materialized);
        continue;
      }

      const projected = Object.fromEntries(
        plan.select.columns.map((column) => [column, materialized[column]]),
      );
      rows.push(projected);
    }
    return rows;
  }

  async push(): Promise<void> {
    await this.waitReady();
    if (this.pendingOps.length === 0) {
      return;
    }

    const ops = [...this.pendingOps];
    const seq = await this.log.append({
      siteId: this.siteId,
      hlc: ops[ops.length - 1]!.hlc,
      ops,
    });
    this.pendingOps = [];
    this.syncedSeqBySite.set(this.siteId, seq);
    await this.persistStateFiles();
  }

  async pull(): Promise<void> {
    await this.waitReady();
    const sites = await this.log.listSites();
    for (const siteId of sites) {
      const since = this.syncedSeqBySite.get(siteId) ?? 0;
      const entries = await this.log.readSince(siteId, since);
      for (const entry of entries) {
        for (const op of entry.ops) {
          this.applyOp(op);
        }
        this.syncedSeqBySite.set(siteId, entry.seq);
      }
    }
    await this.persistStateFiles();
  }

  async sync(): Promise<void> {
    await this.push();
    await this.pull();
  }

  getDataDir(): string {
    return this.dataDir;
  }

  private buildPlan(statement: ReturnType<typeof parseSql>): SqlExecutionPlan {
    return buildSqlExecutionPlanFromStatement(statement, {
      schema: this.schema,
      site: this.siteId,
      nextHlc: () => this.nextLocalHlcHex(),
      resolveSetRemoveTags: ({ table, key, column, value }) =>
        this.resolveSetRemoveTags(table, key, column, value),
    });
  }

  private materializeRow(row: RowState): Record<string, unknown> {
    const values: Record<string, unknown> = {};
    for (const [column, state] of row.columns.entries()) {
      switch (state.typ) {
        case 1:
          values[column] = state.state.val;
          break;
        case 2:
          values[column] = pnCounterValue(state.state);
          break;
        case 3: {
          const seen = new Set<string>();
          const out: SqlValue[] = [];
          for (const element of state.state.elements) {
            const fingerprint = JSON.stringify(element.val);
            if (!seen.has(fingerprint)) {
              seen.add(fingerprint);
              out.push(element.val);
            }
          }
          values[column] = out;
          break;
        }
        case 4:
          values[column] =
            state.state.values.length === 1
              ? state.state.values[0]!.val
              : state.state.values.map((entry) => entry.val);
          break;
      }
    }
    return values;
  }

  private resolveSetRemoveTags(
    table: string,
    key: SqlPrimaryKey,
    column: string,
    value: SqlValue,
  ): SetRemoveTag[] {
    const row = this.rows.get(rowStorageKey(table, key));
    const state = row?.columns.get(column);
    if (!state || state.typ !== 3) {
      return [];
    }
    return state.state.elements
      .filter((element) => valueEquals(element.val, value))
      .map((element) => ({
        hlc: encodeHlcHex(element.tag.addHlc),
        site: element.tag.addSite,
      }));
  }

  private applyOp(op: EncodedCrdtOp): void {
    const key = rowStorageKey(op.tbl, op.key);
    const row = this.rows.get(key) ?? { table: op.tbl, key: op.key, columns: new Map<string, ColumnState>() };
    const current = row.columns.get(op.col);
    const incomingHlc = decodeHlcHex(op.hlc);

    switch (op.typ) {
      case 1: {
        if (!isSqlScalar(op.val)) {
          throw new Error(`invalid LWW payload for ${op.tbl}.${op.col}`);
        }
        const incoming: LwwRegister<SqlValue> = {
          val: op.val,
          hlc: incomingHlc,
          site: op.site,
        };
        if (!current) {
          row.columns.set(op.col, { typ: 1, state: incoming });
        } else if (current.typ === 1) {
          row.columns.set(op.col, { typ: 1, state: mergeLww(current.state, incoming) });
        } else {
          throw new Error(`column '${op.tbl}.${op.col}' was previously typ ${current.typ}, got typ 1`);
        }
        break;
      }
      case 2: {
        if (!assertCounterPayload(op.val)) {
          throw new Error(`invalid PN-Counter payload for ${op.tbl}.${op.col}`);
        }
        if (current && current.typ !== 2) {
          throw new Error(`column '${op.tbl}.${op.col}' was previously typ ${current.typ}, got typ 2`);
        }
        const base = current?.typ === 2 ? current.state : { inc: {}, dec: {} };
        const merged = applyPnCounterDelta(base, op.site, op.val.d, op.val.n);
        row.columns.set(op.col, { typ: 2, state: merged });
        break;
      }
      case 3: {
        if (current && current.typ !== 3) {
          throw new Error(`column '${op.tbl}.${op.col}' was previously typ ${current.typ}, got typ 3`);
        }
        const base = current?.typ === 3 ? current.state : { elements: [], tombstones: [] };
        if (assertSetAddPayload(op.val)) {
          const element: OrSetElement<SqlValue> = {
            val: op.val.val,
            tag: { addHlc: incomingHlc, addSite: op.site },
          };
          row.columns.set(op.col, {
            typ: 3,
            state: mergeOrSet(base, { elements: [element], tombstones: [] }),
          });
          break;
        }
        if (!assertSetRemovePayload(op.val)) {
          throw new Error(`invalid OR-Set payload for ${op.tbl}.${op.col}`);
        }
        const tombstones: OrSetTag[] = op.val.tags.map((tag) => ({
          addHlc: decodeHlcHex(tag.hlc),
          addSite: tag.site,
        }));
        row.columns.set(op.col, {
          typ: 3,
          state: mergeOrSet(base, { elements: [], tombstones }),
        });
        break;
      }
      case 4: {
        if (!isSqlScalar(op.val)) {
          throw new Error(`invalid MV-Register payload for ${op.tbl}.${op.col}`);
        }
        if (current && current.typ !== 4) {
          throw new Error(`column '${op.tbl}.${op.col}' was previously typ ${current.typ}, got typ 4`);
        }
        const base = current?.typ === 4 ? current.state : { values: [] };
        const value: MvRegisterValue<SqlValue> = {
          val: op.val,
          hlc: incomingHlc,
          site: op.site,
        };
        row.columns.set(op.col, {
          typ: 4,
          state: mergeMvRegister(base, { values: [value] }),
        });
        break;
      }
      default:
        throw new Error(`unsupported CRDT op type ${(op as { typ: number }).typ}`);
    }

    this.rows.set(key, row);
  }

  private nextLocalHlcHex(): string {
    const next = nextMonotonicHlc(this.lastLocalHlc, this.now());
    this.lastLocalHlc = next;
    return encodeHlcHex(next);
  }

  private async waitReady(): Promise<void> {
    await this.ready;
  }

  private async loadFromDisk(): Promise<void> {
    await mkdir(this.dataDir, { recursive: true });
    const [schema, state, pending, sync] = await Promise.all([
      this.readOptionalFile<SqlSchema>(this.schemaPath, {}),
      this.readOptionalFile<StateFile>(this.statePath, { v: 1, rows: [], lastLocalHlc: null }),
      this.readOptionalFile<PendingFile>(this.pendingPath, { v: 1, pendingOps: [] }),
      this.readOptionalFile<SyncFile>(this.syncPath, { v: 1, syncedSeqBySite: {} }),
    ]);

    this.schema = schema;
    this.pendingOps = [...pending.pendingOps];
    this.lastLocalHlc = state.lastLocalHlc ? decodeHlcHex(state.lastLocalHlc) : null;
    this.syncedSeqBySite.clear();
    for (const [site, seq] of Object.entries(sync.syncedSeqBySite)) {
      this.syncedSeqBySite.set(site, seq);
    }

    this.rows.clear();
    for (const row of state.rows) {
      const columns = new Map<string, ColumnState>();
      for (const [column, columnState] of Object.entries(row.columns)) {
        columns.set(column, deserializeColumnState(columnState));
      }
      this.rows.set(rowStorageKey(row.table, row.key), {
        table: row.table,
        key: row.key,
        columns,
      });
    }
  }

  private async persistSchema(): Promise<void> {
    await writeFile(this.schemaPath, encodeBin(this.schema));
  }

  private async persistStateFiles(): Promise<void> {
    const rows: SerializedRow[] = [...this.rows.values()].map((row) => ({
      table: row.table,
      key: row.key,
      columns: Object.fromEntries(
        [...row.columns.entries()].map(([column, state]) => [column, serializeColumnState(state)]),
      ),
    }));

    const stateFile: StateFile = {
      v: 1,
      rows,
      lastLocalHlc: this.lastLocalHlc ? encodeHlcHex(this.lastLocalHlc) : null,
    };

    const pendingFile: PendingFile = {
      v: 1,
      pendingOps: this.pendingOps,
    };

    const syncFile: SyncFile = {
      v: 1,
      syncedSeqBySite: Object.fromEntries(this.syncedSeqBySite.entries()),
    };

    await Promise.all([
      writeFile(this.statePath, encodeBin(stateFile)),
      writeFile(this.pendingPath, encodeBin(pendingFile)),
      writeFile(this.syncPath, encodeBin(syncFile)),
    ]);
  }

  private async readOptionalFile<T>(path: string, fallback: T): Promise<T> {
    try {
      const bytes = await readFile(path);
      return decodeBin<T>(bytes);
    } catch (error) {
      const code = (error as { code?: string }).code;
      if (code === 'ENOENT') {
        return fallback;
      }
      throw error;
    }
  }
}
