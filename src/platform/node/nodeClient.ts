import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { decodeBin, encodeBin } from '../../core/encoding';
import { HLC_LIMITS, Hlc } from '../../core/hlc';
import { LogPosition, ReplicatedLog } from '../../core/replication';
import {
  EncodedCrdtOp,
  SqlExecutionPlan,
  SqlSchema,
  buildSqlExecutionPlanFromStatement,
  parseSql,
} from '../../core/sql';
import {
  RuntimeRowState,
  SqlEvalRowState,
  applyCrdtOpToRows,
  decodeHlcHex,
  encodeHlcHex,
  evalRowsToRuntime,
  resolveSetRemoveTagsFromRows,
  runSelectPlan,
  runtimeRowsToEval,
} from '../../core/sqlEval';

type StateFile = {
  v: 1;
  rows: SqlEvalRowState[];
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

function nextMonotonicHlc(previous: Hlc | null, nowMs: number): Hlc {
  const wallMs = previous === null ? nowMs : Math.max(nowMs, previous.wallMs);
  const counter = previous !== null && wallMs === previous.wallMs ? previous.counter + 1 : 0;
  if (wallMs >= HLC_LIMITS.wallMsMax || counter >= HLC_LIMITS.counterMax) {
    throw new Error('unable to allocate monotonic HLC within bounds');
  }
  return { wallMs, counter };
}

export type NodeCrdtClientOptions = {
  siteId: string;
  log: ReplicatedLog;
  dataDir: string;
  now?: () => number;
};

export class NodeCrdtClient {
  private readonly rows = new Map<string, RuntimeRowState>();
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
          applyCrdtOpToRows(this.rows, op);
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
    return runSelectPlan(plan.select, this.schema, this.rows);
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
          applyCrdtOpToRows(this.rows, op);
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
        resolveSetRemoveTagsFromRows(this.rows, table, key, column, value),
    });
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
    for (const [key, row] of evalRowsToRuntime(state.rows).entries()) {
      this.rows.set(key, row);
    }
  }

  private async persistSchema(): Promise<void> {
    await writeFile(this.schemaPath, encodeBin(this.schema));
  }

  private async persistStateFiles(): Promise<void> {
    const stateFile: StateFile = {
      v: 1,
      rows: runtimeRowsToEval(this.rows),
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
