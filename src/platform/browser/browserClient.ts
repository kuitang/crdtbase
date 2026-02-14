import { Hlc, HlcClock, createHlcClock } from '../../core/hlc';
import { LogPosition, ReplicatedLog, takeContiguousEntriesSince } from '../../core/replication';
import {
  EncodedCrdtOp,
  SqlExecutionPlan,
  SqlSchema,
  buildSqlExecutionPlanFromStatement,
  parseSql,
} from '../../core/sql';
import {
  RuntimeRowState,
  applyCrdtOpToRows,
  decodeHlcHex,
  encodeHlcHex,
  resolveSetRemoveTagsFromRows,
  runSelectPlan,
} from '../../core/sqlEval';

export type BrowserCrdtClientOptions = {
  siteId: string;
  log: ReplicatedLog;
  clock?: HlcClock;
  storage?: BrowserHlcStorage | null;
};

export type BrowserHlcStorage = {
  getItem(key: string): string | null;
  setItem(key: string, value: string): void;
};

const BROWSER_HLC_KEY_PREFIX = 'crdtbase.browser.hlc.';

function resolveDefaultBrowserHlcStorage(): BrowserHlcStorage | null {
  try {
    const storage = (globalThis as { localStorage?: BrowserHlcStorage }).localStorage;
    return storage ?? null;
  } catch {
    return null;
  }
}

export class BrowserCrdtClient {
  private readonly rows = new Map<string, RuntimeRowState>();
  private readonly syncedSeqBySite = new Map<string, LogPosition>();
  private readonly syncedHlcBySite = new Map<string, string>();
  private pendingOps: EncodedCrdtOp[] = [];
  private lastLocalHlc: Hlc | null = null;
  private schema: SqlSchema = {};
  private readonly hlcClock: HlcClock;
  private readonly storage: BrowserHlcStorage | null;
  private readonly hlcStorageKey: string;

  constructor(
    public readonly siteId: string,
    private readonly log: ReplicatedLog,
    clock?: HlcClock,
    storage?: BrowserHlcStorage | null,
  ) {
    this.hlcClock = clock ?? createHlcClock();
    this.storage = storage ?? resolveDefaultBrowserHlcStorage();
    this.hlcStorageKey = `${BROWSER_HLC_KEY_PREFIX}${this.siteId}`;
  }

  static async open(options: BrowserCrdtClientOptions): Promise<BrowserCrdtClient> {
    const client = new BrowserCrdtClient(
      options.siteId,
      options.log,
      options.clock,
      options.storage,
    );
    client.loadPersistedLocalHlc();
    return client;
  }

  async exec(sql: string): Promise<void> {
    const statement = parseSql(sql);
    const plan = this.buildPlan(statement);

    switch (plan.kind) {
      case 'ddl_create_table': {
        this.schema[plan.table] = plan.schema;
        return;
      }
      case 'ddl_drop_table': {
        delete this.schema[plan.table];
        return;
      }
      case 'read':
        throw new Error('exec does not accept SELECT statements; use query(sql) instead');
      case 'write': {
        for (const op of plan.ops) {
          applyCrdtOpToRows(this.rows, op);
          this.pendingOps.push(op);
        }
      }
    }
  }

  async query(sql: string): Promise<Record<string, unknown>[]> {
    const statement = parseSql(sql);
    const plan = this.buildPlan(statement);
    if (plan.kind !== 'read') {
      throw new Error(`query requires SELECT statement, got ${plan.kind}`);
    }
    return runSelectPlan(plan.select, this.schema, this.rows);
  }

  async push(): Promise<void> {
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
    this.syncedHlcBySite.set(this.siteId, ops[ops.length - 1]!.hlc);
  }

  async pull(): Promise<void> {
    const sites = await this.log.listSites();
    let localClockAdvanced = false;
    for (const siteId of sites) {
      const since = this.syncedSeqBySite.get(siteId) ?? 0;
      let entries;
      if (since === 0) {
        const pulled = await this.log.readSince(siteId, 0);
        entries = takeContiguousEntriesSince(pulled, 0);
      } else {
        const remoteHead = await this.log.getHead(siteId);
        if (remoteHead < since) {
          throw new Error(
            `local sync cursor for site '${siteId}' (${since}) is ahead of remote head (${remoteHead}); clear local browser client state and retry`,
          );
        }

        const probe = await this.log.readSince(siteId, since - 1);
        const atCursor = probe[0];
        if (!atCursor || atCursor.seq !== since) {
          throw new Error(
            `failed to validate sync cursor for site '${siteId}' at seq ${since}; remote history may be missing or rewritten; clear local browser client state and retry`,
          );
        }

        const expectedHlc = this.syncedHlcBySite.get(siteId);
        if (expectedHlc !== undefined && atCursor.hlc !== expectedHlc) {
          throw new Error(
            `sync cursor mismatch for site '${siteId}' at seq ${since}; local hlc='${expectedHlc}' remote hlc='${atCursor.hlc}'. remote history was likely reset or rewritten; clear local browser client state and retry`,
          );
        }
        if (expectedHlc === undefined) {
          this.syncedHlcBySite.set(siteId, atCursor.hlc);
        }

        entries = takeContiguousEntriesSince(probe.slice(1), since);
      }
      for (const entry of entries) {
        this.lastLocalHlc = this.hlcClock.recv(this.lastLocalHlc, decodeHlcHex(entry.hlc));
        localClockAdvanced = true;
        for (const op of entry.ops) {
          applyCrdtOpToRows(this.rows, op);
        }
        this.syncedSeqBySite.set(siteId, entry.seq);
        this.syncedHlcBySite.set(siteId, entry.hlc);
      }
    }
    if (localClockAdvanced && this.lastLocalHlc !== null) {
      this.persistLocalHlc(encodeHlcHex(this.lastLocalHlc));
    }
  }

  async sync(): Promise<void> {
    await this.push();
    await this.pull();
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
    const next = this.hlcClock.next(this.lastLocalHlc);
    this.lastLocalHlc = next;
    const encoded = encodeHlcHex(next);
    this.persistLocalHlc(encoded);
    return encoded;
  }

  getSyncedHeads(): Record<string, LogPosition> {
    return Object.fromEntries(this.syncedSeqBySite.entries());
  }

  getPendingOpsCount(): number {
    return this.pendingOps.length;
  }

  hydrateForTest(params: {
    schema?: SqlSchema;
    rows?: Map<string, RuntimeRowState>;
    syncedSeqBySite?: Record<string, LogPosition>;
    syncedHlcBySite?: Record<string, string>;
    pendingOps?: EncodedCrdtOp[];
    lastLocalHlcHex?: string | null;
  }): void {
    if (params.schema) {
      this.schema = params.schema;
    }
    if (params.rows) {
      this.rows.clear();
      for (const [key, row] of params.rows.entries()) {
        this.rows.set(key, row);
      }
    }
    if (params.syncedSeqBySite) {
      this.syncedSeqBySite.clear();
      for (const [siteId, seq] of Object.entries(params.syncedSeqBySite)) {
        this.syncedSeqBySite.set(siteId, seq);
      }
    }
    if (params.syncedHlcBySite) {
      this.syncedHlcBySite.clear();
      for (const [siteId, hlc] of Object.entries(params.syncedHlcBySite)) {
        this.syncedHlcBySite.set(siteId, hlc);
      }
    }
    if (params.pendingOps) {
      this.pendingOps = [...params.pendingOps];
    }
    if (params.lastLocalHlcHex !== undefined) {
      this.lastLocalHlc = params.lastLocalHlcHex ? decodeHlcHex(params.lastLocalHlcHex) : null;
    }
  }

  private loadPersistedLocalHlc(): void {
    if (!this.storage) {
      return;
    }
    const encoded = this.storage.getItem(this.hlcStorageKey);
    if (!encoded) {
      return;
    }
    this.lastLocalHlc = decodeHlcHex(encoded);
  }

  private persistLocalHlc(encodedHlc: string): void {
    if (!this.storage) {
      return;
    }
    this.storage.setItem(this.hlcStorageKey, encodedHlc);
  }
}
