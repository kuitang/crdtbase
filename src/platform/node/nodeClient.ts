import { mkdir, readFile, rename, rm, writeFile } from 'node:fs/promises';
import { dirname, join } from 'node:path';
import { ManifestFile, SegmentFile, mergeRuntimeRowMaps, segmentFileToRuntimeRows } from '../../core/compaction';
import { decodeBin, encodeBin } from '../../core/encoding';
import { Hlc, HlcClock, createHlcClock } from '../../core/hlc';
import { LogPosition, ReplicatedLog, takeContiguousEntriesSince } from '../../core/replication';
import { SnapshotStore, assertSafeSnapshotRelativePath } from '../../core/snapshotStore';
import {
  EncodedCrdtOp,
  SqlClientExecutionPlan,
  SqlSchema,
  buildClientSqlExecutionPlanFromStatement,
  buildEffectiveSchemaForPlanning,
  parseSql,
} from '../../core/sql';
import {
  RuntimeRowState,
  SqlEvalRowState,
  applyCrdtOpToRows,
  decodeHlcHex,
  encodeHlcHex,
  evalRowsToRuntime,
  materializeSchemaFromRows,
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

type SyncFileV2 = {
  v: 2;
  syncedBySite: Record<
    string,
    {
      seq: LogPosition;
      hlc: string | null;
    }
  >;
};

type PendingFile = {
  v: 1;
  pendingOps: EncodedCrdtOp[];
};

type AtomicStateBundleFile = {
  v: 1;
  state: StateFile;
  pending: PendingFile;
  sync: SyncFileV2;
};

export type NodeCrdtClientOptions = {
  siteId: string;
  log: ReplicatedLog;
  dataDir: string;
  clock?: HlcClock;
};

export class NodeCrdtClient {
  private readonly rows = new Map<string, RuntimeRowState>();
  private readonly syncedSeqBySite = new Map<string, LogPosition>();
  private readonly syncedHlcBySite = new Map<string, string>();
  private pendingOps: EncodedCrdtOp[] = [];
  private lastLocalHlc: Hlc | null = null;
  private schema: SqlSchema = {};
  private readonly ready: Promise<void>;
  private readonly hlcClock: HlcClock;
  private readonly snapshots: SnapshotStore | null;
  private localSnapshotManifestVersion = 0;

  private readonly schemaPath: string;
  private readonly atomicStateBundlePath: string;
  private readonly statePath: string;
  private readonly pendingPath: string;
  private readonly syncPath: string;
  private readonly snapshotRootDir: string;
  private readonly snapshotManifestPath: string;

  constructor(
    public readonly siteId: string,
    private readonly log: ReplicatedLog,
    private readonly dataDir: string,
    clock?: HlcClock,
  ) {
    this.hlcClock = clock ?? createHlcClock();
    this.snapshots = log.getSnapshotStore?.() ?? null;
    this.schemaPath = join(this.dataDir, 'schema.bin');
    this.atomicStateBundlePath = join(this.dataDir, 'state_bundle.bin');
    this.statePath = join(this.dataDir, 'state.bin');
    this.pendingPath = join(this.dataDir, 'pending.bin');
    this.syncPath = join(this.dataDir, 'sync.bin');
    this.snapshotRootDir = join(this.dataDir, 'snapshots');
    this.snapshotManifestPath = join(this.snapshotRootDir, 'manifest.bin');
    this.ready = this.loadFromDisk();
  }

  static async open(options: NodeCrdtClientOptions): Promise<NodeCrdtClient> {
    const client = new NodeCrdtClient(
      options.siteId,
      options.log,
      options.dataDir,
      options.clock,
    );
    await client.waitReady();
    return client;
  }

  async exec(sql: string): Promise<void> {
    await this.waitReady();
    const statement = parseSql(sql);
    const plan = this.buildPlan(statement);
    switch (plan.kind) {
      case 'read':
        throw new Error(`exec does not accept SELECT statements; use query(sql) instead`);
      case 'write': {
        for (const op of plan.ops) {
          applyCrdtOpToRows(this.rows, op);
          this.pendingOps.push(op);
        }
        this.refreshSchemaFromRows();
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
    return runSelectPlan(plan.select, buildEffectiveSchemaForPlanning(this.schema), this.rows);
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
    this.syncedHlcBySite.set(this.siteId, ops[ops.length - 1]!.hlc);
    await this.persistStateFiles();
  }

  async pull(): Promise<void> {
    await this.waitReady();
    await this.refreshFromSnapshotManifest();
    const sites = await this.log.listSites();
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
            `local sync cursor for site '${siteId}' (${since}) is ahead of remote head (${remoteHead}); reset local data dir '${this.dataDir}' and retry`,
          );
        }

        const probe = await this.log.readSince(siteId, since - 1);
        const atCursor = probe[0];
        if (!atCursor || atCursor.seq !== since) {
          throw new Error(
            `failed to validate sync cursor for site '${siteId}' at seq ${since}; remote history may be missing or rewritten; reset local data dir '${this.dataDir}' and retry`,
          );
        }

        const expectedHlc = this.syncedHlcBySite.get(siteId);
        if (expectedHlc !== undefined && atCursor.hlc !== expectedHlc) {
          throw new Error(
            `sync cursor mismatch for site '${siteId}' at seq ${since}; local hlc='${expectedHlc}' remote hlc='${atCursor.hlc}'. remote history was likely reset or rewritten; reset local data dir '${this.dataDir}' and retry`,
          );
        }
        if (expectedHlc === undefined) {
          this.syncedHlcBySite.set(siteId, atCursor.hlc);
        }

        entries = takeContiguousEntriesSince(probe.slice(1), since);
      }
      for (const entry of entries) {
        this.lastLocalHlc = this.hlcClock.recv(this.lastLocalHlc, decodeHlcHex(entry.hlc));
        for (const op of entry.ops) {
          applyCrdtOpToRows(this.rows, op);
        }
        this.refreshSchemaFromRows();
        this.syncedSeqBySite.set(siteId, entry.seq);
        this.syncedHlcBySite.set(siteId, entry.hlc);
      }
    }
    await this.persistStateFiles();
  }

  async sync(): Promise<void> {
    await this.push();
    await this.pull();
  }

  getSyncedHeads(): Record<string, LogPosition> {
    return Object.fromEntries(this.syncedSeqBySite.entries());
  }

  getPendingOpsCount(): number {
    return this.pendingOps.length;
  }

  getDataDir(): string {
    return this.dataDir;
  }

  private buildPlan(statement: ReturnType<typeof parseSql>): SqlClientExecutionPlan {
    return buildClientSqlExecutionPlanFromStatement(statement, {
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
    return encodeHlcHex(next);
  }

  private refreshSchemaFromRows(): void {
    const materialized = materializeSchemaFromRows(this.rows);
    if (Object.keys(materialized).length === 0) {
      return;
    }
    this.schema = materialized;
  }

  private async waitReady(): Promise<void> {
    await this.ready;
  }

  private async loadFromDisk(): Promise<void> {
    await mkdir(this.dataDir, { recursive: true });
    const [schema, atomicBundle, legacyState, legacyPending, legacySync, localManifest] = await Promise.all([
      this.readOptionalFile<SqlSchema>(this.schemaPath, {}),
      this.readOptionalFile<AtomicStateBundleFile | null>(this.atomicStateBundlePath, null),
      this.readOptionalFile<StateFile>(this.statePath, { v: 1, rows: [], lastLocalHlc: null }),
      this.readOptionalFile<PendingFile>(this.pendingPath, { v: 1, pendingOps: [] }),
      this.readOptionalFile<SyncFile | SyncFileV2>(this.syncPath, { v: 2, syncedBySite: {} }),
      this.readOptionalFile<ManifestFile | null>(this.snapshotManifestPath, null),
    ]);

    const state = atomicBundle?.state ?? legacyState;
    const pending = atomicBundle?.pending ?? legacyPending;
    const sync = atomicBundle?.sync ?? legacySync;

    this.schema = schema;
    this.pendingOps = [...pending.pendingOps];
    this.lastLocalHlc = state.lastLocalHlc ? decodeHlcHex(state.lastLocalHlc) : null;
    this.syncedSeqBySite.clear();
    this.syncedHlcBySite.clear();
    if (sync.v === 1) {
      for (const [site, seq] of Object.entries(sync.syncedSeqBySite)) {
        this.syncedSeqBySite.set(site, seq);
      }
    } else {
      for (const [site, cursor] of Object.entries(sync.syncedBySite)) {
        this.syncedSeqBySite.set(site, cursor.seq);
        if (cursor.hlc !== null) {
          this.syncedHlcBySite.set(site, cursor.hlc);
        }
      }
    }

    this.rows.clear();
    for (const [key, row] of evalRowsToRuntime(state.rows).entries()) {
      this.rows.set(key, row);
    }
    const materializedSchema = materializeSchemaFromRows(this.rows);
    if (Object.keys(materializedSchema).length > 0) {
      this.schema = materializedSchema;
    }

    this.localSnapshotManifestVersion = localManifest?.version ?? 0;
  }

  private async persistSchema(): Promise<void> {
    await this.writeFileAtomically(this.schemaPath, encodeBin(this.schema));
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

    const syncFile: SyncFileV2 = {
      v: 2,
      syncedBySite: Object.fromEntries(
        [...this.syncedSeqBySite.entries()].map(([siteId, seq]) => [
          siteId,
          {
            seq,
            hlc: this.syncedHlcBySite.get(siteId) ?? null,
          },
        ]),
      ),
    };

    const atomicBundle: AtomicStateBundleFile = {
      v: 1,
      state: stateFile,
      pending: pendingFile,
      sync: syncFile,
    };

    // Commit the authoritative local state as one atomically-renamed bundle.
    await this.writeFileAtomically(this.atomicStateBundlePath, encodeBin(atomicBundle));

    // Legacy split files remain for backwards compatibility and tooling.
    await Promise.all([
      this.writeFileAtomically(this.schemaPath, encodeBin(this.schema)),
      this.writeFileAtomically(this.statePath, encodeBin(stateFile)),
      this.writeFileAtomically(this.pendingPath, encodeBin(pendingFile)),
      this.writeFileAtomically(this.syncPath, encodeBin(syncFile)),
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

  private async writeFileAtomically(path: string, bytes: Uint8Array): Promise<void> {
    const tempPath = `${path}.tmp-${process.pid}-${Date.now()}-${Math.random().toString(16).slice(2)}`;
    await mkdir(dirname(path), { recursive: true });
    await writeFile(tempPath, bytes);
    try {
      await rename(tempPath, path);
    } catch (error) {
      await rm(tempPath, { force: true });
      throw error;
    }
  }

  private async refreshFromSnapshotManifest(): Promise<void> {
    if (!this.snapshots) {
      return;
    }
    await this.hydrateSchemaFromSnapshotsIfMissing();
    const manifest = await this.snapshots.getManifest();
    if (manifest === null || manifest.version <= this.localSnapshotManifestVersion) {
      return;
    }
    if (!this.manifestCoversKnownSites(manifest)) {
      // Reject incomplete manifests for sites we already track; otherwise we may
      // replace rows with a partial snapshot and skip required log replay.
      return;
    }

    const rows = new Map<string, RuntimeRowState>();
    await mkdir(this.snapshotRootDir, { recursive: true });

    for (const segmentRef of manifest.segments) {
      assertSafeSnapshotRelativePath(segmentRef.path, 'segment path');
      const bytes = await this.snapshots.getSegment(segmentRef.path);
      if (bytes === null) {
        throw new Error(`manifest references missing segment: ${segmentRef.path}`);
      }

      const cachePath = this.resolveSnapshotSegmentCachePath(segmentRef.path);
      await mkdir(dirname(cachePath), { recursive: true });
      await writeFile(cachePath, bytes);

      const segment = decodeBin<SegmentFile>(bytes);
      const loaded = segmentFileToRuntimeRows(segment);
      mergeRuntimeRowMaps(rows, loaded);
    }

    // Preserve read-your-writes for local unpushed operations across segment reload.
    for (const pending of this.pendingOps) {
      applyCrdtOpToRows(rows, pending);
    }

    this.rows.clear();
    for (const [key, row] of rows.entries()) {
      this.rows.set(key, row);
    }
    this.refreshSchemaFromRows();

    // Reset site cursors to compaction watermarks so uncompacted deltas are replayed exactly once.
    for (const [siteId, seq] of Object.entries(manifest.sites_compacted)) {
      this.syncedSeqBySite.set(siteId, seq);
      this.syncedHlcBySite.delete(siteId);
    }

    await this.writeFileAtomically(this.snapshotManifestPath, encodeBin(manifest));
    this.localSnapshotManifestVersion = manifest.version;
  }

  private manifestCoversKnownSites(manifest: ManifestFile): boolean {
    for (const [siteId, seq] of this.syncedSeqBySite.entries()) {
      if (seq <= 0) {
        continue;
      }
      if (!(siteId in manifest.sites_compacted)) {
        return false;
      }
    }
    return true;
  }

  private async hydrateSchemaFromSnapshotsIfMissing(): Promise<void> {
    if (!this.snapshots) {
      return;
    }
    if (Object.keys(this.schema).length > 0) {
      return;
    }
    const snapshotSchema = await this.snapshots.getSchema();
    if (snapshotSchema === null) {
      return;
    }
    this.schema = snapshotSchema;
    await this.persistSchema();
  }

  private resolveSnapshotSegmentCachePath(segmentPath: string): string {
    assertSafeSnapshotRelativePath(segmentPath, 'segment path');
    return join(this.snapshotRootDir, segmentPath);
  }
}
