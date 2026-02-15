import { createHash } from 'node:crypto';
import { mkdir, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { setTimeout as sleep } from 'node:timers/promises';
import { GetObjectCommand, PutObjectCommand, S3Client } from '@aws-sdk/client-s3';
import { S3ReplicatedLog } from '../../src/backend/s3ReplicatedLog';
import { TigrisSnapshotStore } from '../../src/backend/tigrisSnapshotStore';
import type { SqlSchema } from '../../src/core/sql';
import { createHlcClock } from '../../src/core/hlc';
import { compactReplicatedLog } from '../../src/platform/node/compactor';
import { NodeCrdtClient } from '../../src/platform/node/nodeClient';
import {
  CREATE_TASKS_TABLE_SQL,
  TASK_QUERY_SQL,
  schemaOwnerForSeed,
} from '../shared/tasksSchema';

const TASKS_SCHEMA: SqlSchema = {
  tasks: {
    pk: 'id',
    partitionBy: null,
    columns: {
      id: { crdt: 'scalar' },
      title: { crdt: 'lww' },
      points: { crdt: 'pn_counter' },
      tags: { crdt: 'or_set' },
      status: { crdt: 'mv_register' },
    },
  },
};

type SiteId = 'site-a' | 'site-b' | 'site-c';

type WorkerConfig = {
  runId: string;
  siteId: SiteId;
  region: string;
  bucket: string;
  s3Prefix: string;
  controlPrefix: string;
  compactorSiteId: SiteId | null;
  compactionEveryOps: number;
  snapshotPrefix: string;
  opsPerClient: number;
  barrierEveryOps: number;
  hardBarrierEvery: number;
  rowCount: number;
  pollIntervalMs: number;
  drainRounds: number;
  drainQuiescenceRounds: number;
  drainMaxExtraRounds: number;
  commandTimeoutMs: number;
  seed: number;
  dataDir: string;
};

type NormalizedTaskRow = {
  id: string;
  title: unknown;
  points: number;
  tags: string[];
  status: string[];
};

type BarrierCommand = {
  action: 'continue' | 'drain' | 'abort';
  reason?: string;
  drainRounds?: number;
  targetHeads?: Record<string, number>;
  issuedAt: string;
};

type BarrierCommandPhase = 'entry' | 'release';

type BarrierReport = {
  runId: string;
  siteId: SiteId;
  region: string;
  barrierIndex: number;
  barrierType: 'soft' | 'hard';
  phase: 'pre' | 'drained';
  opIndex: number;
  stateHash: string;
  rowCount: number;
  heads: Record<string, number>;
  syncedHeads: Record<string, number>;
  pendingOps: number;
  invariantOk: boolean;
  invariantErrors: string[];
  expectedLocalPointsByRow: Record<string, number>;
  expectedLocalTagsByRow: Record<string, string[]>;
  stats: {
    writes: number;
    pushes: number;
    pulls: number;
    syncs: number;
  };
  generatedAt: string;
};

type FinalReport = {
  runId: string;
  siteId: SiteId;
  region: string;
  success: boolean;
  stateHash: string | null;
  stats: {
    writes: number;
    pushes: number;
    pulls: number;
    syncs: number;
  };
  error?: string;
  generatedAt: string;
};

type MutableExpectations = {
  points: Map<string, number>;
  tags: Map<string, Set<string>>;
};

function logLine(siteId: string, runId: string, message: string): void {
  process.stdout.write(`[${new Date().toISOString()}] [${runId}] [${siteId}] ${message}\n`);
}

function parsePositiveIntEnv(name: string, fallback: number): number {
  const raw = process.env[name];
  if (!raw || raw.trim().length === 0) {
    return fallback;
  }
  const value = Number.parseInt(raw, 10);
  if (!Number.isFinite(value) || value <= 0) {
    throw new Error(`invalid ${name}='${raw}'`);
  }
  return value;
}

function parseSiteId(raw: string | undefined): SiteId {
  if (raw === 'site-a' || raw === 'site-b' || raw === 'site-c') {
    return raw;
  }
  throw new Error(`invalid SITE_ID='${String(raw)}'`);
}


function parseOptionalSiteId(raw: string | undefined): SiteId | null {
  if (!raw || raw.trim().length === 0) {
    return null;
  }
  return parseSiteId(raw.trim());
}

function readRequiredEnv(name: string): string {
  const value = process.env[name];
  if (!value || value.trim().length === 0) {
    throw new Error(`missing required env ${name}`);
  }
  return value;
}

function createSeededRng(seed: number): () => number {
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

function siteSalt(siteId: SiteId): number {
  switch (siteId) {
    case 'site-a':
      return 0x9e3779b9;
    case 'site-b':
      return 0x85ebca6b;
    case 'site-c':
      return 0xc2b2ae35;
  }
}

function escapeSqlString(value: string): string {
  return value.replaceAll("'", "''");
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

function normalizeTaskRows(rows: Record<string, unknown>[]): NormalizedTaskRow[] {
  return [...rows]
    .map((row) => ({
      id: String(row.id),
      title: row.title,
      points: typeof row.points === 'number' ? row.points : 0,
      tags: normalizeStringArray(row.tags),
      status: normalizeStringArray(row.status),
    }))
    .sort((left, right) => left.id.localeCompare(right.id));
}

function hashRows(rows: NormalizedTaskRow[]): string {
  return createHash('sha256').update(JSON.stringify(rows)).digest('hex');
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

function validateLocalInvariants(params: {
  rows: NormalizedTaskRow[];
  expectations: MutableExpectations;
}): { ok: boolean; errors: string[] } {
  const byId = new Map(params.rows.map((row) => [row.id, row]));
  const errors: string[] = [];

  for (const [rowId, expectedPoints] of params.expectations.points.entries()) {
    const row = byId.get(rowId);
    if (!row) {
      errors.push(`missing row '${rowId}'`);
      continue;
    }
    if (row.points < expectedPoints) {
      errors.push(
        `row '${rowId}' points regressed below local expectation: actual=${row.points} expected>=${expectedPoints}`,
      );
    }
  }

  for (const [rowId, expectedTags] of params.expectations.tags.entries()) {
    const row = byId.get(rowId);
    if (!row) {
      errors.push(`missing row '${rowId}' for tags`);
      continue;
    }
    const actual = new Set(row.tags);
    for (const tag of expectedTags) {
      if (!actual.has(tag)) {
        errors.push(`row '${rowId}' missing local tag '${tag}'`);
      }
    }
  }

  return {
    ok: errors.length === 0,
    errors: errors.slice(0, 50),
  };
}

async function objectBodyToString(body: unknown): Promise<string> {
  if (!body) {
    throw new Error('S3 object body is empty');
  }
  const streamBody = body as {
    transformToString?: (encoding?: string) => Promise<string>;
    transformToByteArray?: () => Promise<Uint8Array>;
  };
  if (typeof streamBody.transformToString === 'function') {
    return streamBody.transformToString('utf-8');
  }
  if (typeof streamBody.transformToByteArray === 'function') {
    const bytes = await streamBody.transformToByteArray();
    return new TextDecoder().decode(bytes);
  }
  throw new Error('unsupported S3 body type');
}

async function putJson(client: S3Client, bucket: string, key: string, value: unknown): Promise<void> {
  const body = JSON.stringify(value);
  await client.send(
    new PutObjectCommand({
      Bucket: bucket,
      Key: key,
      Body: body,
      ContentType: 'application/json',
    }),
  );
}

async function getJson<T>(client: S3Client, bucket: string, key: string): Promise<T | null> {
  try {
    const object = await client.send(
      new GetObjectCommand({
        Bucket: bucket,
        Key: key,
      }),
    );
    const text = await objectBodyToString(object.Body);
    if (text.trim().length === 0) {
      return null;
    }
    try {
      return JSON.parse(text) as T;
    } catch (parseError) {
      if (parseError instanceof SyntaxError) {
        return null;
      }
      throw parseError;
    }
  } catch (error) {
    if ((error as { name?: string }).name === 'NoSuchKey') {
      return null;
    }
    const status = (error as { $metadata?: { httpStatusCode?: number } }).$metadata?.httpStatusCode;
    if (status === 404) {
      return null;
    }
    throw error;
  }
}

function readConfig(): WorkerConfig {
  const runId = readRequiredEnv('RUN_ID');
  const siteId = parseSiteId(readRequiredEnv('SITE_ID'));
  const region = process.env.SITE_REGION ?? process.env.FLY_REGION ?? 'unknown';
  const bucket = readRequiredEnv('BUCKET_NAME');
  const s3Prefix = process.env.S3_PREFIX ?? 'deltas';
  const controlPrefix = process.env.CONTROL_PREFIX ?? 'control';
  const compactorSiteId = parseOptionalSiteId(process.env.STRESS_COMPACTOR_SITE);
  const compactionEveryOps = parsePositiveIntEnv('STRESS_COMPACTION_EVERY_OPS', 3_000);
  const snapshotPrefix = process.env.STRESS_SNAPSHOT_PREFIX?.trim() || 'snapshots';
  const opsPerClient = parsePositiveIntEnv('STRESS_OPS_PER_CLIENT', 30_000);
  const barrierEveryOps = parsePositiveIntEnv('STRESS_BARRIER_EVERY_OPS', 3_000);
  const hardBarrierEvery = parsePositiveIntEnv('STRESS_HARD_BARRIER_EVERY', 2);
  const rowCount = parsePositiveIntEnv('STRESS_ROW_COUNT', 64);
  const pollIntervalMs = parsePositiveIntEnv('STRESS_POLL_INTERVAL_MS', 250);
  const drainRounds = parsePositiveIntEnv('STRESS_DRAIN_ROUNDS', 8);
  const drainQuiescenceRounds = parsePositiveIntEnv('STRESS_DRAIN_QUIESCENCE_ROUNDS', 2);
  const drainMaxExtraRounds = parsePositiveIntEnv('STRESS_DRAIN_MAX_EXTRA_ROUNDS', 200);
  const commandTimeoutMs = parsePositiveIntEnv('STRESS_COMMAND_TIMEOUT_S', 180) * 1000;
  const seedRaw = readRequiredEnv('STRESS_SEED');
  const seed = Number.parseInt(seedRaw, 10) | 0;
  const dataDir =
    process.env.DATA_DIR ??
    join(tmpdir(), 'crdtbase-stress-worker', runId, siteId, `${Date.now()}-${process.pid}`);

  if (barrierEveryOps > opsPerClient) {
    throw new Error(
      `STRESS_BARRIER_EVERY_OPS (${barrierEveryOps}) must be <= STRESS_OPS_PER_CLIENT (${opsPerClient})`,
    );
  }

  return {
    runId,
    siteId,
    region,
    bucket,
    s3Prefix,
    controlPrefix,
    compactorSiteId,
    compactionEveryOps,
    snapshotPrefix,
    opsPerClient,
    barrierEveryOps,
    hardBarrierEvery,
    rowCount,
    pollIntervalMs,
    drainRounds,
    drainQuiescenceRounds,
    drainMaxExtraRounds,
    commandTimeoutMs,
    seed,
    dataDir,
  };
}

function rowIdsFor(count: number): string[] {
  const ids: string[] = [];
  for (let index = 0; index < count; index += 1) {
    ids.push(`t${index + 1}`);
  }
  return ids;
}

function pickRowId(rng: () => number, rowIds: readonly string[]): string {
  const hotSetSize = Math.min(8, rowIds.length);
  if (rng() < 0.72 && hotSetSize > 0) {
    return rowIds[rngInt(rng, 0, hotSetSize - 1)]!;
  }
  return rowIds[rngInt(rng, 0, rowIds.length - 1)]!;
}

function barrierLabel(index: number): string {
  return String(index).padStart(4, '0');
}

function compareHeadsToTarget(
  syncedHeads: Record<string, number>,
  targetHeads: Record<string, number>,
): { reached: boolean; missing: string[] } {
  const missing: string[] = [];
  for (const [siteId, target] of Object.entries(targetHeads)) {
    const targetSeq = Number.isFinite(target) ? target : 0;
    const actualSeq = syncedHeads[siteId] ?? 0;
    if (actualSeq < targetSeq) {
      missing.push(`${siteId}:${actualSeq}<${targetSeq}`);
    }
  }
  return {
    reached: missing.length === 0,
    missing,
  };
}

async function loadHeads(log: S3ReplicatedLog): Promise<Record<string, number>> {
  const out: Record<string, number> = {};
  for (const siteId of ['site-a', 'site-b', 'site-c']) {
    try {
      out[siteId] = await log.getHead(siteId);
    } catch {
      out[siteId] = 0;
    }
  }
  return out;
}

async function waitForCommand(params: {
  s3: S3Client;
  config: WorkerConfig;
  barrierIndex: number;
  allowDrain: boolean;
  phase: BarrierCommandPhase;
}): Promise<BarrierCommand> {
  const key = `${params.config.controlPrefix}/${params.config.runId}/commands/barrier-${barrierLabel(params.barrierIndex)}/${params.phase}.json`;
  const deadline = Date.now() + params.config.commandTimeoutMs;
  let nextLogAt = Date.now() + 10_000;

  while (Date.now() < deadline) {
    const command = await getJson<BarrierCommand>(params.s3, params.config.bucket, key);
    if (!command) {
      if (Date.now() >= nextLogAt) {
        logLine(
          params.config.siteId,
          params.config.runId,
          `still waiting for barrier command index=${params.barrierIndex} phase=${params.phase}`,
        );
        nextLogAt = Date.now() + 10_000;
      }
      await sleep(params.config.pollIntervalMs);
      continue;
    }
    if (command.action === 'abort') {
      return command;
    }
    if (command.action === 'continue') {
      return command;
    }
    if (command.action === 'drain' && params.allowDrain) {
      return command;
    }
    await sleep(params.config.pollIntervalMs);
  }

  throw new Error(
    `timed out waiting for ${params.phase} command at barrier ${params.barrierIndex} after ${params.config.commandTimeoutMs}ms`,
  );
}

async function runMain(): Promise<void> {
  const config = readConfig();
  const schemaOwner = schemaOwnerForSeed(config.seed);
  const isCompactor = config.compactorSiteId === config.siteId;
  logLine(
    config.siteId,
    config.runId,
    `worker starting region=${config.region} ops=${config.opsPerClient} barrierEvery=${config.barrierEveryOps} hardEvery=${config.hardBarrierEvery} pushAfterWrite=true pullBeforeRead=true drainRounds=${config.drainRounds} quiescence=${config.drainQuiescenceRounds} maxExtra=${config.drainMaxExtraRounds} schemaOwner=${schemaOwner} compactorSite=${config.compactorSiteId ?? "none"} isCompactor=${isCompactor ? 1 : 0} compactionEveryOps=${config.compactionEveryOps}`,
  );
  const baseSeed = (config.seed ^ siteSalt(config.siteId)) >>> 0;
  const rng = createSeededRng(baseSeed);
  const rowIds = rowIdsFor(config.rowCount);
  const expectations: MutableExpectations = {
    points: new Map(rowIds.map((rowId) => [rowId, 0])),
    tags: new Map(rowIds.map((rowId) => [rowId, new Set([`seed-${rowId}`])])),
  };
  const stats = {
    writes: 0,
    pushes: 0,
    pulls: 0,
    syncs: 0,
  };

  const endpoint = readRequiredEnv('AWS_ENDPOINT_URL_S3');
  const accessKeyId = readRequiredEnv('AWS_ACCESS_KEY_ID');
  const secretAccessKey = readRequiredEnv('AWS_SECRET_ACCESS_KEY');
  const sessionToken = process.env.AWS_SESSION_TOKEN;
  const region = process.env.AWS_REGION ?? process.env.AWS_DEFAULT_REGION ?? 'auto';

  const s3 = new S3Client({
    endpoint,
    region,
    forcePathStyle: process.env.S3_FORCE_PATH_STYLE === 'true',
    credentials: {
      accessKeyId,
      secretAccessKey,
      ...(sessionToken ? { sessionToken } : {}),
    },
  });

  await mkdir(config.dataDir, { recursive: true });

  const log = new S3ReplicatedLog({
    bucket: config.bucket,
    prefix: config.s3Prefix,
    snapshotPrefix: config.snapshotPrefix,
    clientConfig: {
      endpoint,
      region,
      forcePathStyle: process.env.S3_FORCE_PATH_STYLE === 'true',
      credentials: {
        accessKeyId,
        secretAccessKey,
        ...(sessionToken ? { sessionToken } : {}),
      },
    },
  });

  const snapshots = isCompactor
    ? new TigrisSnapshotStore({
        bucket: config.bucket,
        prefix: config.snapshotPrefix,
        clientConfig: {
          endpoint,
          region,
          forcePathStyle: process.env.S3_FORCE_PATH_STYLE === 'true',
          credentials: {
            accessKeyId,
            secretAccessKey,
            ...(sessionToken ? { sessionToken } : {}),
          },
        },
      })
    : null;
  let snapshotSchemaPublished = false;

  const runCompaction = async (trigger: string): Promise<void> => {
    if (!snapshots) {
      return;
    }
    if (!snapshotSchemaPublished) {
      await snapshots.putSchema(TASKS_SCHEMA);
      snapshotSchemaPublished = true;
      logLine(config.siteId, config.runId, 'published snapshot schema prefix=' + config.snapshotPrefix);
    }
    const result = await compactReplicatedLog({
      log,
      snapshots,
      schema: TASKS_SCHEMA,
    });
    logLine(
      config.siteId,
      config.runId,
      'compaction trigger=' + trigger +
        ' applied=' + String(result.applied ? 1 : 0) +
        ' opsRead=' + String(result.opsRead) +
        ' manifestVersion=' + String(result.manifest.version) +
        ' segments=' + String(result.manifest.segments.length),
    );
  };

  const client = await NodeCrdtClient.open({
    siteId: config.siteId,
    log,
    dataDir: config.dataDir,
    clock: createHlcClock({ nowWallMs: (() => {
      let tick = 10_000;
      return () => {
        tick += 1;
        return tick;
      };
    })() }),
  });

  const publishBarrier = async (params: {
    barrierIndex: number;
    barrierType: 'soft' | 'hard';
    phase: 'pre' | 'drained';
    opIndex: number;
  }): Promise<BarrierReport> => {
    const rows = normalizeTaskRows(await client.query(TASK_QUERY_SQL));
    const invariants = validateLocalInvariants({ rows, expectations });
    const materialized = materializeExpectations(expectations);
    const report: BarrierReport = {
      runId: config.runId,
      siteId: config.siteId,
      region: config.region,
      barrierIndex: params.barrierIndex,
      barrierType: params.barrierType,
      phase: params.phase,
      opIndex: params.opIndex,
      stateHash: hashRows(rows),
      rowCount: rows.length,
      heads: await loadHeads(log),
      syncedHeads: client.getSyncedHeads(),
      pendingOps: client.getPendingOpsCount(),
      invariantOk: invariants.ok,
      invariantErrors: invariants.errors,
      expectedLocalPointsByRow: materialized.expectedPointsByRow,
      expectedLocalTagsByRow: materialized.expectedTagsByRow,
      stats: { ...stats },
      generatedAt: new Date().toISOString(),
    };

    const key = `${config.controlPrefix}/${config.runId}/barrier-${barrierLabel(params.barrierIndex)}/${params.phase}/${config.siteId}.json`;
    await putJson(s3, config.bucket, key, report);
    logLine(
      config.siteId,
      config.runId,
      `published barrier report index=${params.barrierIndex} type=${params.barrierType} phase=${params.phase} hash=${report.stateHash.slice(0, 12)} invariantOk=${report.invariantOk}`,
    );
    return report;
  };

  const runBarrier = async (barrierIndex: number, opIndex: number): Promise<void> => {
    const barrierType: 'soft' | 'hard' =
      barrierIndex % config.hardBarrierEvery === 0 ? 'hard' : 'soft';
    logLine(
      config.siteId,
      config.runId,
      `entering barrier index=${barrierIndex} type=${barrierType} opIndex=${opIndex}`,
    );
    // Flush local writes then refresh remote cursors before publishing pre-barrier heads.
    await client.push();
    stats.pushes += 1;
    await client.pull();
    stats.pulls += 1;
    await publishBarrier({
      barrierIndex,
      barrierType,
      phase: 'pre',
      opIndex,
    });

    const command = await waitForCommand({
      s3,
      config,
      barrierIndex,
      allowDrain: true,
      phase: 'entry',
    });

    if (command.action === 'abort') {
      throw new Error(`coordinator aborted at barrier ${barrierIndex}: ${command.reason ?? 'unknown'}`);
    }
    logLine(
      config.siteId,
      config.runId,
      `received barrier command index=${barrierIndex} action=${command.action}`,
    );

    if (command.action === 'drain') {
      if (isCompactor) {
        await runCompaction(`barrier-${barrierIndex}-entry`);
      }
      const requestedRounds = command.drainRounds ?? config.drainRounds;
      const hardRoundLimit = requestedRounds + config.drainMaxExtraRounds;
      const targetHeads = command.targetHeads ?? {};
      let roundsPerformed = 0;
      let stableRounds = 0;
      let lastHash: string | null = null;
      let reachedTarget = false;
      let missingTarget: string[] = [];

      while (
        (roundsPerformed < requestedRounds ||
          stableRounds < config.drainQuiescenceRounds ||
          !reachedTarget) &&
        roundsPerformed < hardRoundLimit
      ) {
        await client.push();
        stats.pushes += 1;
        await client.pull();
        stats.pulls += 1;
        roundsPerformed += 1;
        const syncedHeads = client.getSyncedHeads();
        const targetCheck = compareHeadsToTarget(syncedHeads, targetHeads);
        reachedTarget = targetCheck.reached;
        missingTarget = targetCheck.missing;
        const rows = normalizeTaskRows(await client.query(TASK_QUERY_SQL));
        const currentHash = hashRows(rows);
        if (lastHash === currentHash) {
          stableRounds += 1;
        } else {
          stableRounds = 0;
        }
        lastHash = currentHash;
      }

      if (stableRounds < config.drainQuiescenceRounds) {
        throw new Error(
          `drain quiescence target not reached index=${barrierIndex} requested=${requestedRounds} performed=${roundsPerformed} stableRounds=${stableRounds}`,
        );
      }
      if (!reachedTarget) {
        throw new Error(
          `drain target heads not reached index=${barrierIndex} requested=${requestedRounds} performed=${roundsPerformed} missing=${missingTarget.join(',')}`,
        );
      }
      logLine(
        config.siteId,
        config.runId,
        `completed drain index=${barrierIndex} requested=${requestedRounds} performed=${roundsPerformed} stableRounds=${stableRounds} target=${JSON.stringify(targetHeads)} localSynced=${JSON.stringify(client.getSyncedHeads())}`,
      );
      if (isCompactor) {
        await runCompaction(`barrier-${barrierIndex}-drained`);
      }
      await publishBarrier({
        barrierIndex,
        barrierType: 'hard',
        phase: 'drained',
        opIndex,
      });

      const followUp = await waitForCommand({
        s3,
        config,
        barrierIndex,
        allowDrain: false,
        phase: 'release',
      });
      if (followUp.action === 'abort') {
        throw new Error(
          `coordinator aborted after drain at barrier ${barrierIndex}: ${followUp.reason ?? 'unknown'}`,
        );
      }
      logLine(
        config.siteId,
        config.runId,
        `received post-drain command index=${barrierIndex} action=${followUp.action}`,
      );
    }
  };

  const publishFinal = async (report: FinalReport): Promise<void> => {
    const key = `${config.controlPrefix}/${config.runId}/final/${config.siteId}.json`;
    await putJson(s3, config.bucket, key, report);
  };

  try {
    if (config.siteId === schemaOwner) {
      await client.exec(CREATE_TASKS_TABLE_SQL);
      for (const rowId of rowIds) {
        await client.exec(
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
      await client.push();
      stats.pushes += 1;
      logLine(config.siteId, config.runId, `seeded ${rowIds.length} rows and pushed initial state`);
    } else {
      const startupDeadline = Date.now() + 180_000;
      while (Date.now() < startupDeadline) {
        await client.pull();
        stats.pulls += 1;
        let rows: NormalizedTaskRow[] = [];
        try {
          rows = normalizeTaskRows(await client.query(TASK_QUERY_SQL));
        } catch {
          await sleep(300);
          continue;
        }
        if (rows.length >= config.rowCount) {
          break;
        }
        await sleep(300);
      }
      let rows: NormalizedTaskRow[] = [];
      try {
        rows = normalizeTaskRows(await client.query(TASK_QUERY_SQL));
      } catch {
        rows = [];
      }
      if (rows.length < config.rowCount) {
        throw new Error(
          `startup pull did not receive seeded rows: expected>=${config.rowCount} got=${rows.length}`,
        );
      }
      logLine(config.siteId, config.runId, `startup pull completed rows=${rows.length}`);
    }

    if (isCompactor) {
      await runCompaction('startup');
    }

    let barrierIndex = 0;
    const statuses = ['open', 'review', 'blocked', 'done'];

    for (let opIndex = 1; opIndex <= config.opsPerClient; opIndex += 1) {
      const rowId = pickRowId(rng, rowIds);
      const opRoll = rng();
      let wrote = false;

      if (opRoll < 0.5) {
        const amount = rngInt(rng, 1, 7);
        await client.exec(`INC tasks.points BY ${amount} WHERE id = '${escapeSqlString(rowId)}';`);
        expectations.points.set(rowId, (expectations.points.get(rowId) ?? 0) + amount);
        wrote = true;
      } else if (opRoll < 0.82) {
        const tag = `${config.siteId}-t-${opIndex}-${rngInt(rng, 10_000, 999_999)}`;
        await client.exec(
          `ADD '${escapeSqlString(tag)}' TO tasks.tags WHERE id = '${escapeSqlString(rowId)}';`,
        );
        const set = expectations.tags.get(rowId);
        if (!set) {
          throw new Error(`unknown row in expectations '${rowId}'`);
        }
        set.add(tag);
        wrote = true;
      } else if (opRoll < 0.92) {
        const title = `${config.siteId}-title-${opIndex}-${rngInt(rng, 1, 999_999)}`;
        await client.exec(
          `UPDATE tasks SET title = '${escapeSqlString(title)}' WHERE id = '${escapeSqlString(rowId)}';`,
        );
        wrote = true;
      } else if (opRoll < 0.97) {
        const status = rngPick(rng, statuses);
        await client.exec(
          `UPDATE tasks SET status = '${escapeSqlString(status)}' WHERE id = '${escapeSqlString(rowId)}';`,
        );
        wrote = true;
      } else {
        await client.pull();
        stats.pulls += 1;
        const rows = normalizeTaskRows(await client.query(TASK_QUERY_SQL));
        const row = rows.find((candidate) => candidate.id === rowId);
        if (!row) {
          throw new Error(`read operation missing row '${rowId}'`);
        }
        const expectedPoints = expectations.points.get(rowId) ?? 0;
        if (row.points < expectedPoints) {
          throw new Error(
            `read operation observed points regression for '${rowId}': actual=${row.points} expected>=${expectedPoints}`,
          );
        }
      }

      if (wrote) {
        stats.writes += 1;
        await client.push();
        stats.pushes += 1;
      }

      if (isCompactor && opIndex % config.compactionEveryOps === 0) {
        await runCompaction(`op-${opIndex}`);
      }

      if (opIndex % config.barrierEveryOps === 0) {
        barrierIndex += 1;
        await runBarrier(barrierIndex, opIndex);
      }

      if (opIndex % 1000 === 0) {
        logLine(
          config.siteId,
          config.runId,
          `progress op=${opIndex}/${config.opsPerClient} stats=${JSON.stringify(stats)}`,
        );
      }
    }

    if (config.opsPerClient % config.barrierEveryOps !== 0) {
      barrierIndex += 1;
      await runBarrier(barrierIndex, config.opsPerClient);
    }

    if (isCompactor) {
      await runCompaction('final');
    }

    await client.push();
    stats.pushes += 1;
    await client.pull();
    stats.pulls += 1;
    const finalRows = normalizeTaskRows(await client.query(TASK_QUERY_SQL));
    await publishFinal({
      runId: config.runId,
      siteId: config.siteId,
      region: config.region,
      success: true,
      stateHash: hashRows(finalRows),
      stats: { ...stats },
      generatedAt: new Date().toISOString(),
    });
    logLine(
      config.siteId,
      config.runId,
      `worker completed success hash=${hashRows(finalRows).slice(0, 12)} stats=${JSON.stringify(stats)}`,
    );
  } catch (error) {
    const message = error instanceof Error ? `${error.message}\n${error.stack ?? ''}` : String(error);
    await putJson(s3, config.bucket, `${config.controlPrefix}/${config.runId}/errors/${config.siteId}.json`, {
      runId: config.runId,
      siteId: config.siteId,
      error: message,
      generatedAt: new Date().toISOString(),
    }).catch(() => undefined);
    await putJson(s3, config.bucket, `${config.controlPrefix}/${config.runId}/final/${config.siteId}.json`, {
      runId: config.runId,
      siteId: config.siteId,
      region: config.region,
      success: false,
      stateHash: null,
      stats: { ...stats },
      error: message,
      generatedAt: new Date().toISOString(),
    } satisfies FinalReport).catch(() => undefined);
    logLine(config.siteId, config.runId, `worker failed error=${message}`);
    throw error;
  } finally {
    await rm(config.dataDir, { recursive: true, force: true }).catch(() => undefined);
    s3.destroy();
  }
}

runMain().catch((error) => {
  const message = error instanceof Error ? `${error.message}\n${error.stack ?? ''}` : String(error);
  process.stderr.write(`${message}\n`);
  process.exitCode = 1;
});
