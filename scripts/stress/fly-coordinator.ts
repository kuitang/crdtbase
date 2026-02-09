import { randomBytes } from 'node:crypto';
import { setTimeout as sleep } from 'node:timers/promises';
import {
  CreateBucketCommand,
  DeleteBucketCommand,
  DeleteObjectsCommand,
  GetObjectCommand,
  HeadObjectCommand,
  ListObjectsV2Command,
  PutObjectCommand,
  S3Client,
  type S3ClientConfig,
} from '@aws-sdk/client-s3';
import type { components } from './fly-machines-openapi';
import {
  SITE_IDS,
  computeTargetHeadsFromPreReports,
  resolveFlyApiBaseUrl,
  sanitizeBucketName,
  validatePreBarrierSyncState,
  type SiteId,
  type WorkerBarrierReport,
} from './flyCoordinatorCore';

type FlyMachine = components['schemas']['Machine'];
type CreateMachineRequest = components['schemas']['CreateMachineRequest'];

type WorkerFinalReport = {
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

type BarrierPhase = 'pre' | 'drained';
type CommandPhase = 'entry' | 'release';

type BarrierCommand = {
  action: 'continue' | 'drain' | 'abort';
  phase: CommandPhase;
  note: string;
  issuedAt: string;
  reason?: string;
  drainRounds?: number;
  targetHeads?: Record<SiteId, number>;
};

type CoordinatorConfig = {
  flyApp: string;
  flyWorkerImage: string;
  flyApiBaseUrl: string;
  flyApiToken: string;
  regions: Record<SiteId, string>;
  stressRuns: number;
  stressOpsPerClient: number;
  stressBarrierEveryOps: number;
  stressHardBarrierEvery: number;
  stressDrainRounds: number;
  stressDrainQuiescenceRounds: number;
  stressDrainMaxExtraRounds: number;
  stressRowCount: number;
  stressPollIntervalMs: number;
  stressSoftBarrierTimeoutS: number;
  stressHardBarrierTimeoutS: number;
  stressFinalTimeoutS: number;
  stressCommandTimeoutS: number;
  awsEndpointUrlS3: string;
  awsRegion: string;
  awsAccessKeyId: string;
  awsSecretAccessKey: string;
  awsSessionToken?: string;
  s3Prefix: string;
  controlPrefix: string;
  bucketPrefix: string;
  s3ForcePathStyle: boolean;
};

type WorkerInstance = {
  siteId: SiteId;
  region: string;
  machineId: string;
};

class FlyMachinesApiClient {
  constructor(
    private readonly baseUrl: string,
    private readonly token: string,
  ) {}

  async createMachine(appName: string, request: CreateMachineRequest): Promise<FlyMachine> {
    return this.requestJson<FlyMachine>(
      `/apps/${encodeURIComponent(appName)}/machines`,
      'POST',
      request,
    );
  }

  async waitMachineState(
    appName: string,
    machineId: string,
    options: { state: 'started' | 'stopped' | 'suspended' | 'destroyed'; timeoutSeconds: number },
  ): Promise<void> {
    const deadline = Date.now() + options.timeoutSeconds * 1000;
    while (Date.now() < deadline) {
      const remainingSeconds = Math.ceil((deadline - Date.now()) / 1000);
      const waitSeconds = Math.max(1, Math.min(60, remainingSeconds));
      const query = new URLSearchParams({
        state: options.state,
        timeout: String(waitSeconds),
      });
      try {
        await this.requestNoContent(
          `/apps/${encodeURIComponent(appName)}/machines/${encodeURIComponent(machineId)}/wait?${query.toString()}`,
          'GET',
        );
        return;
      } catch (error) {
        const message = String(error);
        if (message.includes('status=408') || message.includes('status=504')) {
          continue;
        }
        throw error;
      }
    }
    throw new Error(`timed out waiting for machine ${machineId} to reach state='${options.state}'`);
  }

  async deleteMachine(appName: string, machineId: string, force: boolean): Promise<void> {
    const query = new URLSearchParams();
    if (force) {
      query.set('force', 'true');
    }
    const suffix = query.size > 0 ? `?${query.toString()}` : '';
    await this.requestNoContent(
      `/apps/${encodeURIComponent(appName)}/machines/${encodeURIComponent(machineId)}${suffix}`,
      'DELETE',
    );
  }

  private async requestJson<T>(path: string, method: 'GET' | 'POST' | 'DELETE', body?: unknown): Promise<T> {
    const response = await fetch(`${this.baseUrl}${path}`, {
      method,
      headers: {
        authorization: `Bearer ${this.token}`,
        'content-type': body ? 'application/json' : 'application/json',
      },
      ...(body ? { body: JSON.stringify(body) } : {}),
    });

    const text = await response.text();
    if (!response.ok) {
      throw new Error(
        `Fly API ${method} ${path} failed status=${response.status} body=${text.slice(0, 400)}`,
      );
    }

    if (text.trim().length === 0) {
      throw new Error(`Fly API ${method} ${path} returned empty JSON body`);
    }

    return JSON.parse(text) as T;
  }

  private async requestNoContent(path: string, method: 'GET' | 'POST' | 'DELETE'): Promise<void> {
    const response = await fetch(`${this.baseUrl}${path}`, {
      method,
      headers: {
        authorization: `Bearer ${this.token}`,
      },
    });
    const text = await response.text();
    if (!response.ok) {
      throw new Error(
        `Fly API ${method} ${path} failed status=${response.status} body=${text.slice(0, 400)}`,
      );
    }
  }
}

function timestampUtc(): string {
  return new Date().toISOString();
}

function log(message: string): void {
  process.stdout.write(`[${timestampUtc()}] ${message}\n`);
}

function readRequiredEnv(name: string): string {
  const value = process.env[name];
  if (!value || value.trim().length === 0) {
    throw new Error(`missing required env ${name}`);
  }
  return value;
}

function parsePositiveIntEnv(name: string, fallback: number): number {
  const raw = process.env[name];
  if (!raw || raw.trim().length === 0) {
    return fallback;
  }
  const value = Number.parseInt(raw, 10);
  if (!Number.isFinite(value) || value <= 0) {
    throw new Error(`invalid ${name}='${raw}' (must be positive integer)`);
  }
  return value;
}

function parseRegions(raw: string | undefined): Record<SiteId, string> {
  const value = (raw ?? 'iad,lhr,syd').trim();
  const parts = value
    .split(',')
    .map((part) => part.trim())
    .filter((part) => part.length > 0);
  if (parts.length !== SITE_IDS.length) {
    throw new Error('FLY_REGIONS must contain exactly three comma-separated regions (e.g. iad,lhr,syd)');
  }
  return {
    'site-a': parts[0]!,
    'site-b': parts[1]!,
    'site-c': parts[2]!,
  };
}

function readConfig(): CoordinatorConfig {
  const stressRuns = parsePositiveIntEnv('STRESS_RUNS', 10);
  const stressOpsPerClient = parsePositiveIntEnv('STRESS_OPS_PER_CLIENT', 30_000);
  const stressBarrierEveryOps = parsePositiveIntEnv('STRESS_BARRIER_EVERY_OPS', 3_000);
  if (stressBarrierEveryOps > stressOpsPerClient) {
    throw new Error('STRESS_BARRIER_EVERY_OPS must be <= STRESS_OPS_PER_CLIENT');
  }

  const flyApiToken = process.env.FLY_API_TOKEN ?? process.env.FLY_ACCESS_TOKEN ?? '';
  if (flyApiToken.trim().length === 0) {
    throw new Error('missing FLY_API_TOKEN (or FLY_ACCESS_TOKEN) for Fly Machines REST API');
  }

  return {
    flyApp: readRequiredEnv('FLY_APP'),
    flyWorkerImage: readRequiredEnv('FLY_WORKER_IMAGE'),
    flyApiBaseUrl: resolveFlyApiBaseUrl(process.env.FLY_API_HOSTNAME),
    flyApiToken,
    regions: parseRegions(process.env.FLY_REGIONS),
    stressRuns,
    stressOpsPerClient,
    stressBarrierEveryOps,
    stressHardBarrierEvery: parsePositiveIntEnv('STRESS_HARD_BARRIER_EVERY', 2),
    stressDrainRounds: parsePositiveIntEnv('STRESS_DRAIN_ROUNDS', 8),
    stressDrainQuiescenceRounds: parsePositiveIntEnv('STRESS_DRAIN_QUIESCENCE_ROUNDS', 2),
    stressDrainMaxExtraRounds: parsePositiveIntEnv('STRESS_DRAIN_MAX_EXTRA_ROUNDS', 40),
    stressRowCount: parsePositiveIntEnv('STRESS_ROW_COUNT', 64),
    stressPollIntervalMs: parsePositiveIntEnv('STRESS_POLL_INTERVAL_MS', 250),
    stressSoftBarrierTimeoutS: parsePositiveIntEnv('STRESS_SOFT_BARRIER_TIMEOUT_S', 30),
    stressHardBarrierTimeoutS: parsePositiveIntEnv('STRESS_HARD_BARRIER_TIMEOUT_S', 90),
    stressFinalTimeoutS: parsePositiveIntEnv('STRESS_FINAL_TIMEOUT_S', 120),
    stressCommandTimeoutS: parsePositiveIntEnv('STRESS_COMMAND_TIMEOUT_S', 180),
    awsEndpointUrlS3: readRequiredEnv('AWS_ENDPOINT_URL_S3'),
    awsRegion: process.env.AWS_REGION?.trim() || 'auto',
    awsAccessKeyId: readRequiredEnv('AWS_ACCESS_KEY_ID'),
    awsSecretAccessKey: readRequiredEnv('AWS_SECRET_ACCESS_KEY'),
    awsSessionToken: process.env.AWS_SESSION_TOKEN,
    s3Prefix: process.env.S3_PREFIX?.trim() || 'deltas',
    controlPrefix: process.env.CONTROL_PREFIX?.trim() || 'control',
    bucketPrefix: process.env.BUCKET_PREFIX?.trim() || 'crdtbase-stress',
    s3ForcePathStyle: (process.env.S3_FORCE_PATH_STYLE ?? '').trim() === 'true',
  };
}

function randomU32(): number {
  return randomBytes(4).readUInt32BE(0);
}

function bodyToString(body: unknown): Promise<string> {
  const value = body as {
    transformToString?: (encoding?: string) => Promise<string>;
    transformToByteArray?: () => Promise<Uint8Array>;
  };
  if (typeof value.transformToString === 'function') {
    return value.transformToString('utf-8');
  }
  if (typeof value.transformToByteArray === 'function') {
    return value.transformToByteArray().then((bytes) => new TextDecoder().decode(bytes));
  }
  throw new Error('unsupported S3 body type');
}

async function createBucket(s3: S3Client, bucket: string): Promise<void> {
  await s3.send(new CreateBucketCommand({ Bucket: bucket }));
}

async function putJsonObject(s3: S3Client, bucket: string, key: string, value: unknown): Promise<void> {
  await s3.send(
    new PutObjectCommand({
      Bucket: bucket,
      Key: key,
      Body: JSON.stringify(value),
      ContentType: 'application/json',
    }),
  );
}

async function getJsonObject<T>(s3: S3Client, bucket: string, key: string): Promise<T | null> {
  try {
    const object = await s3.send(new GetObjectCommand({ Bucket: bucket, Key: key }));
    const text = await bodyToString(object.Body);
    if (text.trim().length === 0) {
      return null;
    }
    return JSON.parse(text) as T;
  } catch (error) {
    const code = (error as { name?: string }).name;
    const status = (error as { $metadata?: { httpStatusCode?: number } }).$metadata?.httpStatusCode;
    if (code === 'NoSuchKey' || status === 404) {
      return null;
    }
    throw error;
  }
}

async function objectExists(s3: S3Client, bucket: string, key: string): Promise<boolean> {
  try {
    await s3.send(new HeadObjectCommand({ Bucket: bucket, Key: key }));
    return true;
  } catch (error) {
    const status = (error as { $metadata?: { httpStatusCode?: number } }).$metadata?.httpStatusCode;
    const code = (error as { name?: string }).name;
    if (status === 404 || code === 'NotFound' || code === 'NoSuchKey') {
      return false;
    }
    throw error;
  }
}

async function waitForObject(params: {
  s3: S3Client;
  bucket: string;
  key: string;
  timeoutSeconds: number;
  pollIntervalMs: number;
}): Promise<boolean> {
  const deadline = Date.now() + params.timeoutSeconds * 1000;
  while (Date.now() <= deadline) {
    if (await objectExists(params.s3, params.bucket, params.key)) {
      return true;
    }
    await sleep(params.pollIntervalMs);
  }
  return false;
}

async function emptyBucket(s3: S3Client, bucket: string): Promise<void> {
  let continuationToken: string | undefined;
  do {
    const listed = await s3.send(
      new ListObjectsV2Command({
        Bucket: bucket,
        ContinuationToken: continuationToken,
      }),
    );
    const objects = (listed.Contents ?? [])
      .map((item) => item.Key)
      .filter((key): key is string => typeof key === 'string' && key.length > 0)
      .map((key) => ({ Key: key }));

    if (objects.length > 0) {
      await s3.send(
        new DeleteObjectsCommand({
          Bucket: bucket,
          Delete: { Objects: objects, Quiet: true },
        }),
      );
    }

    continuationToken = listed.IsTruncated ? listed.NextContinuationToken : undefined;
  } while (continuationToken);
}

async function cleanupBucket(s3: S3Client, bucket: string): Promise<void> {
  log(`Cleaning up bucket '${bucket}'`);
  for (let attempt = 1; attempt <= 8; attempt += 1) {
    try {
      await emptyBucket(s3, bucket);
      await s3.send(new DeleteBucketCommand({ Bucket: bucket }));
      log(`Deleted bucket '${bucket}'`);
      return;
    } catch {
      await sleep(attempt * 2_000);
    }
  }
  log(`WARNING: failed to delete bucket '${bucket}' after retries`);
}

function barrierLabel(index: number): string {
  return String(index).padStart(4, '0');
}

function sanitizeMachineName(raw: string): string {
  const value = raw
    .toLowerCase()
    .replace(/[^a-z0-9-]+/g, '-')
    .replace(/^-+/, '')
    .replace(/-+$/, '');
  return value.slice(0, 63);
}

function buildCommandKey(controlPrefix: string, runId: string, barrierIndex: number, phase: CommandPhase): string {
  return `${controlPrefix}/${runId}/commands/barrier-${barrierLabel(barrierIndex)}/${phase}.json`;
}

function buildReportKey(
  controlPrefix: string,
  runId: string,
  barrierIndex: number,
  phase: BarrierPhase,
  siteId: SiteId,
): string {
  return `${controlPrefix}/${runId}/barrier-${barrierLabel(barrierIndex)}/${phase}/${siteId}.json`;
}

async function launchWorkers(params: {
  fly: FlyMachinesApiClient;
  app: string;
  image: string;
  regions: Record<SiteId, string>;
  runId: string;
  bucket: string;
  seed: number;
  config: CoordinatorConfig;
}): Promise<WorkerInstance[]> {
  const workers: WorkerInstance[] = [];

  for (const siteId of SITE_IDS) {
    const region = params.regions[siteId];
    const machineName = sanitizeMachineName(`stress-${params.runId}-${siteId}`);

    const env: Record<string, string> = {
      RUN_ID: params.runId,
      SITE_ID: siteId,
      SITE_REGION: region,
      BUCKET_NAME: params.bucket,
      S3_PREFIX: params.config.s3Prefix,
      CONTROL_PREFIX: params.config.controlPrefix,
      STRESS_SEED: String(params.seed),
      STRESS_OPS_PER_CLIENT: String(params.config.stressOpsPerClient),
      STRESS_BARRIER_EVERY_OPS: String(params.config.stressBarrierEveryOps),
      STRESS_HARD_BARRIER_EVERY: String(params.config.stressHardBarrierEvery),
      STRESS_DRAIN_ROUNDS: String(params.config.stressDrainRounds),
      STRESS_DRAIN_QUIESCENCE_ROUNDS: String(params.config.stressDrainQuiescenceRounds),
      STRESS_DRAIN_MAX_EXTRA_ROUNDS: String(params.config.stressDrainMaxExtraRounds),
      STRESS_ROW_COUNT: String(params.config.stressRowCount),
      STRESS_POLL_INTERVAL_MS: String(params.config.stressPollIntervalMs),
      STRESS_COMMAND_TIMEOUT_S: String(params.config.stressCommandTimeoutS),
      AWS_ENDPOINT_URL_S3: params.config.awsEndpointUrlS3,
      AWS_REGION: params.config.awsRegion,
      AWS_ACCESS_KEY_ID: params.config.awsAccessKeyId,
      AWS_SECRET_ACCESS_KEY: params.config.awsSecretAccessKey,
    };
    if (params.config.awsSessionToken && params.config.awsSessionToken.length > 0) {
      env.AWS_SESSION_TOKEN = params.config.awsSessionToken;
    }
    if (params.config.s3ForcePathStyle) {
      env.S3_FORCE_PATH_STYLE = 'true';
    }

    const requestBody: CreateMachineRequest = {
      name: machineName,
      region,
      config: {
        image: params.image,
        env,
        metadata: {
          crdtbase_role: 'stress-worker',
          crdtbase_run_id: params.runId,
          crdtbase_site_id: siteId,
        },
        restart: {
          policy: 'no',
        },
        auto_destroy: true,
      },
      skip_service_registration: true,
    };

    log(`Launching worker site=${siteId} region=${region} machine=${machineName}`);
    let machine: FlyMachine | null = null;
    let lastError: unknown = null;
    for (let attempt = 1; attempt <= 3; attempt += 1) {
      try {
        machine = await params.fly.createMachine(params.app, requestBody);
        break;
      } catch (error) {
        lastError = error;
        if (attempt < 3) {
          await sleep(1_000 * attempt);
        }
      }
    }
    if (!machine) {
      throw new Error(
        `failed to launch machine for site=${siteId} after retries: ${String(lastError)}`,
      );
    }

    if (!machine.id) {
      throw new Error(`created machine missing id for site=${siteId}`);
    }

    await params.fly.waitMachineState(params.app, machine.id, {
      state: 'started',
      timeoutSeconds: 120,
    });

    workers.push({
      siteId,
      region,
      machineId: machine.id,
    });
  }

  return workers;
}

async function cleanupRunMachines(
  fly: FlyMachinesApiClient,
  appName: string,
  workers: WorkerInstance[],
): Promise<void> {
  for (const worker of workers) {
    try {
      await fly.deleteMachine(appName, worker.machineId, true);
    } catch {
      // Best-effort cleanup; machine may already be auto-destroyed.
    }
  }
}

function validateInvariants(reports: WorkerBarrierReport[]): void {
  for (const report of reports) {
    if (!report.invariantOk) {
      throw new Error(
        `invariant failure at barrier=${barrierLabel(report.barrierIndex)} phase=${report.phase} site=${report.siteId}: ${JSON.stringify(report.invariantErrors)}`,
      );
    }
  }
}

function validateConvergenceHashes(reports: WorkerBarrierReport[]): void {
  let expected = '';
  for (const report of reports) {
    if (!report.stateHash || report.stateHash.length === 0) {
      throw new Error(
        `missing stateHash at barrier=${barrierLabel(report.barrierIndex)} phase=${report.phase} site=${report.siteId}`,
      );
    }
    if (!expected) {
      expected = report.stateHash;
    } else if (report.stateHash !== expected) {
      throw new Error(
        `convergence hash mismatch at barrier=${barrierLabel(report.barrierIndex)} phase=${report.phase}: ${report.siteId}=${report.stateHash} expected=${expected}`,
      );
    }
  }
}

async function waitForBarrierReports(params: {
  s3: S3Client;
  bucket: string;
  controlPrefix: string;
  runId: string;
  barrierIndex: number;
  phase: BarrierPhase;
  timeoutSeconds: number;
  pollIntervalMs: number;
}): Promise<WorkerBarrierReport[]> {
  const reports: WorkerBarrierReport[] = [];
  for (const siteId of SITE_IDS) {
    const key = buildReportKey(params.controlPrefix, params.runId, params.barrierIndex, params.phase, siteId);
    const found = await waitForObject({
      s3: params.s3,
      bucket: params.bucket,
      key,
      timeoutSeconds: params.timeoutSeconds,
      pollIntervalMs: params.pollIntervalMs,
    });
    if (!found) {
      throw new Error(
        `timed out waiting for ${params.phase} report at barrier=${barrierLabel(params.barrierIndex)} site=${siteId}`,
      );
    }
    const report = await getJsonObject<WorkerBarrierReport>(params.s3, params.bucket, key);
    if (!report) {
      throw new Error(
        `report object missing/invalid at barrier=${barrierLabel(params.barrierIndex)} phase=${params.phase} site=${siteId}`,
      );
    }
    reports.push(report);
  }
  return reports;
}

async function publishBarrierCommand(params: {
  s3: S3Client;
  bucket: string;
  controlPrefix: string;
  runId: string;
  barrierIndex: number;
  phase: CommandPhase;
  command: BarrierCommand;
}): Promise<void> {
  const key = buildCommandKey(params.controlPrefix, params.runId, params.barrierIndex, params.phase);
  await putJsonObject(params.s3, params.bucket, key, params.command);
  log(
    `Published command barrier=${barrierLabel(params.barrierIndex)} phase=${params.phase} action=${params.command.action}`,
  );
}

async function abortBarrier(params: {
  s3: S3Client;
  bucket: string;
  controlPrefix: string;
  runId: string;
  barrierIndex: number;
  reason: string;
}): Promise<void> {
  const issuedAt = timestampUtc();
  const entry: BarrierCommand = {
    action: 'abort',
    phase: 'entry',
    note: params.reason,
    reason: params.reason,
    issuedAt,
  };
  const release: BarrierCommand = {
    action: 'abort',
    phase: 'release',
    note: params.reason,
    reason: params.reason,
    issuedAt,
  };
  await publishBarrierCommand({
    s3: params.s3,
    bucket: params.bucket,
    controlPrefix: params.controlPrefix,
    runId: params.runId,
    barrierIndex: params.barrierIndex,
    phase: 'entry',
    command: entry,
  }).catch(() => undefined);
  await publishBarrierCommand({
    s3: params.s3,
    bucket: params.bucket,
    controlPrefix: params.controlPrefix,
    runId: params.runId,
    barrierIndex: params.barrierIndex,
    phase: 'release',
    command: release,
  }).catch(() => undefined);
}

async function checkFinalReports(params: {
  s3: S3Client;
  bucket: string;
  controlPrefix: string;
  runId: string;
  timeoutSeconds: number;
  pollIntervalMs: number;
}): Promise<void> {
  const reports: WorkerFinalReport[] = [];
  for (const siteId of SITE_IDS) {
    const key = `${params.controlPrefix}/${params.runId}/final/${siteId}.json`;
    const found = await waitForObject({
      s3: params.s3,
      bucket: params.bucket,
      key,
      timeoutSeconds: params.timeoutSeconds,
      pollIntervalMs: params.pollIntervalMs,
    });
    if (!found) {
      throw new Error(`timed out waiting for final report site=${siteId}`);
    }
    const report = await getJsonObject<WorkerFinalReport>(params.s3, params.bucket, key);
    if (!report) {
      throw new Error(`final report missing/invalid for site=${siteId}`);
    }
    reports.push(report);
  }

  let expectedHash = '';
  for (const report of reports) {
    if (!report.success) {
      throw new Error(`worker final report failed site=${report.siteId}: ${report.error ?? 'unknown error'}`);
    }
    if (!report.stateHash) {
      throw new Error(`worker final report missing stateHash site=${report.siteId}`);
    }
    if (!expectedHash) {
      expectedHash = report.stateHash;
    } else if (report.stateHash !== expectedHash) {
      throw new Error(
        `final state hash mismatch site=${report.siteId} hash=${report.stateHash} expected=${expectedHash}`,
      );
    }
  }
}

async function runBarriers(params: {
  s3: S3Client;
  bucket: string;
  controlPrefix: string;
  runId: string;
  barrierCount: number;
  config: CoordinatorConfig;
}): Promise<void> {
  for (let barrier = 1; barrier <= params.barrierCount; barrier += 1) {
    const barrierStartedAt = Date.now();
    const hardBarrier =
      barrier % params.config.stressHardBarrierEvery === 0 || barrier === params.barrierCount;
    const timeoutSeconds = hardBarrier
      ? params.config.stressHardBarrierTimeoutS
      : params.config.stressSoftBarrierTimeoutS;

    log(`Waiting for barrier ${barrierLabel(barrier)} pre reports (hard=${hardBarrier ? 1 : 0})`);
    let preReports: WorkerBarrierReport[];
    try {
      preReports = await waitForBarrierReports({
        s3: params.s3,
        bucket: params.bucket,
        controlPrefix: params.controlPrefix,
        runId: params.runId,
        barrierIndex: barrier,
        phase: 'pre',
        timeoutSeconds,
        pollIntervalMs: params.config.stressPollIntervalMs,
      });
    } catch (error) {
      await abortBarrier({
        s3: params.s3,
        bucket: params.bucket,
        controlPrefix: params.controlPrefix,
        runId: params.runId,
        barrierIndex: barrier,
        reason: String(error),
      });
      throw error;
    }

    log(
      `Barrier ${barrierLabel(barrier)} pre reports complete in ${Math.round((Date.now() - barrierStartedAt) / 1000)}s`,
    );

    try {
      validateInvariants(preReports);
      validatePreBarrierSyncState(preReports);
    } catch (error) {
      await abortBarrier({
        s3: params.s3,
        bucket: params.bucket,
        controlPrefix: params.controlPrefix,
        runId: params.runId,
        barrierIndex: barrier,
        reason: String(error),
      });
      throw error;
    }

    if (hardBarrier) {
      const targetHeads = computeTargetHeadsFromPreReports(preReports);
      log(`Hard barrier ${barrierLabel(barrier)}: target_heads=${JSON.stringify(targetHeads)}`);

      await publishBarrierCommand({
        s3: params.s3,
        bucket: params.bucket,
        controlPrefix: params.controlPrefix,
        runId: params.runId,
        barrierIndex: barrier,
        phase: 'entry',
        command: {
          action: 'drain',
          phase: 'entry',
          note: 'hard barrier drain rounds',
          issuedAt: timestampUtc(),
          drainRounds: params.config.stressDrainRounds,
          targetHeads,
        },
      });

      const drainedWaitStarted = Date.now();
      let drainedReports: WorkerBarrierReport[];
      try {
        drainedReports = await waitForBarrierReports({
          s3: params.s3,
          bucket: params.bucket,
          controlPrefix: params.controlPrefix,
          runId: params.runId,
          barrierIndex: barrier,
          phase: 'drained',
          timeoutSeconds: params.config.stressHardBarrierTimeoutS,
          pollIntervalMs: params.config.stressPollIntervalMs,
        });
      } catch (error) {
        await abortBarrier({
          s3: params.s3,
          bucket: params.bucket,
          controlPrefix: params.controlPrefix,
          runId: params.runId,
          barrierIndex: barrier,
          reason: String(error),
        });
        throw error;
      }

      log(
        `Barrier ${barrierLabel(barrier)} drained reports complete in ${Math.round((Date.now() - drainedWaitStarted) / 1000)}s`,
      );

      try {
        validateInvariants(drainedReports);
        validateConvergenceHashes(drainedReports);
      } catch (error) {
        await abortBarrier({
          s3: params.s3,
          bucket: params.bucket,
          controlPrefix: params.controlPrefix,
          runId: params.runId,
          barrierIndex: barrier,
          reason: String(error),
        });
        throw error;
      }

      await publishBarrierCommand({
        s3: params.s3,
        bucket: params.bucket,
        controlPrefix: params.controlPrefix,
        runId: params.runId,
        barrierIndex: barrier,
        phase: 'release',
        command: {
          action: 'continue',
          phase: 'release',
          note: 'drain validated; continue',
          issuedAt: timestampUtc(),
        },
      });
    } else {
      await publishBarrierCommand({
        s3: params.s3,
        bucket: params.bucket,
        controlPrefix: params.controlPrefix,
        runId: params.runId,
        barrierIndex: barrier,
        phase: 'entry',
        command: {
          action: 'continue',
          phase: 'entry',
          note: 'soft barrier validated; continue',
          issuedAt: timestampUtc(),
        },
      });
    }

    log(
      `Barrier ${barrierLabel(barrier)} completed in ${Math.round((Date.now() - barrierStartedAt) / 1000)}s`,
    );
  }
}

async function runOnce(params: {
  index: number;
  config: CoordinatorConfig;
  s3: S3Client;
  fly: FlyMachinesApiClient;
}): Promise<void> {
  const runSeed = randomU32();
  const runId = `run-${new Date().toISOString().replace(/[-:.TZ]/g, '').slice(0, 14)}-${params.index}-${runSeed}`;
  const bucket = sanitizeBucketName(`${params.config.bucketPrefix}-${runId}`);
  const barrierCount = Math.ceil(params.config.stressOpsPerClient / params.config.stressBarrierEveryOps);

  log(`Run ${params.index}/${params.config.stressRuns}: seed=${runSeed} run_id=${runId} bucket=${bucket}`);
  await createBucket(params.s3, bucket);

  let workers: WorkerInstance[] = [];
  try {
    workers = await launchWorkers({
      fly: params.fly,
      app: params.config.flyApp,
      image: params.config.flyWorkerImage,
      regions: params.config.regions,
      runId,
      bucket,
      seed: runSeed,
      config: params.config,
    });

    log(`Workers launched for run_id=${runId}; waiting for ${barrierCount} barriers`);
    await runBarriers({
      s3: params.s3,
      bucket,
      controlPrefix: params.config.controlPrefix,
      runId,
      barrierCount,
      config: params.config,
    });

    await checkFinalReports({
      s3: params.s3,
      bucket,
      controlPrefix: params.config.controlPrefix,
      runId,
      timeoutSeconds: params.config.stressFinalTimeoutS,
      pollIntervalMs: params.config.stressPollIntervalMs,
    });

    log(`Run ${runId} passed all barriers and final checks`);
  } finally {
    await cleanupRunMachines(params.fly, params.config.flyApp, workers);
    await cleanupBucket(params.s3, bucket);
  }
}

async function main(): Promise<void> {
  const config = readConfig();
  const s3Config: S3ClientConfig = {
    endpoint: config.awsEndpointUrlS3,
    region: config.awsRegion,
    forcePathStyle: config.s3ForcePathStyle,
    credentials: {
      accessKeyId: config.awsAccessKeyId,
      secretAccessKey: config.awsSecretAccessKey,
      ...(config.awsSessionToken ? { sessionToken: config.awsSessionToken } : {}),
    },
  };

  const s3 = new S3Client(s3Config);
  const fly = new FlyMachinesApiClient(config.flyApiBaseUrl, config.flyApiToken);

  log('Starting Fly multi-region stress coordinator (TypeScript REST mode)');
  log(`App=${config.flyApp} image=${config.flyWorkerImage} regions=${Object.values(config.regions).join(',')} runs=${config.stressRuns}`);
  log(
    `Barrier defaults: soft_timeout=${config.stressSoftBarrierTimeoutS}s hard_timeout=${config.stressHardBarrierTimeoutS}s drain_rounds=${config.stressDrainRounds} quiescence=${config.stressDrainQuiescenceRounds} max_extra=${config.stressDrainMaxExtraRounds}`,
  );

  try {
    for (let runIndex = 1; runIndex <= config.stressRuns; runIndex += 1) {
      await runOnce({
        index: runIndex,
        config,
        s3,
        fly,
      });
    }
    log(`All ${config.stressRuns} runs completed successfully`);
  } finally {
    s3.destroy();
  }
}

main().catch((error) => {
  const message = error instanceof Error ? `${error.message}\n${error.stack ?? ''}` : String(error);
  process.stderr.write(`${message}\n`);
  process.exitCode = 1;
});
