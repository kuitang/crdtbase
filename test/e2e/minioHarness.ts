import { ChildProcessWithoutNullStreams, spawn } from 'node:child_process';
import { access, chmod, mkdir, rm, stat, writeFile } from 'node:fs/promises';
import { createServer } from 'node:net';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { setTimeout as sleep } from 'node:timers/promises';
import { CreateBucketCommand, S3Client } from '@aws-sdk/client-s3';

const MINIO_ROOT_USER = 'minioadmin';
const MINIO_ROOT_PASSWORD = 'minioadmin';
const MINIO_REGION = 'us-east-1';

function resolveMinioDownloadUrl(): string {
  switch (process.arch) {
    case 'x64':
      return 'https://dl.min.io/server/minio/release/linux-amd64/minio';
    case 'arm64':
      return 'https://dl.min.io/server/minio/release/linux-arm64/minio';
    default:
      throw new Error(`unsupported architecture for MinIO binary download: ${process.arch}`);
  }
}

async function ensureExecutable(path: string): Promise<void> {
  await chmod(path, 0o755);
  await access(path);
}

async function downloadMinioBinary(path: string): Promise<void> {
  const response = await fetch(resolveMinioDownloadUrl());
  if (!response.ok) {
    throw new Error(`failed to download MinIO binary: ${response.status} ${response.statusText}`);
  }
  const bytes = new Uint8Array(await response.arrayBuffer());
  await writeFile(path, bytes);
  await ensureExecutable(path);
}

async function ensureMinioBinary(cacheDir: string): Promise<string> {
  await mkdir(cacheDir, { recursive: true });
  const binaryPath = join(cacheDir, 'minio');
  try {
    await stat(binaryPath);
    await ensureExecutable(binaryPath);
    return binaryPath;
  } catch (error) {
    if ((error as { code?: string }).code !== 'ENOENT') {
      throw error;
    }
  }
  await downloadMinioBinary(binaryPath);
  return binaryPath;
}

async function pickFreePort(): Promise<number> {
  return new Promise<number>((resolve, reject) => {
    const server = createServer();
    server.once('error', reject);
    server.listen(0, '127.0.0.1', () => {
      const address = server.address();
      if (!address || typeof address === 'string') {
        server.close();
        reject(new Error('failed to allocate local port'));
        return;
      }
      const port = address.port;
      server.close((error) => {
        if (error) {
          reject(error);
          return;
        }
        resolve(port);
      });
    });
  });
}

async function waitForMinioReady(endpoint: string): Promise<void> {
  const readyUrl = `${endpoint}/minio/health/ready`;
  const deadline = Date.now() + 30_000;
  while (Date.now() < deadline) {
    try {
      const response = await fetch(readyUrl);
      if (response.ok) {
        return;
      }
    } catch {
      // retry
    }
    await sleep(300);
  }
  throw new Error(`MinIO did not become ready at ${readyUrl}`);
}

export type MinioHarnessOptions = {
  rootDir: string;
  bucket: string;
};

export class MinioHarness {
  private process: ChildProcessWithoutNullStreams | null = null;
  private readonly endpoint: string;
  private readonly bucket: string;
  private readonly binaryPath: string;
  private readonly dataDir: string;

  private constructor(params: {
    endpoint: string;
    bucket: string;
    binaryPath: string;
    dataDir: string;
    process: ChildProcessWithoutNullStreams;
  }) {
    this.endpoint = params.endpoint;
    this.bucket = params.bucket;
    this.binaryPath = params.binaryPath;
    this.dataDir = params.dataDir;
    this.process = params.process;
  }

  static async start(options: MinioHarnessOptions): Promise<MinioHarness> {
    const cacheDir = join(tmpdir(), 'crdtbase-minio-bin');
    const dataDir = join(options.rootDir, 'minio-data');
    await rm(dataDir, { recursive: true, force: true });
    await mkdir(dataDir, { recursive: true });

    const binaryPath = await ensureMinioBinary(cacheDir);
    const apiPort = await pickFreePort();
    const consolePort = await pickFreePort();
    const endpoint = `http://127.0.0.1:${apiPort}`;

    const child = spawn(
      binaryPath,
      [
        'server',
        dataDir,
        '--address',
        `127.0.0.1:${apiPort}`,
        '--console-address',
        `127.0.0.1:${consolePort}`,
      ],
      {
        env: {
          ...globalThis.process.env,
          MINIO_ROOT_USER: MINIO_ROOT_USER,
          MINIO_ROOT_PASSWORD: MINIO_ROOT_PASSWORD,
          MINIO_REGION_NAME: MINIO_REGION,
        },
        stdio: ['ignore', 'pipe', 'pipe'],
      },
    );

    let stderrBuffer = '';
    child.stderr.on('data', (chunk) => {
      stderrBuffer += chunk.toString();
    });

    child.on('exit', (code) => {
      if (code !== 0) {
        // keep buffered logs for test failure context
        // eslint-disable-next-line no-console
        console.error(`MinIO exited with code ${code}\n${stderrBuffer}`);
      }
    });

    try {
      await waitForMinioReady(endpoint);
      const s3 = new S3Client({
        endpoint,
        region: MINIO_REGION,
        forcePathStyle: true,
        credentials: {
          accessKeyId: MINIO_ROOT_USER,
          secretAccessKey: MINIO_ROOT_PASSWORD,
        },
      });
      await s3.send(new CreateBucketCommand({ Bucket: options.bucket }));
      return new MinioHarness({
        endpoint,
        bucket: options.bucket,
        binaryPath,
        dataDir,
        process: child,
      });
    } catch (error) {
      child.kill('SIGTERM');
      throw error;
    }
  }

  getEndpoint(): string {
    return this.endpoint;
  }

  getBucket(): string {
    return this.bucket;
  }

  getS3ClientConfig(): {
    endpoint: string;
    region: string;
    forcePathStyle: true;
    credentials: { accessKeyId: string; secretAccessKey: string };
  } {
    return {
      endpoint: this.endpoint,
      region: MINIO_REGION,
      forcePathStyle: true,
      credentials: {
        accessKeyId: MINIO_ROOT_USER,
        secretAccessKey: MINIO_ROOT_PASSWORD,
      },
    };
  }

  async stop(): Promise<void> {
    if (!this.process) {
      return;
    }
    const active = this.process;
    this.process = null;
    await new Promise<void>((resolve) => {
      active.once('exit', () => resolve());
      active.kill('SIGTERM');
      setTimeout(() => {
        if (!active.killed) {
          active.kill('SIGKILL');
        }
      }, 2_000);
    });
  }

  // Exposed for debugging / assertions in tests.
  getDebugInfo(): { binaryPath: string; dataDir: string } {
    return { binaryPath: this.binaryPath, dataDir: this.dataDir };
  }
}
