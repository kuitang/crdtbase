import { ChildProcessWithoutNullStreams, spawn } from 'node:child_process';
import { createServer } from 'node:net';
import { join } from 'node:path';
import { setTimeout as sleep } from 'node:timers/promises';

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

async function waitForHealth(baseUrl: string): Promise<void> {
  const deadline = Date.now() + 30_000;
  while (Date.now() < deadline) {
    try {
      const response = await fetch(`${baseUrl}/health`);
      if (response.ok) {
        return;
      }
    } catch {
      // retry
    }
    await sleep(250);
  }
  throw new Error(`presign server did not become healthy at ${baseUrl}/health`);
}

export type PresignHarnessOptions = {
  endpoint: string;
  region?: string;
  accessKeyId?: string;
  secretAccessKey?: string;
  forcePathStyle?: boolean;
  host?: string;
  port?: number;
  authToken?: string;
};

export class PresignHarness {
  private process: ChildProcessWithoutNullStreams | null = null;

  private constructor(
    private readonly baseUrl: string,
    process: ChildProcessWithoutNullStreams,
  ) {
    this.process = process;
  }

  static async start(options: PresignHarnessOptions): Promise<PresignHarness> {
    const host = options.host ?? '127.0.0.1';
    const port = options.port ?? (await pickFreePort());
    const baseUrl = `http://${host}:${port}`;
    const tsxPath = join(process.cwd(), 'node_modules', 'tsx', 'dist', 'cli.mjs');

    const args = [
      tsxPath,
      'src/backend/s3PresignServer.ts',
      '--host',
      host,
      '--port',
      String(port),
      '--endpoint',
      options.endpoint,
      '--region',
      options.region ?? 'us-east-1',
      '--force-path-style',
      String(options.forcePathStyle ?? true),
      '--access-key-id',
      options.accessKeyId ?? 'minioadmin',
      '--secret-access-key',
      options.secretAccessKey ?? 'minioadmin',
    ];
    if (options.authToken) {
      args.push('--auth-token', options.authToken);
    }

    const child = spawn(process.execPath, args, {
      env: { ...globalThis.process.env },
      stdio: ['ignore', 'pipe', 'pipe'],
    });

    let stderrBuffer = '';
    child.stderr.on('data', (chunk) => {
      stderrBuffer += chunk.toString();
    });

    try {
      await waitForHealth(baseUrl);
    } catch (error) {
      child.kill('SIGTERM');
      throw new Error(
        `failed to start presign server: ${error instanceof Error ? error.message : String(error)}\n${stderrBuffer}`,
      );
    }

    return new PresignHarness(baseUrl, child);
  }

  getBaseUrl(): string {
    return this.baseUrl;
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
}
