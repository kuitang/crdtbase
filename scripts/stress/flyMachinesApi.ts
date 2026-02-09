import { execFile as execFileWithCallback } from 'node:child_process';
import { promisify } from 'node:util';
import type { components } from './fly-machines-openapi';

type FlyMachine = components['schemas']['Machine'];
type CreateMachineRequest = components['schemas']['CreateMachineRequest'];
type HttpMethod = 'GET' | 'POST' | 'DELETE';

const execFile = promisify(execFileWithCallback);

type ExecFileResult = {
  stdout: string;
  stderr: string;
};

type ExecFileFn = (
  file: string,
  args: readonly string[],
  options?: {
    encoding?: BufferEncoding;
  },
) => Promise<ExecFileResult>;

const defaultExecFile: ExecFileFn = async (file, args, options) => {
  const result = await execFile(file, [...args], options);
  return {
    stdout: result.stdout,
    stderr: result.stderr,
  };
};

export type FlyTokenProvider = {
  getToken(forceRefresh?: boolean): Promise<string>;
};

export type FlyCommandTokenProviderOptions = {
  initialToken?: string;
  refreshCommand?: string;
  log?: (message: string) => void;
  execFile?: ExecFileFn;
};

function splitCommand(command: string): { file: string; args: string[] } {
  const parts = command
    .split(/\s+/)
    .map((part) => part.trim())
    .filter((part) => part.length > 0);
  if (parts.length === 0) {
    throw new Error('empty command');
  }
  return {
    file: parts[0]!,
    args: parts.slice(1),
  };
}

export class FlyCommandTokenProvider implements FlyTokenProvider {
  private cachedToken: string;
  private readonly refreshCommand: string;
  private readonly log: ((message: string) => void) | undefined;
  private readonly execFile: ExecFileFn;

  constructor(options: FlyCommandTokenProviderOptions) {
    this.cachedToken = options.initialToken?.trim() ?? '';
    this.refreshCommand = options.refreshCommand?.trim() ?? '';
    this.log = options.log;
    this.execFile = options.execFile ?? defaultExecFile;
  }

  async getToken(forceRefresh = false): Promise<string> {
    if (!forceRefresh && this.cachedToken.length > 0) {
      return this.cachedToken;
    }

    if (this.refreshCommand.length === 0) {
      if (this.cachedToken.length > 0) {
        return this.cachedToken;
      }
      throw new Error(
        'missing Fly API token: set FLY_API_TOKEN/FLY_ACCESS_TOKEN or provide FLY_API_TOKEN_COMMAND',
      );
    }

    const { file, args } = splitCommand(this.refreshCommand);
    let stdout = '';
    let stderr = '';
    try {
      const result = await this.execFile(file, args, { encoding: 'utf8' });
      stdout = result.stdout;
      stderr = result.stderr;
    } catch (error) {
      const value = error as { message?: string; stderr?: string; stdout?: string };
      const details = [value.stderr ?? '', value.stdout ?? '']
        .map((part) => part.trim())
        .filter((part) => part.length > 0)
        .join(' | ');
      throw new Error(
        `failed to refresh Fly API token via '${this.refreshCommand}': ${value.message ?? String(error)}${details ? ` (${details.slice(0, 300)})` : ''}`,
      );
    }

    const token = stdout.trim();
    if (token.length === 0) {
      throw new Error(
        `token refresh command '${this.refreshCommand}' returned empty token${stderr.trim() ? ` (${stderr.trim().slice(0, 300)})` : ''}`,
      );
    }

    this.cachedToken = token;
    this.log?.(`Refreshed Fly API token via command '${this.refreshCommand}'`);
    return this.cachedToken;
  }
}

export class FlyMachinesApiClient {
  constructor(
    private readonly baseUrl: string,
    private readonly tokenProvider: FlyTokenProvider,
    private readonly fetchFn: typeof fetch = fetch,
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

  private async requestJson<T>(path: string, method: HttpMethod, body?: unknown): Promise<T> {
    const result = await this.requestWithRefreshRetry(path, method, body);
    if (!result.response.ok) {
      throw this.buildHttpError(method, path, result.response.status, result.text);
    }

    if (result.text.trim().length === 0) {
      throw new Error(`Fly API ${method} ${path} returned empty JSON body`);
    }

    return JSON.parse(result.text) as T;
  }

  private async requestNoContent(path: string, method: HttpMethod): Promise<void> {
    const result = await this.requestWithRefreshRetry(path, method);
    if (!result.response.ok) {
      throw this.buildHttpError(method, path, result.response.status, result.text);
    }
  }

  private buildHttpError(method: HttpMethod, path: string, status: number, body: string): Error {
    return new Error(
      `Fly API ${method} ${path} failed status=${status} body=${body.slice(0, 400)}`,
    );
  }

  private async requestWithRefreshRetry(
    path: string,
    method: HttpMethod,
    body?: unknown,
  ): Promise<{ response: Response; text: string }> {
    let refreshed = false;
    while (true) {
      const token = await this.tokenProvider.getToken(refreshed);
      const headers: Record<string, string> = {
        authorization: `Bearer ${token}`,
      };
      if (typeof body !== 'undefined') {
        headers['content-type'] = 'application/json';
      }

      const response = await this.fetchFn(`${this.baseUrl}${path}`, {
        method,
        headers,
        ...(typeof body !== 'undefined' ? { body: JSON.stringify(body) } : {}),
      });
      const text = await response.text();

      if (!refreshed && (response.status === 401 || response.status === 403)) {
        refreshed = true;
        continue;
      }

      return { response, text };
    }
  }
}

export type { FlyMachine, CreateMachineRequest };
