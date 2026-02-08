import { createServer, IncomingMessage, Server, ServerResponse } from 'node:http';
import { mkdir, readdir, readFile, rm, stat, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { AddressInfo } from 'node:net';
import { decodeBin, encodeBin } from '../core/encoding';
import { AppendLogEntry, LogEntry, LogPosition } from '../core/replication';

type JsonRecord = Record<string, unknown>;

function writeJson(response: ServerResponse, statusCode: number, body: JsonRecord): void {
  response.statusCode = statusCode;
  response.setHeader('content-type', 'application/json');
  response.end(JSON.stringify(body));
}

function writeError(response: ServerResponse, statusCode: number, message: string): void {
  writeJson(response, statusCode, { error: message });
}

async function readJsonBody<T>(request: IncomingMessage): Promise<T> {
  const chunks: Buffer[] = [];
  for await (const chunk of request) {
    chunks.push(Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk));
  }
  if (chunks.length === 0) {
    throw new Error('request body is required');
  }
  const raw = Buffer.concat(chunks).toString('utf8');
  return JSON.parse(raw) as T;
}

function parseSince(raw: string | null): number {
  if (raw === null) {
    return 0;
  }
  const value = Number(raw);
  if (!Number.isInteger(value) || value < 0) {
    throw new Error(`invalid 'since' value '${raw}'`);
  }
  return value;
}

function splitPath(pathname: string): string[] {
  return pathname
    .split('/')
    .filter((part) => part.length > 0)
    .map((part) => decodeURIComponent(part));
}

function parseSeqFromFilename(filename: string): number | null {
  if (!filename.endsWith('.bin')) {
    return null;
  }
  const raw = filename.slice(0, -4);
  const seq = Number(raw);
  return Number.isInteger(seq) && seq > 0 ? seq : null;
}

function formatSeqFilename(seq: number): string {
  return `${String(seq).padStart(10, '0')}.bin`;
}

export class FileReplicatedLogServer {
  private server: Server | null = null;
  private baseUrl: string | null = null;
  private readonly logsDir: string;

  constructor(private readonly rootDir: string) {
    this.logsDir = join(rootDir, 'logs');
  }

  async start(port = 0, host = '127.0.0.1'): Promise<string> {
    if (this.server) {
      throw new Error('file log server already started');
    }

    await rm(this.rootDir, { recursive: true, force: true });
    await mkdir(this.logsDir, { recursive: true });

    const server = createServer((request, response) => {
      void this.handleRequest(request, response);
    });

    await new Promise<void>((resolve, reject) => {
      const onListening = () => {
        server.off('error', onError);
        resolve();
      };
      const onError = (error: Error) => {
        server.off('listening', onListening);
        reject(error);
      };
      server.once('listening', onListening);
      server.once('error', onError);
      server.listen(port, host);
    });

    const address = server.address();
    if (!address || typeof address === 'string') {
      throw new Error('file log server failed to bind to TCP address');
    }

    this.server = server;
    this.baseUrl = `http://${host}:${(address as AddressInfo).port}`;
    return this.baseUrl;
  }

  get url(): string {
    if (!this.baseUrl) {
      throw new Error('file log server is not started');
    }
    return this.baseUrl;
  }

  async stop(): Promise<void> {
    if (!this.server) {
      return;
    }
    const activeServer = this.server;
    this.server = null;
    this.baseUrl = null;
    await new Promise<void>((resolve, reject) => {
      activeServer.close((error) => {
        if (error) {
          reject(error);
          return;
        }
        resolve();
      });
    });
  }

  private async handleRequest(
    request: IncomingMessage,
    response: ServerResponse,
  ): Promise<void> {
    try {
      const method = request.method ?? 'GET';
      const url = new URL(request.url ?? '/', 'http://file-log.local');
      const parts = splitPath(url.pathname);

      if (method === 'GET' && parts.length === 1 && parts[0] === 'logs') {
        const sites = await this.listSitesFromDisk();
        writeJson(response, 200, { sites });
        return;
      }

      if (parts[0] !== 'logs') {
        writeError(response, 404, 'not found');
        return;
      }

      if (parts.length === 2 && method === 'POST') {
        await this.handleAppend(parts[1]!, request, response);
        return;
      }

      if (parts.length === 2 && method === 'GET') {
        await this.handleReadSince(parts[1]!, url, response);
        return;
      }

      if (parts.length === 3 && parts[2] === 'head' && method === 'GET') {
        await this.handleHead(parts[1]!, response);
        return;
      }

      writeError(response, 404, 'not found');
    } catch (error) {
      const message =
        error instanceof Error ? error.message : `unexpected error: ${String(error)}`;
      writeError(response, 400, message);
    }
  }

  private async handleAppend(
    siteIdFromPath: string,
    request: IncomingMessage,
    response: ServerResponse,
  ): Promise<void> {
    const payload = await readJsonBody<AppendLogEntry>(request);
    if (!Array.isArray(payload.ops)) {
      throw new Error('append body must include ops[]');
    }
    if (typeof payload.hlc !== 'string') {
      throw new Error('append body must include hlc string');
    }
    if (payload.siteId !== siteIdFromPath) {
      throw new Error('append siteId must match path siteId');
    }

    const seq = (await this.readHeadFromDisk(siteIdFromPath)) + 1;
    const entry: LogEntry = {
      siteId: siteIdFromPath,
      hlc: payload.hlc,
      seq,
      ops: payload.ops,
    };

    const siteDir = this.siteDir(siteIdFromPath);
    await mkdir(siteDir, { recursive: true });
    await writeFile(join(siteDir, formatSeqFilename(seq)), encodeBin(entry));
    writeJson(response, 200, { seq });
  }

  private async handleReadSince(siteId: string, url: URL, response: ServerResponse): Promise<void> {
    const since = parseSince(url.searchParams.get('since'));
    const entries = await this.readEntriesFromDisk(siteId, since);
    writeJson(response, 200, { entries });
  }

  private async handleHead(siteId: string, response: ServerResponse): Promise<void> {
    const seq: LogPosition = await this.readHeadFromDisk(siteId);
    writeJson(response, 200, { seq });
  }

  private siteDir(siteId: string): string {
    return join(this.logsDir, siteId);
  }

  private async readHeadFromDisk(siteId: string): Promise<LogPosition> {
    const siteDir = this.siteDir(siteId);
    let files: string[] = [];
    try {
      files = await readdir(siteDir);
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code === 'ENOENT') {
        return 0;
      }
      throw error;
    }
    let maxSeq = 0;
    for (const file of files) {
      const seq = parseSeqFromFilename(file);
      if (seq !== null && seq > maxSeq) {
        maxSeq = seq;
      }
    }
    return maxSeq;
  }

  private async readEntriesFromDisk(siteId: string, since: number): Promise<LogEntry[]> {
    const siteDir = this.siteDir(siteId);
    let files: string[] = [];
    try {
      files = await readdir(siteDir);
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code === 'ENOENT') {
        return [];
      }
      throw error;
    }

    const seqs = files
      .map((file) => parseSeqFromFilename(file))
      .filter((seq): seq is number => seq !== null && seq > since)
      .sort((a, b) => a - b);

    const entries: LogEntry[] = [];
    for (const seq of seqs) {
      const bytes = await readFile(join(siteDir, formatSeqFilename(seq)));
      entries.push(decodeBin<LogEntry>(bytes));
    }
    return entries;
  }

  private async listSitesFromDisk(): Promise<string[]> {
    let entries: string[] = [];
    try {
      entries = await readdir(this.logsDir);
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code === 'ENOENT') {
        return [];
      }
      throw error;
    }

    const sites: string[] = [];
    for (const entry of entries) {
      const path = this.siteDir(entry);
      try {
        const info = await stat(path);
        if (info.isDirectory()) {
          sites.push(entry);
        }
      } catch (error) {
        if ((error as NodeJS.ErrnoException).code !== 'ENOENT') {
          throw error;
        }
      }
    }
    return sites.sort();
  }
}
