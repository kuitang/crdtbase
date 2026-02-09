import { decodeBin, encodeBin } from '../../core/encoding';
import { AppendLogEntry, LogEntry, LogPosition, ReplicatedLog } from '../../core/replication';

type HttpMethod = 'GET' | 'PUT';

export type SignedRequest = {
  method: HttpMethod;
  url: string;
  headers?: Record<string, string>;
};

export type PresignListObjectsInput = {
  bucket: string;
  prefix: string;
  continuationToken?: string;
  delimiter?: string;
};

export type PresignGetObjectInput = {
  bucket: string;
  key: string;
};

export type PresignPutObjectInput = {
  bucket: string;
  key: string;
  ifNoneMatch?: string;
  contentType?: string;
};

export interface S3PresignProvider {
  signListObjects(input: PresignListObjectsInput): Promise<SignedRequest>;
  signGetObject(input: PresignGetObjectInput): Promise<SignedRequest>;
  signPutObject(input: PresignPutObjectInput): Promise<SignedRequest>;
}

export type HttpS3PresignProviderOptions = {
  baseUrl: string;
  authToken?: string;
};

type SignedRequestResponse = {
  method: HttpMethod;
  url: string;
  headers?: Record<string, string>;
};

function normalizeBaseUrl(baseUrl: string): string {
  return baseUrl.replace(/\/+$/u, '');
}

async function readJsonResponse<T>(response: Response): Promise<T> {
  const raw = await response.text();
  let body: unknown = null;
  if (raw.length > 0) {
    try {
      body = JSON.parse(raw);
    } catch {
      throw new Error(`expected JSON response, got: ${raw}`);
    }
  }

  if (!response.ok) {
    const message =
      body && typeof body === 'object' && 'error' in body
        ? String((body as Record<string, unknown>).error)
        : `${response.status} ${response.statusText}`;
    throw new Error(`presign request failed: ${message}`);
  }

  return body as T;
}

function normalizeSignedRequest(value: SignedRequestResponse): SignedRequest {
  if (value.method !== 'GET' && value.method !== 'PUT') {
    throw new Error(`unsupported signed method '${String(value.method)}'`);
  }
  if (typeof value.url !== 'string' || value.url.length === 0) {
    throw new Error('signed request must contain non-empty url');
  }
  const headers: Record<string, string> = {};
  if (value.headers) {
    for (const [key, headerValue] of Object.entries(value.headers)) {
      headers[key] = String(headerValue);
    }
  }

  return {
    method: value.method,
    url: value.url,
    headers,
  };
}

export class HttpS3PresignProvider implements S3PresignProvider {
  private readonly baseUrl: string;
  private readonly authToken: string | null;

  constructor(options: HttpS3PresignProviderOptions) {
    this.baseUrl = normalizeBaseUrl(options.baseUrl);
    this.authToken = options.authToken ?? null;
  }

  async signListObjects(input: PresignListObjectsInput): Promise<SignedRequest> {
    return this.post('list-objects', input);
  }

  async signGetObject(input: PresignGetObjectInput): Promise<SignedRequest> {
    return this.post('get-object', input);
  }

  async signPutObject(input: PresignPutObjectInput): Promise<SignedRequest> {
    return this.post('put-object', input);
  }

  private async post(path: string, payload: unknown): Promise<SignedRequest> {
    const headers: Record<string, string> = {
      'content-type': 'application/json',
    };
    if (this.authToken) {
      headers.authorization = `Bearer ${this.authToken}`;
    }

    const response = await fetch(`${this.baseUrl}/v1/presign/${path}`, {
      method: 'POST',
      headers,
      body: JSON.stringify(payload),
    });
    const body = await readJsonResponse<SignedRequestResponse>(response);
    return normalizeSignedRequest(body);
  }
}

function trimSlashes(value: string): string {
  return value.replace(/^\/+|\/+$/gu, '');
}

function ensureTrailingSlash(value: string): string {
  return value.endsWith('/') ? value : `${value}/`;
}

function parseSeqFromFilename(filename: string): number | null {
  if (!filename.endsWith('.delta.bin') && !filename.endsWith('.bin')) {
    return null;
  }
  const raw = filename.endsWith('.delta.bin')
    ? filename.slice(0, -10)
    : filename.slice(0, -4);
  const seq = Number(raw);
  if (!Number.isInteger(seq) || seq <= 0) {
    return null;
  }
  return seq;
}

function parseSeqFromObjectKey(prefix: string, key: string): number | null {
  if (!key.startsWith(prefix)) {
    return null;
  }
  const suffix = key.slice(prefix.length);
  return parseSeqFromFilename(suffix);
}

function keyForSeq(seq: number): string {
  return `${String(seq).padStart(10, '0')}.delta.bin`;
}

function decodeXmlEntities(value: string): string {
  return value
    .replaceAll('&amp;', '&')
    .replaceAll('&lt;', '<')
    .replaceAll('&gt;', '>')
    .replaceAll('&quot;', '"')
    .replaceAll('&apos;', "'");
}

function extractTagValues(xml: string, tag: string): string[] {
  const pattern = new RegExp(`<${tag}>([\\s\\S]*?)</${tag}>`, 'gu');
  const values: string[] = [];
  let match: RegExpExecArray | null;
  while ((match = pattern.exec(xml)) !== null) {
    values.push(decodeXmlEntities(match[1]!));
  }
  return values;
}

function extractSingleTag(xml: string, tag: string): string | null {
  const values = extractTagValues(xml, tag);
  return values.length > 0 ? values[0]! : null;
}

function parseIsTruncated(xml: string): boolean {
  const value = extractSingleTag(xml, 'IsTruncated');
  return value?.trim().toLowerCase() === 'true';
}

type ParsedListObjectsXml = {
  keys: string[];
  prefixes: string[];
  nextToken: string | null;
  isTruncated: boolean;
};

function parseListObjectsXml(xml: string): ParsedListObjectsXml {
  return {
    keys: extractTagValues(xml, 'Key'),
    prefixes: extractTagValues(xml, 'Prefix'),
    nextToken: extractSingleTag(xml, 'NextContinuationToken'),
    isTruncated: parseIsTruncated(xml),
  };
}

async function sendSignedRequest(params: {
  signed: SignedRequest;
  expectedMethod: HttpMethod;
  body?: Uint8Array;
}): Promise<Response> {
  if (params.signed.method !== params.expectedMethod) {
    throw new Error(
      `signed request expected method ${params.expectedMethod}, got ${params.signed.method}`,
    );
  }

  const response = await fetch(params.signed.url, {
    method: params.signed.method,
    headers: params.signed.headers,
    body: params.body,
  });
  return response;
}

function isRetryableAppendStatus(status: number): boolean {
  return status === 409 || status === 412;
}

export type PresignedS3ReplicatedLogOptions = {
  bucket: string;
  prefix?: string;
  presign: S3PresignProvider;
};

export class PresignedS3ReplicatedLog implements ReplicatedLog {
  private readonly bucket: string;
  private readonly sitePrefix: string;
  private readonly presign: S3PresignProvider;

  constructor(options: PresignedS3ReplicatedLogOptions) {
    this.bucket = options.bucket;
    const rootPrefix = trimSlashes(options.prefix ?? 'deltas');
    this.sitePrefix = ensureTrailingSlash(rootPrefix);
    this.presign = options.presign;
  }

  async append(entry: AppendLogEntry): Promise<LogPosition> {
    const siteRoot = this.siteRoot(entry.siteId);
    for (let attempt = 0; attempt < 5; attempt += 1) {
      const head = await this.getHead(entry.siteId);
      const nextSeq = head + 1;
      const objectKey = `${siteRoot}${keyForSeq(nextSeq)}`;

      const signed = await this.presign.signPutObject({
        bucket: this.bucket,
        key: objectKey,
        ifNoneMatch: '*',
        contentType: 'application/octet-stream',
      });

      const response = await sendSignedRequest({
        signed,
        expectedMethod: 'PUT',
        body: encodeBin({
          siteId: entry.siteId,
          hlc: entry.hlc,
          seq: nextSeq,
          ops: entry.ops,
        } satisfies LogEntry),
      });

      if (response.ok) {
        return nextSeq;
      }
      if (isRetryableAppendStatus(response.status)) {
        continue;
      }

      const raw = await response.text();
      throw new Error(`presigned append failed: ${response.status} ${response.statusText} ${raw}`);
    }

    throw new Error(`failed to append after retries for site '${entry.siteId}'`);
  }

  async readSince(siteId: string, since: LogPosition): Promise<LogEntry[]> {
    const siteRoot = this.siteRoot(siteId);
    const seqToKey = new Map<number, string>();
    let token: string | undefined;

    do {
      const signed = await this.presign.signListObjects({
        bucket: this.bucket,
        prefix: siteRoot,
        continuationToken: token,
      });
      const response = await sendSignedRequest({
        signed,
        expectedMethod: 'GET',
      });
      if (!response.ok) {
        const raw = await response.text();
        throw new Error(`presigned list failed: ${response.status} ${response.statusText} ${raw}`);
      }
      const xml = await response.text();
      const parsed = parseListObjectsXml(xml);

      for (const key of parsed.keys) {
        const seq = parseSeqFromObjectKey(siteRoot, key);
        if (seq !== null && seq > since) {
          seqToKey.set(seq, key);
        }
      }

      token = parsed.isTruncated ? parsed.nextToken ?? undefined : undefined;
    } while (token);

    const seqs = [...seqToKey.keys()].sort((a, b) => a - b);
    const entries: LogEntry[] = [];

    for (const seq of seqs) {
      const key = seqToKey.get(seq)!;
      const signed = await this.presign.signGetObject({
        bucket: this.bucket,
        key,
      });
      const response = await sendSignedRequest({
        signed,
        expectedMethod: 'GET',
      });
      if (!response.ok) {
        const raw = await response.text();
        throw new Error(`presigned get failed: ${response.status} ${response.statusText} ${raw}`);
      }
      entries.push(decodeBin<LogEntry>(new Uint8Array(await response.arrayBuffer())));
    }

    return entries;
  }

  async listSites(): Promise<string[]> {
    const sites = new Set<string>();
    let token: string | undefined;

    do {
      const signed = await this.presign.signListObjects({
        bucket: this.bucket,
        prefix: this.sitePrefix,
        delimiter: '/',
        continuationToken: token,
      });
      const response = await sendSignedRequest({ signed, expectedMethod: 'GET' });
      if (!response.ok) {
        const raw = await response.text();
        throw new Error(`presigned list sites failed: ${response.status} ${response.statusText} ${raw}`);
      }
      const xml = await response.text();
      const parsed = parseListObjectsXml(xml);

      for (const prefix of parsed.prefixes) {
        if (!prefix.startsWith(this.sitePrefix)) {
          continue;
        }
        const rest = prefix.slice(this.sitePrefix.length).replace(/\/$/u, '');
        if (rest.length > 0) {
          sites.add(rest);
        }
      }

      // Some providers may omit CommonPrefixes, so fall back to keys.
      for (const key of parsed.keys) {
        if (!key.startsWith(this.sitePrefix)) {
          continue;
        }
        const rest = key.slice(this.sitePrefix.length);
        const slash = rest.indexOf('/');
        if (slash > 0) {
          sites.add(rest.slice(0, slash));
        }
      }

      token = parsed.isTruncated ? parsed.nextToken ?? undefined : undefined;
    } while (token);

    return [...sites].sort();
  }

  async getHead(siteId: string): Promise<LogPosition> {
    const siteRoot = this.siteRoot(siteId);
    let token: string | undefined;
    let maxSeq = 0;

    do {
      const signed = await this.presign.signListObjects({
        bucket: this.bucket,
        prefix: siteRoot,
        continuationToken: token,
      });
      const response = await sendSignedRequest({ signed, expectedMethod: 'GET' });
      if (!response.ok) {
        const raw = await response.text();
        throw new Error(`presigned head list failed: ${response.status} ${response.statusText} ${raw}`);
      }
      const xml = await response.text();
      const parsed = parseListObjectsXml(xml);

      for (const key of parsed.keys) {
        const seq = parseSeqFromObjectKey(siteRoot, key);
        if (seq !== null && seq > maxSeq) {
          maxSeq = seq;
        }
      }

      token = parsed.isTruncated ? parsed.nextToken ?? undefined : undefined;
    } while (token);

    return maxSeq;
  }

  private siteRoot(siteId: string): string {
    return `${this.sitePrefix}${siteId}/`;
  }
}
