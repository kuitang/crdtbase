import {
  ListObjectsV2Command,
  ListObjectsV2CommandOutput,
  PutObjectCommand,
  S3Client,
  S3ClientConfig,
  GetObjectCommand,
} from '@aws-sdk/client-s3';
import { decodeBin, encodeBin } from '../core/encoding';
import {
  AppendLogEntry,
  LogEntry,
  LogPosition,
  ReplicatedLog,
  takeContiguousEntriesSince,
} from '../core/replication';

type S3LikeClient = {
  send(command: unknown): Promise<unknown>;
};

export type S3ReplicatedLogOptions = {
  bucket: string;
  prefix?: string;
  client?: S3LikeClient;
  clientConfig?: S3ClientConfig;
};

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

function isRetryableAppendError(error: unknown): boolean {
  const httpStatus = (error as { $metadata?: { httpStatusCode?: number } })?.$metadata
    ?.httpStatusCode;
  return httpStatus === 409 || httpStatus === 412;
}

async function bodyToUint8Array(body: unknown): Promise<Uint8Array> {
  if (!body) {
    throw new Error('S3 object body is empty');
  }

  const withTransform = body as { transformToByteArray?: () => Promise<Uint8Array> };
  if (typeof withTransform.transformToByteArray === 'function') {
    return withTransform.transformToByteArray();
  }

  const withArrayBuffer = body as { arrayBuffer?: () => Promise<ArrayBuffer> };
  if (typeof withArrayBuffer.arrayBuffer === 'function') {
    return new Uint8Array(await withArrayBuffer.arrayBuffer());
  }

  throw new Error('unsupported S3 body type');
}

export class S3ReplicatedLog implements ReplicatedLog {
  private readonly bucket: string;
  private readonly sitePrefix: string;
  private readonly client: S3LikeClient;

  constructor(options: S3ReplicatedLogOptions) {
    this.bucket = options.bucket;
    const rootPrefix = trimSlashes(options.prefix ?? 'deltas');
    this.sitePrefix = ensureTrailingSlash(rootPrefix);
    this.client =
      options.client ??
      new S3Client({
        region: 'auto',
        ...options.clientConfig,
      });
  }

  async append(entry: AppendLogEntry): Promise<LogPosition> {
    const siteRoot = this.siteRoot(entry.siteId);
    for (let attempt = 0; attempt < 5; attempt += 1) {
      const head = await this.getHead(entry.siteId);
      const nextSeq = head + 1;
      const objectKey = `${siteRoot}${keyForSeq(nextSeq)}`;
      try {
        await this.client.send(
          new PutObjectCommand({
            Bucket: this.bucket,
            Key: objectKey,
            Body: encodeBin({
              siteId: entry.siteId,
              hlc: entry.hlc,
              seq: nextSeq,
              ops: entry.ops,
            } satisfies LogEntry),
            ContentType: 'application/octet-stream',
            IfNoneMatch: '*',
          }),
        );
        return nextSeq;
      } catch (error) {
        if (isRetryableAppendError(error)) {
          continue;
        }
        throw error;
      }
    }
    throw new Error(`failed to append after retries for site '${entry.siteId}'`);
  }

  async readSince(siteId: string, since: LogPosition): Promise<LogEntry[]> {
    const siteRoot = this.siteRoot(siteId);
    const seqToKey = new Map<number, string>();
    let token: string | undefined;

    do {
      const response = (await this.client.send(
        new ListObjectsV2Command({
          Bucket: this.bucket,
          Prefix: siteRoot,
          ContinuationToken: token,
        }),
      )) as ListObjectsV2CommandOutput;

      for (const object of response.Contents ?? []) {
        if (!object.Key) {
          continue;
        }
        const seq = parseSeqFromObjectKey(siteRoot, object.Key);
        if (seq !== null && seq > since) {
          seqToKey.set(seq, object.Key);
        }
      }
      token = response.IsTruncated ? response.NextContinuationToken : undefined;
    } while (token);

    const seqs = [...seqToKey.keys()].sort((a, b) => a - b);
    const entries: LogEntry[] = [];
    for (const seq of seqs) {
      const key = seqToKey.get(seq)!;
      const response = (await this.client.send(
        new GetObjectCommand({
          Bucket: this.bucket,
          Key: key,
        }),
      )) as { Body?: unknown };

      const bytes = await bodyToUint8Array(response.Body);
      entries.push(decodeBin<LogEntry>(bytes));
    }
    return takeContiguousEntriesSince(entries, since);
  }

  async listSites(): Promise<string[]> {
    const sites = new Set<string>();
    let token: string | undefined;
    do {
      const response = (await this.client.send(
        new ListObjectsV2Command({
          Bucket: this.bucket,
          Prefix: this.sitePrefix,
          Delimiter: '/',
          ContinuationToken: token,
        }),
      )) as ListObjectsV2CommandOutput;

      for (const prefix of response.CommonPrefixes ?? []) {
        if (!prefix.Prefix) {
          continue;
        }
        const rest = prefix.Prefix.slice(this.sitePrefix.length).replace(/\/$/u, '');
        if (rest.length > 0) {
          sites.add(rest);
        }
      }
      token = response.IsTruncated ? response.NextContinuationToken : undefined;
    } while (token);

    return [...sites].sort();
  }

  async getHead(siteId: string): Promise<LogPosition> {
    const siteRoot = this.siteRoot(siteId);
    let token: string | undefined;
    let maxSeq = 0;
    do {
      const response = (await this.client.send(
        new ListObjectsV2Command({
          Bucket: this.bucket,
          Prefix: siteRoot,
          ContinuationToken: token,
        }),
      )) as ListObjectsV2CommandOutput;

      for (const object of response.Contents ?? []) {
        if (!object.Key) {
          continue;
        }
        const seq = parseSeqFromObjectKey(siteRoot, object.Key);
        if (seq !== null && seq > maxSeq) {
          maxSeq = seq;
        }
      }
      token = response.IsTruncated ? response.NextContinuationToken : undefined;
    } while (token);
    return maxSeq;
  }

  private siteRoot(siteId: string): string {
    return `${this.sitePrefix}${siteId}/`;
  }
}
