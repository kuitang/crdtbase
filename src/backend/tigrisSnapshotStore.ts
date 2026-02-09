import {
  GetObjectCommand,
  PutObjectCommand,
  PutObjectCommandInput,
  S3Client,
  S3ClientConfig,
} from '@aws-sdk/client-s3';
import { ManifestFile } from '../core/compaction';
import { decodeBin, encodeBin } from '../core/encoding';
import {
  DEFAULT_MANIFEST_PATH,
  DEFAULT_SCHEMA_PATH,
  SnapshotStore,
  assertManifestPublishable,
  assertSafeSnapshotRelativePath,
  validateManifestFile,
  validateSqlSchema,
} from '../core/snapshotStore';
import { SqlSchema } from '../core/sql';

type S3LikeClient = {
  send(command: unknown): Promise<unknown>;
};

export type TigrisSnapshotStoreOptions = {
  bucket: string;
  prefix?: string;
  manifestPath?: string;
  schemaPath?: string;
  client?: S3LikeClient;
  clientConfig?: S3ClientConfig;
};

export type CreateTigrisSnapshotStoreOptions = {
  bucket: string;
  accessKeyId: string;
  secretAccessKey: string;
  endpoint: string;
  prefix?: string;
  manifestPath?: string;
  schemaPath?: string;
  region?: string;
};

type ObjectRead = {
  bytes: Uint8Array;
  etag: string | null;
};

function trimSlashes(value: string): string {
  return value.replace(/^\/+|\/+$/gu, '');
}

function ensureTrailingSlash(value: string): string {
  return value.endsWith('/') ? value : `${value}/`;
}

function normalizePrefix(value: string | undefined): string {
  const trimmed = trimSlashes(value ?? 'snapshots');
  if (trimmed.length === 0) {
    return '';
  }
  return ensureTrailingSlash(trimmed);
}

function isMissingObjectError(error: unknown): boolean {
  const status = (error as { $metadata?: { httpStatusCode?: number } })?.$metadata?.httpStatusCode;
  if (status === 404) {
    return true;
  }
  const name = (error as { name?: string }).name;
  return name === 'NoSuchKey' || name === 'NotFound';
}

function isCasConflictError(error: unknown): boolean {
  const status = (error as { $metadata?: { httpStatusCode?: number } })?.$metadata?.httpStatusCode;
  return status === 409 || status === 412;
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

export class TigrisSnapshotStore implements SnapshotStore {
  private readonly bucket: string;
  private readonly prefix: string;
  private readonly manifestPath: string;
  private readonly schemaPath: string;
  private readonly client: S3LikeClient;

  constructor(options: TigrisSnapshotStoreOptions) {
    this.bucket = options.bucket;
    this.prefix = normalizePrefix(options.prefix);
    this.manifestPath = options.manifestPath ?? DEFAULT_MANIFEST_PATH;
    this.schemaPath = options.schemaPath ?? DEFAULT_SCHEMA_PATH;

    assertSafeSnapshotRelativePath(this.manifestPath, 'manifestPath');
    assertSafeSnapshotRelativePath(this.schemaPath, 'schemaPath');

    this.client =
      options.client ??
      new S3Client({
        region: 'auto',
        ...options.clientConfig,
      });
  }

  async getManifest(): Promise<ManifestFile | null> {
    const object = await this.readObject(this.keyForPath(this.manifestPath));
    if (object === null) {
      return null;
    }
    const manifest = decodeBin<ManifestFile>(object.bytes);
    validateManifestFile(manifest);
    return manifest;
  }

  async putManifest(manifest: ManifestFile, expectedVersion: number): Promise<boolean> {
    assertManifestPublishable(manifest, expectedVersion);

    const manifestKey = this.keyForPath(this.manifestPath);
    const current = await this.readObject(manifestKey);
    let currentVersion = 0;
    let currentEtag: string | null = null;

    if (current !== null) {
      const currentManifest = decodeBin<ManifestFile>(current.bytes);
      validateManifestFile(currentManifest);
      currentVersion = currentManifest.version;
      currentEtag = current.etag;
    }

    if (currentVersion !== expectedVersion) {
      return false;
    }

    const putInput: PutObjectCommandInput = {
      Bucket: this.bucket,
      Key: manifestKey,
      Body: encodeBin(manifest),
      ContentType: 'application/octet-stream',
    };

    if (current === null) {
      putInput.IfNoneMatch = '*';
    } else if (currentEtag !== null) {
      putInput.IfMatch = currentEtag;
    } else {
      throw new Error('manifest object is missing ETag required for CAS');
    }

    try {
      await this.client.send(new PutObjectCommand(putInput));
      return true;
    } catch (error) {
      if (isCasConflictError(error)) {
        return false;
      }
      throw error;
    }
  }

  async getSegment(path: string): Promise<Uint8Array | null> {
    assertSafeSnapshotRelativePath(path, 'segment path');
    const object = await this.readObject(this.keyForPath(path));
    return object?.bytes ?? null;
  }

  async putSegment(path: string, data: Uint8Array): Promise<void> {
    assertSafeSnapshotRelativePath(path, 'segment path');
    await this.client.send(
      new PutObjectCommand({
        Bucket: this.bucket,
        Key: this.keyForPath(path),
        Body: data,
        ContentType: 'application/octet-stream',
      }),
    );
  }

  async getSchema(): Promise<SqlSchema | null> {
    const object = await this.readObject(this.keyForPath(this.schemaPath));
    if (object === null) {
      return null;
    }
    const schema = decodeBin<SqlSchema>(object.bytes);
    validateSqlSchema(schema);
    return schema;
  }

  async putSchema(schema: SqlSchema): Promise<void> {
    validateSqlSchema(schema);
    await this.client.send(
      new PutObjectCommand({
        Bucket: this.bucket,
        Key: this.keyForPath(this.schemaPath),
        Body: encodeBin(schema),
        ContentType: 'application/octet-stream',
      }),
    );
  }

  private keyForPath(path: string): string {
    const normalized = path.replace(/\\/gu, '/');
    return `${this.prefix}${normalized}`;
  }

  private async readObject(key: string): Promise<ObjectRead | null> {
    try {
      const response = (await this.client.send(
        new GetObjectCommand({
          Bucket: this.bucket,
          Key: key,
        }),
      )) as { Body?: unknown; ETag?: string };

      return {
        bytes: await bodyToUint8Array(response.Body),
        etag: response.ETag ?? null,
      };
    } catch (error) {
      if (isMissingObjectError(error)) {
        return null;
      }
      throw error;
    }
  }
}

export function createTigrisSnapshotStore(
  options: CreateTigrisSnapshotStoreOptions,
): TigrisSnapshotStore {
  return new TigrisSnapshotStore({
    bucket: options.bucket,
    prefix: options.prefix ?? 'snapshots',
    manifestPath: options.manifestPath,
    schemaPath: options.schemaPath,
    clientConfig: {
      endpoint: options.endpoint,
      region: options.region ?? 'auto',
      forcePathStyle: false,
      credentials: {
        accessKeyId: options.accessKeyId,
        secretAccessKey: options.secretAccessKey,
      },
    },
  });
}
