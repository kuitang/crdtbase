import { ManifestFile } from '../../core/compaction';
import { decodeBin, encodeBin } from '../../core/encoding';
import {
  SnapshotStore,
  assertManifestPublishable,
  assertSafeSnapshotRelativePath,
  validateManifestFile,
  validateSqlSchema,
} from '../../core/snapshotStore';
import { SqlSchema } from '../../core/sql';

function normalizeBaseUrl(baseUrl: string): string {
  return baseUrl.replace(/\/+$/u, '');
}

function encodePath(path: string): string {
  assertSafeSnapshotRelativePath(path, 'snapshot path');
  return path.split('/').map((part) => encodeURIComponent(part)).join('/');
}

async function readBytesResponse(response: Response): Promise<Uint8Array> {
  if (!response.ok) {
    const raw = await response.text();
    throw new Error(`snapshot request failed: ${response.status} ${response.statusText} ${raw}`);
  }
  return new Uint8Array(await response.arrayBuffer());
}

async function is404(response: Response): Promise<boolean> {
  if (response.status !== 404) {
    return false;
  }
  await response.arrayBuffer();
  return true;
}

export class HttpSnapshotStore implements SnapshotStore {
  private readonly baseUrl: string;

  constructor(baseUrl: string) {
    this.baseUrl = normalizeBaseUrl(baseUrl);
  }

  async getManifest(): Promise<ManifestFile | null> {
    const response = await fetch(`${this.baseUrl}/manifest`);
    if (await is404(response)) {
      return null;
    }
    const bytes = await readBytesResponse(response);
    const manifest = decodeBin<ManifestFile>(bytes);
    validateManifestFile(manifest);
    return manifest;
  }

  async putManifest(manifest: ManifestFile, expectedVersion: number): Promise<boolean> {
    assertManifestPublishable(manifest, expectedVersion);
    const response = await fetch(
      `${this.baseUrl}/manifest?expect_version=${encodeURIComponent(String(expectedVersion))}`,
      {
        method: 'PUT',
        headers: {
          'content-type': 'application/octet-stream',
        },
        body: encodeBin(manifest),
      },
    );
    if (response.status === 412) {
      await response.arrayBuffer();
      return false;
    }
    await readBytesResponse(response);
    return true;
  }

  async getSegment(path: string): Promise<Uint8Array | null> {
    const response = await fetch(`${this.baseUrl}/segments/${encodePath(path)}`);
    if (await is404(response)) {
      return null;
    }
    return readBytesResponse(response);
  }

  async putSegment(path: string, data: Uint8Array): Promise<void> {
    const response = await fetch(`${this.baseUrl}/segments/${encodePath(path)}`, {
      method: 'PUT',
      headers: {
        'content-type': 'application/octet-stream',
      },
      body: data,
    });
    await readBytesResponse(response);
  }

  async getSchema(): Promise<SqlSchema | null> {
    const response = await fetch(`${this.baseUrl}/schema`);
    if (await is404(response)) {
      return null;
    }
    const bytes = await readBytesResponse(response);
    const schema = decodeBin<SqlSchema>(bytes);
    validateSqlSchema(schema);
    return schema;
  }

  async putSchema(schema: SqlSchema): Promise<void> {
    validateSqlSchema(schema);
    const response = await fetch(`${this.baseUrl}/schema`, {
      method: 'PUT',
      headers: {
        'content-type': 'application/octet-stream',
      },
      body: encodeBin(schema),
    });
    await readBytesResponse(response);
  }
}
