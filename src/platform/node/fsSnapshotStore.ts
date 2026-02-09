import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { dirname, resolve, sep } from 'node:path';
import { ManifestFile } from '../../core/compaction';
import { decodeBin, encodeBin } from '../../core/encoding';
import {
  DEFAULT_MANIFEST_PATH,
  DEFAULT_SCHEMA_PATH,
  SnapshotStore,
  assertManifestPublishable,
  assertSafeSnapshotRelativePath,
  validateManifestFile,
  validateSqlSchema,
} from '../../core/snapshotStore';
import { SqlSchema } from '../../core/sql';

function isEnoent(error: unknown): boolean {
  return (error as { code?: string }).code === 'ENOENT';
}

export type FsSnapshotStoreOptions = {
  rootDir: string;
  manifestPath?: string;
  schemaPath?: string;
};

export class FsSnapshotStore implements SnapshotStore {
  private readonly rootDir: string;
  private readonly rootPrefix: string;
  private readonly manifestPath: string;
  private readonly schemaPath: string;

  constructor(options: FsSnapshotStoreOptions) {
    this.rootDir = resolve(options.rootDir);
    this.rootPrefix = this.rootDir.endsWith(sep) ? this.rootDir : `${this.rootDir}${sep}`;

    this.manifestPath = options.manifestPath ?? DEFAULT_MANIFEST_PATH;
    this.schemaPath = options.schemaPath ?? DEFAULT_SCHEMA_PATH;

    assertSafeSnapshotRelativePath(this.manifestPath, 'manifestPath');
    assertSafeSnapshotRelativePath(this.schemaPath, 'schemaPath');
  }

  async getManifest(): Promise<ManifestFile | null> {
    const bytes = await this.readOptionalBytes(this.manifestPath);
    if (bytes === null) {
      return null;
    }
    const manifest = decodeBin<ManifestFile>(bytes);
    validateManifestFile(manifest);
    return manifest;
  }

  async putManifest(manifest: ManifestFile, expectedVersion: number): Promise<boolean> {
    assertManifestPublishable(manifest, expectedVersion);

    const priorManifest = await this.getManifest();
    const priorVersion = priorManifest?.version ?? 0;
    if (priorVersion !== expectedVersion) {
      return false;
    }

    // Re-read immediately before write to reduce lost update windows across processes.
    const latestManifest = await this.getManifest();
    const latestVersion = latestManifest?.version ?? 0;
    if (latestVersion !== expectedVersion) {
      return false;
    }

    await this.writeBytes(this.manifestPath, encodeBin(manifest));
    return true;
  }

  async getSegment(path: string): Promise<Uint8Array | null> {
    assertSafeSnapshotRelativePath(path, 'segment path');
    return this.readOptionalBytes(path);
  }

  async putSegment(path: string, data: Uint8Array): Promise<void> {
    assertSafeSnapshotRelativePath(path, 'segment path');
    await this.writeBytes(path, data);
  }

  async getSchema(): Promise<SqlSchema | null> {
    const bytes = await this.readOptionalBytes(this.schemaPath);
    if (bytes === null) {
      return null;
    }
    const schema = decodeBin<SqlSchema>(bytes);
    validateSqlSchema(schema);
    return schema;
  }

  async putSchema(schema: SqlSchema): Promise<void> {
    validateSqlSchema(schema);
    await this.writeBytes(this.schemaPath, encodeBin(schema));
  }

  private async readOptionalBytes(path: string): Promise<Uint8Array | null> {
    const absolutePath = this.resolvePath(path);
    try {
      return await readFile(absolutePath);
    } catch (error) {
      if (isEnoent(error)) {
        return null;
      }
      throw error;
    }
  }

  private async writeBytes(path: string, bytes: Uint8Array): Promise<void> {
    const absolutePath = this.resolvePath(path);
    await mkdir(dirname(absolutePath), { recursive: true });
    await writeFile(absolutePath, bytes);
  }

  private resolvePath(path: string): string {
    const absolutePath = resolve(this.rootDir, path);
    if (absolutePath !== this.rootDir && !absolutePath.startsWith(this.rootPrefix)) {
      throw new Error(`path escapes snapshot root: ${path}`);
    }
    return absolutePath;
  }
}
