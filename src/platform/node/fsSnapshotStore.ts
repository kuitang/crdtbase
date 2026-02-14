import { mkdir, open, readFile, rename, rm, stat, writeFile } from 'node:fs/promises';
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

function isEexist(error: unknown): boolean {
  return (error as { code?: string }).code === 'EEXIST';
}

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

function isProcessAlive(pid: number): boolean {
  try {
    process.kill(pid, 0);
    return true;
  } catch (error) {
    const code = (error as { code?: string }).code;
    return code === 'EPERM';
  }
}

export type FsSnapshotStoreOptions = {
  rootDir: string;
  manifestPath?: string;
  schemaPath?: string;
};

export class FsSnapshotStore implements SnapshotStore {
  private static readonly manifestLockWaitMs = 5_000;
  private static readonly staleManifestLockMs = 30_000;

  private readonly rootDir: string;
  private readonly rootPrefix: string;
  private readonly manifestPath: string;
  private readonly schemaPath: string;
  private readonly manifestLockPath: string;

  constructor(options: FsSnapshotStoreOptions) {
    this.rootDir = resolve(options.rootDir);
    this.rootPrefix = this.rootDir.endsWith(sep) ? this.rootDir : `${this.rootDir}${sep}`;

    this.manifestPath = options.manifestPath ?? DEFAULT_MANIFEST_PATH;
    this.schemaPath = options.schemaPath ?? DEFAULT_SCHEMA_PATH;

    assertSafeSnapshotRelativePath(this.manifestPath, 'manifestPath');
    assertSafeSnapshotRelativePath(this.schemaPath, 'schemaPath');
    this.manifestLockPath = `${this.manifestPath}.lock`;
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

    return this.withManifestLock(async () => {
      const priorManifest = await this.getManifest();
      const priorVersion = priorManifest?.version ?? 0;
      if (priorVersion !== expectedVersion) {
        return false;
      }
      await this.writeBytes(this.manifestPath, encodeBin(manifest));
      return true;
    });
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
    const tempPath = `${absolutePath}.tmp-${process.pid}-${Date.now()}-${Math.random().toString(16).slice(2)}`;
    await mkdir(dirname(absolutePath), { recursive: true });
    await writeFile(tempPath, bytes);
    try {
      await rename(tempPath, absolutePath);
    } catch (error) {
      await rm(tempPath, { force: true });
      throw error;
    }
  }

  private resolvePath(path: string): string {
    const absolutePath = resolve(this.rootDir, path);
    if (absolutePath !== this.rootDir && !absolutePath.startsWith(this.rootPrefix)) {
      throw new Error(`path escapes snapshot root: ${path}`);
    }
    return absolutePath;
  }

  private async withManifestLock<T>(fn: () => Promise<T>): Promise<T> {
    const absoluteLockPath = this.resolvePath(this.manifestLockPath);
    const handle = await this.acquireManifestLock(absoluteLockPath);
    try {
      return await fn();
    } finally {
      await handle.close();
      await rm(absoluteLockPath, { force: true });
    }
  }

  private async acquireManifestLock(path: string): Promise<Awaited<ReturnType<typeof open>>> {
    const startedAt = Date.now();
    while (true) {
      try {
        const handle = await open(path, 'wx');
        await handle.writeFile(`${process.pid}\n${Date.now()}\n`, 'utf8');
        return handle;
      } catch (error) {
        if (!isEexist(error)) {
          throw error;
        }
        await this.tryClearStaleManifestLock(path);
        if (Date.now() - startedAt >= FsSnapshotStore.manifestLockWaitMs) {
          throw new Error(`timed out waiting for manifest lock at ${path}`);
        }
        await sleep(10);
      }
    }
  }

  private async tryClearStaleManifestLock(path: string): Promise<void> {
    let raw: string;
    try {
      raw = await readFile(path, 'utf8');
    } catch (error) {
      if (isEnoent(error)) {
        return;
      }
      throw error;
    }

    const [pidLine, createdAtLine] = raw.split('\n');
    const pid = Number.parseInt(pidLine ?? '', 10);
    let createdAtMs = Number.parseInt(createdAtLine ?? '', 10);
    if (!Number.isFinite(createdAtMs)) {
      try {
        const lockStat = await stat(path);
        createdAtMs = Math.floor(lockStat.mtimeMs);
      } catch (error) {
        if (isEnoent(error)) {
          return;
        }
        throw error;
      }
    }
    if (Date.now() - createdAtMs < FsSnapshotStore.staleManifestLockMs) {
      return;
    }
    if (Number.isFinite(pid) && pid > 0 && isProcessAlive(pid)) {
      return;
    }
    await rm(path, { force: true });
  }
}
