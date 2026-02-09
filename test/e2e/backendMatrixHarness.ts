import { mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { FileReplicatedLogServer } from '../../src/backend/fileLogServer';
import { ReplicatedLog } from '../../src/core/replication';
import { HttpReplicatedLog } from '../../src/platform/node/httpReplicatedLog';
import {
  HttpS3PresignProvider,
  PresignedS3ReplicatedLog,
} from '../../src/platform/shared/presignedS3ReplicatedLog';
import { MinioHarness } from './minioHarness';
import { PresignHarness } from './presignHarness';

export type BackendMatrixKind = 'http' | 's3-minio-presign' | 's3-presign-auth';

export type BackendMatrixHarness = {
  kind: BackendMatrixKind;
  rootDir: string;
  createLog(): ReplicatedLog;
  stop(): Promise<void>;
};

export async function startBackendMatrixHarness(params: {
  kind: BackendMatrixKind;
  authToken?: string;
}): Promise<BackendMatrixHarness> {
  const rootDir = await mkdtemp(join(tmpdir(), `crdtbase-backend-matrix-${params.kind}-`));

  if (params.kind === 'http') {
    const server = new FileReplicatedLogServer(join(rootDir, 'server'));
    const baseUrl = await server.start();
    return {
      kind: params.kind,
      rootDir,
      createLog: () => new HttpReplicatedLog(baseUrl),
      stop: async () => {
        await server.stop();
        await rm(rootDir, { recursive: true, force: true });
      },
    };
  }

  const minio = await MinioHarness.start({
    rootDir,
    bucket: 'crdtbase',
  });
  let presign: PresignHarness | null = null;
  try {
    presign = await PresignHarness.start({
      endpoint: minio.getEndpoint(),
      authToken: params.kind === 's3-presign-auth' ? params.authToken : undefined,
    });
  } catch (error) {
    await minio.stop().catch(() => undefined);
    await rm(rootDir, { recursive: true, force: true }).catch(() => undefined);
    throw error;
  }

  const provider = new HttpS3PresignProvider({
    baseUrl: presign.getBaseUrl(),
    authToken: params.kind === 's3-presign-auth' ? params.authToken : undefined,
  });

  return {
    kind: params.kind,
    rootDir,
    createLog: () =>
      new PresignedS3ReplicatedLog({
        bucket: minio.getBucket(),
        prefix: 'deltas',
        presign: provider,
      }),
    stop: async () => {
      await presign!.stop();
      await minio.stop();
      await rm(rootDir, { recursive: true, force: true });
    },
  };
}
