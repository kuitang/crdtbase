import { mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { FileReplicatedLogServer } from '../../src/backend/fileLogServer';
import { S3ReplicatedLog } from '../../src/backend/s3ReplicatedLog';
import { ReplicatedLog } from '../../src/core/replication';
import { HttpReplicatedLog } from '../../src/platform/node/httpReplicatedLog';
import { MinioHarness } from './minioHarness';

export type BackendMatrixKind = 'http' | 's3-minio';

export type BackendMatrixHarness = {
  kind: BackendMatrixKind;
  rootDir: string;
  createLog(): ReplicatedLog;
  stop(): Promise<void>;
};

export async function startBackendMatrixHarness(params: {
  kind: BackendMatrixKind;
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

  return {
    kind: params.kind,
    rootDir,
    createLog: () =>
      new S3ReplicatedLog({
        bucket: minio.getBucket(),
        prefix: 'deltas',
        clientConfig: minio.getS3ClientConfig(),
      }),
    stop: async () => {
      await minio.stop();
      await rm(rootDir, { recursive: true, force: true });
    },
  };
}
