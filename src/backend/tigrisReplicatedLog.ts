import { S3ReplicatedLog } from './s3ReplicatedLog';

export type TigrisReplicatedLogOptions = {
  bucket: string;
  accessKeyId: string;
  secretAccessKey: string;
  endpoint: string;
  prefix?: string;
  region?: string;
};

export function createTigrisReplicatedLog(options: TigrisReplicatedLogOptions): S3ReplicatedLog {
  return new S3ReplicatedLog({
    bucket: options.bucket,
    prefix: options.prefix ?? 'deltas',
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
