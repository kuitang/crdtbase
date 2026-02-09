import { mkdir } from 'node:fs/promises';
import { resolve } from 'node:path';
import { MinioHarness } from '../test/e2e/minioHarness';

function parseArg(name: string, fallback: string): string {
  const index = process.argv.indexOf(name);
  if (index >= 0 && process.argv[index + 1]) {
    return process.argv[index + 1]!;
  }
  return fallback;
}

async function main(): Promise<void> {
  const rootDir = resolve(parseArg('--root-dir', process.env.MINIO_ROOT_DIR ?? '.crdtbase-minio'));
  const bucket = parseArg('--bucket', process.env.MINIO_BUCKET ?? 'crdtbase');

  await mkdir(rootDir, { recursive: true });
  const harness = await MinioHarness.start({ rootDir, bucket });

  process.stdout.write(
    [
      'MinIO dev harness started',
      `endpoint=${harness.getEndpoint()}`,
      `bucket=${harness.getBucket()}`,
      'accessKeyId=minioadmin',
      'secretAccessKey=minioadmin',
      '',
      'Press Ctrl+C to stop.',
    ].join('\n') + '\n',
  );

  const shutdown = async () => {
    await harness.stop();
    process.exit(0);
  };

  process.on('SIGINT', () => {
    void shutdown();
  });
  process.on('SIGTERM', () => {
    void shutdown();
  });
}

main().catch((error) => {
  process.stderr.write(`${error instanceof Error ? error.message : String(error)}\n`);
  process.exitCode = 1;
});
