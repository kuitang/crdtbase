import { mkdir, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import readline from 'node:readline';
import { parseSql } from '../core/sql';
import { HttpReplicatedLog } from '../platform/node/httpReplicatedLog';
import { NodeCrdtClient } from '../platform/node/nodeClient';
import {
  HttpS3PresignProvider,
  PresignedS3ReplicatedLog,
} from '../platform/shared/presignedS3ReplicatedLog';
import { formatRowsAsTable } from './tableFormat';

type BackendMode = 'http' | 's3-presign';

type Config = {
  backend: BackendMode;
  siteId: string;
  dataDir: string;
  dataDirIsEphemeral: boolean;
  resetState: boolean;
  httpBaseUrl: string;
  bucket: string;
  prefix: string;
  presignBaseUrl: string;
  presignAuthToken: string | null;
};

const EXAMPLE_QUERIES = [
  'CREATE TABLE tasks (id STRING PRIMARY KEY, title LWW<STRING>, points COUNTER, tags SET<STRING>, status REGISTER<STRING>);',
  "INSERT INTO tasks (id, title, points, tags, status) VALUES ('t1', 'hello', 0, 'alpha', 'open');",
  "INC tasks.points BY 3 WHERE id = 't1';",
  "ADD 'beta' TO tasks.tags WHERE id = 't1';",
  "UPDATE tasks SET title = 'from-repl' WHERE id = 't1';",
  'SELECT * FROM tasks;',
];

function printUsage(): void {
  process.stdout.write(
    [
      'Usage: npm run repl:node -- [options]',
      '',
      'Options:',
      '  --backend <http|s3-presign>        (default: http)',
      '  --site-id <site-id>                (default: cli-site)',
      '  --data-dir <path>                  Optional persistent local state dir',
      '  --reset-state                      Delete data-dir before starting',
      '  --http-base-url <url>              Required when backend=http',
      '  --bucket <name>                    Required when backend=s3-presign',
      '  --prefix <prefix>                  (default: deltas)',
      '  --presign-base-url <url>           Required when backend=s3-presign',
      '  --presign-auth-token <token>       Optional bearer token for presign service',
      '',
      'REPL commands:',
      '  .help      show this help',
      '  .examples  print example SQL statements',
      '  .push      push local pending writes',
      '  .pull      pull remote writes',
      '  .sync      push + pull',
      '  .quit      exit',
    ].join('\n') + '\n',
  );
}

function parseBackend(value: string): BackendMode {
  if (value === 'http' || value === 's3-presign') {
    return value;
  }
  throw new Error(`unsupported backend '${value}'`);
}

function buildEphemeralDataDir(siteId: string): string {
  const nonce = Math.random().toString(36).slice(2, 10);
  return join(tmpdir(), 'crdtbase-cli', `${siteId}-${Date.now()}-${process.pid}-${nonce}`);
}

function parseConfig(argv: string[]): Config {
  let backend = parseBackend(process.env.CRDTBASE_BACKEND ?? 'http');
  let siteId = process.env.CRDTBASE_SITE_ID ?? 'cli-site';
  let dataDir = process.env.CRDTBASE_DATA_DIR ?? '';
  let dataDirExplicit = dataDir.trim().length > 0;
  let resetState = false;
  let httpBaseUrl = process.env.CRDTBASE_HTTP_BASE_URL ?? '';
  let bucket = process.env.CRDTBASE_S3_BUCKET ?? '';
  let prefix = process.env.CRDTBASE_S3_PREFIX ?? 'deltas';
  let presignBaseUrl = process.env.CRDTBASE_S3_PRESIGN_BASE_URL ?? '';
  let presignAuthToken = process.env.CRDTBASE_S3_PRESIGN_AUTH_TOKEN ?? null;

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index]!;
    const value = argv[index + 1];

    if (arg === '--backend' && value) {
      backend = parseBackend(value);
      index += 1;
      continue;
    }
    if (arg === '--site-id' && value) {
      siteId = value;
      index += 1;
      continue;
    }
    if (arg === '--data-dir' && value) {
      dataDir = value;
      dataDirExplicit = true;
      index += 1;
      continue;
    }
    if (arg === '--reset-state') {
      resetState = true;
      continue;
    }
    if (arg === '--http-base-url' && value) {
      httpBaseUrl = value;
      index += 1;
      continue;
    }
    if (arg === '--bucket' && value) {
      bucket = value;
      index += 1;
      continue;
    }
    if (arg === '--prefix' && value) {
      prefix = value;
      index += 1;
      continue;
    }
    if (arg === '--presign-base-url' && value) {
      presignBaseUrl = value;
      index += 1;
      continue;
    }
    if (arg === '--presign-auth-token' && value) {
      presignAuthToken = value;
      index += 1;
      continue;
    }
    if (arg === '--help') {
      printUsage();
      process.exit(0);
    }
  }

  const dataDirIsEphemeral = !dataDirExplicit;
  if (!dataDir) {
    dataDir = dataDirIsEphemeral ? buildEphemeralDataDir(siteId) : dataDir;
  }
  if (!dataDir) {
    throw new Error('invalid --data-dir');
  }

  if (backend === 'http' && !httpBaseUrl) {
    throw new Error('missing --http-base-url for backend=http');
  }

  if (backend === 's3-presign') {
    if (!bucket) {
      throw new Error('missing --bucket for backend=s3-presign');
    }
    if (!presignBaseUrl) {
      throw new Error('missing --presign-base-url for backend=s3-presign');
    }
  }

  return {
    backend,
    siteId,
    dataDir,
    dataDirIsEphemeral,
    resetState,
    httpBaseUrl,
    bucket,
    prefix,
    presignBaseUrl,
    presignAuthToken,
  };
}

function printExamples(): void {
  process.stdout.write('\nExample queries:\n');
  for (const example of EXAMPLE_QUERIES) {
    process.stdout.write(`  ${example}\n`);
  }
  process.stdout.write('\n');
}

function isQuitCommand(input: string): boolean {
  return input === '.quit' || input === '.exit';
}

async function main(): Promise<void> {
  const config = parseConfig(process.argv.slice(2));
  if (config.resetState) {
    await rm(config.dataDir, { recursive: true, force: true });
  }
  await mkdir(config.dataDir, { recursive: true });

  const log =
    config.backend === 'http'
      ? new HttpReplicatedLog(config.httpBaseUrl)
      : new PresignedS3ReplicatedLog({
          bucket: config.bucket,
          prefix: config.prefix,
          presign: new HttpS3PresignProvider({
            baseUrl: config.presignBaseUrl,
            authToken: config.presignAuthToken ?? undefined,
          }),
        });

  const client = await NodeCrdtClient.open({
    siteId: config.siteId,
    log,
    dataDir: config.dataDir,
  });

  process.stdout.write(
    [
      `CRDTBase Node REPL connected (backend=${config.backend}, site=${config.siteId})`,
      `dataDir=${config.dataDir}${config.dataDirIsEphemeral ? ' [ephemeral]' : ''}`,
      'Type .help for commands. SQL statements are executed directly.',
    ].join('\n') + '\n\n',
  );

  const rl = readline.createInterface({
    input: process.stdin,
    output: process.stdout,
    prompt: 'crdtbase> ',
  });

  rl.prompt();

  rl.on('line', async (line) => {
    const input = line.trim();
    if (input.length === 0) {
      rl.prompt();
      return;
    }

    try {
      if (input === '.help') {
        printUsage();
        rl.prompt();
        return;
      }
      if (input === '.examples') {
        printExamples();
        rl.prompt();
        return;
      }
      if (isQuitCommand(input)) {
        rl.close();
        return;
      }
      if (input === '.push') {
        await client.push();
        process.stdout.write('ok: pushed local ops\n');
        rl.prompt();
        return;
      }
      if (input === '.pull') {
        await client.pull();
        process.stdout.write('ok: pulled remote ops\n');
        rl.prompt();
        return;
      }
      if (input === '.sync') {
        await client.sync();
        process.stdout.write('ok: synced\n');
        rl.prompt();
        return;
      }

      const statement = parseSql(input);
      if (statement.kind === 'select') {
        const rows = await client.query(input);
        process.stdout.write(`${formatRowsAsTable(rows)}\n`);
      } else {
        await client.exec(input);
        process.stdout.write('ok\n');
      }
    } catch (error) {
      process.stderr.write(`${error instanceof Error ? error.message : String(error)}\n`);
    }

    rl.prompt();
  });

  rl.on('close', () => {
    process.stdout.write('bye\n');
    process.exit(0);
  });
}

main().catch((error) => {
  process.stderr.write(`${error instanceof Error ? error.message : String(error)}\n`);
  process.exitCode = 1;
});
