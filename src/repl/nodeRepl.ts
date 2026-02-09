import { mkdir, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import readline from 'node:readline';
import { S3ClientConfig } from '@aws-sdk/client-s3';
import { parseSql } from '../core/sql';
import { S3ReplicatedLog } from '../backend/s3ReplicatedLog';
import { HttpReplicatedLog } from '../platform/node/httpReplicatedLog';
import { NodeCrdtClient } from '../platform/node/nodeClient';
import { formatRowsAsTable } from './tableFormat';

type BackendMode = 'http' | 's3';

type Config = {
  backend: BackendMode;
  siteId: string;
  dataDir: string;
  dataDirIsEphemeral: boolean;
  resetState: boolean;
  httpBaseUrl: string;
  bucket: string;
  prefix: string;
  s3Endpoint: string;
  s3Region: string;
  s3AccessKeyId: string;
  s3SecretAccessKey: string;
  s3SessionToken: string;
  s3ForcePathStyle: boolean;
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
      '  --backend <http|s3>                (default: http)',
      '  --site-id <site-id>                (default: cli-site)',
      '  --data-dir <path>                  Optional persistent local state dir',
      '  --reset-state                      Delete data-dir before starting',
      '  --http-base-url <url>              Required when backend=http',
      '  --bucket <name>                    Required when backend=s3',
      '  --prefix <prefix>                  (default: deltas)',
      '  --s3-endpoint <url>                Required when backend=s3',
      '  --s3-region <region>               (default: auto)',
      '  --s3-access-key-id <key>           Required when backend=s3',
      '  --s3-secret-access-key <secret>    Required when backend=s3',
      '  --s3-session-token <token>         Optional session token',
      '  --s3-force-path-style <true|false> (default: false)',
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
  if (value === 'http' || value === 's3') {
    return value;
  }
  throw new Error(`unsupported backend '${value}'`);
}

function parseBooleanFlag(value: string, label: string): boolean {
  const lowered = value.trim().toLowerCase();
  if (lowered === '1' || lowered === 'true' || lowered === 'yes' || lowered === 'on') {
    return true;
  }
  if (lowered === '0' || lowered === 'false' || lowered === 'no' || lowered === 'off') {
    return false;
  }
  throw new Error(`invalid ${label}: '${value}'`);
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
  let s3Endpoint =
    process.env.CRDTBASE_S3_ENDPOINT ??
    process.env.AWS_ENDPOINT_URL_S3 ??
    process.env.AWS_ENDPOINT_URL ??
    '';
  let s3Region = process.env.CRDTBASE_S3_REGION ?? process.env.AWS_REGION ?? 'auto';
  let s3AccessKeyId =
    process.env.CRDTBASE_S3_ACCESS_KEY_ID ?? process.env.AWS_ACCESS_KEY_ID ?? '';
  let s3SecretAccessKey =
    process.env.CRDTBASE_S3_SECRET_ACCESS_KEY ?? process.env.AWS_SECRET_ACCESS_KEY ?? '';
  let s3SessionToken =
    process.env.CRDTBASE_S3_SESSION_TOKEN ?? process.env.AWS_SESSION_TOKEN ?? '';
  let s3ForcePathStyle = parseBooleanFlag(
    process.env.CRDTBASE_S3_FORCE_PATH_STYLE ?? 'false',
    'CRDTBASE_S3_FORCE_PATH_STYLE',
  );

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
    if ((arg === '--s3-endpoint' || arg === '--endpoint') && value) {
      s3Endpoint = value;
      index += 1;
      continue;
    }
    if ((arg === '--s3-region' || arg === '--region') && value) {
      s3Region = value;
      index += 1;
      continue;
    }
    if ((arg === '--s3-access-key-id' || arg === '--access-key-id') && value) {
      s3AccessKeyId = value;
      index += 1;
      continue;
    }
    if ((arg === '--s3-secret-access-key' || arg === '--secret-access-key') && value) {
      s3SecretAccessKey = value;
      index += 1;
      continue;
    }
    if ((arg === '--s3-session-token' || arg === '--session-token') && value) {
      s3SessionToken = value;
      index += 1;
      continue;
    }
    if (arg === '--s3-force-path-style' && value) {
      s3ForcePathStyle = parseBooleanFlag(value, '--s3-force-path-style');
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

  if (backend === 's3') {
    if (!bucket) {
      throw new Error('missing --bucket for backend=s3');
    }
    if (!s3Endpoint) {
      throw new Error('missing --s3-endpoint for backend=s3');
    }
    if (!s3AccessKeyId) {
      throw new Error('missing --s3-access-key-id for backend=s3');
    }
    if (!s3SecretAccessKey) {
      throw new Error('missing --s3-secret-access-key for backend=s3');
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
    s3Endpoint,
    s3Region,
    s3AccessKeyId,
    s3SecretAccessKey,
    s3SessionToken,
    s3ForcePathStyle,
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

  const s3ClientConfig: S3ClientConfig = {
    endpoint: config.s3Endpoint,
    region: config.s3Region,
    forcePathStyle: config.s3ForcePathStyle,
    credentials: {
      accessKeyId: config.s3AccessKeyId,
      secretAccessKey: config.s3SecretAccessKey,
      ...(config.s3SessionToken ? { sessionToken: config.s3SessionToken } : {}),
    },
  };

  const log =
    config.backend === 'http'
      ? new HttpReplicatedLog(config.httpBaseUrl)
      : new S3ReplicatedLog({
          bucket: config.bucket,
          prefix: config.prefix,
          clientConfig: s3ClientConfig,
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
