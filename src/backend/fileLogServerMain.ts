import { join } from 'node:path';
import { FileReplicatedLogServer } from './fileLogServer';

type Config = {
  rootDir: string;
  host: string;
  port: number;
};

function printUsage(): void {
  process.stdout.write(
    [
      'Usage: npm run backend:http -- [options]',
      '',
      'Options:',
      '  --root-dir <path>   (default: ./.crdtbase-http-server)',
      '  --host <host>       (default: 127.0.0.1)',
      '  --port <port>       (default: 8788)',
      '',
      'Environment:',
      '  CRDTBASE_HTTP_ROOT_DIR, CRDTBASE_HTTP_HOST, CRDTBASE_HTTP_PORT',
    ].join('\n') + '\n',
  );
}

function parseConfig(argv: string[]): Config {
  const config: Config = {
    rootDir: process.env.CRDTBASE_HTTP_ROOT_DIR ?? join(process.cwd(), '.crdtbase-http-server'),
    host: process.env.CRDTBASE_HTTP_HOST ?? '127.0.0.1',
    port: Number.parseInt(process.env.CRDTBASE_HTTP_PORT ?? '8788', 10),
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index]!;
    const value = argv[index + 1];

    if (arg === '--root-dir' && value) {
      config.rootDir = value;
      index += 1;
      continue;
    }

    if (arg === '--host' && value) {
      config.host = value;
      index += 1;
      continue;
    }

    if (arg === '--port' && value) {
      config.port = Number.parseInt(value, 10);
      index += 1;
      continue;
    }

    if (arg === '--help') {
      printUsage();
      process.exit(0);
    }
  }

  if (!Number.isFinite(config.port) || config.port <= 0) {
    throw new Error(`invalid port: ${String(config.port)}`);
  }

  return config;
}

async function main(): Promise<void> {
  const config = parseConfig(process.argv.slice(2));
  const server = new FileReplicatedLogServer(config.rootDir);
  const url = await server.start(config.port, config.host);

  process.stdout.write(`File replicated log server listening at ${url}\n`);
  process.stdout.write(`Root directory: ${config.rootDir}\n`);

  const shutdown = async () => {
    await server.stop();
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
