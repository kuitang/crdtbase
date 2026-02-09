import { createServer, IncomingMessage, ServerResponse } from 'node:http';
import {
  GetObjectCommand,
  ListObjectsV2Command,
  PutObjectCommand,
  S3Client,
} from '@aws-sdk/client-s3';
import { getSignedUrl } from '@aws-sdk/s3-request-presigner';

type JsonRecord = Record<string, unknown>;

type ServerConfig = {
  host: string;
  port: number;
  endpoint: string;
  region: string;
  forcePathStyle: boolean;
  accessKeyId: string;
  secretAccessKey: string;
  expiresSeconds: number;
  authToken: string | null;
};

function parseArgs(argv: string[]): ServerConfig {
  const defaults = {
    host: process.env.PRESIGN_HOST ?? '127.0.0.1',
    port: Number.parseInt(process.env.PRESIGN_PORT ?? '8787', 10),
    endpoint: process.env.S3_ENDPOINT ?? '',
    region: process.env.S3_REGION ?? 'auto',
    forcePathStyle:
      (process.env.S3_FORCE_PATH_STYLE ?? 'true').toLowerCase() !== 'false',
    accessKeyId: process.env.S3_ACCESS_KEY_ID ?? '',
    secretAccessKey: process.env.S3_SECRET_ACCESS_KEY ?? '',
    expiresSeconds: Number.parseInt(process.env.PRESIGN_EXPIRES_SECONDS ?? '300', 10),
    authToken: process.env.PRESIGN_AUTH_TOKEN ?? null,
  };

  const next = { ...defaults };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index]!;
    const value = argv[index + 1];

    if (arg === '--host' && value) {
      next.host = value;
      index += 1;
      continue;
    }
    if (arg === '--port' && value) {
      next.port = Number.parseInt(value, 10);
      index += 1;
      continue;
    }
    if (arg === '--endpoint' && value) {
      next.endpoint = value;
      index += 1;
      continue;
    }
    if (arg === '--region' && value) {
      next.region = value;
      index += 1;
      continue;
    }
    if (arg === '--force-path-style' && value) {
      next.forcePathStyle = value.toLowerCase() !== 'false';
      index += 1;
      continue;
    }
    if (arg === '--access-key-id' && value) {
      next.accessKeyId = value;
      index += 1;
      continue;
    }
    if (arg === '--secret-access-key' && value) {
      next.secretAccessKey = value;
      index += 1;
      continue;
    }
    if (arg === '--expires-seconds' && value) {
      next.expiresSeconds = Number.parseInt(value, 10);
      index += 1;
      continue;
    }
    if (arg === '--auth-token' && value) {
      next.authToken = value;
      index += 1;
      continue;
    }
    if (arg === '--help') {
      printUsage();
      process.exit(0);
    }
  }

  if (!next.endpoint) {
    throw new Error('missing S3 endpoint (--endpoint or S3_ENDPOINT)');
  }
  if (!next.accessKeyId || !next.secretAccessKey) {
    throw new Error('missing S3 credentials (--access-key-id/--secret-access-key or env vars)');
  }
  if (!Number.isFinite(next.port) || next.port <= 0) {
    throw new Error(`invalid port: ${String(next.port)}`);
  }
  if (!Number.isFinite(next.expiresSeconds) || next.expiresSeconds <= 0) {
    throw new Error(`invalid expires seconds: ${String(next.expiresSeconds)}`);
  }

  return next;
}

function printUsage(): void {
  process.stdout.write(
    [
      'Usage: npm run presign:server -- [options]',
      '',
      'Options:',
      '  --host <host>                    (default: 127.0.0.1)',
      '  --port <port>                    (default: 8787)',
      '  --endpoint <url>                 S3/MinIO endpoint',
      '  --region <region>                (default: auto)',
      '  --force-path-style <true|false>  (default: true)',
      '  --access-key-id <id>',
      '  --secret-access-key <secret>',
      '  --expires-seconds <n>            (default: 300)',
      '  --auth-token <token>             Optional bearer token required by this server',
      '',
      'Env equivalents: PRESIGN_HOST, PRESIGN_PORT, S3_ENDPOINT, S3_REGION,',
      'S3_FORCE_PATH_STYLE, S3_ACCESS_KEY_ID, S3_SECRET_ACCESS_KEY,',
      'PRESIGN_EXPIRES_SECONDS, PRESIGN_AUTH_TOKEN',
    ].join('\n') + '\n',
  );
}

function setCors(response: ServerResponse): void {
  response.setHeader('access-control-allow-origin', '*');
  response.setHeader('access-control-allow-methods', 'GET,POST,OPTIONS');
  response.setHeader('access-control-allow-headers', 'content-type,authorization');
}

function writeJson(response: ServerResponse, statusCode: number, body: JsonRecord): void {
  setCors(response);
  const raw = JSON.stringify(body);
  response.statusCode = statusCode;
  response.setHeader('content-type', 'application/json; charset=utf-8');
  response.setHeader('content-length', Buffer.byteLength(raw));
  response.end(raw);
}

function writeError(response: ServerResponse, statusCode: number, message: string): void {
  writeJson(response, statusCode, { error: message });
}

async function readJsonBody<T>(request: IncomingMessage): Promise<T> {
  const chunks: Buffer[] = [];
  for await (const chunk of request) {
    chunks.push(Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk));
  }
  const raw = Buffer.concat(chunks).toString('utf8');
  if (raw.length === 0) {
    throw new Error('request body is empty');
  }
  try {
    return JSON.parse(raw) as T;
  } catch {
    throw new Error(`invalid JSON body: ${raw}`);
  }
}

function requireString(value: unknown, field: string): string {
  if (typeof value !== 'string' || value.length === 0) {
    throw new Error(`expected non-empty string field '${field}'`);
  }
  return value;
}

function optionalString(value: unknown): string | undefined {
  if (value === undefined || value === null) {
    return undefined;
  }
  if (typeof value !== 'string') {
    throw new Error('expected optional string');
  }
  return value;
}

async function main(): Promise<void> {
  const config = parseArgs(process.argv.slice(2));

  const s3 = new S3Client({
    endpoint: config.endpoint,
    region: config.region,
    forcePathStyle: config.forcePathStyle,
    credentials: {
      accessKeyId: config.accessKeyId,
      secretAccessKey: config.secretAccessKey,
    },
  });

  const server = createServer(async (request, response) => {
    try {
      if (!request.url) {
        writeError(response, 400, 'missing request URL');
        return;
      }

      if (request.method === 'OPTIONS') {
        setCors(response);
        response.statusCode = 204;
        response.end();
        return;
      }

      if (config.authToken !== null) {
        const auth = request.headers.authorization ?? '';
        if (auth !== `Bearer ${config.authToken}`) {
          writeError(response, 401, 'unauthorized');
          return;
        }
      }

      const url = new URL(request.url, `http://${request.headers.host ?? 'localhost'}`);

      if (request.method === 'GET' && url.pathname === '/health') {
        writeJson(response, 200, { ok: true });
        return;
      }

      if (request.method !== 'POST') {
        writeError(response, 404, 'not found');
        return;
      }

      if (url.pathname === '/v1/presign/list-objects') {
        const body = await readJsonBody<{
          bucket?: unknown;
          prefix?: unknown;
          continuationToken?: unknown;
          delimiter?: unknown;
        }>(request);

        const bucket = requireString(body.bucket, 'bucket');
        const prefix = requireString(body.prefix, 'prefix');
        const continuationToken = optionalString(body.continuationToken);
        const delimiter = optionalString(body.delimiter);

        const command = new ListObjectsV2Command({
          Bucket: bucket,
          Prefix: prefix,
          ContinuationToken: continuationToken,
          Delimiter: delimiter,
        });
        const signedUrl = await getSignedUrl(s3, command, {
          expiresIn: config.expiresSeconds,
        });

        writeJson(response, 200, {
          method: 'GET',
          url: signedUrl,
        });
        return;
      }

      if (url.pathname === '/v1/presign/get-object') {
        const body = await readJsonBody<{ bucket?: unknown; key?: unknown }>(request);
        const bucket = requireString(body.bucket, 'bucket');
        const key = requireString(body.key, 'key');

        const command = new GetObjectCommand({
          Bucket: bucket,
          Key: key,
        });
        const signedUrl = await getSignedUrl(s3, command, {
          expiresIn: config.expiresSeconds,
        });

        writeJson(response, 200, {
          method: 'GET',
          url: signedUrl,
        });
        return;
      }

      if (url.pathname === '/v1/presign/put-object') {
        const body = await readJsonBody<{
          bucket?: unknown;
          key?: unknown;
          ifNoneMatch?: unknown;
          contentType?: unknown;
        }>(request);
        const bucket = requireString(body.bucket, 'bucket');
        const key = requireString(body.key, 'key');
        const ifNoneMatch = optionalString(body.ifNoneMatch);
        const contentType = optionalString(body.contentType);

        const command = new PutObjectCommand({
          Bucket: bucket,
          Key: key,
          IfNoneMatch: ifNoneMatch,
          ContentType: contentType,
        });
        const signedUrl = await getSignedUrl(s3, command, {
          expiresIn: config.expiresSeconds,
        });

        const headers: Record<string, string> = {};
        if (ifNoneMatch) {
          headers['if-none-match'] = ifNoneMatch;
        }
        if (contentType) {
          headers['content-type'] = contentType;
        }

        writeJson(response, 200, {
          method: 'PUT',
          url: signedUrl,
          headers,
        });
        return;
      }

      writeError(response, 404, 'not found');
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      writeError(response, 400, message);
    }
  });

  await new Promise<void>((resolve, reject) => {
    server.once('error', reject);
    server.listen(config.port, config.host, () => resolve());
  });

  process.stdout.write(
    `S3 presign server listening on http://${config.host}:${config.port} (endpoint=${config.endpoint})\n`,
  );
}

main().catch((error) => {
  process.stderr.write(`${error instanceof Error ? error.message : String(error)}\n`);
  process.exitCode = 1;
});
