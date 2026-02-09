import { HttpReplicatedLog } from '../../src/platform/node/httpReplicatedLog';
import { BrowserCrdtClient } from '../../src/platform/browser/browserClient';
import { S3ReplicatedLog } from '../../src/backend/s3ReplicatedLog';

type BrowserBridgeClient = BrowserCrdtClient;

type CreateHttpClient = {
  clientId: string;
  siteId: string;
  kind: 'http';
  baseUrl: string;
  nowMs: number;
};

type CreateS3Client = {
  clientId: string;
  siteId: string;
  kind: 's3';
  bucket: string;
  prefix: string;
  endpoint: string;
  region: string;
  accessKeyId: string;
  secretAccessKey: string;
  sessionToken?: string;
  forcePathStyle: boolean;
  nowMs: number;
};

type CreateClientParams = CreateHttpClient | CreateS3Client;

const clients = new Map<string, BrowserBridgeClient>();

function getClient(clientId: string): BrowserBridgeClient {
  const client = clients.get(clientId);
  if (!client) {
    throw new Error(`unknown browser client '${clientId}'`);
  }
  return client;
}

async function createClient(params: CreateClientParams): Promise<void> {
  let tick = params.nowMs;
  const now = (): number => {
    tick += 1;
    return tick;
  };

  if (params.kind === 'http') {
    const client = await BrowserCrdtClient.open({
      siteId: params.siteId,
      log: new HttpReplicatedLog(params.baseUrl),
      now,
    });
    clients.set(params.clientId, client);
    return;
  }

  const client = await BrowserCrdtClient.open({
    siteId: params.siteId,
    log: new S3ReplicatedLog({
      bucket: params.bucket,
      prefix: params.prefix,
      clientConfig: {
        endpoint: params.endpoint,
        region: params.region,
        forcePathStyle: params.forcePathStyle,
        credentials: {
          accessKeyId: params.accessKeyId,
          secretAccessKey: params.secretAccessKey,
          ...(params.sessionToken ? { sessionToken: params.sessionToken } : {}),
        },
      },
    }),
    now,
  });
  clients.set(params.clientId, client);
}

const bridge = {
  async createClient(params: CreateClientParams): Promise<void> {
    await createClient(params);
  },

  async exec(clientId: string, sql: string): Promise<void> {
    await getClient(clientId).exec(sql);
  },

  async query(clientId: string, sql: string): Promise<Record<string, unknown>[]> {
    return getClient(clientId).query(sql);
  },

  async push(clientId: string): Promise<void> {
    await getClient(clientId).push();
  },

  async pull(clientId: string): Promise<void> {
    await getClient(clientId).pull();
  },

  async sync(clientId: string): Promise<void> {
    await getClient(clientId).sync();
  },

  async destroy(clientId: string): Promise<void> {
    clients.delete(clientId);
  },
};

(globalThis as {
  __crdtbaseBrowserBridge?: typeof bridge;
}).__crdtbaseBrowserBridge = bridge;
