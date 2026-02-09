import { HttpReplicatedLog } from '../../src/platform/node/httpReplicatedLog';
import { BrowserCrdtClient } from '../../src/platform/browser/browserClient';
import {
  HttpS3PresignProvider,
  PresignedS3ReplicatedLog,
} from '../../src/platform/shared/presignedS3ReplicatedLog';

type BrowserBridgeClient = BrowserCrdtClient;

type CreateHttpClient = {
  clientId: string;
  siteId: string;
  kind: 'http';
  baseUrl: string;
  nowMs: number;
};

type CreateS3PresignClient = {
  clientId: string;
  siteId: string;
  kind: 's3-presign';
  bucket: string;
  prefix: string;
  presignBaseUrl: string;
  presignAuthToken?: string;
  nowMs: number;
};

type CreateClientParams = CreateHttpClient | CreateS3PresignClient;

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
    log: new PresignedS3ReplicatedLog({
      bucket: params.bucket,
      prefix: params.prefix,
      presign: new HttpS3PresignProvider({
        baseUrl: params.presignBaseUrl,
        authToken: params.presignAuthToken,
      }),
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
