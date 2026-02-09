import { build } from 'esbuild';
import { Browser, BrowserContext, Page, chromium } from 'playwright-core';
import type { E2eClientAdapter } from './orchestrator';

type BridgeApi = {
  createClient(params: unknown): Promise<void>;
  exec(clientId: string, sql: string): Promise<void>;
  query(clientId: string, sql: string): Promise<Record<string, unknown>[]>;
  push(clientId: string): Promise<void>;
  pull(clientId: string): Promise<void>;
  sync(clientId: string): Promise<void>;
  destroy(clientId: string): Promise<void>;
};

let cachedBundle: string | null = null;
const initializedContexts = new WeakSet<BrowserContext>();

async function bridgeExists(page: Page): Promise<boolean> {
  return page.evaluate(() => {
    return Boolean((globalThis as { __crdtbaseBrowserBridge?: unknown }).__crdtbaseBrowserBridge);
  });
}

async function callBridge<T>(page: Page, method: keyof BridgeApi, args: unknown[]): Promise<T> {
  return page.evaluate(
    async ({ method, args }) => {
      const bridge = (globalThis as { __crdtbaseBrowserBridge?: BridgeApi }).__crdtbaseBrowserBridge;
      if (!bridge) {
        throw new Error('browser bridge is not loaded');
      }
      const fn = bridge[method] as (...values: unknown[]) => Promise<T>;
      return fn(...args);
    },
    { method, args },
  );
}

export async function buildBrowserBridgeBundle(): Promise<string> {
  if (cachedBundle !== null) {
    return cachedBundle;
  }

  const result = await build({
    entryPoints: ['test/e2e/browserBridge.entry.ts'],
    bundle: true,
    format: 'iife',
    platform: 'browser',
    target: ['es2022'],
    write: false,
    define: {
      'process.env.NODE_ENV': '"test"',
      global: 'globalThis',
    },
    logLevel: 'silent',
  });

  const text = result.outputFiles[0]?.text;
  if (!text) {
    throw new Error('failed to build browser bridge bundle');
  }

  cachedBundle = text;
  return text;
}

export async function launchPlaywrightBrowser(): Promise<Browser> {
  const executablePath = process.env.PLAYWRIGHT_CHROMIUM_PATH ?? '/usr/bin/google-chrome';
  return chromium.launch({
    executablePath,
    headless: true,
    args: ['--no-sandbox', '--disable-dev-shm-usage'],
  });
}

class PlaywrightClientAdapter implements E2eClientAdapter {
  constructor(
    public readonly siteId: string,
    private readonly page: Page,
    private readonly clientId: string,
  ) {}

  async exec(sql: string): Promise<void> {
    await callBridge<void>(this.page, 'exec', [this.clientId, sql]);
  }

  async query(sql: string): Promise<Record<string, unknown>[]> {
    return callBridge<Record<string, unknown>[]>(this.page, 'query', [this.clientId, sql]);
  }

  async push(): Promise<void> {
    await callBridge<void>(this.page, 'push', [this.clientId]);
  }

  async pull(): Promise<void> {
    await callBridge<void>(this.page, 'pull', [this.clientId]);
  }

  async sync(): Promise<void> {
    await callBridge<void>(this.page, 'sync', [this.clientId]);
  }

  async destroy(): Promise<void> {
    await callBridge<void>(this.page, 'destroy', [this.clientId]);
  }
}

async function preparePage(params: {
  context: BrowserContext;
  originUrl: string;
  bridgeBundle: string;
}): Promise<Page> {
  if (!initializedContexts.has(params.context)) {
    await params.context.addInitScript({ content: params.bridgeBundle });
    initializedContexts.add(params.context);
  }

  const page = await params.context.newPage();
  await page.goto(params.originUrl, { waitUntil: 'domcontentloaded' });

  if (!(await bridgeExists(page))) {
    throw new Error('browser bridge failed to load on page');
  }
  return page;
}

export async function createBrowserHttpAdapter(params: {
  context: BrowserContext;
  bridgeBundle: string;
  siteId: string;
  clientId: string;
  baseUrl: string;
  nowMs: number;
}): Promise<PlaywrightClientAdapter> {
  const page = await preparePage({
    context: params.context,
    originUrl: params.baseUrl,
    bridgeBundle: params.bridgeBundle,
  });

  await callBridge<void>(page, 'createClient', [
    {
      clientId: params.clientId,
      siteId: params.siteId,
      kind: 'http',
      baseUrl: params.baseUrl,
      nowMs: params.nowMs,
    },
  ]);

  return new PlaywrightClientAdapter(params.siteId, page, params.clientId);
}

export async function createBrowserS3PresignAdapter(params: {
  context: BrowserContext;
  bridgeBundle: string;
  siteId: string;
  clientId: string;
  pageUrl: string;
  bucket: string;
  prefix: string;
  presignBaseUrl: string;
  presignAuthToken?: string;
  nowMs: number;
}): Promise<PlaywrightClientAdapter> {
  const page = await preparePage({
    context: params.context,
    originUrl: params.pageUrl,
    bridgeBundle: params.bridgeBundle,
  });

  await callBridge<void>(page, 'createClient', [
    {
      clientId: params.clientId,
      siteId: params.siteId,
      kind: 's3-presign',
      bucket: params.bucket,
      prefix: params.prefix,
      presignBaseUrl: params.presignBaseUrl,
      presignAuthToken: params.presignAuthToken,
      nowMs: params.nowMs,
    },
  ]);

  return new PlaywrightClientAdapter(params.siteId, page, params.clientId);
}

export async function destroyBrowserAdapters(
  adapters: Array<PlaywrightClientAdapter | null>,
): Promise<void> {
  await Promise.all(
    adapters
      .filter((adapter): adapter is PlaywrightClientAdapter => adapter !== null)
      .map(async (adapter) => {
        await adapter.destroy().catch(() => undefined);
      }),
  );
}
