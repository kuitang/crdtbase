import type { S3ClientConfig } from '@aws-sdk/client-s3';
import { parseSql } from '../../core/sql';
import { BrowserCrdtClient } from '../../platform/browser/browserClient';
import { S3ReplicatedLog } from '../../backend/s3ReplicatedLog';
import { HttpReplicatedLog } from '../../platform/node/httpReplicatedLog';
import { formatRowsAsTable } from '../tableFormat';

type BackendMode = 'http' | 's3';

type ParsedS3Config = {
  bucket: string;
  prefix: string;
  endpoint: string;
  region: string;
  accessKeyId: string;
  secretAccessKey: string;
  sessionToken?: string;
  forcePathStyle: boolean;
};

const EXAMPLES = [
  'CREATE TABLE tasks (id STRING PRIMARY KEY, title LWW<STRING>, points COUNTER, tags SET<STRING>, status REGISTER<STRING>);',
  "INSERT INTO tasks (id, title, points, tags, status) VALUES ('t1', 'hello', 0, 'alpha', 'open');",
  "INC tasks.points BY 2 WHERE id = 't1';",
  "ADD 'beta' TO tasks.tags WHERE id = 't1';",
  "UPDATE tasks SET title = 'from-browser' WHERE id = 't1';",
  'SELECT * FROM tasks;',
];

const backendSelect = document.getElementById('backend') as HTMLSelectElement;
const siteIdInput = document.getElementById('site-id') as HTMLInputElement;
const httpBaseUrlInput = document.getElementById('http-base-url') as HTMLInputElement;
const s3ConfigInput = document.getElementById('s3-config') as HTMLTextAreaElement;

const httpFields = document.getElementById('http-fields') as HTMLDivElement;
const s3Fields = document.getElementById('s3-fields') as HTMLDivElement;

const connectBtn = document.getElementById('connect-btn') as HTMLButtonElement;
const statusEl = document.getElementById('status') as HTMLSpanElement;

const sqlInput = document.getElementById('sql-input') as HTMLTextAreaElement;
const runBtn = document.getElementById('run-btn') as HTMLButtonElement;
const pushBtn = document.getElementById('push-btn') as HTMLButtonElement;
const pullBtn = document.getElementById('pull-btn') as HTMLButtonElement;
const syncBtn = document.getElementById('sync-btn') as HTMLButtonElement;
const output = document.getElementById('output') as HTMLPreElement;
const exampleList = document.getElementById('example-list') as HTMLUListElement;

let client: BrowserCrdtClient | null = null;
let opCounter = 0;

function nowCounter(): number {
  opCounter += 1;
  return Date.now() + opCounter;
}

function setStatus(text: string): void {
  statusEl.textContent = text;
}

function appendOutput(text: string): void {
  const prefix = output.textContent && output.textContent.length > 0 ? '\n' : '';
  output.textContent = `${output.textContent ?? ''}${prefix}${text}`;
  output.scrollTop = output.scrollHeight;
}

function setActionsEnabled(enabled: boolean): void {
  runBtn.disabled = !enabled;
  pushBtn.disabled = !enabled;
  pullBtn.disabled = !enabled;
  syncBtn.disabled = !enabled;
}

function disconnectActiveSession(reason: string): void {
  if (!client) {
    return;
  }
  client = null;
  setActionsEnabled(false);
  setStatus('Disconnected');
  appendOutput(`disconnected: ${reason}`);
}

function currentBackend(): BackendMode {
  return backendSelect.value === 's3' ? 's3' : 'http';
}

function refreshBackendVisibility(): void {
  const mode = currentBackend();
  httpFields.classList.toggle('hidden', mode !== 'http');
  s3Fields.classList.toggle('hidden', mode !== 's3');
}

function normalizeConfigKey(key: string): string {
  return key.toLowerCase().replace(/[^a-z0-9]/gu, '');
}

function parseBooleanValue(raw: string, label: string): boolean {
  const value = raw.trim().toLowerCase();
  if (value === '1' || value === 'true' || value === 'yes' || value === 'on') {
    return true;
  }
  if (value === '0' || value === 'false' || value === 'no' || value === 'off') {
    return false;
  }
  throw new Error(`invalid ${label}: '${raw}'`);
}

function unquoteValue(raw: string): string {
  if (raw.length >= 2 && raw.startsWith('"') && raw.endsWith('"')) {
    return JSON.parse(raw) as string;
  }
  if (raw.length >= 2 && raw.startsWith("'") && raw.endsWith("'")) {
    return raw.slice(1, -1).replace(/\\'/gu, "'");
  }
  return raw;
}

function parseLooseKeyValueMap(raw: string): Record<string, string> {
  const entries: Record<string, string> = {};
  const pattern = /([A-Za-z_][A-Za-z0-9_.-]*)\s*=\s*("(?:[^"\\]|\\.)*"|'(?:[^'\\]|\\.)*'|[^\s]+)/gu;
  let match: RegExpExecArray | null;
  while ((match = pattern.exec(raw)) !== null) {
    const key = normalizeConfigKey(match[1]!);
    const valueToken = match[2]!.replace(/[;,]+$/u, '');
    entries[key] = unquoteValue(valueToken);
  }
  if (Object.keys(entries).length === 0) {
    throw new Error('S3 config must be JSON or include KEY=value pairs');
  }
  return entries;
}

function asNormalizedStringMap(value: unknown): Record<string, string> {
  if (typeof value !== 'object' || value === null || Array.isArray(value)) {
    throw new Error('S3 JSON config must be an object');
  }
  const out: Record<string, string> = {};
  for (const [key, inner] of Object.entries(value as Record<string, unknown>)) {
    const normalized = normalizeConfigKey(key);
    if (inner === null || inner === undefined) {
      continue;
    }
    out[normalized] = String(inner);
  }
  return out;
}

function resolveValue(
  map: Record<string, string>,
  aliases: string[],
): string | undefined {
  for (const alias of aliases) {
    const value = map[normalizeConfigKey(alias)];
    if (value !== undefined && value.trim().length > 0) {
      return value.trim();
    }
  }
  return undefined;
}

function parseS3Config(raw: string): ParsedS3Config {
  const trimmed = raw.trim();
  if (trimmed.length === 0) {
    throw new Error('S3 config is required');
  }

  let values: Record<string, string>;
  if (trimmed.startsWith('{')) {
    let parsed: unknown;
    try {
      parsed = JSON.parse(trimmed);
    } catch {
      throw new Error('invalid S3 JSON config');
    }
    values = asNormalizedStringMap(parsed);
  } else {
    values = parseLooseKeyValueMap(trimmed);
  }

  const bucket = resolveValue(values, ['bucket', 'bucket_name', 's3_bucket']);
  const prefix = resolveValue(values, ['prefix', 's3_prefix']) ?? 'deltas';
  const endpoint = resolveValue(values, ['endpoint', 's3_endpoint', 'aws_endpoint_url_s3', 'aws_endpoint_url']);
  const region = resolveValue(values, ['region', 's3_region', 'aws_region', 'aws_default_region']) ?? 'auto';
  const accessKeyId = resolveValue(values, [
    'accessKeyId',
    'access_key_id',
    's3_access_key_id',
    'aws_access_key_id',
  ]);
  const secretAccessKey = resolveValue(values, [
    'secretAccessKey',
    'secret_access_key',
    's3_secret_access_key',
    'aws_secret_access_key',
  ]);
  const sessionToken = resolveValue(values, [
    'sessionToken',
    'session_token',
    's3_session_token',
    'aws_session_token',
  ]);
  const forcePathStyleRaw = resolveValue(values, ['forcePathStyle', 'force_path_style', 's3_force_path_style']);
  const forcePathStyle =
    forcePathStyleRaw === undefined
      ? false
      : parseBooleanValue(forcePathStyleRaw, 'forcePathStyle');

  if (!bucket) {
    throw new Error('S3 config missing bucket');
  }
  if (!endpoint) {
    throw new Error('S3 config missing endpoint');
  }
  if (!accessKeyId) {
    throw new Error('S3 config missing accessKeyId');
  }
  if (!secretAccessKey) {
    throw new Error('S3 config missing secretAccessKey');
  }

  try {
    new URL(endpoint);
  } catch {
    throw new Error(`invalid S3 endpoint URL '${endpoint}'`);
  }

  return {
    bucket,
    prefix,
    endpoint,
    region,
    accessKeyId,
    secretAccessKey,
    sessionToken,
    forcePathStyle,
  };
}

async function connect(): Promise<void> {
  // Always start a fresh in-memory client session on connect.
  client = null;
  setActionsEnabled(false);

  const mode = currentBackend();
  const siteId = siteIdInput.value.trim();
  if (!siteId) {
    throw new Error('site id is required');
  }

  if (mode === 'http') {
    const baseUrl = httpBaseUrlInput.value.trim();
    if (!baseUrl) {
      throw new Error('HTTP base URL is required');
    }

    client = await BrowserCrdtClient.open({
      siteId,
      log: new HttpReplicatedLog(baseUrl),
      now: nowCounter,
    });

    setActionsEnabled(true);
    setStatus(`Connected: HTTP (${baseUrl})`);
    appendOutput(`connected site='${siteId}' backend=http baseUrl='${baseUrl}'`);
    return;
  }

  const config = parseS3Config(s3ConfigInput.value);
  const clientConfig: S3ClientConfig = {
    endpoint: config.endpoint,
    region: config.region,
    forcePathStyle: config.forcePathStyle,
    credentials: {
      accessKeyId: config.accessKeyId,
      secretAccessKey: config.secretAccessKey,
      ...(config.sessionToken ? { sessionToken: config.sessionToken } : {}),
    },
  };

  client = await BrowserCrdtClient.open({
    siteId,
    log: new S3ReplicatedLog({
      bucket: config.bucket,
      prefix: config.prefix,
      clientConfig,
    }),
    now: nowCounter,
  });

  setActionsEnabled(true);
  setStatus(`Connected: S3 (${config.bucket}/${config.prefix})`);
  appendOutput(
    `connected site='${siteId}' backend=s3 bucket='${config.bucket}' prefix='${config.prefix}' endpoint='${config.endpoint}'`,
  );
}

async function runSql(): Promise<void> {
  if (!client) {
    throw new Error('connect first');
  }

  const sql = sqlInput.value.trim();
  if (!sql) {
    return;
  }

  const statement = parseSql(sql);
  if (statement.kind === 'select') {
    const rows = await client.query(sql);
    appendOutput(formatRowsAsTable(rows));
    return;
  }

  await client.exec(sql);
  appendOutput('ok');
}

async function runClientAction(action: '.push' | '.pull' | '.sync'): Promise<void> {
  if (!client) {
    throw new Error('connect first');
  }

  if (action === '.push') {
    await client.push();
  } else if (action === '.pull') {
    await client.pull();
  } else {
    await client.sync();
  }

  appendOutput(`ok ${action}`);
}

function wireExamples(): void {
  for (const example of EXAMPLES) {
    const item = document.createElement('li');
    const button = document.createElement('button');
    button.type = 'button';
    button.textContent = example;
    button.addEventListener('click', () => {
      sqlInput.value = example;
      sqlInput.focus();
    });
    item.appendChild(button);
    exampleList.appendChild(item);
  }
}

async function withUiGuard(task: () => Promise<void>): Promise<void> {
  connectBtn.disabled = true;
  runBtn.disabled = true;
  pushBtn.disabled = true;
  pullBtn.disabled = true;
  syncBtn.disabled = true;

  try {
    await task();
  } catch (error) {
    appendOutput(`error: ${error instanceof Error ? error.message : String(error)}`);
  } finally {
    connectBtn.disabled = false;
    setActionsEnabled(client !== null);
  }
}

backendSelect.addEventListener('change', refreshBackendVisibility);
backendSelect.addEventListener('change', () => {
  disconnectActiveSession('backend changed; reconnect required');
});

for (const field of [siteIdInput, httpBaseUrlInput, s3ConfigInput]) {
  field.addEventListener('change', () => {
    disconnectActiveSession('connection settings changed; reconnect required');
  });
}

connectBtn.addEventListener('click', () => {
  void withUiGuard(connect);
});
runBtn.addEventListener('click', () => {
  void withUiGuard(runSql);
});
pushBtn.addEventListener('click', () => {
  void withUiGuard(() => runClientAction('.push'));
});
pullBtn.addEventListener('click', () => {
  void withUiGuard(() => runClientAction('.pull'));
});
syncBtn.addEventListener('click', () => {
  void withUiGuard(() => runClientAction('.sync'));
});

sqlInput.addEventListener('keydown', (event) => {
  if (event.key === 'Enter' && (event.metaKey || event.ctrlKey)) {
    event.preventDefault();
    void withUiGuard(runSql);
  }
});

refreshBackendVisibility();
wireExamples();
setStatus('Disconnected');
appendOutput('Ready. Connect, then run SQL. Use Ctrl/Cmd+Enter to execute.');
