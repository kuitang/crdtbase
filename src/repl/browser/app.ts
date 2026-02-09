import { parseSql } from '../../core/sql';
import { BrowserCrdtClient } from '../../platform/browser/browserClient';
import { HttpReplicatedLog } from '../../platform/node/httpReplicatedLog';
import {
  HttpS3PresignProvider,
  PresignedS3ReplicatedLog,
} from '../../platform/shared/presignedS3ReplicatedLog';
import { formatRowsAsTable } from '../tableFormat';

type BackendMode = 'http' | 's3-presign';

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
const s3BucketInput = document.getElementById('s3-bucket') as HTMLInputElement;
const s3PrefixInput = document.getElementById('s3-prefix') as HTMLInputElement;
const presignBaseUrlInput = document.getElementById('presign-base-url') as HTMLInputElement;
const presignAuthTokenInput = document.getElementById('presign-auth-token') as HTMLInputElement;

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
  return backendSelect.value === 's3-presign' ? 's3-presign' : 'http';
}

function refreshBackendVisibility(): void {
  const mode = currentBackend();
  httpFields.classList.toggle('hidden', mode !== 'http');
  s3Fields.classList.toggle('hidden', mode !== 's3-presign');
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

  const bucket = s3BucketInput.value.trim();
  const prefix = s3PrefixInput.value.trim() || 'deltas';
  const presignBaseUrl = presignBaseUrlInput.value.trim();
  const authToken = presignAuthTokenInput.value.trim();

  if (!bucket) {
    throw new Error('bucket is required for S3 backend');
  }
  if (!presignBaseUrl) {
    throw new Error('pre-sign service URL is required for S3 backend');
  }

  client = await BrowserCrdtClient.open({
    siteId,
    log: new PresignedS3ReplicatedLog({
      bucket,
      prefix,
      presign: new HttpS3PresignProvider({
        baseUrl: presignBaseUrl,
        authToken: authToken.length > 0 ? authToken : undefined,
      }),
    }),
    now: nowCounter,
  });

  setActionsEnabled(true);
  setStatus(`Connected: S3 pre-sign (${bucket}/${prefix})`);
  appendOutput(
    `connected site='${siteId}' backend=s3-presign bucket='${bucket}' prefix='${prefix}' presign='${presignBaseUrl}'`,
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

for (const field of [
  siteIdInput,
  httpBaseUrlInput,
  s3BucketInput,
  s3PrefixInput,
  presignBaseUrlInput,
  presignAuthTokenInput,
]) {
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
