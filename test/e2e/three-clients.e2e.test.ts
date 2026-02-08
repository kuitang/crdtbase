import { execFile as execFileWithCallback } from 'node:child_process';
import { mkdtemp, readdir, rm, stat } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { promisify } from 'node:util';
import { afterEach, describe, expect, it } from 'vitest';
import { FileReplicatedLogServer } from '../../src/backend/fileLogServer';
import { HttpReplicatedLog } from '../../src/platform/node/httpReplicatedLog';
import { NodeCrdtClient } from '../../src/platform/node/nodeClient';

const execFile = promisify(execFileWithCallback);

describe('Filesystem SQL end-to-end sync', () => {
  let server: FileReplicatedLogServer | null = null;
  let tempRoot: string | null = null;

  afterEach(async () => {
    if (server) {
      await server.stop();
      server = null;
    }
    if (tempRoot) {
      await rm(tempRoot, { recursive: true, force: true });
      tempRoot = null;
    }
  });

  it('syncs 3 clients via SQL with local/server .bin files and CLI dump', async () => {
    tempRoot = await mkdtemp(join(tmpdir(), 'crdtbase-e2e-'));
    const serverDir = join(tempRoot, 'server');
    const clientADir = join(tempRoot, 'client-a');
    const clientBDir = join(tempRoot, 'client-b');
    const clientCDir = join(tempRoot, 'client-c');

    server = new FileReplicatedLogServer(serverDir);
    const baseUrl = await server.start();

    const logA = new HttpReplicatedLog(baseUrl);
    const logB = new HttpReplicatedLog(baseUrl);
    const logC = new HttpReplicatedLog(baseUrl);

    const clientA = await NodeCrdtClient.open({
      siteId: 'site-a',
      log: logA,
      dataDir: clientADir,
      now: () => 1_000,
    });
    const clientB = await NodeCrdtClient.open({
      siteId: 'site-b',
      log: logB,
      dataDir: clientBDir,
      now: () => 2_000,
    });
    const clientC = await NodeCrdtClient.open({
      siteId: 'site-c',
      log: logC,
      dataDir: clientCDir,
      now: () => 3_000,
    });

    const createTableSql = [
      'CREATE TABLE tasks (',
      'id STRING PRIMARY KEY,',
      'title LWW<STRING>,',
      'points COUNTER,',
      'tags SET<STRING>,',
      'status REGISTER<STRING>',
      ')',
    ].join(' ');
    await Promise.all([
      clientA.exec(createTableSql),
      clientB.exec(createTableSql),
      clientC.exec(createTableSql),
    ]);

    await clientA.exec(
      "INSERT INTO tasks (id, title, points, tags, status) VALUES ('t1', 'from-a', 0, 'alpha', 'open');",
    );
    await clientA.sync();
    await clientB.pull();
    await clientC.pull();

    await clientB.exec("UPDATE tasks SET title = 'from-b', status = 'review' WHERE id = 't1';");
    await clientB.exec('INC tasks.points BY 3 WHERE id = \'t1\';');
    await clientB.exec("ADD 'beta' TO tasks.tags WHERE id = 't1';");

    await clientC.exec("UPDATE tasks SET title = 'from-c' WHERE id = 't1';");
    await clientC.exec('INC tasks.points BY 5 WHERE id = \'t1\';');
    await clientC.exec("ADD 'gamma' TO tasks.tags WHERE id = 't1';");

    await clientB.push();
    await clientC.push();
    await clientA.pull();
    await clientB.pull();
    await clientC.pull();

    await clientB.exec("REMOVE 'alpha' FROM tasks.tags WHERE id = 't1';");
    await clientB.push();
    await clientA.pull();
    await clientC.pull();

    const querySql = "SELECT * FROM tasks WHERE id = 't1';";
    const [rowsA, rowsB, rowsC] = await Promise.all([
      clientA.query(querySql),
      clientB.query(querySql),
      clientC.query(querySql),
    ]);

    expect(rowsA).toEqual(rowsB);
    expect(rowsB).toEqual(rowsC);
    expect(rowsA).toHaveLength(1);

    const row = rowsA[0]!;
    expect(row.id).toBe('t1');
    expect(row.title).toBe('from-c');
    expect(row.points).toBe(8);
    expect(row.status).toEqual(['open', 'review']);
    expect(new Set(row.tags as string[])).toEqual(new Set(['beta', 'gamma']));

    expect(await logA.getHead('site-a')).toBe(1);
    expect(await logA.getHead('site-b')).toBe(2);
    expect(await logA.getHead('site-c')).toBe(1);

    for (const clientDir of [clientADir, clientBDir, clientCDir]) {
      await stat(join(clientDir, 'schema.bin'));
      await stat(join(clientDir, 'state.bin'));
      await stat(join(clientDir, 'pending.bin'));
      await stat(join(clientDir, 'sync.bin'));
    }

    const serverSiteAFiles = await readdir(join(serverDir, 'logs', 'site-a'));
    expect(serverSiteAFiles).toEqual(['0000000001.bin']);
    await stat(join(serverDir, 'logs', 'site-b', '0000000001.bin'));
    await stat(join(serverDir, 'logs', 'site-b', '0000000002.bin'));
    await stat(join(serverDir, 'logs', 'site-c', '0000000001.bin'));

    const dumpedPath = join(serverDir, 'logs', 'site-b', '0000000001.bin');
    const { stdout } = await execFile('node', ['cli.mjs', 'dump', dumpedPath], {
      cwd: process.cwd(),
    });
    const parsed = JSON.parse(stdout) as { siteId: string; seq: number; ops: unknown[] };
    expect(parsed.siteId).toBe('site-b');
    expect(parsed.seq).toBe(1);
    expect(Array.isArray(parsed.ops)).toBe(true);
    expect(parsed.ops.length).toBe(4);
  });
});
