import { execFile as execFileWithCallback } from 'node:child_process';
import { mkdir, mkdtemp, readFile, readdir, rm, stat, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { promisify } from 'node:util';
import { afterEach, describe, expect, it } from 'vitest';
import { FileReplicatedLogServer } from '../../src/backend/fileLogServer';
import { decodeBin } from '../../src/core/encoding';
import { SqlSchema } from '../../src/core/sql';
import { HttpReplicatedLog } from '../../src/platform/node/httpReplicatedLog';
import { compactReplicatedLog } from '../../src/platform/node/compactor';
import { HttpSnapshotStore } from '../../src/platform/node/httpSnapshotStore';
import { NodeCrdtClient } from '../../src/platform/node/nodeClient';
import { E2E_SCHEDULES, TASK_QUERY_SQL, runThreeClientConvergenceScenario } from './orchestrator';

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

  it.each(E2E_SCHEDULES)(
    'syncs 3 clients via SQL with local/server .bin files and CLI dump [$name]',
    async (schedule) => {
    tempRoot = await mkdtemp(join(tmpdir(), 'crdtbase-e2e-'));
    const serverDir = join(tempRoot, 'server');
    const clientADir = join(tempRoot, 'client-a');
    const clientBDir = join(tempRoot, 'client-b');
    const clientCDir = join(tempRoot, 'client-c');
    const clientDDir = join(tempRoot, 'client-d');

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

    const result = await runThreeClientConvergenceScenario({
      clients: {
        'site-a': clientA,
        'site-b': clientB,
        'site-c': clientC,
      },
      schedule,
    });
    const rowsA = result.rowsBySite['site-a'];
    const rowsB = result.rowsBySite['site-b'];
    const rowsC = result.rowsBySite['site-c'];
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

    const schemaBytes = await readFile(join(clientADir, 'schema.bin'));
    const schema = decodeBin<SqlSchema>(schemaBytes);
    const snapshots = new HttpSnapshotStore(baseUrl);
    const compaction = await compactReplicatedLog({
      log: logA,
      schema,
      snapshots,
    });

    expect(compaction.applied).toBe(true);
    expect(compaction.opsRead).toBe(12);
    expect(compaction.manifest.sites_compacted).toEqual({
      'site-a': 1,
      'site-b': 2,
      'site-c': 1,
    });
    expect(compaction.manifest.segments).toHaveLength(1);

    const snapshotsDir = join(serverDir, 'snapshots');
    const manifestPath = join(snapshotsDir, 'manifest.bin');
    const { stdout: manifestStdout } = await execFile('node', ['cli.mjs', 'dump', manifestPath], {
      cwd: process.cwd(),
    });
    const manifestDump = JSON.parse(manifestStdout) as {
      version: number;
      compaction_hlc: string;
      segments: Array<{ table: string; partition: string; row_count: number; path: string }>;
      sites_compacted: Record<string, number>;
    };
    expect(manifestDump.version).toBe(compaction.manifest.version);
    expect(manifestDump.sites_compacted).toEqual(compaction.manifest.sites_compacted);
    expect(manifestDump.segments).toHaveLength(1);
    expect(manifestDump.segments[0]!.table).toBe('tasks');
    expect(manifestDump.segments[0]!.partition).toBe('_default');
    expect(manifestDump.segments[0]!.row_count).toBe(1);

    const segmentPath = join(snapshotsDir, manifestDump.segments[0]!.path);
    const { stdout: segmentStdout } = await execFile('node', ['cli.mjs', 'dump', segmentPath], {
      cwd: process.cwd(),
    });
    const segmentDump = JSON.parse(segmentStdout) as {
      table: string;
      partition: string;
      row_count: number;
      bloom: string;
      rows: Array<{
        key: string;
        cols: {
          title: { typ: 1; val: string };
          points: { typ: 2; inc: Record<string, number> };
          tags: { typ: 3; elements: Array<{ val: string }>; tombstones: unknown[] };
          status: { typ: 4; values: Array<{ val: string }> };
        };
      }>;
    };

    expect(segmentDump.table).toBe('tasks');
    expect(segmentDump.partition).toBe('_default');
    expect(segmentDump.row_count).toBe(1);
    expect(segmentDump.bloom.startsWith('<bytes:')).toBe(true);
    expect(segmentDump.rows[0]!.key).toBe('t1');
    expect(segmentDump.rows[0]!.cols.title.val).toBe('from-c');
    expect(segmentDump.rows[0]!.cols.points.inc).toEqual({
      'site-b': 3,
      'site-c': 5,
    });
    expect(segmentDump.rows[0]!.cols.tags.elements.map((item) => item.val).sort()).toEqual([
      'beta',
      'gamma',
    ]);
    expect(segmentDump.rows[0]!.cols.tags.tombstones.length).toBe(1);
    expect(segmentDump.rows[0]!.cols.status.values.map((item) => item.val).sort()).toEqual([
      'open',
      'review',
    ]);

    await mkdir(clientDDir, { recursive: true });
    await writeFile(join(clientDDir, 'schema.bin'), schemaBytes);
    const clientD = await NodeCrdtClient.open({
      siteId: 'site-d',
      log: new HttpReplicatedLog(baseUrl),
      dataDir: clientDDir,
      snapshots,
      now: () => 4_000,
    });
    await clientD.pull();
    const rowsD = await clientD.query(TASK_QUERY_SQL);
    expect(rowsD).toEqual(rowsA);
    await stat(join(clientDDir, 'snapshots', 'manifest.bin'));
    await stat(join(clientDDir, 'snapshots', manifestDump.segments[0]!.path));

    const secondCompaction = await compactReplicatedLog({
      log: logA,
      schema,
      snapshots,
    });
    expect(secondCompaction.applied).toBe(true);
    expect(secondCompaction.opsRead).toBe(0);
    expect(secondCompaction.manifest.sites_compacted).toEqual(compaction.manifest.sites_compacted);
    },
  );
});
