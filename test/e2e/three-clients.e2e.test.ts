import { execFile as execFileWithCallback } from 'node:child_process';
import { mkdir, mkdtemp, readFile, readdir, rm, stat, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { promisify } from 'node:util';
import { afterEach, describe, expect, it } from 'vitest';
import { FileReplicatedLogServer } from '../../src/backend/fileLogServer';
import { decodeBin } from '../../src/core/encoding';
import { createHlcClock } from '../../src/core/hlc';
import { SqlSchema } from '../../src/core/sql';
import { compactReplicatedLog } from '../../src/platform/node/compactor';
import { HttpReplicatedLog } from '../../src/platform/node/httpReplicatedLog';
import { NodeCrdtClient } from '../../src/platform/node/nodeClient';
import { HttpSnapshotStore } from '../../src/platform/node/httpSnapshotStore';
import {
  runThreeClientChaosScenario,
  normalizeTaskRows,
} from './orchestrator';
import { assertAckedWritesVisible, loadChaosEnv } from './chaosShared';

const execFile = promisify(execFileWithCallback);
const CHAOS = loadChaosEnv();

describe('Filesystem SQL chaos end-to-end sync', () => {
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

  it.each(CHAOS.seeds)(
    'converges under random delayed concurrent client activity [seed=%s]',
    async (seed) => {
      tempRoot = await mkdtemp(join(tmpdir(), 'crdtbase-e2e-chaos-'));
      const serverDir = join(tempRoot, 'server');
      const clientADir = join(tempRoot, 'client-a');
      const clientBDir = join(tempRoot, 'client-b');
      const clientCDir = join(tempRoot, 'client-c');
      const observerDir = join(tempRoot, 'observer');
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
        clock: createHlcClock({ nowWallMs: () => 1_000 }),
      });
      const clientB = await NodeCrdtClient.open({
        siteId: 'site-b',
        log: logB,
        dataDir: clientBDir,
        clock: createHlcClock({ nowWallMs: () => 2_000 }),
      });
      const clientC = await NodeCrdtClient.open({
        siteId: 'site-c',
        log: logC,
        dataDir: clientCDir,
        clock: createHlcClock({ nowWallMs: () => 3_000 }),
      });
      const observer = await NodeCrdtClient.open({
        siteId: 'site-observer',
        log: new HttpReplicatedLog(baseUrl),
        dataDir: observerDir,
        clock: createHlcClock({ nowWallMs: () => 3_500 }),
      });

      const result = await runThreeClientChaosScenario({
        clients: {
          'site-a': clientA,
          'site-b': clientB,
          'site-c': clientC,
        },
        observer,
        config: {
          seed,
          stepsPerClient: CHAOS.steps,
          maxDelayMs: CHAOS.maxDelayMs,
          drainRounds: CHAOS.drainRounds,
          quiescenceRounds: CHAOS.quiescenceRounds,
        },
      });

      const rowsA = result.normalizedRowsBySite['site-a'];
      const rowsB = result.normalizedRowsBySite['site-b'];
      const rowsC = result.normalizedRowsBySite['site-c'];

      expect(rowsA).toEqual(rowsB);
      expect(rowsB).toEqual(rowsC);
      expect(rowsA.length).toBeGreaterThan(0);
      expect(result.convergenceRound).toBeGreaterThan(0);
      expect(result.stats.writes).toBeGreaterThan(0);
      expect(result.observerRows).toEqual(rowsA);

      assertAckedWritesVisible({
        rows: rowsA,
        expectedPointsByRow: result.expectedPointsByRow,
        expectedTagsByRow: result.expectedTagsByRow,
      });

      expect(await logA.getHead('site-a')).toBeGreaterThan(0);
      expect(await logA.getHead('site-b')).toBeGreaterThan(0);
      expect(await logA.getHead('site-c')).toBeGreaterThan(0);

      for (const clientDir of [clientADir, clientBDir, clientCDir]) {
        await stat(join(clientDir, 'schema.bin'));
        await stat(join(clientDir, 'state.bin'));
        await stat(join(clientDir, 'pending.bin'));
        await stat(join(clientDir, 'sync.bin'));
      }

      for (const siteId of ['site-a', 'site-b', 'site-c']) {
        const files = await readdir(join(serverDir, 'logs', siteId));
        expect(files.some((file) => file.endsWith('.bin'))).toBe(true);
      }

      const siteBFiles = (await readdir(join(serverDir, 'logs', 'site-b'))).sort();
      const dumpedPath = join(serverDir, 'logs', 'site-b', siteBFiles[0]!);
      const { stdout } = await execFile('node', ['cli.mjs', 'dump', dumpedPath], {
        cwd: process.cwd(),
      });
      const parsed = JSON.parse(stdout) as { siteId: string; seq: number; ops: unknown[] };
      expect(parsed.siteId).toBe('site-b');
      expect(parsed.seq).toBeGreaterThanOrEqual(1);
      expect(Array.isArray(parsed.ops)).toBe(true);
      expect(parsed.ops.length).toBeGreaterThan(0);

      const schemaBytes = await readFile(join(clientADir, 'schema.bin'));
      const schema = decodeBin<SqlSchema>(schemaBytes);
      const snapshots = new HttpSnapshotStore(baseUrl);
      const compaction = await compactReplicatedLog({
        log: logA,
        schema,
        snapshots,
      });

      expect(compaction.applied).toBe(true);
      expect(compaction.opsRead).toBeGreaterThan(0);
      expect(compaction.manifest.segments.length).toBeGreaterThan(0);
      expect(compaction.manifest.sites_compacted['site-a']).toBe(await logA.getHead('site-a'));
      expect(compaction.manifest.sites_compacted['site-b']).toBe(await logA.getHead('site-b'));
      expect(compaction.manifest.sites_compacted['site-c']).toBe(await logA.getHead('site-c'));

      const snapshotsDir = join(serverDir, 'snapshots');
      const manifestPath = join(snapshotsDir, 'manifest.bin');
      const { stdout: manifestStdout } = await execFile('node', ['cli.mjs', 'dump', manifestPath], {
        cwd: process.cwd(),
      });
      const manifestDump = JSON.parse(manifestStdout) as {
        version: number;
        segments: Array<{ table: string; partition: string; row_count: number; path: string }>;
        sites_compacted: Record<string, number>;
      };
      expect(manifestDump.version).toBe(compaction.manifest.version);
      expect(manifestDump.sites_compacted).toEqual(compaction.manifest.sites_compacted);
      expect(manifestDump.segments.length).toBeGreaterThan(0);
      expect(manifestDump.segments[0]!.table).toBe('tasks');
      expect(manifestDump.segments[0]!.partition).toBe('_default');
      expect(manifestDump.segments[0]!.row_count).toBeGreaterThan(0);

      const segmentPath = join(snapshotsDir, manifestDump.segments[0]!.path);
      const { stdout: segmentStdout } = await execFile('node', ['cli.mjs', 'dump', segmentPath], {
        cwd: process.cwd(),
      });
      const segmentDump = JSON.parse(segmentStdout) as {
        table: string;
        partition: string;
        row_count: number;
        bloom: string;
      };
      expect(segmentDump.table).toBe('tasks');
      expect(segmentDump.partition).toBe('_default');
      expect(segmentDump.row_count).toBeGreaterThan(0);
      expect(segmentDump.bloom.startsWith('<bytes:')).toBe(true);

      await mkdir(clientDDir, { recursive: true });
      await writeFile(join(clientDDir, 'schema.bin'), schemaBytes);
      const clientD = await NodeCrdtClient.open({
        siteId: 'site-d',
        log: new HttpReplicatedLog(baseUrl),
        dataDir: clientDDir,
        clock: createHlcClock({ nowWallMs: () => 4_000 }),
      });
      await clientD.pull();
      const rowsD = normalizeTaskRows(await clientD.query('SELECT * FROM tasks;'));
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
