import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { dirname, join } from 'node:path';
import {
  ManifestFile,
  ManifestSegmentRef,
  SegmentFile,
  applyOpsToRuntimeRows,
  buildManifestSegmentRef,
  buildSegmentsFromRows,
  makeEmptyManifest,
  maxHlcHex,
  mergeRuntimeRowMaps,
  segmentFileToRuntimeRows,
} from '../../core/compaction';
import { decodeBin, encodeBin } from '../../core/encoding';
import { LogPosition, ReplicatedLog } from '../../core/replication';
import { SqlSchema } from '../../core/sql';
import { RuntimeRowState } from '../../core/sqlEval';

function isEnoent(error: unknown): boolean {
  return (error as { code?: string }).code === 'ENOENT';
}

async function readOptionalManifest(path: string): Promise<ManifestFile | null> {
  try {
    const bytes = await readFile(path);
    return decodeBin<ManifestFile>(bytes);
  } catch (error) {
    if (isEnoent(error)) {
      return null;
    }
    throw error;
  }
}

async function loadRowsFromManifest(
  outputDir: string,
  manifest: ManifestFile,
): Promise<Map<string, RuntimeRowState>> {
  const rows = new Map<string, RuntimeRowState>();
  for (const segmentRef of manifest.segments) {
    const bytes = await readFile(join(outputDir, segmentRef.path));
    const segment = decodeBin<SegmentFile>(bytes);
    const loaded = segmentFileToRuntimeRows(segment);
    mergeRuntimeRowMaps(rows, loaded);
  }
  return rows;
}

function normalizeSeq(value: LogPosition): number {
  if (!Number.isInteger(value) || value < 0) {
    throw new Error(`invalid log position: ${String(value)}`);
  }
  return value;
}

export type NodeCompactorOptions = {
  log: ReplicatedLog;
  schema: SqlSchema;
  outputDir: string;
  manifestPath?: string;
};

export type NodeCompactionResult = {
  applied: boolean;
  manifest: ManifestFile;
  writtenSegments: string[];
  opsRead: number;
};

export async function compactReplicatedLogToFs(
  options: NodeCompactorOptions,
): Promise<NodeCompactionResult> {
  const outputDir = options.outputDir;
  const manifestPath = options.manifestPath ?? join(outputDir, 'manifest.bin');
  await mkdir(outputDir, { recursive: true });

  const priorManifest = (await readOptionalManifest(manifestPath)) ?? makeEmptyManifest();
  const rows = await loadRowsFromManifest(outputDir, priorManifest);
  const sitesCompacted: Record<string, number> = { ...priorManifest.sites_compacted };

  let compactionHlc = priorManifest.compaction_hlc;
  let opsRead = 0;

  const sites = await options.log.listSites();
  sites.sort();

  for (const siteId of sites) {
    const since = normalizeSeq(sitesCompacted[siteId] ?? 0);
    const entries = await options.log.readSince(siteId, since);
    let nextHead = since;
    for (const entry of entries) {
      nextHead = Math.max(nextHead, normalizeSeq(entry.seq));
      compactionHlc = maxHlcHex(compactionHlc, entry.hlc);
      applyOpsToRuntimeRows(rows, entry.ops);
      for (const op of entry.ops) {
        compactionHlc = maxHlcHex(compactionHlc, op.hlc);
      }
      opsRead += entry.ops.length;
    }
    sitesCompacted[siteId] = nextHead;
  }

  const builtSegments = buildSegmentsFromRows({
    schema: options.schema,
    rows,
    defaultHlcMax: compactionHlc,
  });

  const manifestSegments: ManifestSegmentRef[] = [];
  const writtenSegments: string[] = [];
  for (const built of builtSegments) {
    const segmentPath = join(outputDir, built.path);
    await mkdir(dirname(segmentPath), { recursive: true });
    const bytes = encodeBin(built.segment);
    await writeFile(segmentPath, bytes);
    manifestSegments.push(buildManifestSegmentRef(built.path, built.segment, bytes.byteLength));
    writtenSegments.push(built.path);
  }

  const nextManifest: ManifestFile = {
    v: 1,
    version: priorManifest.version + 1,
    compaction_hlc: compactionHlc,
    segments: manifestSegments,
    sites_compacted: sitesCompacted,
  };

  // File-based CAS: if version changed between read and write, skip publishing.
  const latestManifest = (await readOptionalManifest(manifestPath)) ?? makeEmptyManifest();
  if (latestManifest.version !== priorManifest.version) {
    return {
      applied: false,
      manifest: latestManifest,
      writtenSegments: [],
      opsRead,
    };
  }

  await mkdir(dirname(manifestPath), { recursive: true });
  await writeFile(manifestPath, encodeBin(nextManifest));
  return {
    applied: true,
    manifest: nextManifest,
    writtenSegments,
    opsRead,
  };
}
