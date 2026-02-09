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
import { LogPosition, ReplicatedLog, takeContiguousEntriesSince } from '../../core/replication';
import { SnapshotStore } from '../../core/snapshotStore';
import { SqlSchema } from '../../core/sql';
import { RuntimeRowState } from '../../core/sqlEval';

async function loadRowsFromManifest(
  snapshots: SnapshotStore,
  manifest: ManifestFile,
): Promise<Map<string, RuntimeRowState>> {
  const rows = new Map<string, RuntimeRowState>();
  for (const segmentRef of manifest.segments) {
    const bytes = await snapshots.getSegment(segmentRef.path);
    if (bytes === null) {
      throw new Error(`missing segment referenced by manifest: ${segmentRef.path}`);
    }
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

export type SnapshotCompactorOptions = {
  log: ReplicatedLog;
  snapshots: SnapshotStore;
  schema?: SqlSchema;
};

export type NodeCompactionResult = {
  applied: boolean;
  manifest: ManifestFile;
  writtenSegments: string[];
  opsRead: number;
};

export async function compactReplicatedLog(
  options: SnapshotCompactorOptions,
): Promise<NodeCompactionResult> {
  const schema = options.schema ?? (await options.snapshots.getSchema());
  if (!schema) {
    throw new Error('compaction requires schema: provide options.schema or snapshots.getSchema()');
  }

  const priorManifest = (await options.snapshots.getManifest()) ?? makeEmptyManifest();
  const rows = await loadRowsFromManifest(options.snapshots, priorManifest);
  const sitesCompacted: Record<string, number> = { ...priorManifest.sites_compacted };

  let compactionHlc = priorManifest.compaction_hlc;
  let opsRead = 0;

  const sites = await options.log.listSites();
  sites.sort();

  for (const siteId of sites) {
    const since = normalizeSeq(sitesCompacted[siteId] ?? 0);
    const readEntries = await options.log.readSince(siteId, since);
    const entries = takeContiguousEntriesSince(readEntries, since);
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
    schema,
    rows,
    defaultHlcMax: compactionHlc,
  });

  const manifestSegments: ManifestSegmentRef[] = [];
  const writtenSegments: string[] = [];
  for (const built of builtSegments) {
    const bytes = encodeBin(built.segment);
    await options.snapshots.putSegment(built.path, bytes);
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

  const applied = await options.snapshots.putManifest(nextManifest, priorManifest.version);
  if (!applied) {
    const latestManifest = (await options.snapshots.getManifest()) ?? makeEmptyManifest();
    return {
      applied: false,
      manifest: latestManifest,
      writtenSegments: [],
      opsRead,
    };
  }

  return {
    applied: true,
    manifest: nextManifest,
    writtenSegments,
    opsRead,
  };
}
