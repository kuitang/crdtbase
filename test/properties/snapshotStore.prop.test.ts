import { mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { describe, expect } from 'vitest';
import { ManifestFile, ManifestSegmentRef, SegmentFile, compareSqlPrimaryKeys } from '../../src/core/compaction';
import { decodeBin, encodeBin } from '../../src/core/encoding';
import { HLC_LIMITS } from '../../src/core/hlc';
import { SqlColumnCrdt, SqlPrimaryKey, SqlSchema, SqlValue } from '../../src/core/sql';
import {
  assertManifestPublishable,
  assertSafeSnapshotRelativePath,
  validateManifestFile,
  validateSegmentFile,
  validateSqlSchema,
} from '../../src/core/snapshotStore';
import { SqlEvalColumnState } from '../../src/core/sqlEval';
import { FsSnapshotStore } from '../../src/platform/node/fsSnapshotStore';

const arbIdentifier = fc.stringMatching(/^[a-z][a-z0-9_]{0,10}$/u);
const arbPartition = fc.stringMatching(/^[a-z0-9._-]{1,12}$/u);
const arbSiteId = fc.hexaString({ minLength: 8, maxLength: 8 });

const arbSqlScalar: fc.Arbitrary<SqlValue> = fc.oneof(
  fc.string({ maxLength: 20 }),
  fc.integer({ min: -1_000_000, max: 1_000_000 }),
  fc.boolean(),
  fc.constant(null),
);

const arbPrimaryKey: fc.Arbitrary<SqlPrimaryKey> = fc.oneof(
  fc.string({ maxLength: 20 }),
  fc.integer({ min: -10_000, max: 10_000 }),
);

const arbPackedHlcHex = fc
  .record({
    wallMs: fc.nat({ max: HLC_LIMITS.wallMsMax - 1 }),
    counter: fc.nat({ max: HLC_LIMITS.counterMax - 1 }),
  })
  .map(({ wallMs, counter }) => `0x${((BigInt(wallMs) << 16n) | BigInt(counter)).toString(16)}`);

const arbSqlEvalColumnState: fc.Arbitrary<SqlEvalColumnState> = fc.oneof(
  fc.record({
    typ: fc.constant<1>(1),
    val: arbSqlScalar,
    hlc: arbPackedHlcHex,
    site: arbSiteId,
  }),
  fc.record({
    typ: fc.constant<2>(2),
    inc: fc.dictionary(arbSiteId, fc.nat({ max: 100_000 })),
    dec: fc.dictionary(arbSiteId, fc.nat({ max: 100_000 })),
  }),
  fc.record({
    typ: fc.constant<3>(3),
    elements: fc.array(
      fc.record({
        val: arbSqlScalar,
        hlc: arbPackedHlcHex,
        site: arbSiteId,
      }),
      { maxLength: 20 },
    ),
    tombstones: fc.array(
      fc.record({
        hlc: arbPackedHlcHex,
        site: arbSiteId,
      }),
      { maxLength: 20 },
    ),
  }),
  fc.record({
    typ: fc.constant<4>(4),
    values: fc.array(
      fc.record({
        val: arbSqlScalar,
        hlc: arbPackedHlcHex,
        site: arbSiteId,
      }),
      { maxLength: 20 },
    ),
  }),
);

const arbSegmentFile: fc.Arbitrary<SegmentFile> = fc
  .record({
    table: arbIdentifier,
    partition: arbPartition,
    hlc_max: arbPackedHlcHex,
    bloom: fc.uint8Array({ maxLength: 256 }),
    bloom_k: fc.nat({ max: 20 }),
    rows: fc.array(
      fc.record({
        key: arbPrimaryKey,
        cols: fc.dictionary(arbIdentifier, arbSqlEvalColumnState, {
          minKeys: 1,
          maxKeys: 6,
        }),
      }),
      { maxLength: 40 },
    ),
  })
  .map((segment): SegmentFile => {
    const rows = [...segment.rows].sort((left, right) => compareSqlPrimaryKeys(left.key, right.key));
    return {
      v: 1,
      table: segment.table,
      partition: segment.partition,
      hlc_max: segment.hlc_max,
      row_count: rows.length,
      bloom: segment.bloom,
      bloom_k: rows.length === 0 ? 0 : Math.max(1, segment.bloom_k),
      rows,
    };
  });

const arbOrderedKeyPair: fc.Arbitrary<readonly [SqlPrimaryKey, SqlPrimaryKey]> = fc
  .tuple(arbPrimaryKey, arbPrimaryKey)
  .map(([left, right]) =>
    compareSqlPrimaryKeys(left, right) <= 0
      ? ([left, right] as const)
      : ([right, left] as const),
  );

const arbManifestSegmentRef: fc.Arbitrary<ManifestSegmentRef> = fc
  .record({
    table: arbIdentifier,
    partition: arbPartition,
    row_count: fc.integer({ min: 1, max: 100_000 }),
    size_bytes: fc.integer({ min: 1, max: 5_000_000 }),
    hlc_max: arbPackedHlcHex,
    keyPair: arbOrderedKeyPair,
    suffix: fc.hexaString({ minLength: 8, maxLength: 8 }),
  })
  .map((item) => ({
    path: `segments/${item.table}_${item.partition}_${item.suffix}.seg.bin`,
    table: item.table,
    partition: item.partition,
    row_count: item.row_count,
    size_bytes: item.size_bytes,
    hlc_max: item.hlc_max,
    key_min: item.keyPair[0],
    key_max: item.keyPair[1],
  }));

const arbManifestFile: fc.Arbitrary<ManifestFile> = fc
  .record({
    version: fc.nat({ max: 100_000 }),
    compaction_hlc: arbPackedHlcHex,
    segments: fc.uniqueArray(arbManifestSegmentRef, {
      selector: (segment) => segment.path,
      maxLength: 40,
    }),
    sites_compacted: fc.dictionary(arbSiteId, fc.nat({ max: 1_000_000 })),
  })
  .map((manifest) => ({
    v: 1 as const,
    version: manifest.version,
    compaction_hlc: manifest.compaction_hlc,
    segments: manifest.segments,
    sites_compacted: manifest.sites_compacted,
  }));

const arbColumnCrdt = fc.constantFrom<SqlColumnCrdt>(
  'scalar',
  'lww',
  'pn_counter',
  'or_set',
  'mv_register',
);

const arbTableSchema: fc.Arbitrary<SqlSchema[string]> = fc
  .uniqueArray(
    fc.record({
      name: arbIdentifier,
      crdt: arbColumnCrdt,
    }),
    { selector: (entry) => entry.name, maxLength: 8 },
  )
  .chain((entries) => {
    const columns: Record<string, { crdt: SqlColumnCrdt }> = { id: { crdt: 'scalar' } };
    for (const entry of entries) {
      if (entry.name === 'id') {
        continue;
      }
      columns[entry.name] = { crdt: entry.crdt };
    }
    const columnNames = Object.keys(columns);
    return fc.constantFrom<string | null>(null, ...columnNames).map((partitionBy) => ({
      pk: 'id',
      partitionBy,
      columns,
    }));
  });

const arbSqlSchema: fc.Arbitrary<SqlSchema> = fc.dictionary(arbIdentifier, arbTableSchema, {
  maxKeys: 6,
});

function manifestForVersion(version: number): ManifestFile {
  return {
    v: 1,
    version,
    compaction_hlc: '0x0',
    segments: [],
    sites_compacted: {},
  };
}

describe('Snapshot store properties', () => {
  test.prop([arbManifestFile])('manifest encode/decode round-trip preserves validity', (manifest) => {
    validateManifestFile(manifest);
    const decoded = decodeBin<ManifestFile>(encodeBin(manifest));
    expect(decoded).toEqual(manifest);
    validateManifestFile(decoded);
  });

  test.prop([arbSegmentFile])('segment encode/decode round-trip preserves validity', (segment) => {
    validateSegmentFile(segment);
    const decoded = decodeBin<SegmentFile>(encodeBin(segment));
    expect(decoded).toEqual(segment);
    validateSegmentFile(decoded);
  });

  test.prop([arbSqlSchema])('schema encode/decode round-trip preserves validity', (schema) => {
    validateSqlSchema(schema);
    const decoded = decodeBin<SqlSchema>(encodeBin(schema));
    expect(decoded).toEqual(schema);
    validateSqlSchema(decoded);
  });

  test.prop([fc.nat({ max: 10_000 })])(
    'manifest publication requires next version to be exactly expectedVersion + 1',
    (expectedVersion) => {
      const validNext = manifestForVersion(expectedVersion + 1);
      expect(() => assertManifestPublishable(validNext, expectedVersion)).not.toThrow();

      const invalidSame = manifestForVersion(expectedVersion);
      expect(() => assertManifestPublishable(invalidSame, expectedVersion)).toThrow();

      const invalidJump = manifestForVersion(expectedVersion + 2);
      expect(() => assertManifestPublishable(invalidJump, expectedVersion)).toThrow();
    },
  );

  test.prop(
    [fc.nat({ max: 12 }), fc.nat({ max: 12 })],
    { numRuns: 40 },
  )('filesystem snapshot store enforces manifest CAS by version', async (currentVersion, expectedVersion) => {
    const root = await mkdtemp(join(tmpdir(), 'crdtbase-snapshots-prop-'));
    try {
      const store = new FsSnapshotStore({ rootDir: root });

      for (let version = 1; version <= currentVersion; version += 1) {
        const seeded = await store.putManifest(manifestForVersion(version), version - 1);
        expect(seeded).toBe(true);
      }

      const applied = await store.putManifest(
        manifestForVersion(expectedVersion + 1),
        expectedVersion,
      );
      const shouldApply = expectedVersion === currentVersion;
      expect(applied).toBe(shouldApply);

      const finalManifest = await store.getManifest();
      const finalVersion = finalManifest?.version ?? 0;
      expect(finalVersion).toBe(shouldApply ? expectedVersion + 1 : currentVersion);
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  test.prop([arbIdentifier, arbIdentifier])('snapshot paths reject traversal but accept safe paths', (a, b) => {
    expect(() => assertSafeSnapshotRelativePath(`segments/${a}_${b}.seg.bin`)).not.toThrow();
    expect(() => assertSafeSnapshotRelativePath(`segments/../${a}.seg.bin`)).toThrow();
    expect(() => assertSafeSnapshotRelativePath(`/segments/${a}.seg.bin`)).toThrow();
  });
});
