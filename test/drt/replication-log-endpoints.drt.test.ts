import { afterAll, beforeAll, describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import {
  GetObjectCommand,
  ListObjectsV2Command,
  type ListObjectsV2CommandOutput,
} from '@aws-sdk/client-s3';
import { S3ReplicatedLog } from '../../src/backend/s3ReplicatedLog';
import { encodeBin } from '../../src/core/encoding';
import type { LogEntry } from '../../src/core/replication';
import { LeanDrtClient } from './harness';

const leanBin = LeanDrtClient.findBinary();
const drt = leanBin ? test : test.skip;
const drtRuns = Number(process.env.DRT_NUM_RUNS ?? 50);
const drtTimeoutMs = Number(process.env.DRT_TIMEOUT_MS ?? 30_000);

type SiteId = 'site-a' | 'site-b' | 'site-c';

type GeneratedEntry = {
  siteId: SiteId;
  seq: number;
};

function continuationToIndex(token: string | undefined): number {
  if (!token) {
    return 0;
  }
  const parsed = Number.parseInt(token, 10);
  return Number.isFinite(parsed) && parsed >= 0 ? parsed : 0;
}

class InMemoryS3ReaderClient {
  private readonly objects = new Map<string, Uint8Array>();

  constructor(private readonly pageSize: number) {}

  seedEntry(key: string, entry: LogEntry): void {
    this.objects.set(key, encodeBin(entry));
  }

  async send(command: unknown): Promise<unknown> {
    if (command instanceof ListObjectsV2Command) {
      return this.handleList(command);
    }
    if (command instanceof GetObjectCommand) {
      return this.handleGet(command);
    }
    throw new Error(`unsupported command: ${String(command)}`);
  }

  private handleList(command: ListObjectsV2Command): ListObjectsV2CommandOutput {
    const input = command.input;
    const prefix = input.Prefix ?? '';
    const token = continuationToIndex(input.ContinuationToken);

    const matchingKeys = [...this.objects.keys()]
      .filter((key) => key.startsWith(prefix))
      .sort((left, right) => left.localeCompare(right));

    if (input.Delimiter) {
      const delimiter = input.Delimiter;
      const prefixes = new Set<string>();
      for (const key of matchingKeys) {
        const rest = key.slice(prefix.length);
        const delimiterIndex = rest.indexOf(delimiter);
        if (delimiterIndex > 0) {
          prefixes.add(`${prefix}${rest.slice(0, delimiterIndex + delimiter.length)}`);
        }
      }
      const ordered = [...prefixes].sort((left, right) => left.localeCompare(right));
      const page = ordered.slice(token, token + this.pageSize);
      const next = token + this.pageSize;
      return {
        CommonPrefixes: page.map((value) => ({ Prefix: value })),
        IsTruncated: next < ordered.length,
        NextContinuationToken: next < ordered.length ? String(next) : undefined,
      };
    }

    const pageKeys = matchingKeys.slice(token, token + this.pageSize);
    const next = token + this.pageSize;
    return {
      Contents: pageKeys.map((key) => ({ Key: key })),
      IsTruncated: next < matchingKeys.length,
      NextContinuationToken: next < matchingKeys.length ? String(next) : undefined,
    };
  }

  private handleGet(command: GetObjectCommand): { Body: { transformToByteArray: () => Promise<Uint8Array> } } {
    const input = command.input;
    const key = input.Key;
    if (!key || !this.objects.has(key)) {
      const error = new Error('not found') as Error & { $metadata: { httpStatusCode: number } };
      error.$metadata = { httpStatusCode: 404 };
      throw error;
    }
    const bytes = this.objects.get(key)!;
    return {
      Body: {
        transformToByteArray: async () => bytes,
      },
    };
  }
}

function keyForEntry(siteId: string, seq: number): string {
  return `deltas/${siteId}/${String(seq).padStart(10, '0')}.delta.bin`;
}

function materializeSeedEntries(generated: GeneratedEntry[]): LogEntry[] {
  const byKey = new Map<string, LogEntry>();
  for (const candidate of generated) {
    const key = keyForEntry(candidate.siteId, candidate.seq);
    byKey.set(key, {
      siteId: candidate.siteId,
      hlc: `0x${candidate.seq.toString(16)}`,
      seq: candidate.seq,
      ops: [],
    });
  }
  return [...byKey.values()];
}

describe('DRT: replication log endpoints', () => {
  let client: LeanDrtClient | null = null;

  beforeAll(() => {
    if (leanBin) {
      client = new LeanDrtClient(leanBin);
    }
  });

  afterAll(() => {
    client?.close();
  });

  const arbEntry: fc.Arbitrary<GeneratedEntry> = fc.record({
    siteId: fc.constantFrom<SiteId>('site-a', 'site-b', 'site-c'),
    seq: fc.integer({ min: 1, max: 30 }),
  });

  drt
    .prop(
      [
        fc.array(arbEntry, { minLength: 0, maxLength: 80 }),
        fc.constantFrom('site-a', 'site-b', 'site-c', 'site-missing'),
        fc.nat({ max: 30 }),
        fc.integer({ min: 1, max: 4 }),
      ],
      { numRuns: drtRuns },
    )('listSites/getHead/readSince match Lean model', async (generated, querySite, since, pageSize) => {
      const seededEntries = materializeSeedEntries(generated);
      const s3Client = new InMemoryS3ReaderClient(pageSize);
      for (const entry of seededEntries) {
        s3Client.seedEntry(keyForEntry(entry.siteId, entry.seq), entry);
      }

      const log = new S3ReplicatedLog({
        bucket: 'test-bucket',
        prefix: 'deltas',
        client: s3Client,
      });

      const leanEntries = seededEntries.map((entry) => ({
        siteId: entry.siteId,
        seq: entry.seq,
      }));

      const expectedSites = await client!.replicationListSites<{ result: string[] }>(leanEntries);
      const expectedHead = await client!.replicationGetHead<{ result: number }>(leanEntries, querySite);
      const expectedReadSince = await client!.replicationReadSince<{ result: number[] }>(
        leanEntries,
        querySite,
        since,
      );

      await expect(log.listSites()).resolves.toEqual(expectedSites.result);
      await expect(log.getHead(querySite)).resolves.toBe(expectedHead.result);
      await expect(
        log.readSince(querySite, since).then((entries) => entries.map((entry) => entry.seq)),
      ).resolves.toEqual(expectedReadSince.result);
    }, drtTimeoutMs);
});
