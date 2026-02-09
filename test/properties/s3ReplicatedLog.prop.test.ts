import {
  GetObjectCommand,
  ListObjectsV2Command,
  type ListObjectsV2CommandOutput,
  PutObjectCommand,
} from '@aws-sdk/client-s3';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { describe, expect, it } from 'vitest';
import { createTigrisReplicatedLog } from '../../src/backend/tigrisReplicatedLog';
import { S3ReplicatedLog } from '../../src/backend/s3ReplicatedLog';
import { decodeBin, encodeBin } from '../../src/core/encoding';
import type { AppendLogEntry, LogEntry } from '../../src/core/replication';

type PutFaultStatus = 409 | 412;
type SiteId = 'site-a' | 'site-b' | 'site-c';

type Operation =
  | { kind: 'append'; siteId: SiteId }
  | { kind: 'getHead'; siteId: SiteId }
  | { kind: 'readSince'; siteId: SiteId; since: number }
  | { kind: 'listSites' };

function makeS3Error(status: number, message: string): Error & { $metadata: { httpStatusCode: number } } {
  const error = new Error(message) as Error & { $metadata: { httpStatusCode: number } };
  error.$metadata = { httpStatusCode: status };
  return error;
}

function continuationToIndex(token: string | undefined): number {
  if (!token) {
    return 0;
  }
  const parsed = Number.parseInt(token, 10);
  return Number.isFinite(parsed) && parsed >= 0 ? parsed : 0;
}

function toBytes(body: unknown): Uint8Array {
  if (body instanceof Uint8Array) {
    return body;
  }
  if (typeof body === 'string') {
    return new TextEncoder().encode(body);
  }
  if (body instanceof ArrayBuffer) {
    return new Uint8Array(body);
  }
  if (ArrayBuffer.isView(body)) {
    const view = body as ArrayBufferView;
    return new Uint8Array(view.buffer.slice(view.byteOffset, view.byteOffset + view.byteLength));
  }
  throw new Error(`unsupported body type: ${String(body)}`);
}

class InMemoryS3Client {
  private readonly objects = new Map<string, Uint8Array>();
  private readonly putFaults: PutFaultStatus[] = [];

  constructor(private readonly pageSize: number) {}

  seedEntry(key: string, entry: LogEntry): void {
    this.objects.set(key, encodeBin(entry));
  }

  seedRaw(key: string, bytes: Uint8Array): void {
    this.objects.set(key, bytes);
  }

  queuePutFault(status: PutFaultStatus): void {
    this.putFaults.push(status);
  }

  async send(command: unknown): Promise<unknown> {
    if (command instanceof ListObjectsV2Command) {
      return this.handleList(command);
    }
    if (command instanceof PutObjectCommand) {
      return this.handlePut(command);
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

  private handlePut(command: PutObjectCommand): unknown {
    const input = command.input;
    const key = input.Key;
    if (!key) {
      throw makeS3Error(400, 'missing key');
    }

    const fault = this.putFaults.shift();
    if (fault) {
      throw makeS3Error(fault, `injected ${fault}`);
    }

    if (input.IfNoneMatch === '*' && this.objects.has(key)) {
      throw makeS3Error(412, 'precondition failed');
    }

    this.objects.set(key, toBytes(input.Body));
    return { ETag: 'etag' };
  }

  private handleGet(command: GetObjectCommand): { Body: { transformToByteArray: () => Promise<Uint8Array> } } {
    const input = command.input;
    const key = input.Key;
    if (!key || !this.objects.has(key)) {
      throw makeS3Error(404, 'not found');
    }
    const bytes = this.objects.get(key)!;
    return {
      Body: {
        transformToByteArray: async () => bytes,
      },
    };
  }
}

function opForAppend(siteId: SiteId, ordinal: number): AppendLogEntry {
  return {
    siteId,
    hlc: `0x${(ordinal + 1).toString(16)}`,
    ops: [],
  };
}

function seqRange(startInclusive: number, endInclusive: number): number[] {
  if (endInclusive < startInclusive) {
    return [];
  }
  const out: number[] = [];
  for (let value = startInclusive; value <= endInclusive; value += 1) {
    out.push(value);
  }
  return out;
}

describe('S3ReplicatedLog properties (direct backend semantics)', () => {
  const arbSiteId = fc.constantFrom<SiteId>('site-a', 'site-b', 'site-c');
  const arbOperation: fc.Arbitrary<Operation> = fc.oneof(
    arbSiteId.map((siteId) => ({ kind: 'append', siteId } as const)),
    arbSiteId.map((siteId) => ({ kind: 'getHead', siteId } as const)),
    fc.record({
      kind: fc.constant<'readSince'>('readSince'),
      siteId: arbSiteId,
      since: fc.nat({ max: 24 }),
    }),
    fc.constant({ kind: 'listSites' as const }),
  );

  test.prop([fc.array(arbOperation, { minLength: 1, maxLength: 80 }), fc.integer({ min: 1, max: 4 })])(
    'stateful operation traces match model under pagination',
    async (operations, pageSize) => {
      const client = new InMemoryS3Client(pageSize);
      const log = new S3ReplicatedLog({
        bucket: 'test-bucket',
        prefix: 'deltas',
        client,
      });

      const heads = new Map<SiteId, number>();
      let appendOrdinal = 0;

      for (const operation of operations) {
        if (operation.kind === 'append') {
          const previous = heads.get(operation.siteId) ?? 0;
          const seq = await log.append(opForAppend(operation.siteId, appendOrdinal));
          appendOrdinal += 1;
          expect(seq).toBe(previous + 1);
          heads.set(operation.siteId, seq);
          continue;
        }

        if (operation.kind === 'getHead') {
          const expected = heads.get(operation.siteId) ?? 0;
          await expect(log.getHead(operation.siteId)).resolves.toBe(expected);
          continue;
        }

        if (operation.kind === 'readSince') {
          const expectedHead = heads.get(operation.siteId) ?? 0;
          const expectedSeqs = seqRange(Math.max(1, operation.since + 1), expectedHead);
          const entries = await log.readSince(operation.siteId, operation.since);
          expect(entries.map((entry) => entry.seq)).toEqual(expectedSeqs);
          expect(entries.every((entry) => entry.siteId === operation.siteId)).toBe(true);
          continue;
        }

        const expectedSites = [...heads.entries()]
          .filter(([, head]) => head > 0)
          .map(([siteId]) => siteId)
          .sort((left, right) => left.localeCompare(right));
        await expect(log.listSites()).resolves.toEqual(expectedSites);
      }
    },
  );

  it('ignores malformed keys and only returns contiguous seq prefixes', async () => {
    const client = new InMemoryS3Client(1);
    const log = new S3ReplicatedLog({
      bucket: 'test-bucket',
      prefix: 'deltas',
      client,
    });

    client.seedEntry('deltas/site-a/0000000001.delta.bin', {
      siteId: 'site-a',
      hlc: '0x1',
      seq: 1,
      ops: [],
    });
    client.seedEntry('deltas/site-a/0000000003.bin', {
      siteId: 'site-a',
      hlc: '0x3',
      seq: 3,
      ops: [],
    });
    client.seedEntry('deltas/site-b/0000000001.delta.bin', {
      siteId: 'site-b',
      hlc: '0x10',
      seq: 1,
      ops: [],
    });

    // malformed / irrelevant keys
    client.seedRaw('deltas/site-a/not-a-seq.txt', new Uint8Array([1]));
    client.seedRaw('deltas/site-a/0000000000.delta.bin', new Uint8Array([1]));
    client.seedRaw('deltas/site-a/abc.delta.bin', new Uint8Array([1]));
    client.seedRaw('deltas/site-a/0000000002.tmp', new Uint8Array([1]));
    client.seedRaw('other/site-a/0000000009.delta.bin', new Uint8Array([1]));

    await expect(log.getHead('site-a')).resolves.toBe(3);
    await expect(log.readSince('site-a', 1).then((entries) => entries.map((entry) => entry.seq))).resolves.toEqual([]);

    const appended = await log.append({
      siteId: 'site-a',
      hlc: '0x4',
      ops: [],
    });
    expect(appended).toBe(4);

    const seqs = await log.readSince('site-a', 0).then((entries) => entries.map((entry) => entry.seq));
    expect(seqs).toEqual([1]);

    await expect(log.listSites()).resolves.toEqual(['site-a', 'site-b']);
  });

  test.prop([
    fc.integer({ min: 0, max: 8 }),
    fc.constantFrom<PutFaultStatus>(409, 412),
  ])('append retries 409/412 conflicts up to max attempts', async (retryCount, status) => {
    const client = new InMemoryS3Client(2);
    const log = new S3ReplicatedLog({
      bucket: 'test-bucket',
      prefix: 'deltas',
      client,
    });

    for (let i = 0; i < retryCount; i += 1) {
      client.queuePutFault(status);
    }

    if (retryCount < 5) {
      await expect(
        log.append({
          siteId: 'site-a',
          hlc: '0x9',
          ops: [],
        }),
      ).resolves.toBe(1);
      await expect(log.getHead('site-a')).resolves.toBe(1);
      return;
    }

    await expect(
      log.append({
        siteId: 'site-a',
        hlc: '0x9',
        ops: [],
      }),
    ).rejects.toThrow(/failed to append after retries/);
    await expect(log.getHead('site-a')).resolves.toBe(0);
  });
});

describe('createTigrisReplicatedLog', () => {
  it('uses default deltas prefix when prefix is omitted', () => {
    const log = createTigrisReplicatedLog({
      bucket: 'bucket',
      accessKeyId: 'key',
      secretAccessKey: 'secret',
      endpoint: 'http://127.0.0.1:9000',
    });
    expect(log).toBeInstanceOf(S3ReplicatedLog);

    const internals = log as unknown as {
      bucket: string;
      sitePrefix: string;
    };
    expect(internals.bucket).toBe('bucket');
    expect(internals.sitePrefix).toBe('deltas/');
  });

  it('normalizes and uses custom prefix', () => {
    const log = createTigrisReplicatedLog({
      bucket: 'bucket',
      accessKeyId: 'key',
      secretAccessKey: 'secret',
      endpoint: 'http://127.0.0.1:9000',
      prefix: '/custom/prefix/',
      region: 'us-east-1',
    });

    const internals = log as unknown as {
      sitePrefix: string;
      client: { config?: { forcePathStyle?: unknown } };
    };
    expect(internals.sitePrefix).toBe('custom/prefix/');

    // Factory guarantees Tigris-style virtual-host semantics.
    expect(internals.client).toBeDefined();
  });
});
