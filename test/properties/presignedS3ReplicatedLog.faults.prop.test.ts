import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { describe, expect } from 'vitest';
import {
  PresignGetObjectInput,
  PresignListObjectsInput,
  PresignPutObjectInput,
  PresignedS3ReplicatedLog,
  S3PresignProvider,
  SignedRequest,
} from '../../src/platform/shared/presignedS3ReplicatedLog';
import { decodeBin, encodeBin } from '../../src/core/encoding';
import type { LogEntry } from '../../src/core/replication';

type PutFault = 'ok' | '409' | '412' | '403' | '500' | 'timeout' | 'stale';
type ReadFault = '403' | '500' | 'timeout' | 'stale';
type ReadOp = 'getHead' | 'listSites' | 'readSinceList' | 'readSinceGet';

function escapeXml(value: string): string {
  return value
    .replaceAll('&', '&amp;')
    .replaceAll('<', '&lt;')
    .replaceAll('>', '&gt;')
    .replaceAll('"', '&quot;')
    .replaceAll("'", '&apos;');
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

class FakePresignProvider implements S3PresignProvider {
  private readonly baseUrl: string;

  constructor(baseUrl: string) {
    this.baseUrl = baseUrl;
  }

  async signListObjects(input: PresignListObjectsInput): Promise<SignedRequest> {
    const url = new URL(`${this.baseUrl}/list`);
    url.searchParams.set('bucket', input.bucket);
    url.searchParams.set('prefix', input.prefix);
    if (input.continuationToken) {
      url.searchParams.set('continuationToken', input.continuationToken);
    }
    if (input.delimiter) {
      url.searchParams.set('delimiter', input.delimiter);
    }
    return { method: 'GET', url: String(url) };
  }

  async signGetObject(input: PresignGetObjectInput): Promise<SignedRequest> {
    const url = new URL(`${this.baseUrl}/get`);
    url.searchParams.set('bucket', input.bucket);
    url.searchParams.set('key', input.key);
    return { method: 'GET', url: String(url) };
  }

  async signPutObject(input: PresignPutObjectInput): Promise<SignedRequest> {
    const url = new URL(`${this.baseUrl}/put`);
    url.searchParams.set('bucket', input.bucket);
    url.searchParams.set('key', input.key);
    if (input.ifNoneMatch) {
      url.searchParams.set('ifNoneMatch', input.ifNoneMatch);
    }
    if (input.contentType) {
      url.searchParams.set('contentType', input.contentType);
    }
    return { method: 'PUT', url: String(url) };
  }
}

class FaultingPresignTransport {
  private readonly objects = new Map<string, Uint8Array>();
  private readonly originalFetch: typeof fetch;

  readonly provider: S3PresignProvider;
  putFaults: PutFault[] = [];
  listFaults: ReadFault[] = [];
  getFaults: ReadFault[] = [];

  constructor() {
    this.provider = new FakePresignProvider('https://presign.test.local');
    this.originalFetch = globalThis.fetch;
    globalThis.fetch = this.fetchImpl as typeof fetch;
  }

  restore(): void {
    globalThis.fetch = this.originalFetch;
  }

  seedEntry(key: string, entry: LogEntry): void {
    this.objects.set(key, encodeBin(entry));
  }

  private readonly fetchImpl: typeof fetch = async (input, init) => {
    const url = new URL(typeof input === 'string' ? input : input.url);
    const method = init?.method ?? 'GET';

    if (url.pathname === '/list' && method === 'GET') {
      return this.handleList(url);
    }
    if (url.pathname === '/put' && method === 'PUT') {
      return this.handlePut(url, init?.body);
    }
    if (url.pathname === '/get' && method === 'GET') {
      return this.handleGet(url);
    }

    return new Response('unsupported route', { status: 500, statusText: 'Unsupported route' });
  };

  private applyReadFault(queue: ReadFault[]): Response | null {
    const fault = queue.shift();
    if (!fault) {
      return null;
    }
    if (fault === 'timeout') {
      throw new Error('timeout');
    }
    if (fault === 'stale') {
      return new Response('<Error><Code>SignatureDoesNotMatch</Code></Error>', {
        status: 403,
        statusText: 'Forbidden',
      });
    }
    const status = Number(fault);
    return new Response(`fault-${fault}`, {
      status,
      statusText: 'Fault',
    });
  }

  private handleList(url: URL): Response {
    const maybeFault = this.applyReadFault(this.listFaults);
    if (maybeFault) {
      return maybeFault;
    }

    const prefix = url.searchParams.get('prefix') ?? '';
    const delimiter = url.searchParams.get('delimiter');
    const keys = [...this.objects.keys()]
      .filter((key) => key.startsWith(prefix))
      .sort((left, right) => left.localeCompare(right));

    const prefixes = delimiter
      ? [...new Set(keys
        .map((key) => key.slice(prefix.length))
        .map((rest) => {
          const slash = rest.indexOf(delimiter);
          if (slash <= 0) {
            return null;
          }
          return `${prefix}${rest.slice(0, slash + delimiter.length)}`;
        })
        .filter((value): value is string => value !== null))]
      : [];

    const body = [
      '<ListBucketResult>',
      ...keys.map((key) => `<Contents><Key>${escapeXml(key)}</Key></Contents>`),
      ...prefixes.map((value) => `<CommonPrefixes><Prefix>${escapeXml(value)}</Prefix></CommonPrefixes>`),
      '<IsTruncated>false</IsTruncated>',
      '</ListBucketResult>',
    ].join('');

    return new Response(body, {
      status: 200,
      headers: { 'content-type': 'application/xml' },
    });
  }

  private handlePut(url: URL, body: BodyInit | null | undefined): Response {
    const fault = this.putFaults.shift() ?? 'ok';
    if (fault === 'timeout') {
      throw new Error('timeout');
    }
    if (fault === 'stale') {
      return new Response('<Error><Code>SignatureDoesNotMatch</Code></Error>', {
        status: 403,
        statusText: 'Forbidden',
      });
    }
    if (fault !== 'ok') {
      return new Response(`fault-${fault}`, {
        status: Number(fault),
        statusText: 'Fault',
      });
    }

    const key = url.searchParams.get('key');
    if (!key) {
      return new Response('missing key', { status: 400, statusText: 'Bad Request' });
    }

    if (this.objects.has(key)) {
      return new Response('precondition failed', {
        status: 412,
        statusText: 'Precondition Failed',
      });
    }

    this.objects.set(key, toBytes(body));
    return new Response('', { status: 200, statusText: 'OK' });
  }

  private handleGet(url: URL): Response {
    const maybeFault = this.applyReadFault(this.getFaults);
    if (maybeFault) {
      return maybeFault;
    }

    const key = url.searchParams.get('key');
    if (!key || !this.objects.has(key)) {
      return new Response('not found', { status: 404, statusText: 'Not Found' });
    }

    return new Response(this.objects.get(key)!, {
      status: 200,
      statusText: 'OK',
      headers: { 'content-type': 'application/octet-stream' },
    });
  }
}

function expectedFirstAppendSuccess(faults: PutFault[]): boolean {
  for (let attempt = 0; attempt < 5; attempt += 1) {
    const fault = faults[attempt] ?? 'ok';
    if (fault === 'ok') {
      return true;
    }
    if (fault === '409' || fault === '412') {
      continue;
    }
    return false;
  }
  return false;
}

function makeEntry(siteId: string, seq: number): LogEntry {
  return {
    siteId,
    seq,
    hlc: `0x${seq.toString(16)}`,
    ops: [],
  };
}

describe('PresignedS3ReplicatedLog fault injection properties', () => {
  test.prop([
    fc.array(
      fc.constantFrom<PutFault>('ok', '409', '412', '403', '500', 'timeout', 'stale'),
      { minLength: 1, maxLength: 8 },
    ),
  ])('append preserves retry and idempotent sequencing invariants under mixed faults', async (faults) => {
    const transport = new FaultingPresignTransport();
    const log = new PresignedS3ReplicatedLog({
      bucket: 'test-bucket',
      prefix: 'deltas',
      presign: transport.provider,
    });

    try {
      transport.putFaults = [...faults];
      const firstShouldSucceed = expectedFirstAppendSuccess(faults);

      if (firstShouldSucceed) {
        await expect(
          log.append({
            siteId: 'site-a',
            hlc: '0x1',
            ops: [],
          }),
        ).resolves.toBe(1);
      } else {
        await expect(
          log.append({
            siteId: 'site-a',
            hlc: '0x1',
            ops: [],
          }),
        ).rejects.toThrow();
      }

      const headAfterFirst = await log.getHead('site-a');
      expect(headAfterFirst).toBe(firstShouldSucceed ? 1 : 0);

      // Caller retry must produce contiguous sequence numbers.
      transport.putFaults = [];
      const secondSeq = await log.append({
        siteId: 'site-a',
        hlc: '0x2',
        ops: [],
      });
      expect(secondSeq).toBe(firstShouldSucceed ? 2 : 1);

      const allEntries = await log.readSince('site-a', 0);
      expect(allEntries.map((entry) => entry.seq)).toEqual(
        firstShouldSucceed ? [1, 2] : [1],
      );
    } finally {
      transport.restore();
    }
  });

  test.prop([
    fc.constantFrom<ReadFault>('403', '500', 'timeout', 'stale'),
    fc.constantFrom<ReadOp>('getHead', 'listSites', 'readSinceList', 'readSinceGet'),
  ])('read/list operations fail predictably under transport/auth faults and preserve stored state', async (fault, op) => {
    const transport = new FaultingPresignTransport();
    const log = new PresignedS3ReplicatedLog({
      bucket: 'test-bucket',
      prefix: 'deltas',
      presign: transport.provider,
    });

    transport.seedEntry('deltas/site-a/0000000001.delta.bin', makeEntry('site-a', 1));

    try {
      if (op === 'getHead' || op === 'listSites' || op === 'readSinceList') {
        transport.listFaults = [fault];
      }
      if (op === 'readSinceGet') {
        transport.getFaults = [fault];
      }

      if (op === 'getHead') {
        await expect(log.getHead('site-a')).rejects.toThrow();
      } else if (op === 'listSites') {
        await expect(log.listSites()).rejects.toThrow();
      } else {
        await expect(log.readSince('site-a', 0)).rejects.toThrow();
      }

      // Under read/list failures, persisted bytes must remain unmodified.
      transport.listFaults = [];
      transport.getFaults = [];
      const entries = await log.readSince('site-a', 0);
      expect(entries).toHaveLength(1);
      expect(entries[0]!.seq).toBe(1);
      expect(decodeBin<LogEntry>(encodeBin(entries[0]!)).seq).toBe(1);
    } finally {
      transport.restore();
    }
  });
});
