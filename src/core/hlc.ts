export type Hlc = {
  wallMs: number;
  counter: number;
};

const WALL_MS_MAX = 2 ** 48;
const COUNTER_MAX = 2 ** 16;
export const HLC_DRIFT_LIMIT_MS = 60_000;

export const HLC_LIMITS = {
  wallMsMax: WALL_MS_MAX,
  counterMax: COUNTER_MAX,
  driftLimitMs: HLC_DRIFT_LIMIT_MS,
};

type MonotonicPerformance = {
  now(): number;
};

function normalizeMs(value: number, source: string): number {
  if (!Number.isFinite(value) || value < 0) {
    throw new Error(`invalid ${source} clock value`);
  }
  return Math.floor(value);
}

function normalizeDriftLimitMs(driftLimitMs: number): number {
  if (!Number.isInteger(driftLimitMs) || driftLimitMs < 0) {
    throw new Error('invalid HLC drift limit');
  }
  return driftLimitMs;
}

function assertHlcInBounds(hlc: Hlc): void {
  if (
    !Number.isInteger(hlc.wallMs) ||
    !Number.isInteger(hlc.counter) ||
    hlc.wallMs < 0 ||
    hlc.counter < 0 ||
    hlc.wallMs >= WALL_MS_MAX ||
    hlc.counter >= COUNTER_MAX
  ) {
    throw new Error('HLC out of bounds');
  }
}

function resolvePerformanceClock(performanceClock?: MonotonicPerformance | null): MonotonicPerformance | null {
  if (performanceClock !== undefined) {
    return performanceClock;
  }
  const candidate = (globalThis as { performance?: MonotonicPerformance }).performance;
  if (!candidate || typeof candidate.now !== 'function') {
    return null;
  }
  return candidate;
}

export function packHlc(hlc: Hlc): bigint {
  assertHlcInBounds(hlc);
  return (BigInt(hlc.wallMs) << 16n) | BigInt(hlc.counter);
}

export function compareHlc(a: Hlc, b: Hlc): number {
  const packedA = packHlc(a);
  const packedB = packHlc(b);
  if (packedA === packedB) return 0;
  return packedA > packedB ? 1 : -1;
}

export function compareWithSite(a: Hlc, aSite: string, b: Hlc, bSite: string): number {
  const hlcCmp = compareHlc(a, b);
  if (hlcCmp !== 0) return hlcCmp;
  if (aSite === bSite) return 0;
  return aSite > bSite ? 1 : -1;
}

export function assertHlcDrift(
  hlc: Hlc,
  nowMs: number,
  driftLimitMs: number = HLC_DRIFT_LIMIT_MS,
): void {
  const now = normalizeMs(nowMs, 'wall');
  const driftLimit = normalizeDriftLimitMs(driftLimitMs);
  assertHlcInBounds(hlc);
  if (hlc.wallMs > now + driftLimit) {
    throw new Error(
      `HLC drift violation: wall clock ${hlc.wallMs}ms exceeds local wall clock ${now}ms by more than ${driftLimit}ms`,
    );
  }
}

export function nextMonotonicHlc(
  previous: Hlc | null,
  nowMs: number,
  driftLimitMs: number = HLC_DRIFT_LIMIT_MS,
): Hlc {
  const now = normalizeMs(nowMs, 'wall');
  const driftLimit = normalizeDriftLimitMs(driftLimitMs);
  if (previous !== null) {
    assertHlcDrift(previous, now, driftLimit);
  }
  const wallMs = previous === null ? now : Math.max(now, previous.wallMs);
  const counter = previous !== null && wallMs === previous.wallMs ? previous.counter + 1 : 0;
  const next = { wallMs, counter };
  assertHlcInBounds(next);
  assertHlcDrift(next, now, driftLimit);
  return next;
}

export function recvMonotonicHlc(
  local: Hlc | null,
  remote: Hlc,
  nowMs: number,
  driftLimitMs: number = HLC_DRIFT_LIMIT_MS,
): Hlc {
  const now = normalizeMs(nowMs, 'wall');
  const driftLimit = normalizeDriftLimitMs(driftLimitMs);
  assertHlcDrift(remote, now, driftLimit);
  const localHlc = local ?? { wallMs: 0, counter: 0 };
  assertHlcInBounds(localHlc);
  const wallMs = Math.max(localHlc.wallMs, remote.wallMs, now);
  let counter = 0;
  if (wallMs === localHlc.wallMs && wallMs === remote.wallMs) {
    counter = Math.max(localHlc.counter, remote.counter) + 1;
  } else if (wallMs === localHlc.wallMs) {
    counter = localHlc.counter + 1;
  } else if (wallMs === remote.wallMs) {
    counter = remote.counter + 1;
  }
  const received = { wallMs, counter };
  assertHlcInBounds(received);
  return received;
}

export function createMonotonicWallClock(input: {
  dateNow?: () => number;
  performance?: MonotonicPerformance | null;
} = {}): () => number {
  const dateNow = input.dateNow ?? (() => Date.now());
  const performanceClock = resolvePerformanceClock(input.performance);

  if (performanceClock === null) {
    let last = 0;
    return () => {
      const wallNow = normalizeMs(dateNow(), 'wall');
      last = Math.max(last, wallNow);
      return last;
    };
  }

  let offsetMs = normalizeMs(dateNow(), 'wall') - normalizeMs(performanceClock.now(), 'monotonic');
  let last = 0;
  return () => {
    const monotonicNow = normalizeMs(performanceClock.now(), 'monotonic');
    const wallNow = normalizeMs(dateNow(), 'wall');
    const monotonicWallNow = offsetMs + monotonicNow;
    if (wallNow > monotonicWallNow) {
      offsetMs = wallNow - monotonicNow;
    }
    last = Math.max(last, offsetMs + monotonicNow, wallNow);
    return last;
  };
}

export type HlcClock = {
  driftLimitMs: number;
  nowWallMs(): number;
  next(previous: Hlc | null): Hlc;
  recv(local: Hlc | null, remote: Hlc): Hlc;
};

export function createHlcClock(options: {
  nowWallMs?: () => number;
  driftLimitMs?: number;
} = {}): HlcClock {
  const nowWallMs = options.nowWallMs ?? createMonotonicWallClock();
  const driftLimitMs = normalizeDriftLimitMs(options.driftLimitMs ?? HLC_DRIFT_LIMIT_MS);
  return {
    driftLimitMs,
    nowWallMs,
    next(previous: Hlc | null): Hlc {
      return nextMonotonicHlc(previous, nowWallMs(), driftLimitMs);
    },
    recv(local: Hlc | null, remote: Hlc): Hlc {
      return recvMonotonicHlc(local, remote, nowWallMs(), driftLimitMs);
    },
  };
}

export function assertHlcStrictlyIncreases(previous: Hlc | null, candidate: Hlc): void {
  if (previous !== null && compareHlc(candidate, previous) <= 0) {
    throw new Error('HLC monotonicity violation: candidate timestamp is not strictly greater');
  }
}

export class PersistedHlcFence {
  private highWater: Hlc | null;

  constructor(initial: Hlc | null = null) {
    this.highWater = initial;
  }

  loadPersisted(highWater: Hlc | null): void {
    this.highWater = highWater;
  }

  assertNext(candidate: Hlc): void {
    assertHlcStrictlyIncreases(this.highWater, candidate);
  }

  commit(candidate: Hlc): void {
    this.assertNext(candidate);
    this.highWater = candidate;
  }

  snapshot(): Hlc | null {
    return this.highWater;
  }
}
