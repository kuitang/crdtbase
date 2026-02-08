export type Hlc = {
  wallMs: number;
  counter: number;
};

const WALL_MS_MAX = 2 ** 48;
const COUNTER_MAX = 2 ** 16;

export const HLC_LIMITS = {
  wallMsMax: WALL_MS_MAX,
  counterMax: COUNTER_MAX,
};

export function packHlc(hlc: Hlc): bigint {
  if (hlc.wallMs >= WALL_MS_MAX || hlc.counter >= COUNTER_MAX) {
    throw new Error('HLC out of bounds');
  }
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
