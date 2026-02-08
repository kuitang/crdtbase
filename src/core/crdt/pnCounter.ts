export type SiteCountMap = Record<string, number>;

export type PnCounter = {
  inc: SiteCountMap;
  dec: SiteCountMap;
};

export type PnDirection = 'inc' | 'dec';

function assertFiniteNonNegative(value: number, label: string): void {
  if (!Number.isFinite(value) || value < 0) {
    throw new Error(`${label} must be a finite non-negative number`);
  }
}

function normalizeSiteCountMap(input: SiteCountMap): SiteCountMap {
  const out: SiteCountMap = {};
  for (const [site, count] of Object.entries(input)) {
    assertFiniteNonNegative(count, `count for site '${site}'`);
    if (count === 0) {
      continue;
    }
    out[site] = count;
  }
  return out;
}

function mergeSiteCountMaps(a: SiteCountMap, b: SiteCountMap): SiteCountMap {
  const out: SiteCountMap = {};
  const keys = new Set([...Object.keys(a), ...Object.keys(b)]);
  for (const key of keys) {
    const left = a[key] ?? 0;
    const right = b[key] ?? 0;
    const merged = Math.max(left, right);
    if (merged !== 0) {
      out[key] = merged;
    }
  }
  return out;
}

export function normalizePnCounter(counter: PnCounter): PnCounter {
  return {
    inc: normalizeSiteCountMap(counter.inc),
    dec: normalizeSiteCountMap(counter.dec),
  };
}

export function mergePnCounter(a: PnCounter, b: PnCounter): PnCounter {
  const left = normalizePnCounter(a);
  const right = normalizePnCounter(b);
  return {
    inc: mergeSiteCountMaps(left.inc, right.inc),
    dec: mergeSiteCountMaps(left.dec, right.dec),
  };
}

export function applyPnCounterDelta(
  counter: PnCounter,
  site: string,
  direction: PnDirection,
  amount: number,
): PnCounter {
  assertFiniteNonNegative(amount, 'counter delta amount');
  const normalized = normalizePnCounter(counter);
  const target = direction === 'inc' ? normalized.inc : normalized.dec;
  const next = {
    ...target,
    [site]: (target[site] ?? 0) + amount,
  };
  return direction === 'inc'
    ? normalizePnCounter({ inc: next, dec: normalized.dec })
    : normalizePnCounter({ inc: normalized.inc, dec: next });
}

export function pnCounterValue(counter: PnCounter): number {
  const normalized = normalizePnCounter(counter);
  const inc = Object.values(normalized.inc).reduce((sum, value) => sum + value, 0);
  const dec = Object.values(normalized.dec).reduce((sum, value) => sum + value, 0);
  return inc - dec;
}
