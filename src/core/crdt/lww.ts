import { compareWithSite, Hlc } from '../hlc';

export type LwwRegister<T> = {
  val: T;
  hlc: Hlc;
  site: string;
};

export function isSameLwwEvent<T>(a: LwwRegister<T>, b: LwwRegister<T>): boolean {
  return compareWithSite(a.hlc, a.site, b.hlc, b.site) === 0;
}

export function isConflictingLwwEvent<T>(a: LwwRegister<T>, b: LwwRegister<T>): boolean {
  return isSameLwwEvent(a, b) && !Object.is(a.val, b.val);
}

export function assertLwwEventConsistency<T>(a: LwwRegister<T>, b: LwwRegister<T>): void {
  if (isConflictingLwwEvent(a, b)) {
    throw new Error('conflicting LWW event identity: same (hlc, site) with different payloads');
  }
}

export function mergeLww<T>(a: LwwRegister<T>, b: LwwRegister<T>): LwwRegister<T> {
  assertLwwEventConsistency(a, b);
  const cmp = compareWithSite(a.hlc, a.site, b.hlc, b.site);
  if (cmp >= 0) {
    return a;
  }
  return b;
}
