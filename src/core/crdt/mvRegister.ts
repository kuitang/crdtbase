import { Hlc } from '../hlc';

export type MvRegisterValue<T> = {
  val: T;
  hlc: Hlc;
  site: string;
};

export type MvRegister<T> = {
  values: Array<MvRegisterValue<T>>;
};

function valueFingerprint(value: unknown): string {
  const kind = typeof value;
  if (value === null || kind === 'string' || kind === 'number' || kind === 'boolean') {
    return `${kind}:${String(value)}`;
  }
  return `json:${JSON.stringify(value)}`;
}

function eventKey<T>(entry: MvRegisterValue<T>): string {
  return `${entry.hlc.wallMs}:${entry.hlc.counter}:${entry.site}`;
}

function entrySortKey<T>(entry: MvRegisterValue<T>): string {
  return `${eventKey(entry)}|${valueFingerprint(entry.val)}`;
}

function compareKeys(left: string, right: string): number {
  if (left < right) return -1;
  if (left > right) return 1;
  return 0;
}

export function isSameMvEvent<T>(a: MvRegisterValue<T>, b: MvRegisterValue<T>): boolean {
  return eventKey(a) === eventKey(b);
}

export function isConflictingMvEvent<T>(a: MvRegisterValue<T>, b: MvRegisterValue<T>): boolean {
  return isSameMvEvent(a, b) && !Object.is(a.val, b.val);
}

export function hasConflictingMvEvents<T>(a: MvRegister<T>, b: MvRegister<T>): boolean {
  for (const left of a.values) {
    for (const right of b.values) {
      if (isConflictingMvEvent(left, right)) {
        return true;
      }
    }
  }
  return false;
}

export function assertMvEventConsistency<T>(values: Array<MvRegisterValue<T>>): void {
  const seen = new Map<string, string>();
  for (const entry of values) {
    const key = eventKey(entry);
    const fingerprint = valueFingerprint(entry.val);
    const prior = seen.get(key);
    if (prior !== undefined && prior !== fingerprint) {
      throw new Error(
        'conflicting MV-Register event identity: same (hlc, site) with different payloads',
      );
    }
    seen.set(key, fingerprint);
  }
}

function dedupeByEvent<T>(values: Array<MvRegisterValue<T>>): Array<MvRegisterValue<T>> {
  const seen = new Map<string, MvRegisterValue<T>>();
  for (const entry of values) {
    seen.set(eventKey(entry), entry);
  }
  return [...seen.values()];
}

export function canonicalizeMvRegister<T>(state: MvRegister<T>): MvRegister<T> {
  assertMvEventConsistency(state.values);
  const deduped = dedupeByEvent(state.values);
  const values = deduped.sort((left, right) => compareKeys(entrySortKey(left), entrySortKey(right)));
  return { values };
}

export function mergeMvRegister<T>(a: MvRegister<T>, b: MvRegister<T>): MvRegister<T> {
  return canonicalizeMvRegister({
    values: [...a.values, ...b.values],
  });
}
