import { Hlc } from '../hlc';

export type OrSetTag = {
  addHlc: Hlc;
  addSite: string;
};

export type OrSetElement<T> = {
  val: T;
  tag: OrSetTag;
};

export type OrSet<T> = {
  elements: Array<OrSetElement<T>>;
  tombstones: OrSetTag[];
};

function valueFingerprint(value: unknown): string {
  const kind = typeof value;
  if (value === null || kind === 'string' || kind === 'number' || kind === 'boolean') {
    return `${kind}:${String(value)}`;
  }
  return `json:${JSON.stringify(value)}`;
}

function tagKey(tag: OrSetTag): string {
  return `${tag.addHlc.wallMs}:${tag.addHlc.counter}:${tag.addSite}`;
}

function elementSortKey<T>(element: OrSetElement<T>): string {
  return `${tagKey(element.tag)}|${valueFingerprint(element.val)}`;
}

function compareKeys(left: string, right: string): number {
  if (left < right) return -1;
  if (left > right) return 1;
  return 0;
}

export function isSameOrSetTag(a: OrSetTag, b: OrSetTag): boolean {
  return tagKey(a) === tagKey(b);
}

export function isConflictingOrSetElement<T>(a: OrSetElement<T>, b: OrSetElement<T>): boolean {
  return isSameOrSetTag(a.tag, b.tag) && !Object.is(a.val, b.val);
}

export function hasConflictingOrSetEvents<T>(a: OrSet<T>, b: OrSet<T>): boolean {
  for (const left of a.elements) {
    for (const right of b.elements) {
      if (isConflictingOrSetElement(left, right)) {
        return true;
      }
    }
  }
  return false;
}

export function assertOrSetElementConsistency<T>(elements: Array<OrSetElement<T>>): void {
  const seen = new Map<string, string>();
  for (const element of elements) {
    const key = tagKey(element.tag);
    const fingerprint = valueFingerprint(element.val);
    const prior = seen.get(key);
    if (prior !== undefined && prior !== fingerprint) {
      throw new Error(
        'conflicting OR-Set add tag identity: same (add_hlc, add_site) with different payloads',
      );
    }
    seen.set(key, fingerprint);
  }
}

function dedupeAndSortTags(tags: OrSetTag[]): OrSetTag[] {
  const seen = new Map<string, OrSetTag>();
  for (const tag of tags) {
    seen.set(tagKey(tag), tag);
  }
  return [...seen.values()].sort((left, right) => compareKeys(tagKey(left), tagKey(right)));
}

function dedupeAndSortElements<T>(elements: Array<OrSetElement<T>>): Array<OrSetElement<T>> {
  const seen = new Map<string, OrSetElement<T>>();
  for (const element of elements) {
    seen.set(elementSortKey(element), element);
  }
  return [...seen.values()].sort((left, right) => compareKeys(elementSortKey(left), elementSortKey(right)));
}

export function canonicalizeOrSet<T>(state: OrSet<T>): OrSet<T> {
  assertOrSetElementConsistency(state.elements);
  const tombstones = dedupeAndSortTags(state.tombstones);
  const tombstoneKeys = new Set(tombstones.map((tag) => tagKey(tag)));
  const elements = dedupeAndSortElements(state.elements).filter(
    (element) => !tombstoneKeys.has(tagKey(element.tag)),
  );
  return { elements, tombstones };
}

export function mergeOrSet<T>(a: OrSet<T>, b: OrSet<T>): OrSet<T> {
  return canonicalizeOrSet({
    elements: [...a.elements, ...b.elements],
    tombstones: [...a.tombstones, ...b.tombstones],
  });
}
