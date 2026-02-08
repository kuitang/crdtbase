import { compareWithSite, Hlc } from '../hlc';

export type LwwRegister<T> = {
  val: T;
  hlc: Hlc;
  site: string;
};

export function mergeLww<T>(a: LwwRegister<T>, b: LwwRegister<T>): LwwRegister<T> {
  const cmp = compareWithSite(a.hlc, a.site, b.hlc, b.site);
  if (cmp >= 0) {
    return a;
  }
  return b;
}
