import { decode, encode } from '@msgpack/msgpack';

export function encodeBin(value: unknown): Uint8Array {
  return encode(value);
}

export function decodeBin<T>(bytes: Uint8Array): T {
  return decode(bytes) as T;
}
