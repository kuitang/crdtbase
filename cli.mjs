#!/usr/bin/env node

import { readFile } from 'node:fs/promises';
import { decode } from '@msgpack/msgpack';

function toJsonFriendly(value) {
  if (value instanceof Uint8Array) {
    return `<bytes:${value.length}>`;
  }
  if (Array.isArray(value)) {
    return value.map((item) => toJsonFriendly(item));
  }
  if (value && typeof value === 'object') {
    return Object.fromEntries(
      Object.entries(value).map(([key, entry]) => [key, toJsonFriendly(entry)]),
    );
  }
  return value;
}

async function dumpFile(path) {
  const bytes = await readFile(path);
  const decoded = decode(bytes);
  process.stdout.write(`${JSON.stringify(toJsonFriendly(decoded), null, 2)}\n`);
}

function printUsage() {
  process.stderr.write('Usage: node cli.mjs dump <path-to-bin>\n');
}

const [, , command, ...args] = process.argv;

if (command === 'dump' && args.length === 1) {
  dumpFile(args[0]).catch((error) => {
    process.stderr.write(`${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 1;
  });
} else {
  printUsage();
  process.exitCode = 1;
}
