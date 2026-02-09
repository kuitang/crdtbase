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
  dumpBytes(bytes);
}

function printUsage() {
  process.stderr.write('Usage: node cli.mjs dump <path-to-bin|->\n');
}

function dumpBytes(bytes) {
  const decoded = decode(bytes);
  process.stdout.write(`${JSON.stringify(toJsonFriendly(decoded), null, 2)}\n`);
}

async function readStdinBytes() {
  const chunks = [];
  for await (const chunk of process.stdin) {
    chunks.push(Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk));
  }
  return Buffer.concat(chunks);
}

async function dumpStdin() {
  const bytes = await readStdinBytes();
  if (bytes.length === 0) {
    throw new Error('stdin is empty');
  }
  dumpBytes(bytes);
}

const [, , command, ...args] = process.argv;

if (command === 'dump' && args.length === 1) {
  const action = args[0] === '-' ? dumpStdin : () => dumpFile(args[0]);
  action().catch((error) => {
    process.stderr.write(`${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 1;
  });
} else {
  printUsage();
  process.exitCode = 1;
}
