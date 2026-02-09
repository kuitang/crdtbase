#!/usr/bin/env node

import { createServer } from 'node:http';
import { mkdir, readFile, rm } from 'node:fs/promises';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { build } from 'esbuild';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);
const projectRoot = join(__dirname, '..');

function parseArg(name, fallback) {
  const index = process.argv.indexOf(name);
  if (index >= 0 && process.argv[index + 1]) {
    return process.argv[index + 1];
  }
  return fallback;
}

const host = parseArg('--host', process.env.BROWSER_REPL_HOST ?? '127.0.0.1');
const port = Number.parseInt(parseArg('--port', process.env.BROWSER_REPL_PORT ?? '4173'), 10);
if (!Number.isFinite(port) || port <= 0) {
  throw new Error(`invalid port ${String(port)}`);
}

const sourceDir = join(projectRoot, 'src', 'repl', 'browser');
const outDir = join(projectRoot, '.repl-dist');
const outFile = join(outDir, 'app.js');

async function buildBundle() {
  await rm(outDir, { recursive: true, force: true });
  await mkdir(outDir, { recursive: true });
  await build({
    entryPoints: [join(sourceDir, 'app.ts')],
    outfile: outFile,
    bundle: true,
    format: 'esm',
    platform: 'browser',
    target: ['es2022'],
    sourcemap: false,
    logLevel: 'silent',
  });
}

function contentType(pathname) {
  if (pathname.endsWith('.html')) return 'text/html; charset=utf-8';
  if (pathname.endsWith('.css')) return 'text/css; charset=utf-8';
  if (pathname.endsWith('.js')) return 'application/javascript; charset=utf-8';
  return 'text/plain; charset=utf-8';
}

async function resolvePath(urlPath) {
  if (urlPath === '/' || urlPath === '/index.html') {
    return join(sourceDir, 'index.html');
  }
  if (urlPath === '/styles.css') {
    return join(sourceDir, 'styles.css');
  }
  if (urlPath === '/app.js') {
    return outFile;
  }
  return null;
}

async function startServer() {
  await buildBundle();

  const server = createServer(async (request, response) => {
    try {
      const url = new URL(request.url ?? '/', `http://${request.headers.host ?? 'localhost'}`);
      if (url.pathname === '/health') {
        response.statusCode = 200;
        response.setHeader('content-type', 'application/json; charset=utf-8');
        response.end(JSON.stringify({ ok: true }));
        return;
      }

      const path = await resolvePath(url.pathname);
      if (!path) {
        response.statusCode = 404;
        response.setHeader('content-type', 'text/plain; charset=utf-8');
        response.end('not found');
        return;
      }

      const bytes = await readFile(path);
      response.statusCode = 200;
      response.setHeader('content-type', contentType(path));
      response.end(bytes);
    } catch (error) {
      response.statusCode = 500;
      response.setHeader('content-type', 'text/plain; charset=utf-8');
      response.end(error instanceof Error ? error.message : String(error));
    }
  });

  await new Promise((resolve, reject) => {
    server.once('error', reject);
    server.listen(port, host, resolve);
  });

  process.stdout.write(`Browser REPL: http://${host}:${port}\n`);

  const shutdown = () => {
    server.close(() => process.exit(0));
  };
  process.on('SIGINT', shutdown);
  process.on('SIGTERM', shutdown);
}

startServer().catch((error) => {
  process.stderr.write(`${error instanceof Error ? error.message : String(error)}\n`);
  process.exitCode = 1;
});
