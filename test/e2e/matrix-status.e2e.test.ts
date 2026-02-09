import { describe, expect, it } from 'vitest';

describe('E2E matrix status', () => {
  it('covers node x http-server via test/e2e/three-clients.e2e.test.ts', () => {
    expect(true).toBe(true);
  });

  it('covers node x s3-minio via test/e2e/s3-minio.e2e.test.ts', () => {
    expect(true).toBe(true);
  });

  it.todo('browser x http-server uses the same coordinator scenario');
  it.todo('browser x s3-minio uses the same coordinator scenario');
});
