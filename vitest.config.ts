import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: {
    environment: 'node',
    // Keep the pre-upgrade worker model and bound parallel filesystem/property
    // workloads while the patched runner performs module transforms.
    pool: 'threads',
    maxWorkers: 2,
  },
});
