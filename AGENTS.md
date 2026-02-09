# Agent Notes

## Test Commands

- Run everything (Lean build + full Vitest suite):
```bash
npm run test:all
```

- Run Lean parity tests only (TypeScript vs Lean oracle / DRT):
```bash
npx vitest run test/drt/*.drt.test.ts
```

- Run Lean parity tests with higher confidence (more random runs):
```bash
DRT_NUM_RUNS=1000 DRT_TIMEOUT_MS=120000 npx vitest run test/drt/*.drt.test.ts
```

- Build Lean proof/oracle targets only:
```bash
npm run lean:build
```

- Lean-only proof/parity gate (ignore unrelated E2E while proving):
```bash
cd lean && lake build CrdtBase CrdtBaseDRT
npx vitest run test/drt/*.drt.test.ts
```

- Run current E2E matrix rows implemented in CI today (`node x http-server`, `node x s3-minio`):
```bash
npx vitest run test/e2e/three-clients.e2e.test.ts test/e2e/s3-minio.e2e.test.ts
```
