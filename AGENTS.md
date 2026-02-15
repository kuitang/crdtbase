# Agent Notes

## Setup

- Install dependencies:
```bash
npm install
```

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

- Run current Node E2E matrix rows (`node x http-server`, `node x s3-minio (direct S3 transport)`):
```bash
npx vitest run test/e2e/three-clients.e2e.test.ts test/e2e/s3-minio.e2e.test.ts
```

- Run TypeScript coverage with property tests + DRT + Node E2E matrix:
```bash
npm run test:coverage
```

- Run full TypeScript coverage (includes browser E2E if Playwright Chromium is available):
```bash
npm run test:coverage:all
```

- Coverage reports are emitted under:
```text
coverage/index.html
coverage/lcov.info
coverage/coverage-summary.json
```

Coverage is generated via `c8` wrapped around Vitest (stable for this property-heavy suite).
Coverage commands run Vitest with single-worker settings to avoid MinIO port collisions between parallel suites.

## Runtime Commands

- Start HTTP backend in tmux (binds `0.0.0.0:8788`):
```bash
tmux new-session -d -s crdtbase-http "cd /home/kuitang/git/crdtbase && npm run backend:http -- --host 0.0.0.0 --port 8788 --root-dir ./.crdtbase-http-server"
```

- Start Browser REPL in tmux (binds `0.0.0.0:4183`):
```bash
tmux new-session -d -s crdtbase-browser "cd /home/kuitang/git/crdtbase && npm run repl:browser -- --host 0.0.0.0 --port 4183"
```

- List tmux sessions:
```bash
tmux ls
```

- Attach to an existing tmux session (for manual control):
```bash
tmux attach -t crdtbase-http
tmux attach -t crdtbase-browser
```

- If already inside tmux, switch to another session:
```bash
tmux switch-client -t crdtbase-http
tmux switch-client -t crdtbase-browser
```

- Check Browser REPL tmux session output:
```bash
tmux capture-pane -pt crdtbase-browser
```

- Check HTTP backend tmux session output:
```bash
tmux capture-pane -pt crdtbase-http
```

- Stop tmux sessions:
```bash
tmux kill-session -t crdtbase-http
tmux kill-session -t crdtbase-browser
```

- Start Node REPL against S3/Tigris using canonical AWS env only:
```bash
source deploy/tigris/.env.local
SITE_ID=site-a npm run repl:node
```

## Tigris/AWS Commands

- Apply bucket CORS with canonical AWS CLI:
```bash
source deploy/tigris/.env.local
aws --endpoint-url "$AWS_ENDPOINT_URL_S3" s3api put-bucket-cors \
  --bucket "$BUCKET_NAME" \
  --cors-configuration file://deploy/tigris/cors.example.json
```

- Verify bucket CORS:
```bash
source deploy/tigris/.env.local
aws --endpoint-url "$AWS_ENDPOINT_URL_S3" s3api get-bucket-cors \
  --bucket "$BUCKET_NAME"
```

- Decode a remote delta object via pipe (no temp file):
```bash
source deploy/tigris/.env.local
aws --endpoint-url "$AWS_ENDPOINT_URL_S3" s3 cp \
  "s3://$BUCKET_NAME/deltas/site-a/0000000001.delta.bin" \
  - | node cli.mjs dump -
```

## Fly Stress Checklist

Use this checklist before running Fly multi-region stress to avoid token and image mismatches.

- Ensure `flyctl` is installed at `/home/kuitang/.fly/bin/flyctl` and on `PATH`:
```bash
export PATH="$HOME/.fly/bin:$PATH"
flyctl version
```

- Load canonical Tigris/AWS environment:
```bash
source deploy/tigris/.env.local
```

- Build and push a fresh stress worker image from current repo state:
```bash
APP=crdtbase-stress-260209055135
TAG="stress-$(date -u +%Y%m%d)-$(date -u +%H%M%S)"
IMAGE="registry.fly.io/${APP}:${TAG}"

export PATH="$HOME/.fly/bin:$PATH"
flyctl auth docker
docker build -f Dockerfile.stress -t "$IMAGE" .
docker push "$IMAGE"
```

- Export coordinator env (do not disable token refresh):
```bash
export FLY_APP="$APP"
export FLY_WORKER_IMAGE="$IMAGE"
export FLY_API_TOKEN_COMMAND='flyctl auth token --quiet'
export FLY_API_TOKEN="$(flyctl auth token --quiet)"
```

- Run the coordinator (example timing shape used in reports):
```bash
export STRESS_RUNS=3
export STRESS_OPS_PER_CLIENT=120
export STRESS_BARRIER_EVERY_OPS=30
export STRESS_HARD_BARRIER_EVERY=1
export STRESS_COMPACTION_EVERY_OPS=30

# Use bash built-in time (portable even when /usr/bin/time is unavailable)
TIMEFORMAT='real %3R\nuser %3U\nsys %3S'
time npm run stress:fly:coordinator
```
