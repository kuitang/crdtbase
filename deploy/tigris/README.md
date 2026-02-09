# Tigris Service Setup (No App Deploy)

This repository does not deploy a `tigris-presign` app.
Runtime replication uses direct S3 credentials (`S3ReplicatedLog`).

## 1) Provision Tigris

Create:
- one bucket (example: `crdtbase`)
- one access key pair with read/write access to that bucket

From the provisioning output or console, record:
- `bucket`
- `endpoint`
- `accessKeyId`
- `secretAccessKey`
- `region` (or use `auto`)

## 2) Configure Bucket CORS for Browser REPL

Use `deploy/tigris/cors.example.json` as a dev-safe baseline.
It currently allows all origins (`"*"`), which avoids host/port mismatch issues during local testing.
For stricter environments, replace `AllowedOrigins` with explicit origins.

With AWS CLI:

```bash
source deploy/tigris/.env.local
aws --endpoint-url "${AWS_ENDPOINT_URL_S3}" s3api put-bucket-cors \
  --bucket "${BUCKET_NAME}" \
  --cors-configuration file://deploy/tigris/cors.example.json
```

## 3) Export Environment Variables

Copy `deploy/tigris/env.tigris.example` to your local shell env file and fill in values.

Minimum variables used by this repo:
- `BUCKET_NAME`
- `AWS_ENDPOINT_URL_S3`
- `AWS_ACCESS_KEY_ID`
- `AWS_SECRET_ACCESS_KEY`
- `AWS_REGION`

## 4) Smoke Test (Node REPL)

```bash
SITE_ID=site-a \
BUCKET_NAME="$BUCKET_NAME" \
S3_PREFIX=deltas \
AWS_ENDPOINT_URL_S3="$AWS_ENDPOINT_URL_S3" \
AWS_REGION="${AWS_REGION:-auto}" \
AWS_ACCESS_KEY_ID="$AWS_ACCESS_KEY_ID" \
AWS_SECRET_ACCESS_KEY="$AWS_SECRET_ACCESS_KEY" \
npm run repl:node
```

Run:

```sql
CREATE TABLE tasks (id STRING PRIMARY KEY, title LWW<STRING>);
INSERT INTO tasks (id, title) VALUES ('t1', 'hello');
SELECT * FROM tasks;
```

## 5) Browser REPL Notes

- Start browser REPL: `npm run repl:browser -- --host 0.0.0.0 --port 4173`
- In S3 mode, you can paste JSON or env-style `KEY=value` lines (for example `BUCKET_NAME`, `AWS_ENDPOINT_URL_S3`, `AWS_ACCESS_KEY_ID`, `AWS_SECRET_ACCESS_KEY`, `AWS_REGION`).
- Unknown keys are ignored.
- CORS must allow the REPL origin.

## 6) Fly Multi-Region Stress

The repository includes a Fly coordinator that runs three region-pinned workers
against Tigris using one fresh bucket per run:

- `scripts/stress/fly-coordinator.sh`
- `test/stress/flyWorker.ts`
- `test/stress/PLAN.md`

Prerequisites:
- `flyctl`, `aws`, and `jq`
- worker image built from `Dockerfile.stress`
- exported `FLY_APP`, `FLY_WORKER_IMAGE`, and AWS/Tigris env vars

Run:

```bash
npm run stress:fly:coordinator
```
