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

Use `deploy/tigris/cors.example.json` as a starting point and replace origins.

For local MinIO-style tooling:

```bash
mc alias set tigris "${CRDTBASE_S3_ENDPOINT}" "${CRDTBASE_S3_ACCESS_KEY_ID}" "${CRDTBASE_S3_SECRET_ACCESS_KEY}"
mc cors set tigris/"${CRDTBASE_S3_BUCKET}" deploy/tigris/cors.example.json
```

## 3) Export Environment Variables

Copy `deploy/tigris/env.tigris.example` to your local shell env file and fill in values.

Minimum variables used by this repo:
- `CRDTBASE_S3_BUCKET`
- `CRDTBASE_S3_ENDPOINT`
- `CRDTBASE_S3_ACCESS_KEY_ID`
- `CRDTBASE_S3_SECRET_ACCESS_KEY`

## 4) Smoke Test (Node REPL)

```bash
CRDTBASE_BACKEND=s3 \
CRDTBASE_SITE_ID=site-a \
CRDTBASE_S3_BUCKET="$CRDTBASE_S3_BUCKET" \
CRDTBASE_S3_PREFIX=deltas \
CRDTBASE_S3_ENDPOINT="$CRDTBASE_S3_ENDPOINT" \
CRDTBASE_S3_REGION="${CRDTBASE_S3_REGION:-auto}" \
CRDTBASE_S3_ACCESS_KEY_ID="$CRDTBASE_S3_ACCESS_KEY_ID" \
CRDTBASE_S3_SECRET_ACCESS_KEY="$CRDTBASE_S3_SECRET_ACCESS_KEY" \
npm run repl:node -- --backend s3
```

Run:

```sql
CREATE TABLE tasks (id STRING PRIMARY KEY, title LWW<STRING>);
INSERT INTO tasks (id, title) VALUES ('t1', 'hello');
SELECT * FROM tasks;
```

## 5) Browser REPL Notes

- Start browser REPL: `npm run repl:browser -- --host 0.0.0.0 --port 4173`
- In S3 mode, paste JSON config with `bucket`, `endpoint`, `accessKeyId`, `secretAccessKey`, and optional `prefix`, `region`, `forcePathStyle`.
- CORS must allow the REPL origin.
