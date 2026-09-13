#!/usr/bin/env bash
# One self-limited verification job. Do not wrap this script in another slot.
# Existing compiled artifacts are required; this does not silently rebuild.
set -euo pipefail
task_root="$(cd "$(dirname "$0")/.." && pwd -P)"
cd "$task_root"
exec bash "$task_root/scripts/build-slot-run.sh" bash -c '
set -euo pipefail
mkdir -p .local-verification
task_report="$(mktemp -d .local-verification/kernel-replay-XXXXXXXX)"
printf "Replay report: %s\n" "$task_report"
date -u +%Y-%m-%dT%H:%M:%SZ > "$task_report/started_utc.txt"
python3 scripts/core-source-manifest.py \
  --entry PrimeGapNormality.Paper \
  --entry PrimeGapNormality.PaperAudit > "$task_report/source_manifest_before.json"
python3 scripts/core-trust-scan.py \
  --entry PrimeGapNormality.Paper \
  --entry PrimeGapNormality.PaperAudit > "$task_report/trust_scan.json"
lake --log-level=error build --no-build \
  PrimeGapNormality.Paper \
  PrimeGapNormality.PaperAudit 2>&1 | tee "$task_report/freshness_before.txt"
set +e
lake env leanchecker --fresh --verbose PrimeGapNormality.PaperAudit \
  2>&1 | tee "$task_report/kernel_replay.txt"
task_exit=$?
set -e
printf "%s\n" "$task_exit" > "$task_report/kernel_exit.txt"
if [ "$task_exit" -ne 0 ]; then exit "$task_exit"; fi
lake --log-level=error build --no-build \
  PrimeGapNormality.Paper \
  PrimeGapNormality.PaperAudit 2>&1 | tee "$task_report/freshness_after.txt"
python3 scripts/core-source-manifest.py \
  --entry PrimeGapNormality.Paper \
  --entry PrimeGapNormality.PaperAudit > "$task_report/source_manifest_after.json"
cmp "$task_report/source_manifest_before.json" "$task_report/source_manifest_after.json"
date -u +%Y-%m-%dT%H:%M:%SZ > "$task_report/finished_utc.txt"
printf "PASS: kernel replay and unchanged local source inventory. See %s\n" "$task_report"
'
