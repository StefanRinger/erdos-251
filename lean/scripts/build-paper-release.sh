#!/usr/bin/env bash
# One self-limited full build; dependency versions must already be prepared.
set -euo pipefail
task_root="$(cd "$(dirname "$0")/.." && pwd -P)"
cd "$task_root"
exec bash "$task_root/scripts/build-slot-run.sh" bash -c '
set -euo pipefail
mkdir -p .local-verification
task_report="$(mktemp -d .local-verification/paper-build-XXXXXXXX)"
printf "Build report: %s\n" "$task_report"
date -u +%Y-%m-%dT%H:%M:%SZ > "$task_report/started_utc.txt"
python3 scripts/core-source-manifest.py --entry PrimeGapNormality.Paper --entry PrimeGapNormality.PaperAudit > "$task_report/source_before.json"
python3 scripts/core-trust-scan.py --entry PrimeGapNormality.Paper --entry PrimeGapNormality.PaperAudit > "$task_report/trust_before.json"
set +e
lake build PrimeGapNormality.Paper PrimeGapNormality.PaperAudit > "$task_report/build.txt" 2>&1
task_exit=$?
set -e
printf "%s\n" "$task_exit" > "$task_report/build_exit.txt"
if [ "$task_exit" -ne 0 ]; then tail -100 "$task_report/build.txt"; exit "$task_exit"; fi
lake --log-level=error build --no-build PrimeGapNormality.Paper PrimeGapNormality.PaperAudit > "$task_report/freshness.txt" 2>&1
python3 scripts/core-source-manifest.py --entry PrimeGapNormality.Paper --entry PrimeGapNormality.PaperAudit > "$task_report/source_after.json"
cmp "$task_report/source_before.json" "$task_report/source_after.json"
date -u +%Y-%m-%dT%H:%M:%SZ > "$task_report/finished_utc.txt"
python3 scripts/audit-paper-build.py "$task_report" --output "$task_report/audit"
tail -5 "$task_report/build.txt"
printf "PASS: complete build, freshness, unchanged inventory and axiom audit. See %s\n" "$task_report"
'
