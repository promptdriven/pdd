#!/usr/bin/env bash
# Phase 3 (M3): checkup drift on M2 code (requires M2 output per task/arm).
#
# Underlying pdd command (via run_drift_benchmark.py or cmd/pdd_drift.sh):
#   pdd checkup drift <devunit> --from-evidence <evidence.json> --code-file <code.py> [--dry-run] --json
#
# Usage:
#   bash benchmarks/formalization/scripts/run_m3.sh                    # live regen
#   MODE=dry-run bash benchmarks/formalization/scripts/run_m3.sh       # no regen
#
# Env:
#   M1_DIR, M2_DIR, M3_DIR
#   MODE       live | dry-run  (default: live)
#   M3_RUNS    (default: 2)
#   MAX_COST_M3 (default: 20)
#   TASKS
set -euo pipefail
# shellcheck source=_common.sh
source "$(dirname "$0")/_common.sh"

MODE="${MODE:-live}"
TASKS_ARG=(--tasks "${M2_TASKS}")

if [[ ! -d "${M2_DIR}" ]]; then
  echo "ERROR: M2_DIR not found: ${M2_DIR}" >&2
  echo "Run: bash benchmarks/formalization/scripts/run_m2.sh" >&2
  exit 1
fi

echo "==> Phase 3 (M3): regeneration drift"
echo "    m2_dir: ${M2_DIR}"
echo "    output: ${M3_DIR}"
echo "    mode: ${MODE}"

CMD=(
  python benchmarks/formalization/pipelines/run_drift_benchmark.py
  --output-dir "${M3_DIR}"
  --m2-dir "${M2_DIR}"
  --m1-dir "${M1_DIR}"
  "${TASKS_ARG[@]}"
  --runs "${M3_RUNS}"
  --max-cost-usd "${MAX_COST_M3}"
)

case "${MODE}" in
  live)
    CMD+=(--allow-llm)
    ;;
  dry-run)
    CMD+=(--dry-run)
    ;;
  *)
    echo "ERROR: MODE must be 'live' or 'dry-run' (got: ${MODE})" >&2
    exit 1
    ;;
esac

_run "${CMD[@]}"

echo "==> M3 complete"
echo "    REPORT: ${M3_DIR}/REPORT.md"
echo "    summary: ${M3_DIR}/summary.json"
