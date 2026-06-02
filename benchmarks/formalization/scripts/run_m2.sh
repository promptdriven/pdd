#!/usr/bin/env bash
# Phase 2 (M2): pdd generate + test on A0 and A1; oracle vs non-oracle scoring.
#
# Underlying pdd commands (via generation_loop.py, or cmd/*.sh for micro-steps):
#   pdd --force generate <prompt> --output <code.py> --evidence
#   pdd --force test <prompt> <code.py> --output <test_*.py> --evidence
#   pdd fix <prompt> <code.py> <test_*.py>
#
# Usage:
#   bash benchmarks/formalization/scripts/run_m2.sh              # live (API keys)
#   MODE=replay bash benchmarks/formalization/scripts/run_m2.sh  # CI fixtures
#
# Env:
#   M1_DIR         (default: experiments/latest) — must contain <task>/A1.prompt
#   M2_DIR         (default: experiments/m2_latest)
#   MODE           live | replay  (default: live)
#   M2_MAX_ROUNDS  (default: 3)
#   MAX_COST_M2    (default: 50)
#   SAVE_FIXTURES  (1 = persist to tier_gold after live run)
#   TASKS          (default: gold m2 tasks)
set -euo pipefail
# shellcheck source=_common.sh
source "$(dirname "$0")/_common.sh"

MODE="${MODE:-live}"
TASKS_ARG=(--tasks "${M2_TASKS}")

echo "==> Phase 2 (M2): generation economics"
echo "    m1_dir: ${M1_DIR}"
echo "    output: ${M2_DIR}"
echo "    mode: ${MODE}"

CMD=(
  python benchmarks/formalization/pipelines/run_generation_benchmark.py
  --output-dir "${M2_DIR}"
  --m1-dir "${M1_DIR}"
  --skip-formalize
  "${TASKS_ARG[@]}"
  --max-rounds "${M2_MAX_ROUNDS}"
)

case "${MODE}" in
  live)
    CMD+=(--allow-llm --max-cost-usd "${MAX_COST_M2}")
    if [[ "${SAVE_FIXTURES:-0}" == "1" ]]; then
      CMD+=(--save-fixtures)
    fi
    ;;
  replay)
    CMD+=(--replay-fixtures)
    ;;
  *)
    echo "ERROR: MODE must be 'live' or 'replay' (got: ${MODE})" >&2
    exit 1
    ;;
esac

_run "${CMD[@]}"

echo "==> M2 complete"
echo "    manifest: ${M2_DIR}/run_manifest.json"
echo "    Next: bash benchmarks/formalization/scripts/run_m3.sh"
