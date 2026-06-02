#!/usr/bin/env bash
# Phase 1 (M1): A0 → A1 prompt formalization + checkability metrics.
#
# Underlying pdd commands (via checkup_formalize.py):
#   pdd checkup lint <A0.prompt> [--stories <dir>] --json
#   pdd checkup contract check <A0.prompt> [--stories <dir>] --json
#   pdd checkup coverage <A0.prompt> [--stories-dir <dir>] --json
#
# Usage:
#   bash benchmarks/formalization/scripts/run_m1.sh              # deterministic
#   ALLOW_LLM=1 bash benchmarks/formalization/scripts/run_m1.sh  # LLM stages
#
# Env:
#   OUTPUT_DIR   (default: experiments/latest)
#   ALLOW_LLM    (1 = --allow-llm)
#   MAX_COST_M1  (default: 25)
#   TASKS        (comma-separated; default: all corpus tasks)
set -euo pipefail
# shellcheck source=_common.sh
source "$(dirname "$0")/_common.sh"

OUTPUT_DIR="${OUTPUT_DIR:-${M1_DIR}}"
ALLOW_LLM="${ALLOW_LLM:-0}"
TASKS_ARG=()
if [[ -n "${TASKS:-}" ]]; then
  TASKS_ARG=(--tasks "${TASKS}")
fi
echo "==> Phase 1 (M1): prompt formalization"
echo "    output: ${OUTPUT_DIR}"
echo "    allow_llm: ${ALLOW_LLM}"

CMD=(
  python benchmarks/formalization/pipelines/run_experiment.py
  --output-dir "${OUTPUT_DIR}"
  "${TASKS_ARG[@]}"
)
if [[ "${ALLOW_LLM}" == "1" ]]; then
  CMD+=(--allow-llm --max-cost-usd "${MAX_COST_M1}")
fi

_run "${CMD[@]}"

echo "==> M1 complete"
echo "    REPORT: ${OUTPUT_DIR}/REPORT.md"
echo "    EVALUATION: ${OUTPUT_DIR}/EVALUATION_RESULT.md"
echo "    Next: M1_DIR=${OUTPUT_DIR} bash benchmarks/formalization/scripts/run_m2.sh"
