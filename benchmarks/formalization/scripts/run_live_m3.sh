#!/usr/bin/env bash
# Live M2 generation + M3 drift (requires pdd setup + API keys).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$ROOT"

M1_DIR="${M1_DIR:-benchmarks/formalization/experiments/latest}"
M2_DIR="${M2_DIR:-benchmarks/formalization/experiments/m2_live}"
M3_DIR="${M3_DIR:-benchmarks/formalization/experiments/m3_live}"
TASKS="${TASKS:-email_validator,token_bucket,refund_handler}"
MAX_COST_M2="${MAX_COST_M2:-50}"
MAX_COST_M3="${MAX_COST_M3:-20}"
M3_RUNS="${M3_RUNS:-2}"

echo "==> M1 dir: ${M1_DIR}"
echo "==> Tasks: ${TASKS}"
echo "==> Live M2 (pdd generate/test) + M3 (pdd checkup drift regen)"

python benchmarks/formalization/pipelines/run_m3_pipeline.py \
  --allow-llm \
  --save-fixtures \
  --m1-dir "${M1_DIR}" \
  --m2-dir "${M2_DIR}" \
  --m3-dir "${M3_DIR}" \
  --tasks "${TASKS}" \
  --runs "${M3_RUNS}" \
  --max-rounds 3 \
  --max-cost-usd-m2 "${MAX_COST_M2}" \
  --max-cost-usd-m3 "${MAX_COST_M3}"

echo "==> Done"
echo "  M2: ${M2_DIR}/run_manifest.json"
echo "  M3: ${M3_DIR}/REPORT.md"
echo "  Pipeline: ${M3_DIR}/PIPELINE_RESULT.md"
