#!/usr/bin/env bash
set -euo pipefail

# Run all 6 SCR steps (0-5) sequentially for one arm/run.
# Usage: ./scripts/run_scr_full.sh <arm> <run_id>

if [[ $# -ne 2 ]]; then
  echo "Usage: $0 <agentic|pdd> <run_id>"
  exit 1
fi

ARM="$1"
RUN_ID="$2"

if [[ "$ARM" != "agentic" && "$ARM" != "pdd" ]]; then
  echo "Error: arm must be 'agentic' or 'pdd'."
  exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
RUN_DIR="${ROOT_DIR}/runs/${ARM}/run_${RUN_ID}"
WORKSPACE="${RUN_DIR}/workspace"

echo "============================================"
echo "SCR Full Run: arm=${ARM} run_id=${RUN_ID}"
echo "============================================"

# Create workspace from baseline
"${SCRIPT_DIR}/create_run_workspace.sh" "$ARM" "$RUN_ID"

for STEP in 0 1 2 3 4 5; do
  echo ""
  echo "========================================"
  echo "Step ${STEP} — ${ARM} — Run ${RUN_ID}"
  echo "========================================"

  START_SECONDS=$(date +%s)

  # Run the step (continue on failure — record broken code and move on)
  "${SCRIPT_DIR}/run_scr_step.sh" "$ARM" "$RUN_ID" "$STEP" || true

  END_SECONDS=$(date +%s)
  ELAPSED_SECONDS=$(( END_SECONDS - START_SECONDS ))
  ELAPSED_MINUTES=$(echo "scale=3; ${ELAPSED_SECONDS} / 60" | bc)

  # Read step metadata for attempt count
  META_FILE="${RUN_DIR}/step_${STEP}_meta.txt"
  ATTEMPTS=1
  if [[ -f "$META_FILE" ]]; then
    ATTEMPTS=$(grep "^attempts=" "$META_FILE" | cut -d= -f2 || echo "1")
  fi

  # Evaluate with evaluate_run.py
  python3 "${SCRIPT_DIR}/evaluate_run.py" \
    --arm "$ARM" \
    --run-id "$RUN_ID" \
    --workspace "$WORKSPACE" \
    --active-minutes "$ELAPSED_MINUTES" \
    --test-command "pytest -q tests/test_acceptance_step_${STEP}.py" \
    --notes "SCR;step=${STEP};attempts=${ATTEMPTS}" \
    || true

  # Collect code metrics
  "${SCRIPT_DIR}/scr_collect_metrics.sh" "$ARM" "$RUN_ID" "$WORKSPACE" "$STEP" || true

done

echo ""
echo "============================================"
echo "All steps complete for ${ARM}/run_${RUN_ID}."
echo "============================================"
