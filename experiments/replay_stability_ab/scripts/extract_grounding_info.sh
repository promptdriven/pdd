#!/usr/bin/env bash
set -euo pipefail

# Extract grounding metadata from PDD Cloud run logs.
# Checks model used, grounding examples injected, and cloud fallbacks.
#
# Usage: ./scripts/extract_grounding_info.sh [run_id...]
#   Default: runs 16, 17, 18

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"

if [[ $# -gt 0 ]]; then
  RUN_IDS=("$@")
else
  RUN_IDS=(16 17 18)
fi

echo "============================================"
echo "Grounding Info Extraction"
echo "============================================"

for RUN_ID in "${RUN_IDS[@]}"; do
  RUN_DIR="${ROOT_DIR}/runs/pdd/run_${RUN_ID}"

  if [[ ! -d "$RUN_DIR" ]]; then
    echo "WARNING: Run directory not found: ${RUN_DIR}"
    continue
  fi

  echo ""
  echo "--- Run ${RUN_ID} ---"

  for STEP in 0 1 2 3 4 5; do
    LOG_FILE="${RUN_DIR}/pdd_step_${STEP}.log"

    if [[ ! -f "$LOG_FILE" ]]; then
      echo "  Step ${STEP}: LOG MISSING"
      continue
    fi

    # Check cloud mode
    CLOUD_MODE=$(grep -c "use_cloud: True" "$LOG_FILE" 2>/dev/null || echo "0")

    # Check for cloud fallback (invalidates grounding test)
    FALLBACK=$(grep -c "falling back to local" "$LOG_FILE" 2>/dev/null || echo "0")

    # Extract model name from cloud response
    MODEL=$(grep "Model:" "$LOG_FILE" 2>/dev/null | head -1 | sed 's/.*Model: //' || echo "unknown")

    # Check for grounding examples used
    EXAMPLES=$(grep -c "Examples used" "$LOG_FILE" 2>/dev/null || echo "0")
    EXAMPLE_SLUGS=$(grep -A1 "Examples used" "$LOG_FILE" 2>/dev/null | grep "^ *-" | sed 's/^ *- //' || echo "")

    # Status
    if [[ "$FALLBACK" -gt 0 ]]; then
      STATUS="FALLBACK (cloud failed, used local)"
    elif [[ "$CLOUD_MODE" -gt 0 ]]; then
      STATUS="cloud"
    else
      STATUS="local"
    fi

    if [[ -n "$EXAMPLE_SLUGS" ]]; then
      echo "  Step ${STEP}: mode=${STATUS} model=${MODEL} grounding=YES (${EXAMPLE_SLUGS})"
    else
      echo "  Step ${STEP}: mode=${STATUS} model=${MODEL} grounding=no"
    fi
  done
done

echo ""
echo "============================================"
echo "Done."
echo "============================================"
