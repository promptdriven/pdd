#!/usr/bin/env bash
set -euo pipefail

# Collect secondary code metrics after each SCR step.
# Usage: ./scripts/scr_collect_metrics.sh <arm> <run_id> <workspace> <step>

if [[ $# -ne 4 ]]; then
  echo "Usage: $0 <arm> <run_id> <workspace> <step>"
  exit 1
fi

ARM="$1"
RUN_ID="$2"
WORKSPACE="$3"
STEP="$4"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
CSV="${ROOT_DIR}/results/scr_code_metrics.csv"

SOURCE="${WORKSPACE}/src/user_id_parser.py"

CODE_LINES=0
AVG_COMPLEXITY="0"
FUNCTION_COUNT=0

if [[ -f "$SOURCE" ]]; then
  CODE_LINES=$(wc -l < "$SOURCE" | tr -d ' ')

  # Use radon if available
  if command -v radon &>/dev/null; then
    # Average cyclomatic complexity
    AVG_LINE=$(radon cc "$SOURCE" -a -nc 2>/dev/null | grep "Average" || true)
    if [[ -n "$AVG_LINE" ]]; then
      # Extract numeric value from "Average complexity: X (N.N)"
      AVG_COMPLEXITY=$(echo "$AVG_LINE" | awk -F'[()]' '{print $2}' || echo "0")
    fi

    # Function count: lines starting with whitespace + F/M/C (radon function markers)
    FUNCTION_COUNT=$(radon cc "$SOURCE" -nc 2>/dev/null | grep -cE '^\s+[FMC] ' || echo "0")
  fi
fi

# Ensure CSV directory and header exist
mkdir -p "$(dirname "$CSV")"
if [[ ! -f "$CSV" ]] || [[ ! -s "$CSV" ]]; then
  echo "arm,run_id,step,code_lines,avg_complexity,function_count" > "$CSV"
fi

echo "${ARM},${RUN_ID},${STEP},${CODE_LINES},${AVG_COMPLEXITY},${FUNCTION_COUNT}" >> "$CSV"

echo "Metrics: step=${STEP} lines=${CODE_LINES} complexity=${AVG_COMPLEXITY} functions=${FUNCTION_COUNT}"
