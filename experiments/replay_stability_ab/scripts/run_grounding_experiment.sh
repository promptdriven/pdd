#!/usr/bin/env bash
set -euo pipefail

# Grounding Experiment: PDD Cloud (with few-shot examples) vs PDD Local
#
# Runs 3 PDD Cloud runs (16, 17, 18) through all 6 SCR steps.
# Control arm (runs 13-15, PDD --local, no grounding) already exists.
#
# Usage: ./scripts/run_grounding_experiment.sh
#
# Prerequisites:
#   - Firebase credentials in environment (PDD_JWT_TOKEN or NEXT_PUBLIC_FIREBASE_API_KEY + GITHUB_CLIENT_ID)
#   - PDD Cloud Function deployed and accessible

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Enable cloud mode (disables --local flag in run_scr_step.sh)
export PDD_CLOUD=1

echo "============================================"
echo "Grounding Experiment — PDD Cloud"
echo "PDD_CLOUD=${PDD_CLOUD}"
echo "============================================"

for RUN_ID in 16 17 18; do
  echo ""
  echo "=== Grounding Run ${RUN_ID} (PDD Cloud) ==="
  "${SCRIPT_DIR}/run_scr_full.sh" pdd "$RUN_ID"
done

echo ""
echo "============================================"
echo "Grounding experiment complete."
echo "Next steps:"
echo "  ./scripts/extract_grounding_info.sh"
echo "  python3 scripts/grounding_summarize.py"
echo "============================================"
