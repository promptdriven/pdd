#!/usr/bin/env bash
# Phase 3 — one task drift check (both arms unless ARM is set).
#
# Runs one pdd command per arm via cmd/pdd_drift.sh:
#   pdd checkup drift <devunit> --from-evidence <evidence.json> --code-file <code.py> [--dry-run] --json
#
#   TASK=email_validator ARM=A0 MODE=dry-run bash .../run_m3_arm.sh
#   TASK=email_validator ARM=A1 MODE=live     bash .../run_m3_arm.sh
#   TASK=email_validator MODE=dry-run         bash .../run_m3_arm.sh   # A0 + A1
#
# Env: TASK, ARM (optional), M1_DIR, M2_DIR, M3_DIR, MODE (live|dry-run)
set -euo pipefail
# shellcheck source=_common.sh
source "$(dirname "$0")/_common.sh"

TASK="${TASK:?Set TASK=email_validator}"
ARM="${ARM:-}"
MODE="${MODE:-dry-run}"

export TASK M1_DIR M2_DIR M3_DIR
OUT="${M3_DIR}/${TASK}"
mkdir -p "${OUT}"

ARMS=(A0 A1)
if [[ -n "${ARM}" ]]; then
  ARMS=("${ARM}")
fi

echo "==> M3 arm: task=${TASK} arms=${ARMS[*]} mode=${MODE} output=${OUT}"

for drift_arm in "${ARMS[@]}"; do
  echo "--- ${TASK}/${drift_arm} ---"
  ARM="${drift_arm}" bash "${_CMD_DIR}/pdd_drift.sh"
done

echo "==> M3 per-arm drift complete for ${TASK}"
echo "    logs: ${M3_DIR}/${TASK}/evidence_{A0,A1}.json"
echo "    For aggregated result.json use: bash benchmarks/formalization/scripts/run_m3.sh"
