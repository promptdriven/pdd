#!/usr/bin/env bash
# Phase 2 — one micro-step for one task + one arm.
#
# Single-step invocations call cmd/*.sh directly (one pdd or pytest command each):
#   STEP=generate → pdd --force generate <prompt> --output <code> --evidence
#   STEP=test     → pdd --force test <prompt> <code> --output <test> --evidence
#   STEP=fix      → pdd fix <prompt> <code> <test>
#   STEP=score    → pytest generated + pytest oracle
#
# Examples:
#   TASK=email_validator ARM=A0 STEP=generate bash .../run_m2_arm.sh
#   TASK=email_validator ARM=A1 STEP=test     bash .../run_m2_arm.sh
#   TASK=email_validator ARM=A0 STEP=fix      bash .../run_m2_arm.sh   # one fix round
#   TASK=email_validator ARM=A1 STEP=score    bash .../run_m2_arm.sh   # pytest only
#   TASK=email_validator ARM=A0 STEP=all      bash .../run_m2_arm.sh   # full arm loop
#   TASK=email_validator ARM=A0 STEP=replay MODE=replay bash .../run_m2_arm.sh
#
# Env: TASK, ARM (A0|A1), STEP (generate|test|fix|score|replay|all)
#      M1_DIR, M2_DIR, MODE (live|replay), M2_MAX_ROUNDS
set -euo pipefail
# shellcheck source=_common.sh
source "$(dirname "$0")/_common.sh"

TASK="${TASK:?Set TASK=email_validator}"
ARM="${ARM:?Set ARM=A0 or ARM=A1}"
STEP="${STEP:?Set STEP=generate|test|fix|score|replay|all}"
MODE="${MODE:-live}"

export TASK ARM M1_DIR M2_DIR

case "${STEP}" in
  generate)
    if [[ "${MODE}" == "replay" ]]; then
      echo "ERROR: STEP=generate with MODE=replay — use STEP=replay instead" >&2
      exit 1
    fi
    echo "==> M2 micro-step: ${TASK}/${ARM} step=${STEP} mode=${MODE}"
    bash "${_CMD_DIR}/pdd_generate.sh"
    ;;
  test)
    if [[ "${MODE}" == "replay" ]]; then
      echo "ERROR: STEP=test with MODE=replay — use STEP=replay instead" >&2
      exit 1
    fi
    echo "==> M2 micro-step: ${TASK}/${ARM} step=${STEP} mode=${MODE}"
    bash "${_CMD_DIR}/pdd_test.sh"
    ;;
  fix)
    if [[ "${MODE}" == "replay" ]]; then
      echo "ERROR: STEP=fix with MODE=replay — not applicable" >&2
      exit 1
    fi
    echo "==> M2 micro-step: ${TASK}/${ARM} step=${STEP} mode=${MODE}"
    bash "${_CMD_DIR}/pdd_fix.sh"
    ;;
  score)
    echo "==> M2 micro-step: ${TASK}/${ARM} step=${STEP} mode=${MODE}"
    bash "${_CMD_DIR}/pytest_generated.sh"
    bash "${_CMD_DIR}/pytest_oracle.sh"
    ;;
  replay|all)
    CMD=(
      python benchmarks/formalization/pipelines/run_m2_step.py
      --task "${TASK}"
      --arm "${ARM}"
      --step "${STEP}"
      --m1-dir "${M1_DIR}"
      --m2-dir "${M2_DIR}"
      --max-rounds "${M2_MAX_ROUNDS}"
    )
    case "${MODE}" in
      live)
        if [[ "${STEP}" != "replay" ]]; then
          CMD+=(--allow-llm)
        fi
        ;;
      replay)
        CMD+=(--replay-fixtures)
        ;;
      *)
        echo "ERROR: MODE must be live or replay" >&2
        exit 1
        ;;
    esac
    echo "==> M2 micro-step: ${TASK}/${ARM} step=${STEP} mode=${MODE}"
    _run "${CMD[@]}"
    ;;
  *)
    echo "ERROR: STEP must be generate|test|fix|score|replay|all (got: ${STEP})" >&2
    exit 1
    ;;
esac
