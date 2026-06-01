#!/usr/bin/env bash
# Phase 2 — one gold task, both arms (A0 + A1).
# Full arm runs pdd generate + test + fix loop via run_m2.sh.
#   TASK=email_validator bash benchmarks/formalization/scripts/run_m2_task.sh
set -euo pipefail
# shellcheck source=_common.sh
source "$(dirname "$0")/_common.sh"

TASK="${TASK:?Set TASK=email_validator}"
export M2_TASKS="${TASK}"
bash "$(dirname "$0")/run_m2.sh"
