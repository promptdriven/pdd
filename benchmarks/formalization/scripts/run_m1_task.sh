#!/usr/bin/env bash
# Phase 1 — one corpus task.
# Delegates to run_m1.sh (checkup loop: pdd checkup lint / contract check / coverage).
#   TASK=email_validator bash benchmarks/formalization/scripts/run_m1_task.sh
set -euo pipefail
# shellcheck source=_common.sh
source "$(dirname "$0")/_common.sh"

TASK="${TASK:?Set TASK=email_validator (or hello_fn, token_bucket, ...)}"
export TASKS="${TASK}"
bash "$(dirname "$0")/run_m1.sh"
