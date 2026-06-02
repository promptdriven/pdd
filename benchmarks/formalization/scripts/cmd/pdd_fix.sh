#!/usr/bin/env bash
# Exactly one command: pdd fix <prompt> <code> <test>
#   TASK=email_validator ARM=A0 bash benchmarks/formalization/scripts/cmd/pdd_fix.sh
set -euo pipefail
# shellcheck source=_env.sh
source "$(dirname "$0")/_env.sh"
_resolve m2
[[ -f "${CODE}" ]] || { echo "Missing code: ${CODE}" >&2; exit 1; }
[[ -f "${TEST}" ]] || { echo "Missing test — run pdd_test.sh first: ${TEST}" >&2; exit 1; }
CMD=(pdd fix "${PROMPT}" "${CODE}" "${TEST}")
_run_cmd "${CMD[@]}"
