#!/usr/bin/env bash
# Exactly one command: pdd --force test <prompt> <code> --output <test> --evidence
#   TASK=email_validator ARM=A0 bash benchmarks/formalization/scripts/cmd/pdd_test.sh
set -euo pipefail
# shellcheck source=_env.sh
source "$(dirname "$0")/_env.sh"
_resolve m2
[[ -f "${CODE}" ]] || { echo "Missing code — run pdd_generate.sh first: ${CODE}" >&2; exit 1; }
mkdir -p "$(dirname "${TEST}")"
CMD=(pdd --force test "${PROMPT}" "${CODE}" --output "${TEST}" --language "${LANGUAGE:-python}" --evidence)
_run_cmd "${CMD[@]}"
