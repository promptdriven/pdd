#!/usr/bin/env bash
# Exactly one command: pdd --force generate <prompt> --output <code> --evidence
#   TASK=email_validator ARM=A0 bash benchmarks/formalization/scripts/cmd/pdd_generate.sh
set -euo pipefail
# shellcheck source=_env.sh
source "$(dirname "$0")/_env.sh"
_resolve m2
mkdir -p "$(dirname "${CODE}")"
CMD=(pdd --force generate "${PROMPT}" --output "${CODE}" --language "${LANGUAGE:-python}" --evidence)
_run_cmd "${CMD[@]}"
