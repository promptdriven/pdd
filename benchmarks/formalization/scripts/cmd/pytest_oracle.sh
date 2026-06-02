#!/usr/bin/env bash
# Not a pdd command — scores oracle tests only (~1s). Run after pdd generate.
#   pytest <oracle_dir>/test_*.py --import-mode=importlib -q --override-ini=pythonpath=<src>
#   TASK=email_validator ARM=A0 bash .../pytest_oracle.sh
set -euo pipefail
# shellcheck source=_env.sh
source "$(dirname "$0")/_env.sh"
_resolve m2
[[ -f "${CODE}" ]] || { echo "Missing code: ${CODE}" >&2; exit 1; }
[[ -n "${ORACLE_DIR}" ]] || { echo "No oracle_tests for task ${TASK}" >&2; exit 1; }
cd "${REPO_ROOT}"
CMD=(pytest "${ORACLE_DIR}"/test_*.py --import-mode=importlib -q --override-ini="pythonpath=${SRC_DIR}")
_run_cmd "${CMD[@]}"
