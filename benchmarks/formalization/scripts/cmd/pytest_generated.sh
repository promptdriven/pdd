#!/usr/bin/env bash
# Not a pdd command — scores pdd test output only (~1s).
#   pytest <test> --import-mode=importlib -q --override-ini=pythonpath=<src>
#   TASK=email_validator ARM=A0 bash .../pytest_generated.sh
set -euo pipefail
# shellcheck source=_env.sh
source "$(dirname "$0")/_env.sh"
_resolve m2
[[ -f "${TEST}" ]] || { echo "Missing test — run pdd_test.sh first: ${TEST}" >&2; exit 1; }
cd "${REPO_ROOT}"
CMD=(pytest "${TEST}" --import-mode=importlib -q --override-ini="pythonpath=${SRC_DIR}")
_run_cmd "${CMD[@]}"
