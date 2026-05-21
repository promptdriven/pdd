#!/usr/bin/env bash
# End-to-end demo for pdd prompt lint on a verifier LLM template.
#
#   bash examples/prompt_lint_e2e_demo/demo.sh             # deterministic, no API
#   bash examples/prompt_lint_e2e_demo/demo.sh --live      # real LLM clarify + smoke
#   bash examples/prompt_lint_e2e_demo/demo.sh --cleanup   # remove work copy

set -euo pipefail
export PDD_SKIP_UPDATE_CHECK=1

DEMO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$DEMO_DIR/../.." && pwd)"

pick_python() {
    if command -v python3.12 >/dev/null 2>&1; then
        command -v python3.12
        return
    fi
    command -v python3
}

PY="$(pick_python)"

if ! "$PY" -c "import pdd.cli" >/dev/null 2>&1; then
    VENV="$DEMO_DIR/.venv"
    if [[ ! -d "$VENV" ]]; then
        "$PY" -m venv "$VENV"
    fi
    # shellcheck disable=SC1091
    source "$VENV/bin/activate"
    pip install -e "$REPO_ROOT" -q
    PY=python
fi

exec "$PY" "$DEMO_DIR/lib/run_e2e.py" "$@"
