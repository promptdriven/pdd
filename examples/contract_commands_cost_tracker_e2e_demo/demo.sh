#!/usr/bin/env bash
# E2E demo for pdd gate / evidence / contracts author / drift on cost_tracker prompt.
#
#   bash examples/contract_commands_cost_tracker_e2e_demo/demo.sh
#   bash examples/contract_commands_cost_tracker_e2e_demo/demo.sh --live --keep-artifacts
#   bash examples/contract_commands_cost_tracker_e2e_demo/demo.sh --cleanup

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
    VENV="$REPO_ROOT/.venv"
    if [[ -d "$VENV/bin" ]]; then
        # shellcheck disable=SC1091
        source "$VENV/bin/activate"
        PY=python
    else
        echo "Install PDD: pip install -e $REPO_ROOT" >&2
        exit 1
    fi
fi

exec "$PY" "$DEMO_DIR/lib/run_e2e.py" "$@"
