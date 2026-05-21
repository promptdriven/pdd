#!/usr/bin/env bash
# Strict A/B pipeline for cost_tracker contract commands.
#
#   bash demo.sh --experiment-a          # deterministic, no API
#   bash demo.sh --live-ab               # Experiment B: clarify sandwich (API)
#   bash demo.sh --live-ab --keep-artifacts
#   bash demo.sh --cleanup

set -euo pipefail
export PDD_SKIP_UPDATE_CHECK=1

DEMO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$DEMO_DIR/../.." && pwd)"

if [[ -x "$REPO_ROOT/.venv/bin/python" ]] \
    && "$REPO_ROOT/.venv/bin/python" -c "import pdd.cli" >/dev/null 2>&1; then
    PY="$REPO_ROOT/.venv/bin/python"
elif command -v python3.12 >/dev/null 2>&1 \
    && python3.12 -c "import pdd.cli" >/dev/null 2>&1; then
    PY="$(command -v python3.12)"
elif command -v python3 >/dev/null 2>&1 \
    && python3 -c "import pdd.cli" >/dev/null 2>&1; then
    PY="$(command -v python3)"
else
    echo "ERROR: no Python with editable pdd found." >&2
    echo "  Run: cd $REPO_ROOT && pip install -e ." >&2
    echo "  Then: $REPO_ROOT/.venv/bin/python -c 'import pdd.cli'" >&2
    exit 1
fi

cleanup() {
    rm -f "$DEMO_DIR/prompts/cost_tracker_work_python.prompt"
    rm -f "$DEMO_DIR/tests/test_cost_tracker_work_before.py"
    rm -f "$DEMO_DIR/tests/test_cost_tracker_work_after.py"
    rm -rf "$DEMO_DIR/src"
    echo "Cleaned ephemeral strict_ab artifacts."
}

if [[ "${1:-}" == "--cleanup" ]]; then
    cleanup
    exit 0
fi

if [[ "${1:-}" == "--experiment-a" || "${1:-}" == "-a" ]]; then
    exec "$PY" "$DEMO_DIR/scripts/run_experiment_a.py"
fi

if [[ "${1:-}" == "--live-ab" || "${1:-}" == "--live" ]]; then
    shift || true
    keep=0
    for arg in "$@"; do
        if [[ "$arg" == "--keep-artifacts" ]]; then keep=1; fi
    done
    export KEEP_ARTIFACTS="$keep"
    exec bash "$DEMO_DIR/scripts/live_ab_pipeline.sh"
fi

echo "Usage: $0 --experiment-a | --live-ab [--keep-artifacts] | --cleanup" >&2
exit 1
