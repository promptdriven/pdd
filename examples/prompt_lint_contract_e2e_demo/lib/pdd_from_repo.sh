#!/usr/bin/env bash
# Prefer editable ``pdd`` from the repo (includes test postprocess fixes).
DEMO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO_ROOT="$(cd "$DEMO_DIR/../.." && pwd)"
if [[ -x "$REPO_ROOT/.venv/bin/pdd" ]]; then
    exec "$REPO_ROOT/.venv/bin/pdd" "$@"
fi
exec pdd "$@"
