#!/usr/bin/env bash
# Human-runnable touchpoint for issue #826 snapshot / replay / checkup snapshot.
set -euo pipefail

DEMO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${DEMO_DIR}/../.." && pwd)"

echo "==> Automated touchpoint (no API keys)"
cd "${REPO_ROOT}"
pytest -vv tests/test_issue_826_snapshot_touchpoint.py

echo ""
echo "==> Optional live CLI demo in ${DEMO_DIR}"
echo "    export PYTHONPATH=${REPO_ROOT}"
echo "    cd ${DEMO_DIR}"
echo "    pdd preprocess prompts/dynamic_python.prompt --snapshot"
echo "    pdd checkup snapshot prompts/dynamic_python.prompt --project-root ."
echo "    pdd replay \$(ls -1t .pdd/evidence/runs/*.json | head -1) --verify-only"
