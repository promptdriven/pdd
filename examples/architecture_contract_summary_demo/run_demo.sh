#!/usr/bin/env bash
# Human-runnable touchpoint for issue #830 contract_summary sync.
set -euo pipefail

DEMO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${DEMO_DIR}/../.." && pwd)"

echo "==> Pytest touchpoint (no API keys; copies demo into tmp and syncs)"
cd "${REPO_ROOT}"
pytest -vv tests/test_issue_830_contract_summary_touchpoint.py

echo ""
echo "Demo fixture project: ${DEMO_DIR}"
echo "  prompts/refund_python.prompt  — contracts + capabilities"
echo "  user_stories/story__refund_cap.md"
echo "  .pdd/evidence/devunits/refund.latest.json  (from write_evidence_manifest in pytest)"
echo ""
echo "Optional (editable install from repo root: pip install -e .):"
echo "  cd ${DEMO_DIR} && PYTHONPATH=${REPO_ROOT} python3 run_demo.py"
