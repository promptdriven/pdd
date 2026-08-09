#!/usr/bin/env bash
# Human-runnable touchpoint for issue #826 snapshot / replay / checkup snapshot.
set -euo pipefail

DEMO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${DEMO_DIR}/../.." && pwd)"

echo "==> Automated test plan (no API keys)"
cd "${REPO_ROOT}"
pytest -q \
  tests/test_context_snapshot_replay.py \
  tests/test_context_snapshot_policy.py \
  tests/test_evidence_manifest.py \
  tests/test_issue_826_snapshot_touchpoint.py

echo ""
echo "==> Manual CLI walkthrough (from ${DEMO_DIR})"
echo "    export PYTHONPATH=${REPO_ROOT}"
echo "    cd ${DEMO_DIR}"
echo ""
echo "  # 1) Snapshot preprocess (test-plan prompt)"
echo "  pdd preprocess prompts/foo_python.prompt --snapshot"
echo ""
echo "  # 2) checkup snapshot fails until a snapshot exists"
echo "  pdd checkup snapshot prompts/with_shell_python.prompt --project-root . && echo UNEXPECTED_PASS || echo expected_fail"
echo ""
echo "  # 3) Replay latest run manifest"
echo "  RUN=\$(ls -1t .pdd/evidence/runs/*.json | head -1)"
echo "  pdd replay \"\$RUN\" --verify-only --json"
echo ""
echo "  # 4) After step 1, with_shell should still fail (different prompt); foo/dynamic pass after their own snapshot"
echo "  pdd checkup snapshot prompts/foo_python.prompt --project-root ."
echo ""
echo "  # 5) Optional: generate with snapshot + evidence (requires LLM or stub in CI tests)"
echo "  # pdd generate prompts/foo_python.prompt --output pdd/foo.py --snapshot-context --evidence --force"
echo "  # pdd replay \$(ls -1t .pdd/evidence/runs/*.json | head -1) --verify-only"
