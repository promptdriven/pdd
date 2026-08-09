#!/usr/bin/env bash
# Execute the issue #826 / PR #33 manual test plan (no merge with other branches).
set -euo pipefail

DEMO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${DEMO_DIR}/../.." && pwd)"
export PYTHONPATH="${REPO_ROOT}"
export PATH="${REPO_ROOT}/.venv/bin:${PATH}"

cd "${DEMO_DIR}"
rm -rf .pdd

echo "==> 1/4: pdd preprocess prompts/foo_python.prompt --snapshot"
pdd --quiet --force preprocess prompts/foo_python.prompt --snapshot

RUN="$(ls -1t .pdd/evidence/runs/*.json | head -1)"
echo "    wrote ${RUN}"

echo ""
echo "==> 2/4: pdd checkup snapshot prompts/with_shell_python.prompt (expect FAIL)"
set +e
pdd --quiet checkup snapshot prompts/with_shell_python.prompt --project-root .
WITH_SHELL_EXIT=$?
set -e
if [[ "${WITH_SHELL_EXIT}" -ne 1 ]]; then
  echo "ERROR: expected exit 1, got ${WITH_SHELL_EXIT}" >&2
  exit 1
fi
echo "    OK: exited ${WITH_SHELL_EXIT} as expected"

echo ""
echo "==> 3/4: pdd checkup snapshot prompts/foo_python.prompt (expect PASS)"
pdd --quiet checkup snapshot prompts/foo_python.prompt --project-root .

echo ""
echo "==> 4/4: pdd replay ${RUN}"
pdd --quiet replay "${RUN}" --verify-only --json

echo ""
echo "==> 5/5: generate --snapshot-context --evidence + replay (stubbed; no LLM keys)"
cd "${REPO_ROOT}"
pytest -q tests/test_issue_826_snapshot_touchpoint.py::test_test_plan_generate_snapshot_context_evidence_and_replay_cli

echo ""
echo "All manual test-plan steps completed."
