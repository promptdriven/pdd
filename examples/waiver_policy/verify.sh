#!/usr/bin/env bash
# Human-runnable waiver policy verification (issue #832 / PR #1331).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

FIXTURES="$ROOT/tests/fixtures/contract_check"
POLICY="$ROOT/examples/waiver_policy/gate_policy.yaml"

# Prefer the repo's editable install over a stale global `pdd` binary.
if python -m pdd.cli --help >/dev/null 2>&1; then
  PDD=(python -m pdd.cli)
elif command -v pdd >/dev/null 2>&1; then
  PDD=(pdd)
else
  echo "ERROR: install this repo first: pip install -e '.[dev]'" >&2
  exit 1
fi
export PDD_SKIP_UPDATE_CHECK=1

echo "== Waiver policy verification =="
echo "Repo: $ROOT"
echo

run() {
  echo ">> $*"
  "$@"
  echo
}

pdd_cmd() {
  "${PDD[@]}" "$@"
}

echo "--- pytest (waiver-focused) ---"
run pytest -q \
  tests/test_waiver_policy.py \
  tests/test_waiver_integration.py \
  tests/commands/test_gate.py \
  tests/test_contract_check.py::TestCheckWaivers \
  tests/test_contract_check.py::TestExtractWaivers

echo "--- pdd contracts check (valid waiver) ---"
run pdd_cmd contracts check "$FIXTURES/waiver_valid_python.prompt"

echo "--- pdd checkup coverage --json (waived rule; exit 1 = test-only gaps) ---"
echo ">> pdd checkup coverage $FIXTURES/waiver_valid_python.prompt --json"
pdd_cmd checkup coverage "$FIXTURES/waiver_valid_python.prompt" --json | head -40 || true
echo

echo "--- pdd gate: allow waivers (expect pass) ---"
run pdd_cmd gate "$FIXTURES/waiver_valid_python.prompt" --allow-waivers

echo "--- pdd gate: forbid waivers (expect fail) ---"
if pdd_cmd gate "$FIXTURES/waiver_valid_python.prompt" --forbid-waivers; then
  echo "ERROR: expected exit 1 for --forbid-waivers" >&2
  exit 1
fi
echo "(expected failure)"
echo

echo "--- pdd gate: enforce expiration (expect fail on expired fixture) ---"
if pdd_cmd gate "$FIXTURES/waiver_expired_python.prompt" --enforce-expiration; then
  echo "ERROR: expected exit 1 for expired waiver" >&2
  exit 1
fi
echo "(expected failure)"
echo

echo "--- pdd gate: policy file ---"
run pdd_cmd gate "$FIXTURES/waiver_valid_python.prompt" --policy-file "$POLICY" --allow-waivers

echo "All waiver verification steps completed successfully."
