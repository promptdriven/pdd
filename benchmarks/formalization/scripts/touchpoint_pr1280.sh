#!/usr/bin/env bash
# Human-verifiable smoke after merging main into PR #1280 (issue #1273 / epic #833).
# No API keys; finishes in under ~2 minutes on a typical laptop.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "${ROOT}"

echo "==> 1. Gate + drift unit tests (merged checkup gate / waiver policy)"
python -m pytest -q \
  tests/test_gate_main.py \
  tests/test_drift_main.py \
  tests/commands/test_checkup.py \
  -k "gate"

echo "==> 2. Formalization benchmark harness"
python -m pytest -q \
  tests/test_formalization_benchmark.py \
  tests/test_formalization_pipeline.py

echo "==> 3. CLI wiring (checkup gate + drift help)"
export PDD_AUTO_UPDATE=false
PYTHON="${PYTHON:-python}"
"${PYTHON}" -m pdd checkup gate --help >/dev/null
"${PYTHON}" -m pdd checkup drift --help >/dev/null

echo "==> 4. Corpus M1→M3 CI smoke (no LLM)"
bash benchmarks/formalization/scripts/run_eval.sh

echo "OK: touchpoint_pr1280.sh passed"
