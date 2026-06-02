#!/usr/bin/env bash
# Human-verifiable smoke for PR #1280 (issue #1273 — A0 vs A1 formalization benchmark).
# No API keys; finishes in under ~2 minutes on a typical laptop.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "${ROOT}"

echo "==> 1. CI regressions (construct_paths + M4 harness)"
python -m pytest -q \
  tests/test_construct_paths.py::test_determine_language_from_output_path_without_prompt_suffix \
  tests/test_model_efficiency_benchmark.py::test_m4_harness_smoke

echo "==> 2. Gate + drift unit tests (merged checkup gate / waiver policy)"
python -m pytest -q \
  tests/test_gate_main.py \
  tests/test_drift_main.py \
  tests/commands/test_checkup.py \
  -k "gate"

echo "==> 3. Formalization benchmark harness"
python -m pytest -q \
  tests/test_formalization_benchmark.py \
  tests/test_formalization_pipeline.py

echo "==> 4. CLI wiring (checkup gate + drift help)"
export PDD_AUTO_UPDATE=false
PYTHON="${PYTHON:-python}"
"${PYTHON}" -m pdd checkup gate --help >/dev/null
"${PYTHON}" -m pdd checkup drift --help >/dev/null

echo "==> 5. M1 A0 vs A1 (deterministic, single task)"
export PDD_AUTO_UPDATE=false
SMOKE_OUT="$(mktemp -d)"
"${PYTHON}" benchmarks/formalization/pipelines/run_experiment.py \
  --output-dir "${SMOKE_OUT}" --tasks hello_fn --dry-run
"${PYTHON}" -c "
import json, sys
from pathlib import Path
p = Path('${SMOKE_OUT}') / 'hello_fn' / 'result.json'
block = json.loads(p.read_text())['a0_vs_a1']
assert block['deterministic'] and block['a1_improves_readiness'], block
print('a0_vs_a1 OK:', block['a1']['implementation_readiness_score'],
      '>', block['a0']['implementation_readiness_score'])
"
rm -rf "${SMOKE_OUT}"

echo "==> 6. Corpus M1→M3 CI smoke (no LLM)"
bash benchmarks/formalization/scripts/run_eval.sh

echo "OK: touchpoint_pr1280.sh passed"
