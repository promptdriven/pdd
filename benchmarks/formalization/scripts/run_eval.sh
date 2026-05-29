#!/usr/bin/env bash
# Formalization benchmark evaluation (issue #1273 / epic #833).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$ROOT"
echo "==> Smoke tests"
pytest -q tests/test_formalization_benchmark.py tests/test_formalization_pipeline.py
echo "==> M1 formalization experiment (deterministic, no LLM)"
python benchmarks/formalization/pipelines/run_experiment.py \
  --output-dir benchmarks/formalization/experiments/ci_smoke
echo "==> M1 headline"
jq -r '.headline' benchmarks/formalization/experiments/ci_smoke/summary.json
echo "==> M2 generation economics (fixture replay, no LLM)"
python benchmarks/formalization/pipelines/run_generation_benchmark.py \
  --replay-fixtures \
  --skip-formalize \
  --m1-dir benchmarks/formalization/experiments/ci_smoke \
  --output-dir benchmarks/formalization/experiments/ci_m2_smoke \
  --tasks email_validator
echo "==> M3 drift (dry-run on replayed M2 code, no LLM)"
python benchmarks/formalization/pipelines/run_m3_pipeline.py \
  --replay-fixtures \
  --skip-m2 \
  --m1-dir benchmarks/formalization/experiments/ci_smoke \
  --m2-dir benchmarks/formalization/experiments/ci_m2_smoke \
  --m3-dir benchmarks/formalization/experiments/ci_m3_smoke \
  --tasks email_validator
echo "==> v0.3 static harness + report"
python benchmarks/formalization/run_benchmark.py --report
echo "==> v0.3 headline"
jq -r '.headline' benchmarks/formalization/results/summary.json
echo "==> Done. See experiments/ci_smoke/REPORT.md and results/REPORT.md"
