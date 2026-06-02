#!/usr/bin/env bash
# Model-efficiency benchmark smoke (M4) — no API keys.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$ROOT"
echo "==> M4 model-efficiency harness (replay fixtures + recorded A1)"
python benchmarks/model_efficiency/pipelines/run_model_efficiency.py \
  --harness-only \
  --tasks email_validator \
  --runs 1 \
  --output-dir benchmarks/model_efficiency/experiments/ci_smoke
echo "==> M4 headline"
jq -r '.headline' benchmarks/model_efficiency/experiments/ci_smoke/summary.json
echo "==> Core comparison (budget+A1 vs smart+A0)"
jq '.core_comparison.budget_A1_minus_smart_A0' \
  benchmarks/model_efficiency/experiments/ci_smoke/summary.json
echo "==> Done."
