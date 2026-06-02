#!/usr/bin/env bash
# Optional: record live M2 outputs into corpus/tier_gold for CI replay.
#
# Usage (after live M2):
#   M1_DIR=experiments/latest bash benchmarks/formalization/scripts/run_record_fixtures.sh
#
# Note: run_m2.sh with SAVE_FIXTURES=1 does this inline; use this if you ran M2 earlier.
set -euo pipefail
# shellcheck source=_common.sh
source "$(dirname "$0")/_common.sh"

echo "==> Recording pdd generate/test fixtures (requires prior live M2 or this re-runs generate)"
_run python benchmarks/formalization/pipelines/record_pdd_fixtures.py \
  --m1-dir "${M1_DIR}" \
  --tasks "${M2_TASKS}"

echo "==> Fixtures under corpus/tier_gold/*/pdd_generated/"
