# Shared env for formalization benchmark scripts. Source only; do not execute.
# shellcheck shell=bash
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$ROOT"

# Phase output directories (override per run)
export M1_DIR="${M1_DIR:-benchmarks/formalization/experiments/latest}"
export M2_DIR="${M2_DIR:-benchmarks/formalization/experiments/m2_latest}"
export M3_DIR="${M3_DIR:-benchmarks/formalization/experiments/m3_latest}"

# Gold tasks (M2/M3). Leave unset for M1 to run all corpus tasks.
export M2_TASKS="${M2_TASKS:-email_validator,token_bucket,refund_handler}"

export MAX_COST_M1="${MAX_COST_M1:-25}"
export MAX_COST_M2="${MAX_COST_M2:-50}"
export MAX_COST_M3="${MAX_COST_M3:-20}"
export M2_MAX_ROUNDS="${M2_MAX_ROUNDS:-3}"
export M3_RUNS="${M3_RUNS:-2}"

_CMD_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/cmd" && pwd)"

_echo_cmd() {
  printf '==> '
  printf '%q ' "$@"
  printf '\n'
}

_run() {
  _echo_cmd "$@"
  "$@"
}
