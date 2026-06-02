# Source after setting TASK, ARM (for M2/M3), M1_DIR, M2_DIR, M3_DIR.
# shellcheck shell=bash
_CMD_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
_BENCH_ROOT="$(cd "${_CMD_ROOT}/../.." && pwd)"
_REPO_ROOT="$(cd "${_BENCH_ROOT}/../.." && pwd)"

: "${TASK:?Set TASK=email_validator}"
: "${M1_DIR:=${_BENCH_ROOT}/experiments/latest}"
: "${M2_DIR:=${_BENCH_ROOT}/experiments/m2_latest}"
: "${M3_DIR:=${_BENCH_ROOT}/experiments/m3_latest}"
: "${ARM:=A0}"

_resolve() {
  local mode="$1"
  # shellcheck disable=SC1090
  eval "$(
    python "${_CMD_ROOT}/_resolve_paths.py" "${mode}" \
      --task "${TASK}" \
      --arm "${ARM}" \
      --m1-dir "${M1_DIR}" \
      --m2-dir "${M2_DIR}" \
      --m3-dir "${M3_DIR}"
  )"
}

_echo_cmd() {
  printf '==> '
  printf '%q ' "$@"
  printf '\n'
}

_log_cmd() {
  local log_path="${COMMANDS_LOG:-}"
  [[ -n "${log_path}" ]] || return 0
  mkdir -p "$(dirname "${log_path}")"
  python3 -c 'import json, sys; print(json.dumps({"command": sys.argv[1:]}, sort_keys=True))' "$@" >>"${log_path}" 2>/dev/null || true
}

_run_cmd() {
  _echo_cmd "$@"
  _log_cmd "$@"
  exec "$@"
}
