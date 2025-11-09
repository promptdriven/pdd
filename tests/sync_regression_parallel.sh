#!/bin/bash
#
# Run sync regression segments in parallel by invoking tests/sync_regression.sh
# for each numbered scenario. Defaults to running cases 1-10 with up to
# SYNC_MAX_PROCS concurrent workers.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
SYNC_SCRIPT="$SCRIPT_DIR/sync_regression.sh"
OUTPUT_BASE="$REPO_ROOT/staging"
LOG_BASE="$REPO_ROOT/test_results/sync_parallel_logs"

TARGET="${1:-all}"

# If a specific test number was requested, defer to the original script.
if [[ "$TARGET" != "all" ]]; then
    exec "$SYNC_SCRIPT" "$TARGET"
fi

mkdir -p "$LOG_BASE"

SYNC_CASES=${SYNC_TEST_CASES:-"1 2 3 4 5 6 7 8 9 10"}
MAX_PROCS=${SYNC_MAX_PROCS:-3}

declare -A PID_TO_CASE=()

launch_case() {
    local case_id=$1
    local unique_dir="$OUTPUT_BASE/sync_regression_case_${case_id}_$(date +%Y%m%d_%H%M%S)_$RANDOM"
    mkdir -p "$unique_dir"
    REGRESSION_TARGET_DIR="$unique_dir" "$SYNC_SCRIPT" "$case_id"
}

for case_id in $SYNC_CASES; do
    # Throttle background jobs to MAX_PROCS
    while [[ "$(jobs -rp | wc -l)" -ge "$MAX_PROCS" ]]; do
        sleep 2
    done

    {
        launch_case "$case_id"
    } > "$LOG_BASE/case_${case_id}.log" 2>&1 &

    PID_TO_CASE[$!]="$case_id"
done

status=0
while (( ${#PID_TO_CASE[@]} )); do
    if wait -n; then
        case_status=0
    else
        case_status=$?
    fi

    # Identify which PID finished (removed from job list).
    running_pids="$(jobs -rp)"
    finished_pid=""
    for pid in "${!PID_TO_CASE[@]}"; do
        if ! grep -qx "$pid" <<< "$running_pids"; then
            finished_pid="$pid"
            break
        fi
    done
    # Fallback: if grep failed (e.g., last job), pick remaining key.
    if [[ -z "$finished_pid" ]]; then
        for pid in "${!PID_TO_CASE[@]}"; do
            finished_pid="$pid"
            break
        done
    fi

    case_id="${PID_TO_CASE[$finished_pid]}"
    unset PID_TO_CASE["$finished_pid"]

    if [[ $case_status -eq 0 ]]; then
        echo "[sync-regression] Case $case_id completed successfully"
    else
        echo "[sync-regression] Case $case_id failed (exit $case_status)" >&2
        status=1
    fi
done

exit $status
