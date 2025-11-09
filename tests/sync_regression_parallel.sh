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

declare -a PIDS=()
declare -a CASE_IDS=()

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

    PIDS+=($!)
    CASE_IDS+=("$case_id")
done

status=0
for idx in "${!PIDS[@]}"; do
    pid=${PIDS[$idx]}
    case_id=${CASE_IDS[$idx]}
    if wait "$pid"; then
        echo "[sync-regression] Case $case_id completed successfully"
    else
        echo "[sync-regression] Case $case_id failed" >&2
        status=1
    fi
done

exit $status
