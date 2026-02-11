#!/usr/bin/env bash
set -euo pipefail

# ── Arguments ──────────────────────────────────────────────────────────────
PROJECT_ID="${1:?Usage: collect-results.sh PROJECT_ID BUCKET JOB_RUN_ID JOB_NAME}"
BUCKET="${2:?}"
JOB_RUN_ID="${3:?}"
JOB_NAME="${4:?}"

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
RESULTS_LOCAL="/tmp/pdd-batch-results-${JOB_RUN_ID}"
OUTPUT_FILE="${REPO_ROOT}/test-results/cloud-batch-results.md"

# ── Download results ──────────────────────────────────────────────────────
echo "=== Downloading results from GCS ==="
mkdir -p "${RESULTS_LOCAL}"
gsutil -q -m cp "gs://${BUCKET}/${JOB_RUN_ID}/results/*" "${RESULTS_LOCAL}/" 2>/dev/null || true

# ── Generate markdown report ──────────────────────────────────────────────
mkdir -p "${REPO_ROOT}/test-results"

COMMIT_SHA=$(cd "${REPO_ROOT}" && git rev-parse --short HEAD 2>/dev/null || echo "unknown")
TIMESTAMP=$(date -u +"%Y-%m-%d %H:%M:%S UTC")

PASSED=0
FAILED=0
ERRORS=0
TOTAL=56

# Parse all JSON results
TABLE_ROWS=()
FAILURE_LOGS=()

for i in $(seq 0 55); do
    JSON_FILE="${RESULTS_LOCAL}/task_${i}.json"
    LOG_FILE="${RESULTS_LOCAL}/task_${i}.log"

    if [ -f "${JSON_FILE}" ]; then
        STATUS=$(python3 -c "import json; d=json.load(open('${JSON_FILE}')); print(d.get('status','error'))" 2>/dev/null || echo "error")
        SUITE=$(python3 -c "import json; d=json.load(open('${JSON_FILE}')); print(d.get('suite','unknown'))" 2>/dev/null || echo "unknown")
        DETAIL=$(python3 -c "import json; d=json.load(open('${JSON_FILE}')); print(d.get('detail',''))" 2>/dev/null || echo "")
        DURATION=$(python3 -c "import json; d=json.load(open('${JSON_FILE}')); print(d.get('duration_seconds',0))" 2>/dev/null || echo "0")
    else
        STATUS="missing"
        SUITE="unknown"
        DETAIL="no result file"
        DURATION="0"
    fi

    case "${STATUS}" in
        passed) PASSED=$((PASSED + 1)); STATUS_ICON="PASS" ;;
        failed) FAILED=$((FAILED + 1)); STATUS_ICON="FAIL" ;;
        *)      ERRORS=$((ERRORS + 1)); STATUS_ICON="ERR"  ;;
    esac

    TABLE_ROWS+=("| ${i} | ${SUITE} | ${DETAIL} | ${STATUS_ICON} | ${DURATION}s |")

    # Collect failure logs
    if [ "${STATUS}" != "passed" ] && [ -f "${LOG_FILE}" ]; then
        FAILURE_LOGS+=("### Task ${i}: ${SUITE} / ${DETAIL}

\`\`\`
$(cat "${LOG_FILE}")
\`\`\`
")
    fi
done

# ── Write report ──────────────────────────────────────────────────────────
{
    echo "# Cloud Batch Test Results"
    echo ""
    echo "- **Job**: ${JOB_NAME}"
    echo "- **Commit**: ${COMMIT_SHA}"
    echo "- **Timestamp**: ${TIMESTAMP}"
    echo ""

    if [ "${FAILED}" -eq 0 ] && [ "${ERRORS}" -eq 0 ]; then
        echo "**${PASSED} passed, ${FAILED} failed, ${ERRORS} errors (of ${TOTAL} tasks)**"
    else
        echo "**${PASSED} passed, ${FAILED} failed, ${ERRORS} errors (of ${TOTAL} tasks)**"
    fi

    echo ""
    echo "## Results"
    echo ""
    echo "| Task | Suite | Detail | Status | Duration |"
    echo "|------|-------|--------|--------|----------|"
    if [ ${#TABLE_ROWS[@]} -gt 0 ]; then
        for row in "${TABLE_ROWS[@]}"; do
            echo "${row}"
        done
    fi

    if [ ${#FAILURE_LOGS[@]} -gt 0 ]; then
        echo ""
        echo "## Failures"
        echo ""
        for log in "${FAILURE_LOGS[@]}"; do
            echo "${log}"
            echo ""
        done
    fi
} > "${OUTPUT_FILE}"

# ── Print summary to terminal ─────────────────────────────────────────────
echo ""
echo "=============================================="
echo "  Cloud Batch Test Results"
echo "  Job: ${JOB_NAME}"
echo "  Commit: ${COMMIT_SHA}"
echo ""
echo "  ${PASSED} passed, ${FAILED} failed, ${ERRORS} errors (of ${TOTAL} tasks)"
echo "=============================================="
echo ""
echo "Full report: ${OUTPUT_FILE}"

# Clean up
rm -rf "${RESULTS_LOCAL}"

# Exit with failure if any tests failed
if [ "${FAILED}" -gt 0 ] || [ "${ERRORS}" -gt 0 ]; then
    exit 1
fi
