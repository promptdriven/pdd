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

# ── Auto-update test durations from junitxml ─────────────────────────────
DURATIONS_FILE="${REPO_ROOT}/ci/cloud-batch/test-durations.json"
if ls "${RESULTS_LOCAL}"/task_*_junit.xml >/dev/null 2>&1 || ls "${RESULTS_LOCAL}"/task_*.log >/dev/null 2>&1; then
    echo "=== Updating test durations ==="
    python3 "${SCRIPT_DIR}/balance-chunks.py" record \
        --log-dir "${RESULTS_LOCAL}" \
        --output "${DURATIONS_FILE}" || echo "WARNING: Failed to update test durations"
fi

# ── Generate markdown report ──────────────────────────────────────────────
mkdir -p "${REPO_ROOT}/test-results"

COMMIT_SHA=$(cd "${REPO_ROOT}" && git rev-parse --short HEAD 2>/dev/null || echo "unknown")
TIMESTAMP=$(date -u +"%Y-%m-%d %H:%M:%S UTC")

PASSED=0
FAILED=0
ERRORS=0

# Derive task count from the Cloud Batch job (avoids hardcoding)
TOTAL=$(gcloud batch jobs describe "${JOB_NAME}" \
    --project="${PROJECT_ID}" \
    --location="${GCP_REGION:-us-central1}" \
    --format="value(taskGroups[0].taskCount)" 2>/dev/null || echo "64")
TOTAL=${TOTAL:-64}

# Parse all JSON results
TABLE_ROWS=()
FAILURE_LOGS=()

for i in $(seq 0 $((TOTAL - 1))); do
    JSON_FILE="${RESULTS_LOCAL}/task_${i}.json"
    LOG_FILE="${RESULTS_LOCAL}/task_${i}.log"

    if [ -f "${JSON_FILE}" ]; then
        STATUS=$(python3 -c "import json; d=json.load(open('${JSON_FILE}')); print(d.get('status','error'))" 2>/dev/null || echo "error")
        SUITE=$(python3 -c "import json; d=json.load(open('${JSON_FILE}')); print(d.get('suite','unknown'))" 2>/dev/null || echo "unknown")
        DETAIL=$(python3 -c "import json; d=json.load(open('${JSON_FILE}')); print(d.get('detail',''))" 2>/dev/null || echo "")
        DURATION=$(python3 -c "import json; d=json.load(open('${JSON_FILE}')); print(d.get('duration_seconds',0))" 2>/dev/null || echo "0")
        SETUP=$(python3 -c "import json; d=json.load(open('${JSON_FILE}')); print(d.get('setup_seconds',''))" 2>/dev/null || echo "")
    else
        STATUS="missing"
        SUITE="unknown"
        DETAIL="no result file"
        DURATION="0"
        SETUP=""
    fi

    case "${STATUS}" in
        passed) PASSED=$((PASSED + 1)); STATUS_ICON="PASS" ;;
        failed) FAILED=$((FAILED + 1)); STATUS_ICON="FAIL" ;;
        *)      ERRORS=$((ERRORS + 1)); STATUS_ICON="ERR"  ;;
    esac

    if [ -n "${SETUP}" ] && [ "${SETUP}" != "0" ]; then
        DURATION_COL="${DURATION}s (setup: ${SETUP}s)"
    else
        DURATION_COL="${DURATION}s"
    fi
    TABLE_ROWS+=("| ${i} | ${SUITE} | ${DETAIL} | ${STATUS_ICON} | ${DURATION_COL} |")

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

    # ── Chunk balance metrics ────────────────────────────────────────────
    BALANCE_OUTPUT=$(python3 -c "
import json, sys
results_dir = '${RESULTS_LOCAL}'
durations_file = '${DURATIONS_FILE}'

# Gather actual pytest chunk durations
chunk_durations = {}
for i in range(${TOTAL}):
    try:
        with open(f'{results_dir}/task_{i}.json') as f:
            d = json.load(f)
        if d.get('suite') == 'pytest':
            chunk_durations[d.get('detail', '')] = d.get('duration_seconds', 0)
    except (FileNotFoundError, json.JSONDecodeError):
        pass

if len(chunk_durations) < 2:
    sys.exit(0)

times = list(chunk_durations.values())
slowest = max(times)
fastest = min(t for t in times if t > 0) if any(t > 0 for t in times) else 1
ratio = slowest / fastest if fastest > 0 else 0

slowest_name = [k for k, v in chunk_durations.items() if v == slowest][0]
fastest_name = [k for k, v in chunk_durations.items() if v == fastest][0]

print(f'| Slowest chunk | {slowest_name} | {slowest}s |')
print(f'| Fastest chunk | {fastest_name} | {fastest}s |')
print(f'| Slowest/fastest ratio | | {ratio:.1f}x |')
print(f'| Total pytest chunks | | {len(chunk_durations)} |')
" 2>/dev/null || true)

    if [ -n "${BALANCE_OUTPUT}" ]; then
        echo ""
        echo "## Chunk Balance"
        echo ""
        echo "| Metric | Chunk | Value |"
        echo "|--------|-------|-------|"
        echo "${BALANCE_OUTPUT}"
    fi

    # ── Profiling: per-suite summary & slowest tests ────────────────────
    PROFILING_OUTPUT=$(python3 -c "
import json, os, sys
from collections import defaultdict

results_dir = '${RESULTS_LOCAL}'
total = ${TOTAL}

# Group task durations by suite
suite_durations = defaultdict(list)
for i in range(total):
    try:
        with open(f'{results_dir}/task_{i}.json') as f:
            d = json.load(f)
        suite = d.get('suite', 'unknown')
        dur = d.get('duration_seconds', 0)
        if dur > 0:
            suite_durations[suite].append(dur)
    except (FileNotFoundError, json.JSONDecodeError):
        pass

if not suite_durations:
    sys.exit(0)

# Per-suite summary
print('## Profiling')
print()
print('### Per-Suite Summary')
print()
print('| Suite | Min | Max | Avg | Count |')
print('|-------|-----|-----|-----|-------|')
for suite in sorted(suite_durations):
    durations = suite_durations[suite]
    mn = min(durations)
    mx = max(durations)
    avg = sum(durations) / len(durations)
    print(f'| {suite} | {mn:.0f}s | {mx:.0f}s | {avg:.0f}s | {len(durations)} |')

# Pytest chunk histogram
if 'pytest' in suite_durations:
    times = sorted(suite_durations['pytest'])
    print()
    print('### Pytest Chunk Distribution')
    print()
    max_dur = max(times)
    bar_max = 40
    for idx, t in enumerate(times):
        bar_len = int(t / max_dur * bar_max) if max_dur > 0 else 0
        bar = '#' * bar_len
        print(f'| {t:>5.0f}s | {bar} |')

# Top 20 slowest individual tests from junitxml
try:
    import xml.etree.ElementTree as ET
    slowest_tests = []
    for i in range(total):
        xml_path = f'{results_dir}/task_{i}_junit.xml'
        try:
            tree = ET.parse(xml_path)
            for tc in tree.iter('testcase'):
                t = float(tc.get('time', '0'))
                name = tc.get('name', '?')
                classname = tc.get('classname', '?')
                slowest_tests.append((t, classname, name))
        except (FileNotFoundError, ET.ParseError):
            pass

    if slowest_tests:
        slowest_tests.sort(reverse=True)
        print()
        print('### Top 20 Slowest Tests')
        print()
        print('| Duration | Module | Test |')
        print('|----------|--------|------|')
        for t, cls, name in slowest_tests[:20]:
            print(f'| {t:.1f}s | {cls} | {name} |')
except Exception:
    pass
" 2>/dev/null || true)

    if [ -n "${PROFILING_OUTPUT}" ]; then
        echo ""
        echo "${PROFILING_OUTPUT}"
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

if [ "${KEEP_RAW:-0}" = "1" ]; then
    RAW_RESULTS_DIR="${REPO_ROOT}/test-results/cloud-batch-raw"
    rm -rf "${RAW_RESULTS_DIR}"
    mkdir -p "${RAW_RESULTS_DIR}"
    cp "${RESULTS_LOCAL}"/task_*.json "${RAW_RESULTS_DIR}/" 2>/dev/null || true
    cp "${RESULTS_LOCAL}"/task_*_junit.xml "${RAW_RESULTS_DIR}/" 2>/dev/null || true
else
    rm -rf "${REPO_ROOT}/test-results/cloud-batch-raw"
    echo "(Raw JSON/XML not saved. Set KEEP_RAW=1 to preserve.)"
fi

# Clean up
rm -rf "${RESULTS_LOCAL}"

# Exit with failure if any tests failed
if [ "${FAILED}" -gt 0 ] || [ "${ERRORS}" -gt 0 ]; then
    exit 1
fi
