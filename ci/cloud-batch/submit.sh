#!/usr/bin/env bash
set -euo pipefail

# ── Configuration ──────────────────────────────────────────────────────────
PROJECT_ID="${GCP_PROJECT_ID:-prompt-driven-development-stg}"
REGION="${GCP_REGION:-us-central1}"
BUCKET="${GCS_BUCKET:-pdd-stg-ci-results}"
JOB_RUN_ID="run-$(date +%Y%m%d-%H%M%S)-$(git rev-parse --short HEAD)"
JOB_NAME="pdd-test-${JOB_RUN_ID}"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
POLL_INTERVAL=10
POLL_TIMEOUT=1800  # 30 minutes

# Portable timeout (macOS lacks GNU timeout)
_with_timeout() {
    local secs=$1; shift
    "$@" &
    local cmd_pid=$!
    ( sleep "$secs" && kill "$cmd_pid" 2>/dev/null ) >/dev/null 2>&1 &
    local sleep_pid=$!
    local rc=0
    wait "$cmd_pid" || rc=$?
    kill "$sleep_pid" 2>/dev/null || true
    wait "$sleep_pid" 2>/dev/null || true
    return "$rc"
}

# ── Prepare source path allowlist ─────────────────────────────────────────
cd "${REPO_ROOT}"
SOURCE_PATHS=(
    pdd
    tests
    data
    prompts
    context
    docs
    Makefile
    pyproject.toml
    requirements.txt
    pdd-local.sh
    ci
    scripts
)

if [ -d ".pdd" ]; then
    SOURCE_PATHS+=(".pdd")
fi

if [ -f ".pddrc" ]; then
    SOURCE_PATHS+=(".pddrc")
fi

if ! git diff --quiet HEAD 2>/dev/null || ! git diff --cached --quiet HEAD 2>/dev/null; then
    echo "=== Including local working tree changes in source upload ==="
fi

# ── Upload source tarball ─────────────────────────────────────────────────
echo "=== Uploading source tarball ==="
SOURCE_GCS="gs://${BUCKET}/${JOB_RUN_ID}/source/pdd-source.tar.gz"
# Only include directories needed for tests (skip demos/, experiments/, examples/ etc.)
# Use the current working tree so local fixes can be validated without an
# intermediate commit, but derive the file list from git so ignored files
# (for example caches or node_modules) are not uploaded.
# Create plain tar first; gzip once at the end to avoid decompress/recompress cycle
SOURCE_LIST_FILE=$(mktemp)
git -c core.quotePath=false ls-files --cached --others --exclude-standard -- "${SOURCE_PATHS[@]}" > "${SOURCE_LIST_FILE}"
COPYFILE_DISABLE=1 COPY_EXTENDED_ATTRIBUTES_DISABLE=1 tar -cf /tmp/pdd-source.tar -T "${SOURCE_LIST_FILE}"
rm -f "${SOURCE_LIST_FILE}"

# Include pdd_cloud .pddrc if available (for TestActualPddrcConfiguration tests)
PARENT_PDDRC="${REPO_ROOT}/../.pddrc"
if [ -f "${PARENT_PDDRC}" ]; then
    cp "${PARENT_PDDRC}" /tmp/.pddrc_pddcloud
    tar -C /tmp -rf /tmp/pdd-source.tar .pddrc_pddcloud
    rm /tmp/.pddrc_pddcloud
fi

gzip -f /tmp/pdd-source.tar

gcloud storage cp --quiet /tmp/pdd-source.tar.gz "${SOURCE_GCS}"
rm /tmp/pdd-source.tar.gz
echo "Uploaded to ${SOURCE_GCS}"

# ── Prepare job templates ─────────────────────────────────────────────────
echo "=== Preparing job templates ==="
RESULTS_GCS_PATH="${BUCKET}/${JOB_RUN_ID}/results"
SOURCE_GCS_PATH="${BUCKET}/${JOB_RUN_ID}/source"

_render_template() {
    sed \
        -e "s|{{PROJECT_ID}}|${PROJECT_ID}|g" \
        -e "s|{{REGION}}|${REGION}|g" \
        -e "s|{{RESULTS_GCS_PATH}}|${RESULTS_GCS_PATH}|g" \
        -e "s|{{SOURCE_GCS_PATH}}|${SOURCE_GCS_PATH}|g" \
        "$1" > "$2"
}

_render_template "${SCRIPT_DIR}/job-template.json" /tmp/pdd-batch-job-spot.json
_render_template "${SCRIPT_DIR}/job-template-standard.json" /tmp/pdd-batch-job-std.json

# ── Submit jobs ───────────────────────────────────────────────────────────
# Main SPOT job (76 tasks — everything except the slow sync_regression case_1)
JOB_NAME_SPOT="${JOB_NAME}"
echo "=== Submitting SPOT job: ${JOB_NAME_SPOT} (76 tasks) ==="
gcloud batch jobs submit "${JOB_NAME_SPOT}" \
    --project="${PROJECT_ID}" \
    --location="${REGION}" \
    --config=/tmp/pdd-batch-job-spot.json

# STANDARD job for the slow task (sync_regression case_1, immune to preemption)
JOB_NAME_STD="${JOB_NAME}-std"
echo "=== Submitting STANDARD job: ${JOB_NAME_STD} (1 task) ==="
gcloud batch jobs submit "${JOB_NAME_STD}" \
    --project="${PROJECT_ID}" \
    --location="${REGION}" \
    --config=/tmp/pdd-batch-job-std.json

rm /tmp/pdd-batch-job-spot.json /tmp/pdd-batch-job-std.json

# ── Poll for completion (both jobs) ───────────────────────────────────────
echo "=== Polling for completion (${POLL_INTERVAL}s intervals, ${POLL_TIMEOUT}s timeout) ==="
ELAPSED=0
STREAMING_DIR=$(mktemp -d)
trap 'rm -rf "${STREAMING_DIR}"' EXIT

TOTAL=77  # 76 (spot) + 1 (standard)
STREAM_FAILURES=0

_job_status() {
    _with_timeout 15 gcloud batch jobs describe "$1" \
        --project="${PROJECT_ID}" \
        --location="${REGION}" \
        --format="value(status.state)" 2>/dev/null || echo "UNKNOWN"
}

while [ "${ELAPSED}" -lt "${POLL_TIMEOUT}" ]; do
    STATUS_SPOT=$(_job_status "${JOB_NAME_SPOT}")
    STATUS_STD=$(_job_status "${JOB_NAME_STD}")

    # ── Stream completed task results ─────────────────────────────────
    _with_timeout 15 gcloud storage cp --quiet "gs://${BUCKET}/${JOB_RUN_ID}/results/task_*.json" "${STREAMING_DIR}/" 2>/dev/null || true
    COMPLETED=$(find "${STREAMING_DIR}" -maxdepth 1 -name "task_*.json" | wc -l | tr -d ' ')
    COMPLETED=${COMPLETED:-0}

    # Check for new failures
    for json_file in "${STREAMING_DIR}"/task_*.json; do
        [ -f "${json_file}" ] || continue
        # Skip files that are too small (likely partially flushed by GCS FUSE)
        [ "$(wc -c < "${json_file}")" -lt 10 ] && continue
        basename_file=$(basename "${json_file}")
        # Skip if already seen
        [ -f "${STREAMING_DIR}/seen_${basename_file}" ] && continue
        touch "${STREAMING_DIR}/seen_${basename_file}"

        TASK_STATUS=$(python3 -c "import json; d=json.load(open('${json_file}')); print(d.get('status','error'))" 2>/dev/null || echo "unknown")
        if [ "${TASK_STATUS}" != "passed" ]; then
            STREAM_FAILURES=$((STREAM_FAILURES + 1))
            TASK_NUM=$(echo "${basename_file}" | sed 's/task_\([0-9]*\)\.json/\1/')
            TASK_SUITE=$(python3 -c "import json; d=json.load(open('${json_file}')); print(d.get('suite','unknown'))" 2>/dev/null || echo "unknown")
            TASK_DETAIL=$(python3 -c "import json; d=json.load(open('${json_file}')); print(d.get('detail',''))" 2>/dev/null || echo "")
            echo ""
            echo "!! FAILURE: Task ${TASK_NUM} (${TASK_SUITE} / ${TASK_DETAIL}) !!"
            gcloud storage cat "gs://${BUCKET}/${JOB_RUN_ID}/results/task_${TASK_NUM}.log" 2>/dev/null || echo "(log not available)"
            echo ""
        fi
    done

    # ── Progress line ─────────────────────────────────────────────────
    if [ "${STREAM_FAILURES}" -gt 0 ]; then
        echo "[$(date +%H:%M:%S)] SPOT: ${STATUS_SPOT} | STD: ${STATUS_STD} | ${COMPLETED}/${TOTAL} complete (${STREAM_FAILURES} failed) (${ELAPSED}s elapsed)"
    else
        echo "[$(date +%H:%M:%S)] SPOT: ${STATUS_SPOT} | STD: ${STATUS_STD} | ${COMPLETED}/${TOTAL} complete (${ELAPSED}s elapsed)"
    fi

    # ── Check terminal states ─────────────────────────────────────────
    # Both jobs must reach a terminal state before we exit
    _is_terminal() { [[ "$1" == "SUCCEEDED" || "$1" == "FAILED" ]]; }

    if _is_terminal "${STATUS_SPOT}" && _is_terminal "${STATUS_STD}"; then
        if [ "${STATUS_SPOT}" = "SUCCEEDED" ] && [ "${STATUS_STD}" = "SUCCEEDED" ]; then
            echo "=== Both jobs completed successfully ==="
            bash "${SCRIPT_DIR}/collect-results.sh" \
                "${PROJECT_ID}" "${BUCKET}" "${JOB_RUN_ID}" "${JOB_NAME_SPOT}" "${JOB_NAME_STD}"
            exit 0
        else
            echo "=== Job(s) FAILED (spot=${STATUS_SPOT}, std=${STATUS_STD}) ==="
            bash "${SCRIPT_DIR}/collect-results.sh" \
                "${PROJECT_ID}" "${BUCKET}" "${JOB_RUN_ID}" "${JOB_NAME_SPOT}" "${JOB_NAME_STD}"
            exit 1
        fi
    fi

    # Bail on unexpected states
    for _s in "${STATUS_SPOT}" "${STATUS_STD}"; do
        case "${_s}" in
            DELETION_IN_PROGRESS|STATE_UNSPECIFIED)
                echo "=== Job in unexpected state: ${_s} ==="
                exit 1
                ;;
        esac
    done

    sleep "${POLL_INTERVAL}"
    ELAPSED=$((ELAPSED + POLL_INTERVAL))
done

echo "=== TIMEOUT after ${POLL_TIMEOUT}s ==="
echo "Jobs still running. Check manually:"
echo "  gcloud batch jobs describe ${JOB_NAME_SPOT} --project=${PROJECT_ID} --location=${REGION}"
echo "  gcloud batch jobs describe ${JOB_NAME_STD} --project=${PROJECT_ID} --location=${REGION}"
exit 1
