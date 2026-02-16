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

# ── Check for uncommitted changes ─────────────────────────────────────────
cd "${REPO_ROOT}"
if ! git diff --quiet HEAD 2>/dev/null || ! git diff --cached --quiet HEAD 2>/dev/null; then
    echo "WARNING: You have uncommitted changes. git archive HEAD only includes committed files."
    echo "         Uncommitted changes will NOT be tested. Commit first or use 'git stash'."
    echo ""
fi

# ── Upload source tarball ─────────────────────────────────────────────────
echo "=== Uploading source tarball ==="
SOURCE_GCS="gs://${BUCKET}/${JOB_RUN_ID}/source/pdd-source.tar.gz"
# Only include directories needed for tests (skip demos/, experiments/, examples/ etc.)
# Create plain tar first; gzip once at the end to avoid decompress/recompress cycle
git archive HEAD -- pdd/ tests/ data prompts context/ docs/ Makefile pyproject.toml requirements.txt .pdd/ .pddrc pdd-local.sh ci/ scripts/ > /tmp/pdd-source.tar

# Include pdd_cloud .pddrc if available (for TestActualPddrcConfiguration tests)
PARENT_PDDRC="${REPO_ROOT}/../.pddrc"
if [ -f "${PARENT_PDDRC}" ]; then
    cp "${PARENT_PDDRC}" /tmp/.pddrc_pddcloud
    tar -C /tmp -rf /tmp/pdd-source.tar .pddrc_pddcloud
    rm /tmp/.pddrc_pddcloud
fi

gzip /tmp/pdd-source.tar

gsutil -q cp /tmp/pdd-source.tar.gz "${SOURCE_GCS}"
rm /tmp/pdd-source.tar.gz
echo "Uploaded to ${SOURCE_GCS}"

# ── Prepare job template ──────────────────────────────────────────────────
echo "=== Preparing job template ==="
RESULTS_GCS_PATH="${BUCKET}/${JOB_RUN_ID}/results"
SOURCE_GCS_PATH="${BUCKET}/${JOB_RUN_ID}/source"

sed \
    -e "s|{{PROJECT_ID}}|${PROJECT_ID}|g" \
    -e "s|{{REGION}}|${REGION}|g" \
    -e "s|{{RESULTS_GCS_PATH}}|${RESULTS_GCS_PATH}|g" \
    -e "s|{{SOURCE_GCS_PATH}}|${SOURCE_GCS_PATH}|g" \
    "${SCRIPT_DIR}/job-template.json" > /tmp/pdd-batch-job.json

# ── Submit job ────────────────────────────────────────────────────────────
echo "=== Submitting Cloud Batch job: ${JOB_NAME} ==="
gcloud batch jobs submit "${JOB_NAME}" \
    --project="${PROJECT_ID}" \
    --location="${REGION}" \
    --config=/tmp/pdd-batch-job.json

rm /tmp/pdd-batch-job.json

# ── Poll for completion ───────────────────────────────────────────────────
echo "=== Polling for completion (${POLL_INTERVAL}s intervals, ${POLL_TIMEOUT}s timeout) ==="
ELAPSED=0
STREAMING_DIR=$(mktemp -d)
trap 'rm -rf "${STREAMING_DIR}"' EXIT

TOTAL=$(gcloud batch jobs describe "${JOB_NAME}" \
    --project="${PROJECT_ID}" --location="${REGION}" \
    --format="value(taskGroups[0].taskCount)" 2>/dev/null || echo "72")
TOTAL=${TOTAL:-72}
STREAM_FAILURES=0

while [ "${ELAPSED}" -lt "${POLL_TIMEOUT}" ]; do
    STATUS=$(gcloud batch jobs describe "${JOB_NAME}" \
        --project="${PROJECT_ID}" \
        --location="${REGION}" \
        --format="value(status.state)" 2>/dev/null || echo "UNKNOWN")

    # ── Stream completed task results ─────────────────────────────────
    gsutil -q -m cp "gs://${BUCKET}/${JOB_RUN_ID}/results/task_*.json" "${STREAMING_DIR}/" 2>/dev/null || true
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
            gsutil cat "gs://${BUCKET}/${JOB_RUN_ID}/results/task_${TASK_NUM}.log" 2>/dev/null || echo "(log not available)"
            echo ""
        fi
    done

    # ── Progress line ─────────────────────────────────────────────────
    if [ "${STREAM_FAILURES}" -gt 0 ]; then
        echo "[$(date +%H:%M:%S)] Job: ${STATUS} | ${COMPLETED}/${TOTAL} complete (${STREAM_FAILURES} failed) (${ELAPSED}s elapsed)"
    else
        echo "[$(date +%H:%M:%S)] Job: ${STATUS} | ${COMPLETED}/${TOTAL} complete (${ELAPSED}s elapsed)"
    fi

    case "${STATUS}" in
        SUCCEEDED)
            echo "=== Job completed successfully ==="
            bash "${SCRIPT_DIR}/collect-results.sh" \
                "${PROJECT_ID}" "${BUCKET}" "${JOB_RUN_ID}" "${JOB_NAME}"
            exit 0
            ;;
        FAILED)
            echo "=== Job FAILED ==="
            bash "${SCRIPT_DIR}/collect-results.sh" \
                "${PROJECT_ID}" "${BUCKET}" "${JOB_RUN_ID}" "${JOB_NAME}"
            exit 1
            ;;
        DELETION_IN_PROGRESS|STATE_UNSPECIFIED)
            echo "=== Job in unexpected state: ${STATUS} ==="
            exit 1
            ;;
    esac

    sleep "${POLL_INTERVAL}"
    ELAPSED=$((ELAPSED + POLL_INTERVAL))
done

echo "=== TIMEOUT after ${POLL_TIMEOUT}s ==="
echo "Job ${JOB_NAME} is still running. Check manually:"
echo "  gcloud batch jobs describe ${JOB_NAME} --project=${PROJECT_ID} --location=${REGION}"
exit 1
