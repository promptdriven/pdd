#!/usr/bin/env bash
set -euo pipefail

# ── Configuration ──────────────────────────────────────────────────────────
PROJECT_ID="${GCP_PROJECT_ID:-prompt-driven-development-stg}"
REGION="${GCP_REGION:-us-central1}"
BUCKET="${GCS_BUCKET:-pdd-ci-results}"
JOB_RUN_ID="run-$(date +%Y%m%d-%H%M%S)-$(git rev-parse --short HEAD)"
JOB_NAME="pdd-test-${JOB_RUN_ID}"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
POLL_INTERVAL=15
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
git archive HEAD -- pdd/ tests/ data/ prompts/ context/ docs/ Makefile pyproject.toml requirements.txt .pdd/ .pddrc pdd-local.sh ci/ scripts/ | gzip > /tmp/pdd-source.tar.gz
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

while [ "${ELAPSED}" -lt "${POLL_TIMEOUT}" ]; do
    STATUS=$(gcloud batch jobs describe "${JOB_NAME}" \
        --project="${PROJECT_ID}" \
        --location="${REGION}" \
        --format="value(status.state)" 2>/dev/null || echo "UNKNOWN")

    echo "[$(date +%H:%M:%S)] Job status: ${STATUS} (${ELAPSED}s elapsed)"

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
