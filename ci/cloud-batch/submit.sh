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
POLL_INTERVAL="${POLL_INTERVAL:-5}"
POLL_TIMEOUT="${POLL_TIMEOUT:-12600}"  # Serial cloud cases: 8x1200s + bounded margins.
SPOT_PROVISIONING_MODEL="${PDD_CLOUD_BATCH_SPOT_PROVISIONING_MODEL:-SPOT}"
AR_IMAGE="${REGION}-docker.pkg.dev/${PROJECT_ID}/pdd-ci/pdd-test"

if ! [[ "${PROJECT_ID}" =~ ^[a-z][a-z0-9-]{4,28}[a-z0-9]$ ]]; then
    echo "Invalid GCP project identity" >&2
    exit 2
fi

case "${SPOT_PROVISIONING_MODEL}" in
    SPOT|STANDARD) ;;
    *)
        echo "Invalid PDD_CLOUD_BATCH_SPOT_PROVISIONING_MODEL='${SPOT_PROVISIONING_MODEL}'. Expected SPOT or STANDARD." >&2
        exit 2
        ;;
esac

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

# Snapshot pre-existing multiprocessing PIDs so we can later identify gcloud-leaked workers.
_pre_gcloud_workers="$(pgrep -f 'multiprocessing\.spawn|multiprocessing\.resource_tracker' 2>/dev/null | sort -u || true)"
trap 'cleanup_leaked_gcloud_workers' EXIT

# Sweep gcloud's leaked multiprocessing workers that this script spawned.
# Scope is bounded by the pre-script snapshot: only workers that didn't exist before
# the script started are killed. The PPID==1 filter was dropped because gcloud's
# workers don't always re-parent to init by the time the EXIT trap fires — some
# parents in gcloud's pool stay alive past the gcloud-cli command exit and only
# die later. Snapshot-and-diff alone is narrow enough to avoid killing unrelated
# workers from other processes that pre-existed this script.
cleanup_leaked_gcloud_workers() {
    [ -z "${_pre_gcloud_workers+x}" ] && return 0
    local now_workers new_workers pid
    local -a term_pids=()
    now_workers="$(pgrep -f 'multiprocessing\.spawn|multiprocessing\.resource_tracker' 2>/dev/null | sort -u || true)"
    [ -z "${now_workers}" ] && return 0
    new_workers="$(comm -13 <(printf '%s\n' "${_pre_gcloud_workers}") <(printf '%s\n' "${now_workers}") 2>/dev/null || true)"
    [ -z "${new_workers}" ] && return 0
    while IFS= read -r pid; do
        [ -z "${pid}" ] && continue
        term_pids+=("${pid}")
    done < <(printf '%s\n' "${new_workers}")
    [ "${#term_pids[@]}" -eq 0 ] && return 0
    kill -TERM "${term_pids[@]}" 2>/dev/null || true
    sleep 1
    kill -KILL "${term_pids[@]}" 2>/dev/null || true
}

# ── Prepare source path allowlist ─────────────────────────────────────────
cd "${REPO_ROOT}"
if [ -n "$(git status --porcelain=v1 --untracked-files=all)" ]; then
    echo "Cloud Batch release candidate worktree is not clean" >&2
    exit 2
fi
IMAGE_DEPS_SHA256="$(make -s cloud-image-hash)"
case "${IMAGE_DEPS_SHA256}" in
    ''|*[!0-9a-f]*) echo "Invalid Cloud Batch image dependency hash" >&2; exit 2 ;;
esac
[ "${#IMAGE_DEPS_SHA256}" -eq 64 ] || { echo "Invalid Cloud Batch image dependency hash" >&2; exit 2; }
IMAGE_TAG="deps-${IMAGE_DEPS_SHA256}"
IMAGE_DIGEST=$(gcloud artifacts docker images describe "${AR_IMAGE}:${IMAGE_TAG}" \
    --project="${PROJECT_ID}" \
    --format='value(image_summary.digest)')
case "${IMAGE_DIGEST}" in
    sha256:[0-9a-f][0-9a-f]*) ;;
    *) echo "Candidate Cloud Batch image digest unavailable" >&2; exit 2 ;;
esac
[ "${#IMAGE_DIGEST}" -eq 71 ] || { echo "Candidate Cloud Batch image digest unavailable" >&2; exit 2; }
case "${IMAGE_DIGEST#sha256:}" in
    *[!0-9a-f]*) echo "Candidate Cloud Batch image digest unavailable" >&2; exit 2 ;;
esac
IMAGE_URI="${AR_IMAGE}@${IMAGE_DIGEST}"

_resolve_secret_resource() {
    local secret_name="$1" described version
    described=$(gcloud secrets versions describe latest \
        --secret="${secret_name}" \
        --project="${PROJECT_ID}" \
        --format='value(name)')
    version="${described##*/}"
    case "${version}" in
        ''|0|*[!0-9]*) echo "Pinned credential version unavailable" >&2; return 1 ;;
    esac
    printf 'projects/%s/secrets/%s/versions/%s\n' \
        "${PROJECT_ID}" "${secret_name}" "${version}"
}

GCS_HMAC_ACCESS_KEY_ID_SECRET_RESOURCE=$(_resolve_secret_resource GCS_HMAC_ACCESS_KEY_ID)
GCS_HMAC_SECRET_ACCESS_KEY_SECRET_RESOURCE=$(_resolve_secret_resource GCS_HMAC_SECRET_ACCESS_KEY)
OPENAI_API_KEY_SECRET_RESOURCE=$(_resolve_secret_resource OPENAI_API_KEY)
FIREBASE_API_KEY_SECRET_RESOURCE=$(_resolve_secret_resource staging-firebase-api-key)
GITHUB_CLIENT_ID_SECRET_RESOURCE=$(_resolve_secret_resource github-client-id)
PDD_REFRESH_TOKEN_SECRET_RESOURCE=$(_resolve_secret_resource pdd-refresh-token)
CLAUDE_CODE_OAUTH_TOKEN_SECRET_RESOURCE=$(_resolve_secret_resource CLAUDE_CODE_OAUTH_TOKEN)
PINNED_SECRET_RESOURCES=(
    "${GCS_HMAC_ACCESS_KEY_ID_SECRET_RESOURCE}"
    "${GCS_HMAC_SECRET_ACCESS_KEY_SECRET_RESOURCE}"
    "${OPENAI_API_KEY_SECRET_RESOURCE}"
    "${FIREBASE_API_KEY_SECRET_RESOURCE}"
    "${GITHUB_CLIENT_ID_SECRET_RESOURCE}"
    "${PDD_REFRESH_TOKEN_SECRET_RESOURCE}"
    "${CLAUDE_CODE_OAUTH_TOKEN_SECRET_RESOURCE}"
)

# ── Upload source tarball ─────────────────────────────────────────────────
echo "=== Uploading source tarball ==="
SOURCE_GCS_OBJECT="${JOB_RUN_ID}/source/pdd-source.tar.gz"
SOURCE_GCS="gs://${BUCKET}/${JOB_RUN_ID}/source/pdd-source.tar.gz"
# Reproduce setuptools-scm's version for the exact candidate; pass it as a
# nonsecret job identity rather than appending host-local files to the archive.
_pdd_tag="$(git describe --tags --abbrev=0 --match 'v*' 2>/dev/null | sed 's/^v//' || true)"
_pdd_tag="${_pdd_tag:-0.0.0}"
_pdd_distance="$(git rev-list --count "v${_pdd_tag}..HEAD" 2>/dev/null || echo 0)"
case "${_pdd_distance}" in ''|*[!0-9]*) _pdd_distance=0 ;; esac
if [ "${_pdd_distance}" -eq 0 ]; then
    PDD_PACKAGE_VERSION="${_pdd_tag}"
else
    _pdd_major="${_pdd_tag%%.*}"
    _pdd_rest="${_pdd_tag#*.}"
    _pdd_minor="${_pdd_rest%%.*}"
    _pdd_patch="${_pdd_rest#*.}"
    case "${_pdd_patch}" in ''|*[!0-9]*) _pdd_patch=0 ;; esac
    _pdd_next_patch=$((_pdd_patch + 1))
    PDD_PACKAGE_VERSION="${_pdd_major}.${_pdd_minor}.${_pdd_next_patch}.dev${_pdd_distance}"
fi

SOURCE_IDENTITY_JSON=$(python3 "${SCRIPT_DIR}/source-identity.py" archive \
    --repo "${REPO_ROOT}" \
    --output /tmp/pdd-source.tar.gz)
CANDIDATE_SHA=$(python3 -c 'import json,sys; print(json.load(sys.stdin)["candidate_sha"])' <<<"${SOURCE_IDENTITY_JSON}")
CANDIDATE_TREE=$(python3 -c 'import json,sys; print(json.load(sys.stdin)["candidate_tree"])' <<<"${SOURCE_IDENTITY_JSON}")
SOURCE_SHA256=$(python3 -c 'import json,sys; print(json.load(sys.stdin)["source_sha256"])' <<<"${SOURCE_IDENTITY_JSON}")
SOURCE_SIZE=$(python3 -c 'import json,sys; print(json.load(sys.stdin)["source_size"])' <<<"${SOURCE_IDENTITY_JSON}")

gcloud storage cp --quiet --if-generation-match=0 /tmp/pdd-source.tar.gz "${SOURCE_GCS}"
SOURCE_OBJECT_JSON=$(gcloud storage objects describe "${SOURCE_GCS}" \
    --format='json(generation,size)')
SOURCE_GCS_GENERATION=$(python3 -c 'import json,sys; print(json.load(sys.stdin)["generation"])' <<<"${SOURCE_OBJECT_JSON}")
UPLOADED_SOURCE_SIZE=$(python3 -c 'import json,sys; print(json.load(sys.stdin)["size"])' <<<"${SOURCE_OBJECT_JSON}")
[[ "${SOURCE_GCS_GENERATION}" =~ ^[1-9][0-9]*$ ]] || {
    echo "Uploaded source identity invalid" >&2
    exit 2
}
[[ "${SOURCE_SIZE}" =~ ^[1-9][0-9]*$ ]] || {
    echo "Uploaded source identity invalid" >&2
    exit 2
}
[ "${UPLOADED_SOURCE_SIZE}" = "${SOURCE_SIZE}" ] || { echo "Uploaded source identity mismatch" >&2; exit 2; }
rm /tmp/pdd-source.tar.gz
echo "Uploaded immutable candidate source."

# ── Prepare job templates ─────────────────────────────────────────────────
echo "=== Preparing job templates ==="
RESULTS_GCS_PATH="${BUCKET}/${JOB_RUN_ID}/results"
SOURCE_GCS_PATH="${BUCKET}/${JOB_RUN_ID}/source"
JOB_NAME_PYTEST="${JOB_NAME}-pytest"
JOB_NAME_MAIN="${JOB_NAME}"
JOB_NAME_STD="${JOB_NAME}-std"
JOB_NAME_CLOUD="${JOB_NAME}-cloud"

_render_template() {
    local job_name="$3"
    sed \
        -e "s|{{PROJECT_ID}}|${PROJECT_ID}|g" \
        -e "s|{{REGION}}|${REGION}|g" \
        -e "s|{{SPOT_PROVISIONING_MODEL}}|${SPOT_PROVISIONING_MODEL}|g" \
        -e "s|{{RESULTS_GCS_PATH}}|${RESULTS_GCS_PATH}|g" \
        -e "s|{{SOURCE_GCS_PATH}}|${SOURCE_GCS_PATH}|g" \
        -e "s|{{IMAGE_URI}}|${IMAGE_URI}|g" \
        -e "s|{{CANDIDATE_SHA}}|${CANDIDATE_SHA}|g" \
        -e "s|{{CANDIDATE_TREE}}|${CANDIDATE_TREE}|g" \
        -e "s|{{SOURCE_SHA256}}|${SOURCE_SHA256}|g" \
        -e "s|{{SOURCE_SIZE}}|${SOURCE_SIZE}|g" \
        -e "s|{{SOURCE_GCS_BUCKET}}|${BUCKET}|g" \
        -e "s|{{SOURCE_GCS_OBJECT}}|${SOURCE_GCS_OBJECT}|g" \
        -e "s|{{SOURCE_GCS_GENERATION}}|${SOURCE_GCS_GENERATION}|g" \
        -e "s|{{IMAGE_DIGEST}}|${IMAGE_DIGEST}|g" \
        -e "s|{{PDD_PACKAGE_VERSION}}|${PDD_PACKAGE_VERSION}|g" \
        -e "s|{{BATCH_JOB_NAME}}|${job_name}|g" \
        -e "s|{{GCS_HMAC_ACCESS_KEY_ID_SECRET_RESOURCE}}|${GCS_HMAC_ACCESS_KEY_ID_SECRET_RESOURCE}|g" \
        -e "s|{{GCS_HMAC_SECRET_ACCESS_KEY_SECRET_RESOURCE}}|${GCS_HMAC_SECRET_ACCESS_KEY_SECRET_RESOURCE}|g" \
        -e "s|{{OPENAI_API_KEY_SECRET_RESOURCE}}|${OPENAI_API_KEY_SECRET_RESOURCE}|g" \
        -e "s|{{FIREBASE_API_KEY_SECRET_RESOURCE}}|${FIREBASE_API_KEY_SECRET_RESOURCE}|g" \
        -e "s|{{GITHUB_CLIENT_ID_SECRET_RESOURCE}}|${GITHUB_CLIENT_ID_SECRET_RESOURCE}|g" \
        -e "s|{{PDD_REFRESH_TOKEN_SECRET_RESOURCE}}|${PDD_REFRESH_TOKEN_SECRET_RESOURCE}|g" \
        -e "s|{{CLAUDE_CODE_OAUTH_TOKEN_SECRET_RESOURCE}}|${CLAUDE_CODE_OAUTH_TOKEN_SECRET_RESOURCE}|g" \
        "$1" > "$2"
}

_render_template "${SCRIPT_DIR}/job-template-pytest.json" /tmp/pdd-batch-job-pytest.json "${JOB_NAME_PYTEST}"
_render_template "${SCRIPT_DIR}/job-template.json" /tmp/pdd-batch-job-main.json "${JOB_NAME_MAIN}"
_render_template "${SCRIPT_DIR}/job-template-standard.json" /tmp/pdd-batch-job-std.json "${JOB_NAME_STD}"
_render_template "${SCRIPT_DIR}/job-template-cloud-regression.json" /tmp/pdd-batch-job-cloud.json "${JOB_NAME_CLOUD}"

_validate_rendered_template() {
    python3 - "$1" "$2" "$3" "${PROJECT_ID}" "${REGION}" \
        "${IMAGE_URI}" "${PINNED_SECRET_RESOURCES[@]}" <<'PY'
import json
import re
import sys

path, expected_count, expected_job, project, location, image_uri, *resources = sys.argv[1:]
with open(path, encoding="utf-8") as handle:
    document = json.load(handle)
serialized = json.dumps(document)
if "{{" in serialized:
    raise SystemExit("rendered Batch template contains unresolved identity")
group = document["taskGroups"][0]
runnable = group["taskSpec"]["runnables"][0]
if group["taskCount"] != expected_count or runnable["container"]["imageUri"] != image_uri:
    raise SystemExit("rendered Batch template identity mismatch")
variables = runnable["environment"]["variables"]
if (
    variables.get("PDD_BATCH_PROJECT") != project
    or variables.get("PDD_BATCH_LOCATION") != location
    or variables.get("PDD_BATCH_JOB_NAME") != expected_job
):
    raise SystemExit("rendered Batch task identity mismatch")
rendered_resources = {
    value for key, value in variables.items() if key.endswith("_SECRET_RESOURCE")
}
if rendered_resources != set(resources):
    raise SystemExit("rendered Batch credential identity mismatch")
if any(
    not re.fullmatch(r"projects/[^/]+/secrets/[^/]+/versions/[1-9][0-9]*", value)
    for value in rendered_resources
):
    raise SystemExit("rendered Batch credential version is not immutable")
PY
}

_validate_rendered_template /tmp/pdd-batch-job-pytest.json 32 "${JOB_NAME_PYTEST}"
_validate_rendered_template /tmp/pdd-batch-job-main.json 36 "${JOB_NAME_MAIN}"
_validate_rendered_template /tmp/pdd-batch-job-std.json 1 "${JOB_NAME_STD}"
_validate_rendered_template /tmp/pdd-batch-job-cloud.json 1 "${JOB_NAME_CLOUD}"

# ── Submit jobs ───────────────────────────────────────────────────────────
# Only pytest shards need privileged containers for the protected Linux
# sandbox. Keep them isolated from every other suite. Both normally-SPOT jobs
# honor the STANDARD override used by release gates.
echo "=== Submitting ${SPOT_PROVISIONING_MODEL} privileged pytest job: ${JOB_NAME_PYTEST} (32 tasks) ==="
gcloud batch jobs submit "${JOB_NAME_PYTEST}" \
    --project="${PROJECT_ID}" \
    --location="${REGION}" \
    --config=/tmp/pdd-batch-job-pytest.json

# Unprivileged regression, sync-regression (except slow case 1), and Vitest.
echo "=== Submitting ${SPOT_PROVISIONING_MODEL} unprivileged main job: ${JOB_NAME_MAIN} (36 tasks) ==="
gcloud batch jobs submit "${JOB_NAME_MAIN}" \
    --project="${PROJECT_ID}" \
    --location="${REGION}" \
    --config=/tmp/pdd-batch-job-main.json

# STANDARD job for the slow task (sync_regression case_1, immune to preemption)
echo "=== Submitting STANDARD job: ${JOB_NAME_STD} (1 task) ==="
gcloud batch jobs submit "${JOB_NAME_STD}" \
    --project="${PROJECT_ID}" \
    --location="${REGION}" \
    --config=/tmp/pdd-batch-job-std.json

# One STANDARD task runs all eight cloud-regression cases sequentially and
# reuses one JWT. It still emits logical task_68 through task_75 artifacts.
echo "=== Submitting STANDARD cloud-regression job: ${JOB_NAME_CLOUD} (1 physical task, 8 logical results) ==="
gcloud batch jobs submit "${JOB_NAME_CLOUD}" \
    --project="${PROJECT_ID}" \
    --location="${REGION}" \
    --config=/tmp/pdd-batch-job-cloud.json

_job_uid() {
    gcloud batch jobs describe "$1" \
        --project="${PROJECT_ID}" \
        --location="${REGION}" \
        --format='value(uid)'
}

JOB_UID_PYTEST=$(_job_uid "${JOB_NAME_PYTEST}")
JOB_UID_MAIN=$(_job_uid "${JOB_NAME_MAIN}")
JOB_UID_STD=$(_job_uid "${JOB_NAME_STD}")
JOB_UID_CLOUD=$(_job_uid "${JOB_NAME_CLOUD}")
for job_uid in "${JOB_UID_PYTEST}" "${JOB_UID_MAIN}" "${JOB_UID_STD}" "${JOB_UID_CLOUD}"; do
    case "${job_uid}" in
        ''|*[!A-Za-z0-9-]*) echo "Submitted Batch job UID unavailable" >&2; exit 2 ;;
    esac
done

EVIDENCE_FILE="/tmp/pdd-cloud-batch-identity-${JOB_RUN_ID}.json"
python3 - "${EVIDENCE_FILE}" <<PY
import json
import sys

evidence = {
    "project": "${PROJECT_ID}",
    "location": "${REGION}",
    "candidate_sha": "${CANDIDATE_SHA}",
    "candidate_tree": "${CANDIDATE_TREE}",
    "source_sha256": "${SOURCE_SHA256}",
    "source_size": "${SOURCE_SIZE}",
    "source_bucket": "${BUCKET}",
    "source_object": "${SOURCE_GCS_OBJECT}",
    "source_generation": "${SOURCE_GCS_GENERATION}",
    "image_deps_sha256": "${IMAGE_DEPS_SHA256}",
    "image_digest": "${IMAGE_DIGEST}",
    "image_uri": "${IMAGE_URI}",
    "secret_resources": [
        "${GCS_HMAC_ACCESS_KEY_ID_SECRET_RESOURCE}",
        "${GCS_HMAC_SECRET_ACCESS_KEY_SECRET_RESOURCE}",
        "${OPENAI_API_KEY_SECRET_RESOURCE}",
        "${FIREBASE_API_KEY_SECRET_RESOURCE}",
        "${GITHUB_CLIENT_ID_SECRET_RESOURCE}",
        "${PDD_REFRESH_TOKEN_SECRET_RESOURCE}",
        "${CLAUDE_CODE_OAUTH_TOKEN_SECRET_RESOURCE}",
    ],
    "job_uids": {
        "${JOB_NAME_PYTEST}": {
            "uid": "${JOB_UID_PYTEST}", "task_indexes": list(range(0, 32))
        },
        "${JOB_NAME_MAIN}": {
            "uid": "${JOB_UID_MAIN}",
            "task_indexes": [*range(32, 54), *range(55, 68), 76],
        },
        "${JOB_NAME_STD}": {"uid": "${JOB_UID_STD}", "task_indexes": [54]},
        "${JOB_NAME_CLOUD}": {
            "uid": "${JOB_UID_CLOUD}",
            "task_indexes": list(range(68, 76)),
            "physical_task_indexes": [0] * 8,
        },
    },
}
with open(sys.argv[1], "w", encoding="utf-8") as handle:
    json.dump(evidence, handle, sort_keys=True, indent=2)
    handle.write("\n")
PY
gcloud storage cp --quiet "${EVIDENCE_FILE}" \
    "gs://${BUCKET}/${JOB_RUN_ID}/evidence/identity.json"

rm /tmp/pdd-batch-job-pytest.json /tmp/pdd-batch-job-main.json \
    /tmp/pdd-batch-job-std.json /tmp/pdd-batch-job-cloud.json

_verify_secret_log_boundary() {
    local -a verifier_args=(
        --project "${PROJECT_ID}"
        --region "${REGION}"
        --job-spec "${JOB_NAME_PYTEST}=${JOB_UID_PYTEST}=32"
        --job-spec "${JOB_NAME_MAIN}=${JOB_UID_MAIN}=36"
        --job-spec "${JOB_NAME_STD}=${JOB_UID_STD}=1"
        --job-spec "${JOB_NAME_CLOUD}=${JOB_UID_CLOUD}=1"
        --evidence "${EVIDENCE_FILE}"
        --results "${STREAMING_DIR}"
    )
    local secret_resource
    for secret_resource in "${PINNED_SECRET_RESOURCES[@]}"; do
        verifier_args+=(--secret-resource "${secret_resource}")
    done
    local artifact_log
    for artifact_log in \
        "${STREAMING_DIR}"/task_*.json "${STREAMING_DIR}"/task_*.log \
        "${STREAMING_DIR}"/cloud_regression_attempt_*.jsonl; do
        [ -f "${artifact_log}" ] || continue
        verifier_args+=(--log-file "${artifact_log}")
    done
    python3 "${SCRIPT_DIR}/verify-secret-logs.py" "${verifier_args[@]}"
}

# ── Poll for completion (all jobs) ────────────────────────────────────────
echo "=== Polling for completion (${POLL_INTERVAL}s intervals, ${POLL_TIMEOUT}s timeout) ==="
ELAPSED=0
STREAMING_DIR=$(mktemp -d)
trap 'rm -rf "${STREAMING_DIR}"; cleanup_leaked_gcloud_workers' EXIT

PHYSICAL_TOTAL=70  # 32 pytest + 36 unprivileged main + 1 slow sync + 1 cloud task
LOGICAL_TOTAL=77   # The cloud task emits eight identity-bound logical results.
_job_status() {
    _with_timeout 15 gcloud batch jobs describe "$1" \
        --project="${PROJECT_ID}" \
        --location="${REGION}" \
        --format="value(status.state)" 2>/dev/null || echo "UNKNOWN"
}

while [ "${ELAPSED}" -lt "${POLL_TIMEOUT}" ]; do
    STATUS_PYTEST=$(_job_status "${JOB_NAME_PYTEST}")
    STATUS_MAIN=$(_job_status "${JOB_NAME_MAIN}")
    STATUS_STD=$(_job_status "${JOB_NAME_STD}")
    STATUS_CLOUD=$(_job_status "${JOB_NAME_CLOUD}")

    # ── Stream completed task results ─────────────────────────────────
    _with_timeout 15 gcloud storage cp --quiet "gs://${BUCKET}/${JOB_RUN_ID}/results/task_*.json" "${STREAMING_DIR}/" 2>/dev/null || true

    # Count completed tasks. Tasks pre-create task_N.json with
    # status="preempted" at startup so SIGKILL leaves a diagnosable marker;
    # those provisional files must NOT count as completed and must NOT trigger
    # the failure-reporting loop until the job is in a terminal state (because
    # write_result will overwrite them with the real result on normal exit).
    COMPLETED=0
    STREAM_FAILURES=0
    for json_file in "${STREAMING_DIR}"/task_*.json; do
        [ -f "${json_file}" ] || continue
        [ "$(wc -c < "${json_file}")" -lt 10 ] && continue
        _stream_status=$(python3 -c "import json; d=json.load(open('${json_file}')); print(d.get('status','error'))" 2>/dev/null || echo "unknown")
        [ "${_stream_status}" = "preempted" ] && continue
        COMPLETED=$((COMPLETED + 1))
        [ "${_stream_status}" = "passed" ] || STREAM_FAILURES=$((STREAM_FAILURES + 1))
    done

    # ── Progress line ─────────────────────────────────────────────────
    if [ "${STREAM_FAILURES}" -gt 0 ]; then
        echo "[$(date +%H:%M:%S)] PYTEST: ${STATUS_PYTEST} | MAIN: ${STATUS_MAIN} | STD: ${STATUS_STD} | CLOUD: ${STATUS_CLOUD} | ${COMPLETED}/${LOGICAL_TOTAL} logical results (${PHYSICAL_TOTAL} physical tasks; ${STREAM_FAILURES} failed) (${ELAPSED}s elapsed)"
    else
        echo "[$(date +%H:%M:%S)] PYTEST: ${STATUS_PYTEST} | MAIN: ${STATUS_MAIN} | STD: ${STATUS_STD} | CLOUD: ${STATUS_CLOUD} | ${COMPLETED}/${LOGICAL_TOTAL} logical results (${PHYSICAL_TOTAL} physical tasks) (${ELAPSED}s elapsed)"
    fi

    # ── Check terminal states ─────────────────────────────────────────
    # All jobs must reach a terminal state before we exit
    _is_terminal() { [[ "$1" == "SUCCEEDED" || "$1" == "FAILED" ]]; }

    if _is_terminal "${STATUS_PYTEST}" && _is_terminal "${STATUS_MAIN}" && _is_terminal "${STATUS_STD}" && _is_terminal "${STATUS_CLOUD}"; then
        _with_timeout 30 gcloud storage cp --quiet \
            "gs://${BUCKET}/${JOB_RUN_ID}/results/task_*.json" "${STREAMING_DIR}/"
        _with_timeout 30 gcloud storage cp --quiet \
            "gs://${BUCKET}/${JOB_RUN_ID}/results/task_*.log" "${STREAMING_DIR}/"
        _with_timeout 30 gcloud storage cp --quiet \
            "gs://${BUCKET}/${JOB_RUN_ID}/results/cloud_regression_attempt_*.jsonl" \
            "${STREAMING_DIR}/"
        echo "=== Verifying attributable logs contain no credential fingerprints ==="
        if ! _verify_secret_log_boundary; then
            echo "=== Credential-log boundary verification FAILED ==="
            exit 1
        fi
        if [ "${STATUS_PYTEST}" = "SUCCEEDED" ] && [ "${STATUS_MAIN}" = "SUCCEEDED" ] && [ "${STATUS_STD}" = "SUCCEEDED" ] && [ "${STATUS_CLOUD}" = "SUCCEEDED" ]; then
            echo "=== All jobs completed successfully ==="
            bash "${SCRIPT_DIR}/collect-results.sh" \
                "${PROJECT_ID}" "${BUCKET}" "${JOB_RUN_ID}" "${EVIDENCE_FILE}" "${STREAMING_DIR}" "${JOB_NAME_PYTEST}" "${JOB_NAME_MAIN}" "${JOB_NAME_STD}" "${JOB_NAME_CLOUD}"
            exit 0
        else
            echo "=== Job(s) FAILED (pytest=${STATUS_PYTEST}, main=${STATUS_MAIN}, std=${STATUS_STD}, cloud=${STATUS_CLOUD}) ==="
            bash "${SCRIPT_DIR}/collect-results.sh" \
                "${PROJECT_ID}" "${BUCKET}" "${JOB_RUN_ID}" "${EVIDENCE_FILE}" "${STREAMING_DIR}" "${JOB_NAME_PYTEST}" "${JOB_NAME_MAIN}" "${JOB_NAME_STD}" "${JOB_NAME_CLOUD}"
            exit 1
        fi
    fi

    # Bail on unexpected states
    for _s in "${STATUS_PYTEST}" "${STATUS_MAIN}" "${STATUS_STD}" "${STATUS_CLOUD}"; do
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
echo "  gcloud batch jobs describe ${JOB_NAME_PYTEST} --project=${PROJECT_ID} --location=${REGION}"
echo "  gcloud batch jobs describe ${JOB_NAME_MAIN} --project=${PROJECT_ID} --location=${REGION}"
echo "  gcloud batch jobs describe ${JOB_NAME_STD} --project=${PROJECT_ID} --location=${REGION}"
echo "  gcloud batch jobs describe ${JOB_NAME_CLOUD} --project=${PROJECT_ID} --location=${REGION}"
exit 1
