#!/usr/bin/env bash
set -euo pipefail

# ── Configuration ──────────────────────────────────────────────────────────
TASK_INDEX="${BATCH_TASK_INDEX:?BATCH_TASK_INDEX not set}"
RESULTS_DIR="/mnt/disks/results"
SOURCE_DIR="/mnt/disks/source"
WORK_DIR="/workspace"
RESULT_JSON="${RESULTS_DIR}/task_${TASK_INDEX}.json"
RESULT_LOG="${RESULTS_DIR}/task_${TASK_INDEX}.log"

# Task ranges
PYTEST_START=0
PYTEST_END=31
PYTEST_CHUNKS=32

REGRESSION_START=32
REGRESSION_END=53

SYNC_REGRESSION_START=54
SYNC_REGRESSION_END=63

CLOUD_REGRESSION_START=64
CLOUD_REGRESSION_END=71

# ── Helper: write result JSON ──────────────────────────────────────────────
write_result() {
    local status="$1" duration="$2" suite="$3" detail="$4"
    cat > "${RESULT_JSON}" <<JSONEOF
{
    "task_index": ${TASK_INDEX},
    "suite": "${suite}",
    "detail": "${detail}",
    "status": "${status}",
    "duration_seconds": ${duration},
    "setup_seconds": ${SETUP_SECONDS:-0},
    "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
JSONEOF
}

# ── Extract source code ───────────────────────────────────────────────────
SETUP_START=$(date +%s)
echo "=== Task ${TASK_INDEX}: extracting source ==="
mkdir -p "${WORK_DIR}"
tar xzf "${SOURCE_DIR}/pdd-source.tar.gz" -C "${WORK_DIR}"
cd "${WORK_DIR}"

# Install package in dev mode (deps already in image, --no-deps is fast ~5s)
pip install -e ".[dev]" --no-deps --quiet 2>/dev/null || pip install -e . --no-deps --quiet
SETUP_END=$(date +%s)
SETUP_SECONDS=$((SETUP_END - SETUP_START))

# ── Vertex AI auth via ADC (service account attached to VM) ───────────────
export VERTEX_PROJECT="${VERTEX_PROJECT:-prompt-driven-development-stg}"
export VERTEX_LOCATION="global"
export GOOGLE_GENAI_USE_VERTEXAI="true"
export GOOGLE_CLOUD_PROJECT="${VERTEX_PROJECT}"
export GOOGLE_CLOUD_LOCATION="us-central1"

# ── Set common env vars ──────────────────────────────────────────────────
export PDD_MODEL_DEFAULT="vertex_ai/gemini-3-flash-preview"
export PDD_AGENTIC_PROVIDER="google,anthropic,openai"
export PDD_RUN_REAL_LLM_TESTS=1
export PDD_RUN_LLM_TESTS=1
export PDD_PATH="${WORK_DIR}/pdd"
export PYTHONPATH="${WORK_DIR}/pdd:${PYTHONPATH:-}"

# ── Exchange refresh token for fresh JWT ──────────────────────────────────
if [ -n "${PDD_REFRESH_TOKEN:-}" ] && [ -n "${FIREBASE_API_KEY:-}" ]; then
    JWT_RESPONSE=$(curl -s "https://securetoken.googleapis.com/v1/token?key=${FIREBASE_API_KEY}" \
        -H "Content-Type: application/x-www-form-urlencoded" \
        -d "grant_type=refresh_token&refresh_token=${PDD_REFRESH_TOKEN}")

    # Check for error in response before extracting token
    JWT_ERROR=$(echo "${JWT_RESPONSE}" | python3 -c "
import sys, json
d = json.load(sys.stdin)
err = d.get('error', {})
if isinstance(err, dict):
    print(err.get('message', ''))
elif err:
    print(err)
else:
    print('')
" 2>/dev/null || echo "parse_failed")

    if [ -n "${JWT_ERROR}" ] && [ "${JWT_ERROR}" != "" ]; then
        echo "WARNING: JWT token exchange failed: ${JWT_ERROR}"
        echo "Cloud regression tests will likely fail."
    else
        export PDD_JWT_TOKEN=$(echo "${JWT_RESPONSE}" | python3 -c "import sys,json; print(json.load(sys.stdin)['id_token'])")
        echo "JWT token obtained from refresh token (${#PDD_JWT_TOKEN} chars)"
    fi
fi

# ── Claude Code OAuth ──────────────────────────────────────────────────
# CLAUDE_CODE_OAUTH_TOKEN is injected by Cloud Batch secretVariables.
# Do NOT set a dummy ANTHROPIC_API_KEY here — it causes LiteLLM auth
# failures when non-agentic tests try to use it for direct API calls.

# ── Dispatch by task index ────────────────────────────────────────────────
START_TIME=$(date +%s)

run_test() {
    local suite="$1" detail="$2"
    shift 2
    echo "=== Running: suite=${suite} detail=${detail} ==="
    echo "Command: $*"

    if "$@" > "${RESULT_LOG}" 2>&1; then
        local end_time=$(date +%s)
        local duration=$((end_time - START_TIME))
        echo "=== PASSED (${duration}s) ==="
        write_result "passed" "${duration}" "${suite}" "${detail}"
    else
        local exit_code=$?
        local end_time=$(date +%s)
        local duration=$((end_time - START_TIME))
        echo "=== FAILED exit=${exit_code} (${duration}s) ==="
        write_result "failed" "${duration}" "${suite}" "${detail}"
        # Print last 50 lines for Cloud Batch logs
        tail -50 "${RESULT_LOG}" || true
        exit 1
    fi
}

if [ "${TASK_INDEX}" -ge "${PYTEST_START}" ] && [ "${TASK_INDEX}" -le "${PYTEST_END}" ]; then
    # ── Pytest chunk ──────────────────────────────────────────────────
    CHUNK_INDEX="${TASK_INDEX}"
    DURATIONS_FILE="${WORK_DIR}/ci/cloud-batch/test-durations.json"

    if [ -f "${DURATIONS_FILE}" ]; then
        # Duration-based bin packing for balanced chunks
        echo "=== Using duration-based chunk balancing ==="
        ASSIGN_OUTPUT=$(mktemp)
        if python3 "${WORK_DIR}/ci/cloud-batch/balance-chunks.py" assign \
            --chunk-index "${CHUNK_INDEX}" \
            --num-chunks "${PYTEST_CHUNKS}" \
            --durations "${DURATIONS_FILE}" \
            --test-dir tests/ > "${ASSIGN_OUTPUT}"; then
            mapfile -t CHUNK_TESTS < "${ASSIGN_OUTPUT}"
        else
            echo "=== balance-chunks.py failed, falling back to alphabetical split ==="
            mapfile -t ALL_TESTS < <(find tests/ -name 'test_*.py' | sort)
            TOTAL=${#ALL_TESTS[@]}
            CHUNK_SIZE=$(( (TOTAL + PYTEST_CHUNKS - 1) / PYTEST_CHUNKS ))
            START_IDX=$(( CHUNK_INDEX * CHUNK_SIZE ))
            CHUNK_TESTS=("${ALL_TESTS[@]:${START_IDX}:${CHUNK_SIZE}}")
        fi
        rm -f "${ASSIGN_OUTPUT}"
    else
        # Fallback: alphabetical split
        echo "=== No durations file, using alphabetical split ==="
        mapfile -t ALL_TESTS < <(find tests/ -name 'test_*.py' | sort)
        TOTAL=${#ALL_TESTS[@]}
        CHUNK_SIZE=$(( (TOTAL + PYTEST_CHUNKS - 1) / PYTEST_CHUNKS ))
        START_IDX=$(( CHUNK_INDEX * CHUNK_SIZE ))
        CHUNK_TESTS=("${ALL_TESTS[@]:${START_IDX}:${CHUNK_SIZE}}")
    fi

    if [ ${#CHUNK_TESTS[@]} -eq 0 ]; then
        echo "=== No test files in chunk ${CHUNK_INDEX}, marking pass ==="
        END_TIME=$(date +%s)
        write_result "passed" "$((END_TIME - START_TIME))" "pytest" "chunk_${CHUNK_INDEX}(empty)"
        exit 0
    fi

    TOTAL_FILES=$(find tests/ -name 'test_*.py' | wc -l)
    echo "=== Pytest chunk ${CHUNK_INDEX}: ${#CHUNK_TESTS[@]} files (of ${TOTAL_FILES} total) ==="
    printf '  %s\n' "${CHUNK_TESTS[@]}"

    JUNIT_XML="${RESULTS_DIR}/task_${TASK_INDEX}_junit.xml"
    run_test "pytest" "chunk_${CHUNK_INDEX}" \
        python -m pytest -vv -n auto --dist load \
        --junitxml="${JUNIT_XML}" "${CHUNK_TESTS[@]}"

elif [ "${TASK_INDEX}" -ge "${REGRESSION_START}" ] && [ "${TASK_INDEX}" -le "${REGRESSION_END}" ]; then
    # ── Regression test ───────────────────────────────────────────────
    CASE_NUM=$((TASK_INDEX - REGRESSION_START))
    run_test "regression" "case_${CASE_NUM}" \
        bash tests/regression.sh "${CASE_NUM}"

elif [ "${TASK_INDEX}" -ge "${SYNC_REGRESSION_START}" ] && [ "${TASK_INDEX}" -le "${SYNC_REGRESSION_END}" ]; then
    # ── Sync regression test ──────────────────────────────────────────
    CASE_NUM=$((TASK_INDEX - SYNC_REGRESSION_START + 1))
    run_test "sync_regression" "case_${CASE_NUM}" \
        bash tests/sync_regression.sh "${CASE_NUM}"

elif [ "${TASK_INDEX}" -ge "${CLOUD_REGRESSION_START}" ] && [ "${TASK_INDEX}" -le "${CLOUD_REGRESSION_END}" ]; then
    # ── Cloud regression test ─────────────────────────────────────────
    CASE_NUM=$((TASK_INDEX - CLOUD_REGRESSION_START + 1))
    run_test "cloud_regression" "case_${CASE_NUM}" \
        bash tests/cloud_regression.sh "${CASE_NUM}"

else
    echo "ERROR: Unknown task index ${TASK_INDEX}"
    END_TIME=$(date +%s)
    write_result "error" "$((END_TIME - START_TIME))" "unknown" "index_${TASK_INDEX}"
    exit 1
fi
