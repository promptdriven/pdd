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
PYTEST_END=23
PYTEST_CHUNKS=24

REGRESSION_START=24
REGRESSION_END=45

SYNC_REGRESSION_START=46
SYNC_REGRESSION_END=55

CLOUD_REGRESSION_START=56
CLOUD_REGRESSION_END=63

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
    "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
JSONEOF
}

# ── Extract source code ───────────────────────────────────────────────────
echo "=== Task ${TASK_INDEX}: extracting source ==="
mkdir -p "${WORK_DIR}"
tar xzf "${SOURCE_DIR}/pdd-source.tar.gz" -C "${WORK_DIR}"
cd "${WORK_DIR}"

# Install package in dev mode (deps already in image, --no-deps is fast ~5s)
pip install -e ".[dev]" --no-deps --quiet 2>/dev/null || pip install -e . --no-deps --quiet

# ── Vertex AI auth via ADC (service account attached to VM) ───────────────
export VERTEX_PROJECT="${VERTEX_PROJECT:-prompt-driven-development-stg}"
export VERTEX_CREDENTIALS="/tmp/adc-fallback"

# ── Set common env vars ──────────────────────────────────────────────────
export PDD_MODEL_DEFAULT="vertex_ai/gemini-3-flash-preview"
export PDD_RUN_REAL_LLM_TESTS=1
export PDD_RUN_LLM_TESTS=1
export PDD_PATH="${WORK_DIR}/pdd"
export PYTHONPATH="${WORK_DIR}/pdd:${PYTHONPATH:-}"

# ── Exchange refresh token for fresh JWT ──────────────────────────────────
if [ -n "${PDD_REFRESH_TOKEN:-}" ] && [ -n "${FIREBASE_API_KEY:-}" ]; then
    JWT_RESPONSE=$(curl -s "https://securetoken.googleapis.com/v1/token?key=${FIREBASE_API_KEY}" \
        -H "Content-Type: application/x-www-form-urlencoded" \
        -d "grant_type=refresh_token&refresh_token=${PDD_REFRESH_TOKEN}")
    export PDD_JWT_TOKEN=$(echo "${JWT_RESPONSE}" | python3 -c "import sys,json; print(json.load(sys.stdin)['id_token'])")
    echo "JWT token obtained from refresh token (${#PDD_JWT_TOKEN} chars)"
fi

# ── Claude Code OAuth → set ANTHROPIC_API_KEY for test skip gates ─────
if [ -n "${CLAUDE_CODE_OAUTH_TOKEN:-}" ]; then
    export ANTHROPIC_API_KEY="claude-code-oauth"
fi

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

    # Dynamically list and chunk test files
    mapfile -t ALL_TESTS < <(find tests/ -name 'test_*.py' | sort)
    TOTAL=${#ALL_TESTS[@]}
    CHUNK_SIZE=$(( (TOTAL + PYTEST_CHUNKS - 1) / PYTEST_CHUNKS ))
    START_IDX=$(( CHUNK_INDEX * CHUNK_SIZE ))

    # Slice the array for this chunk
    CHUNK_TESTS=("${ALL_TESTS[@]:${START_IDX}:${CHUNK_SIZE}}")

    if [ ${#CHUNK_TESTS[@]} -eq 0 ]; then
        echo "=== No test files in chunk ${CHUNK_INDEX}, marking pass ==="
        END_TIME=$(date +%s)
        write_result "passed" "$((END_TIME - START_TIME))" "pytest" "chunk_${CHUNK_INDEX}(empty)"
        exit 0
    fi

    echo "=== Pytest chunk ${CHUNK_INDEX}: ${#CHUNK_TESTS[@]} files (of ${TOTAL} total) ==="
    printf '  %s\n' "${CHUNK_TESTS[@]}"

    run_test "pytest" "chunk_${CHUNK_INDEX}" \
        python -m pytest -vv -n auto --dist loadfile "${CHUNK_TESTS[@]}"

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
