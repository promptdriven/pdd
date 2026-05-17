#!/usr/bin/env bash
set -euo pipefail

# ── Configuration ──────────────────────────────────────────────────────────
# Support multi-group jobs: FIXED_TASK_INDEX overrides BATCH_TASK_INDEX
# (used by the STANDARD group for slow tasks). SKIP_INDEX causes the SPOT
# group to skip one index so effective indices stay contiguous.
if [ -n "${FIXED_TASK_INDEX:-}" ]; then
    TASK_INDEX="${FIXED_TASK_INDEX}"
elif [ -n "${SKIP_INDEX:-}" ]; then
    _RAW="${BATCH_TASK_INDEX:?BATCH_TASK_INDEX not set}"
    if [ "${_RAW}" -ge "${SKIP_INDEX}" ]; then
        TASK_INDEX=$((_RAW + 1))
    else
        TASK_INDEX="${_RAW}"
    fi
else
    TASK_INDEX="${BATCH_TASK_INDEX:?BATCH_TASK_INDEX not set}"
fi
RESULTS_DIR="/mnt/disks/results"
SOURCE_DIR="/mnt/disks/source"
WORK_DIR="/workspace"
RESULT_JSON="${RESULTS_DIR}/task_${TASK_INDEX}.json"
RESULT_LOG="${RESULTS_DIR}/task_${TASK_INDEX}.log"

# ── Pre-create result file so SPOT preemption is visible ──────────────────
# Cloud Batch SPOT VMs receive SIGTERM then SIGKILL ~30s later when preempted.
# SIGKILL bypasses traps, so if the test is mid-execution when SIGKILL fires
# no task_N.json is ever written and the aggregator reports an opaque
# "ERR / no result file" — indistinguishable from a real crash. Pre-creating
# the file with status="preempted" means SIGKILL leaves a diagnosable artifact
# behind: write_result overwrites on normal completion, term_handler
# overwrites on SIGTERM, and only true preemption leaves the preempted marker.
# Single heredoc keeps the write to one syscall (the streaming reader in
# submit.sh skips files <10 bytes, so a partial pre-create won't poison
# the aggregator if preempted mid-write).
mkdir -p "${RESULTS_DIR}"
WROTE_FINAL_RESULT=0
cat > "${RESULT_JSON}" <<JSON
{
    "task_index": ${TASK_INDEX},
    "suite": "unknown",
    "detail": "task killed before completion (likely SPOT preemption)",
    "status": "preempted",
    "duration_seconds": 0,
    "setup_seconds": 0,
    "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
JSON

# Task ranges
PYTEST_START=0
PYTEST_END=31
PYTEST_CHUNKS=32
# Keep each Cloud Batch pytest shard single-process. We tested xdist (`-n 2`)
# and saw mixed results: plain scheduling caused real failures in
# tests/test_sync_orchestration.py, while `--dist loadfile` avoided those
# failures but created worse long-tail chunks. If runtime needs more work,
# prefer carving the heaviest test modules into dedicated batch shards.

REGRESSION_START=32
REGRESSION_END=53

# Cloud Batch uses a finer-grained split for sync regression than the direct
# shell harness. Case 3 is expanded into dedicated shard IDs 13/14/15 so the
# budget, max-attempts, and target-coverage checks can run in parallel without
# changing the behavior of `tests/sync_regression.sh all`.
SYNC_CASE_IDS=(1 2 13 14 15 4 5 6 7 8 9 10 11 12)
SYNC_REGRESSION_START=54
SYNC_REGRESSION_END=67

CLOUD_REGRESSION_START=68
CLOUD_REGRESSION_END=75

VITEST_START=76
VITEST_END=76

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
    # Mark that the real result has been written so trap handlers don't
    # clobber it. We can't use `[ ! -f "${RESULT_JSON}" ]` as a guard now
    # that the file is pre-created at startup — the file always exists.
    WROTE_FINAL_RESULT=1
}

# ── Trap handler: ensure result file on forced termination ────────────────
# Installed early — BEFORE source extract, pip install, preflight, and JWT
# setup — so any `set -e` failure in those phases triggers the trap and
# overwrites the pre-create with the actual exit info. Without early
# installation a corrupt tarball or transient pip failure would leave the
# pre-create as status="preempted" and be mis-reported as preemption.
# Guards use WROTE_FINAL_RESULT (set by write_result) instead of `[ ! -f ]`
# because the pre-create makes the file always exist.
trap_handler() {
    local rc=$?
    local end_time=$(date +%s)
    local duration=$((end_time - START_TIME))
    if [ "${rc}" -eq 124 ]; then
        return 0
    fi
    if [ "${WROTE_FINAL_RESULT}" -eq 0 ]; then
        write_result "error" "${duration}" "unknown" "exit_code_${rc}"
    fi
}
term_handler() {
    local end_time=$(date +%s)
    local duration=$((end_time - START_TIME))
    if [ "${WROTE_FINAL_RESULT}" -eq 0 ]; then
        write_result "error" "${duration}" "unknown" "terminated"
    fi
    exit 143
}
START_TIME=$(date +%s)
trap term_handler TERM INT
trap trap_handler EXIT

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

# ── Phantom-contract preflight ────────────────────────────────────────────
# Image plugin contract: confirm pytest plugins required by markers in tests/
# are actually importable. Catches a stale image, or someone bumping
# requirements.txt without updating Dockerfile's explicit plugin install.
python -c "import pytest_timeout, xdist, pytest_mock, pytest_asyncio, pytest_cov, testmon" || {
    echo "FATAL: image missing expected pytest plugins"
    write_result "failed" "${SETUP_SECONDS}" "preflight" "missing pytest plugins"
    exit 1
}

# Pytest config contract: confirm pyproject.toml [tool.pytest.ini_options]
# parses cleanly and all markers we use are registered (strict-markers).
# Exit 5 ("no tests collected") is the expected success case here: the
# -k __nonexistent__ filter selects zero tests on purpose, so collection
# exercises config parsing and marker registration without running anything.
PREFLIGHT_EXIT=0
python -m pytest --collect-only --quiet --strict-markers --strict-config tests/ -k __nonexistent__ >/dev/null 2>&1 || PREFLIGHT_EXIT=$?
if [ "$PREFLIGHT_EXIT" -ne 0 ] && [ "$PREFLIGHT_EXIT" -ne 5 ]; then
    echo "FATAL: pytest config or marker registration is broken (exit=$PREFLIGHT_EXIT)"
    write_result "failed" "${SETUP_SECONDS}" "preflight" "pytest config invalid"
    exit 1
fi

# ── Vertex AI auth via ADC (service account attached to VM) ───────────────
export VERTEX_PROJECT="${VERTEX_PROJECT:-prompt-driven-development-stg}"
export VERTEX_LOCATION="global"
export GOOGLE_GENAI_USE_VERTEXAI="true"
export GOOGLE_CLOUD_PROJECT="${VERTEX_PROJECT}"
export GOOGLE_CLOUD_LOCATION="us-central1"

# ── Set common env vars ──────────────────────────────────────────────────
export PDD_MODEL_DEFAULT="vertex_ai/gemini-3-flash-preview"
export PDD_STRENGTH_DEFAULT="0.5"
export PDD_AGENTIC_PROVIDER="google,anthropic,openai"
export PDD_RUN_REAL_LLM_TESTS=1
export PDD_RUN_LLM_TESTS=1
export PDD_PATH="${WORK_DIR}/pdd"
export PYTHONPATH="${WORK_DIR}/pdd:${PYTHONPATH:-}"
export LLM_CALL_TIMEOUT="${LLM_CALL_TIMEOUT:-60}"
export PDD_EXTRACTS_STRENGTH="${PDD_EXTRACTS_STRENGTH:-0.5}"

# ── Exchange refresh token for fresh JWT (with retry + jitter) ────────────
# Firebase's secure-token endpoint occasionally fails transiently when many
# Cloud Batch tasks call it concurrently. Retry with exponential backoff
# (plus jitter to scatter sibling retries) so a single blip doesn't kill
# cloud_regression cases (which exit 1 at their pre-flight auth check).
#
# Diagnostics on failure: curl transport errors, parser-script crashes, and
# bad-shape tokens are each distinguishable in the WARNING/ERROR output and
# in the final RESULT_JSON written for cloud_regression tasks.
if [ -n "${PDD_REFRESH_TOKEN:-}" ] && [ -n "${FIREBASE_API_KEY:-}" ]; then
    JWT_MAX_ATTEMPTS=4
    JWT_ATTEMPT=0
    JWT_LAST_ERROR=""
    while [ "${JWT_ATTEMPT}" -lt "${JWT_MAX_ATTEMPTS}" ]; do
        JWT_ATTEMPT=$((JWT_ATTEMPT + 1))

        # Capture curl's rc separately so transport errors (DNS, TLS, timeout)
        # stay visible. The 2>&1 merges curl -S diagnostics into JWT_RESPONSE
        # for inclusion in JWT_ERROR when the assignment "fails" — bash treats
        # the assignment as exempt from set -e, but the || captures the rc.
        JWT_CURL_RC=0
        JWT_RESPONSE=$(curl -sS --max-time 15 \
            "https://securetoken.googleapis.com/v1/token?key=${FIREBASE_API_KEY}" \
            -H "Content-Type: application/x-www-form-urlencoded" \
            -d "grant_type=refresh_token&refresh_token=${PDD_REFRESH_TOKEN}" 2>&1) || JWT_CURL_RC=$?

        if [ "${JWT_CURL_RC}" -ne 0 ]; then
            JWT_ERROR="curl_failed(rc=${JWT_CURL_RC}): $(printf '%s' "${JWT_RESPONSE}" | tr '\n' ' ' | cut -c1-200)"
        else
            # Parse the JSON body. Capture python's stderr separately so a
            # heredoc bug, missing python3, or import failure produces a
            # distinct error string from a malformed Firebase response.
            # The `|| JWT_PARSE_RC=$?` pattern is critical: under `set -e`,
            # a bare `X=$(failing_cmd)` aborts the script before $? can be
            # read, so the parser_script_crashed branch would be unreachable.
            JWT_PARSE_STDERR=$(mktemp 2>/dev/null || echo "/tmp/jwt_parse_stderr.$$")
            JWT_PARSE_RC=0
            JWT_ERROR=$(echo "${JWT_RESPONSE}" | python3 -c "
import sys, json
try:
    d = json.load(sys.stdin)
except Exception as e:
    print('parse_failed: ' + str(e))
    sys.exit(0)
if not isinstance(d, dict):
    print('non_dict_response: ' + type(d).__name__)
    sys.exit(0)
err = d.get('error', {})
if isinstance(err, dict):
    print(err.get('message', ''))
elif err:
    print(err)
else:
    print('')
" 2>"${JWT_PARSE_STDERR}") || JWT_PARSE_RC=$?
            if [ "${JWT_PARSE_RC}" -ne 0 ]; then
                JWT_ERROR="parser_script_crashed(rc=${JWT_PARSE_RC}): $(tr '\n' ' ' < "${JWT_PARSE_STDERR}" 2>/dev/null | cut -c1-200)"
            fi
            rm -f "${JWT_PARSE_STDERR}"

            if [ -z "${JWT_ERROR}" ]; then
                JWT_TOKEN_STDERR=$(mktemp 2>/dev/null || echo "/tmp/jwt_token_stderr.$$")
                JWT_TOKEN_RC=0
                PDD_JWT_TOKEN_CANDIDATE=$(echo "${JWT_RESPONSE}" | python3 -c "import sys,json; print(json.load(sys.stdin).get('id_token','') or '')" 2>"${JWT_TOKEN_STDERR}") || JWT_TOKEN_RC=$?
                if [ "${JWT_TOKEN_RC}" -ne 0 ]; then
                    JWT_ERROR="token_extract_crashed(rc=${JWT_TOKEN_RC}): $(tr '\n' ' ' < "${JWT_TOKEN_STDERR}" 2>/dev/null | cut -c1-200)"
                    PDD_JWT_TOKEN_CANDIDATE=""
                fi
                rm -f "${JWT_TOKEN_STDERR}"

                # Normalize and require JWS shape (two dots) — guards against
                # whitespace-only or literal "None"/null tokens slipping through.
                PDD_JWT_TOKEN_CANDIDATE=$(printf '%s' "${PDD_JWT_TOKEN_CANDIDATE}" | tr -d '[:space:]')
                JWT_DOT_COUNT=$(printf '%s' "${PDD_JWT_TOKEN_CANDIDATE}" | tr -cd '.' | wc -c | tr -d '[:space:]')
                if [ -n "${PDD_JWT_TOKEN_CANDIDATE}" ] && [ "${JWT_DOT_COUNT}" = "2" ]; then
                    export PDD_JWT_TOKEN="${PDD_JWT_TOKEN_CANDIDATE}"
                    echo "JWT token obtained from refresh token (${#PDD_JWT_TOKEN} chars, attempt ${JWT_ATTEMPT}/${JWT_MAX_ATTEMPTS})"
                    break
                fi
                if [ -z "${JWT_ERROR}" ]; then
                    JWT_ERROR="invalid_id_token_shape(len=${#PDD_JWT_TOKEN_CANDIDATE},dots=${JWT_DOT_COUNT})"
                fi
            fi
        fi

        JWT_LAST_ERROR="${JWT_ERROR}"
        if [ "${JWT_ATTEMPT}" -lt "${JWT_MAX_ATTEMPTS}" ]; then
            # Backoff 2/4/8s base + 0-2s jitter to scatter concurrent retries
            # across sibling Cloud Batch tasks (avoids re-creating the herd).
            JWT_BACKOFF=$((2 ** JWT_ATTEMPT + RANDOM % 3))
            echo "WARNING: JWT exchange attempt ${JWT_ATTEMPT}/${JWT_MAX_ATTEMPTS} failed (${JWT_ERROR}); retrying in ${JWT_BACKOFF}s"
            sleep "${JWT_BACKOFF}"
        fi
    done

    if [ -z "${PDD_JWT_TOKEN:-}" ]; then
        echo "ERROR: JWT exchange failed after ${JWT_MAX_ATTEMPTS} attempts: ${JWT_LAST_ERROR}"
        # For cloud_regression tasks, write a structured RESULT_JSON now so
        # the failure is reported as "jwt_exchange_failed" by the aggregator
        # instead of being masked by cloud_regression.sh's generic auth check.
        if [ "${TASK_INDEX}" -ge "${CLOUD_REGRESSION_START}" ] && [ "${TASK_INDEX}" -le "${CLOUD_REGRESSION_END}" ]; then
            JWT_FAIL_CASE_NUM=$((TASK_INDEX - CLOUD_REGRESSION_START + 1))
            # Strip characters that would break the result JSON (write_result
            # uses heredoc substitution without escaping). Drop quotes,
            # backslashes, and ALL ASCII control chars (U+0000–U+001F) —
            # JSON forbids unescaped controls, so leaving \r or similar in
            # would produce malformed task_N.json that the aggregator can't
            # parse.
            JWT_LAST_ERROR_SAFE=$(printf '%s' "${JWT_LAST_ERROR}" | tr -d '"\\' | tr -d '\000-\037' | cut -c1-160)
            write_result "error" "${SETUP_SECONDS:-0}" "cloud_regression" "jwt_exchange_failed_case_${JWT_FAIL_CASE_NUM}: ${JWT_LAST_ERROR_SAFE}"
            exit 1
        fi
        echo "Continuing without PDD_JWT_TOKEN (task ${TASK_INDEX} does not require it)."
    fi
fi

# ── Claude Code OAuth ──────────────────────────────────────────────────
# CLAUDE_CODE_OAUTH_TOKEN is injected by Cloud Batch secretVariables.
# Do NOT set a dummy ANTHROPIC_API_KEY here — it causes LiteLLM auth
# failures when non-agentic tests try to use it for direct API calls.

# ── Dispatch by task index ────────────────────────────────────────────────
# START_TIME and trap installations moved above (right after write_result
# definition) so setup failures are captured.

run_with_timeout() {
    local seconds="$1"
    shift

    if command -v timeout >/dev/null 2>&1; then
        timeout --kill-after=10s "${seconds}s" "$@"
    else
        "$@"
    fi
}

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
        if [ "${exit_code}" -eq 124 ]; then
            # Exit 124 indicates the GNU coreutils `timeout` killed the task.
            # Cloud Batch lifecycle policy no longer retries 124 (see PR
            # change 3); record a failed result so post-run reports show the
            # timeout instead of leaving a gap, then exit non-zero.
            echo "=== Task timed out (exit 124); recording failed result ==="
            write_result "failed" "${duration}" "${suite}" "${detail} (timeout)"
            tail -50 "${RESULT_LOG}" || true
            exit "${exit_code}"
        fi
        write_result "failed" "${duration}" "${suite}" "${detail}"
        # Print last 50 lines for Cloud Batch logs
        tail -50 "${RESULT_LOG}" || true
        exit "${exit_code}"
    fi
}

if [ "${TASK_INDEX}" -ge "${PYTEST_START}" ] && [ "${TASK_INDEX}" -le "${PYTEST_END}" ]; then
    # ── Pytest chunk ──────────────────────────────────────────────────
    CHUNK_INDEX="${TASK_INDEX}"
    DURATIONS_FILE="${WORK_DIR}/ci/cloud-batch/test-durations.json"

    # CI model cap: restrict real-LLM pytest tests to Google Vertex AI gemini
    # rows. The selector at strength=1.0 (e.g. test_generate_test_maximum_values)
    # otherwise escalates to the highest-ELO row in the full CSV (claude-opus-4-7),
    # which is too slow to be a reliable CI dependency. After this filter the
    # highest ELO is a Gemini Pro variant — fast, cheap, and stable. PDD prefers
    # <cwd>/.pdd/llm_model.csv when present (see pdd/llm_invoke.py:778-781).
    mkdir -p "${WORK_DIR}/.pdd"
    head -1 "${WORK_DIR}/pdd/data/llm_model.csv" > "${WORK_DIR}/.pdd/llm_model.csv"
    grep -E '^Google Vertex AI,[^,]*gemini' "${WORK_DIR}/pdd/data/llm_model.csv" >> "${WORK_DIR}/.pdd/llm_model.csv"
    echo "=== CI-restricted llm_model.csv ($(( $(wc -l < "${WORK_DIR}/.pdd/llm_model.csv") - 1 )) gemini rows) ==="

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
            mapfile -t ALL_TESTS < <(find tests/ -name 'test_*.py' ! -path 'tests/fixtures/one_session_eval/*' | sort)
            TOTAL=${#ALL_TESTS[@]}
            CHUNK_SIZE=$(( (TOTAL + PYTEST_CHUNKS - 1) / PYTEST_CHUNKS ))
            START_IDX=$(( CHUNK_INDEX * CHUNK_SIZE ))
            CHUNK_TESTS=("${ALL_TESTS[@]:${START_IDX}:${CHUNK_SIZE}}")
        fi
        rm -f "${ASSIGN_OUTPUT}"
    else
        # Fallback: alphabetical split
        echo "=== No durations file, using alphabetical split ==="
        mapfile -t ALL_TESTS < <(find tests/ -name 'test_*.py' ! -path 'tests/fixtures/one_session_eval/*' | sort)
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

    TOTAL_FILES=$(find tests/ -name 'test_*.py' ! -path 'tests/fixtures/one_session_eval/*' | wc -l)
    echo "=== Pytest chunk ${CHUNK_INDEX}: ${#CHUNK_TESTS[@]} files (of ${TOTAL_FILES} total) ==="
    printf '  %s\n' "${CHUNK_TESTS[@]}"

    JUNIT_XML="${RESULTS_DIR}/task_${TASK_INDEX}_junit.xml"
    PYTEST_CHUNK_TIMEOUT="${PYTEST_CHUNK_TIMEOUT:-1200}"
    run_test "pytest" "chunk_${CHUNK_INDEX}" \
        run_with_timeout "${PYTEST_CHUNK_TIMEOUT}" \
        python -m pytest -vv \
        --junitxml="${JUNIT_XML}" "${CHUNK_TESTS[@]}"

elif [ "${TASK_INDEX}" -ge "${REGRESSION_START}" ] && [ "${TASK_INDEX}" -le "${REGRESSION_END}" ]; then
    # ── Regression test ───────────────────────────────────────────────
    CASE_NUM=$((TASK_INDEX - REGRESSION_START))
    run_test "regression" "case_${CASE_NUM}" \
        bash tests/regression.sh "${CASE_NUM}"

elif [ "${TASK_INDEX}" -ge "${SYNC_REGRESSION_START}" ] && [ "${TASK_INDEX}" -le "${SYNC_REGRESSION_END}" ]; then
    # ── Sync regression test ──────────────────────────────────────────
    SYNC_OFFSET=$((TASK_INDEX - SYNC_REGRESSION_START))
    CASE_NUM="${SYNC_CASE_IDS[$SYNC_OFFSET]}"
    # 10 min was tight for case_7 (complex sync data_processor — strength 0.3,
    # 1 attempt, $5 budget; legit LLM completion + scaffold can run 8-10 min).
    # 15 min gives realistic headroom without weakening fail-fast for hangs.
    export PDD_CMD_TIMEOUT="${PDD_CMD_TIMEOUT:-900}"
    run_test "sync_regression" "case_${CASE_NUM}" \
        bash tests/sync_regression.sh "${CASE_NUM}"

elif [ "${TASK_INDEX}" -ge "${CLOUD_REGRESSION_START}" ] && [ "${TASK_INDEX}" -le "${CLOUD_REGRESSION_END}" ]; then
    # ── Cloud regression test ─────────────────────────────────────────
    CASE_NUM=$((TASK_INDEX - CLOUD_REGRESSION_START + 1))
    run_test "cloud_regression" "case_${CASE_NUM}" \
        bash tests/cloud_regression.sh "${CASE_NUM}"

elif [ "${TASK_INDEX}" -ge "${VITEST_START}" ] && [ "${TASK_INDEX}" -le "${VITEST_END}" ]; then
    # ── Frontend Vitest tests ─────────────────────────────────────────
    echo "=== Installing frontend dependencies ==="
    cd pdd/frontend
    npm install --prefer-offline --no-audit --no-fund 2>&1 | tail -5

    run_test "vitest" "frontend" \
        npx vitest run

else
    echo "ERROR: Unknown task index ${TASK_INDEX}"
    END_TIME=$(date +%s)
    write_result "error" "$((END_TIME - START_TIME))" "unknown" "index_${TASK_INDEX}"
    exit 1
fi
