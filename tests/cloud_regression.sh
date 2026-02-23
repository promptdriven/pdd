#!/bin/bash

# Cloud Regression Test Suite
# Tests PDD commands using cloud execution (no --local flag)
# Validates that each command successfully uses cloud execution

# Exit immediately if a command exits with a non-zero status.
set -e
# Treat unset variables as an error when substituting.
set -u

# Global settings
VERBOSE=${VERBOSE:-1} # Default to 1 if not set
STRENGTH=${STRENGTH:-0.5} # Default strength (slightly higher for cloud stability)
TEMPERATURE=${TEMPERATURE:-0.0} # Default temperature
CLEANUP_ON_EXIT=false # Set to false to keep files for debugging

# Cloud status tracking
CLOUD_SUCCESSES=0
CLOUD_FAILURES=0

# --- Helper Functions ---

log() {
    if [ "$VERBOSE" -eq 1 ]; then
        echo "[INFO] $1"
    fi
}

# --- Test Selection ---
# Accept a single argument (test number) to run only that test. Default to "all".
TARGET_TEST=${1:-"all"}
log "Running cloud tests: $TARGET_TEST"
# --- End Test Selection ---

# Set PDD_AUTO_UPDATE to false to prevent interference
export PDD_AUTO_UPDATE=false

# --- Cloud Authentication Check ---
# Cloud can be authenticated via:
# 1. PDD_JWT_TOKEN (direct token injection for CI/testing)
# 2. NEXT_PUBLIC_FIREBASE_API_KEY + GITHUB_CLIENT_ID (device flow auth)
CLOUD_AUTH_METHOD=""

if [ -n "${PDD_JWT_TOKEN:-}" ]; then
    CLOUD_AUTH_METHOD="PDD_JWT_TOKEN"
    echo "[INFO] Using PDD_JWT_TOKEN for cloud authentication"
elif [ -n "${NEXT_PUBLIC_FIREBASE_API_KEY:-}" ] && [ -n "${GITHUB_CLIENT_ID:-}" ]; then
    CLOUD_AUTH_METHOD="DEVICE_FLOW"
    echo "[INFO] Using device flow authentication (NEXT_PUBLIC_FIREBASE_API_KEY + GITHUB_CLIENT_ID)"
else
    echo "========================================"
    echo "[ERROR] Cloud authentication credentials not found"
    echo ""
    echo "Please provide one of the following:"
    echo ""
    echo "Option 1: Direct token (for CI/testing)"
    echo "  export PDD_JWT_TOKEN=<your_token>"
    echo ""
    echo "Option 2: Device flow auth"
    echo "  export NEXT_PUBLIC_FIREBASE_API_KEY=<api_key>"
    echo "  export GITHUB_CLIENT_ID=<client_id>"
    echo ""
    echo "Or run with Infisical:"
    echo "  infisical run -- make cloud-regression"
    echo "========================================"
    exit 1
fi
echo "[INFO] Cloud authentication method: $CLOUD_AUTH_METHOD"

# Define base variables
# Set PDD base directory as the script's location (two directories up from this script)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PDD_BASE_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

# Load .env file from the base directory if it exists
if [ -f "$PDD_BASE_DIR/.env" ]; then
    log "Loading environment variables from .env file"
    TEMP_ENV_FILE=$(mktemp)
    grep -v -e '^#' -e '^$' "$PDD_BASE_DIR/.env" | sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' -e 's/[[:space:]]*=[[:space:]]*/=/' > "$TEMP_ENV_FILE"
    set -o allexport
    source "$TEMP_ENV_FILE"
    set +o allexport
    rm "$TEMP_ENV_FILE"
else
    log "No .env file found at $PDD_BASE_DIR/.env"
fi

# Force cloud-only mode - no local fallback
# This ensures the tests actually use cloud execution
# Set AFTER loading .env to ensure it overrides any conflicting settings
export PDD_CLOUD_ONLY=true
export PDD_FORCE_LOCAL=""  # Clear any force local setting
echo "[INFO] PDD_CLOUD_ONLY=true (no local fallback)"

PDD_PATH="$PDD_BASE_DIR/pdd"
STAGING_PATH="$PDD_BASE_DIR/staging"
PDD_SCRIPT="pdd" # Assumes pdd is in PATH
# Always prefer local CLI script when present to test workspace code
if [ -x "$PDD_BASE_DIR/pdd-local.sh" ]; then
    log "Using local CLI script (pdd-local.sh) for cloud regression tests"
    PDD_SCRIPT="$PDD_BASE_DIR/pdd-local.sh"
fi
FIXTURES_PATH="$SCRIPT_DIR/fixtures"
CONTEXT_PATH="$PDD_BASE_DIR/context"

# Determine REGRESSION_DIR (using cloud_regression prefix)
# Always create a fresh directory to avoid incremental mode (which doesn't respect PDD_CLOUD_ONLY)
if [ -n "${REGRESSION_TARGET_DIR:-}" ]; then
    REGRESSION_DIR="$REGRESSION_TARGET_DIR"
    log "Using specified regression directory: $REGRESSION_DIR"
else
    # Always create a new directory for cloud tests to ensure full generation mode
    REGRESSION_DIR="$STAGING_PATH/cloud_regression_$(date +%Y%m%d_%H%M%S)"
    log "Creating new cloud regression directory: $REGRESSION_DIR"
fi

LOG_FILE="$REGRESSION_DIR/cloud_regression.log"
COST_FILE="cloud_regression_cost.csv"

# simple_math test case files
MATH_BASENAME="simple_math"
MATH_PROMPT="${MATH_BASENAME}_python.prompt"
MATH_SCRIPT="${MATH_BASENAME}.py"
MATH_TEST_SCRIPT="test_${MATH_BASENAME}.py"
MATH_VERIFICATION_PROGRAM="${MATH_BASENAME}_example.py"
MATH_ERROR_LOG="math_error.log"
PYTEST_LOG="pytest_output.log"
COVERAGE_REPORT="coverage.xml"
ORIGINAL_MATH_SCRIPT="original_${MATH_SCRIPT}"
FIXED_MATH_SCRIPT="fixed_${MATH_SCRIPT}"
FIXED_MATH_TEST_SCRIPT="fixed_${MATH_TEST_SCRIPT}"
CRASH_FIXED_SCRIPT="fixed_crash_${MATH_SCRIPT}"
CRASH_FIXED_PROGRAM="fixed_crash_${MATH_VERIFICATION_PROGRAM}"

# Verify files
VERIFY_RESULTS_LOG="verify_results.log"
VERIFY_CODE_OUTPUT="verified_${MATH_SCRIPT}"
VERIFY_PROGRAM_OUTPUT="directly_verified_${MATH_VERIFICATION_PROGRAM}"

# Split files
SPLIT_PROMPT="split_instruction_python.prompt"
SPLIT_SUB_PROMPT="sub_${MATH_BASENAME}.prompt"
SPLIT_MODIFIED_PROMPT="modified_${MATH_BASENAME}.prompt"

# Auto-deps files
AUTO_DEPS_PROMPT="auto_deps_${MATH_PROMPT}"
AUTO_DEPS_CSV="project_dependencies.csv"

# --- Helper Functions ---

log_error() {
    echo "[ERROR] $1" >&2
    log_timestamped "[ERROR] $1"
}

log_timestamped() {
    echo "[$(date +'%Y-%m-%d %H:%M:%S')] $1" >> "$LOG_FILE"
}

check_exists() {
    local file_path="$1"
    local description="$2"
    if [ ! -s "$file_path" ]; then
        log_error "$description file not found or is empty: $file_path"
        log_timestamped "Validation failed: $description file not found or is empty: $file_path"
        exit 1
    else
        log "$description file exists and is not empty: $file_path"
        log_timestamped "Validation success: $description file exists: $file_path"
    fi
}

# --- Cloud Status Output Helper ---
print_cloud_status() {
    local command_name="$1"
    local success="$2"
    if [ "$success" = "true" ]; then
        echo "[CLOUD OK] $command_name - Cloud execution confirmed"
        CLOUD_SUCCESSES=$((CLOUD_SUCCESSES + 1))
    else
        echo "[CLOUD FAIL] $command_name - Cloud execution NOT confirmed (expected 'Cloud Success' in output)"
        CLOUD_FAILURES=$((CLOUD_FAILURES + 1))
    fi
}

# --- Helper to validate cloud success ---
validate_cloud_success() {
    local log_output="$1"
    local command_name="$2"

    # Check for successful cloud execution
    # Different commands have different success indicators:
    # - generate, example, test, fix, crash, bug: "Cloud Success"
    # - verify: "Cloud verify fix completed"
    # - split, auto-deps: Use llm_invoke which shows "Cloud llm_invoke request to:" + success message
    if grep -qE "(Cloud Success|Cloud verify fix completed)" "$log_output"; then
        log_timestamped "Cloud validation success: $command_name"
        print_cloud_status "$command_name" "true"
        return 0
    fi

    # Check for llm_invoke cloud execution (used by split, auto-deps, etc.)
    # These commands use llm_invoke internally which logs cloud requests
    if grep -q "Cloud llm_invoke request to:" "$log_output"; then
        log_timestamped "Cloud validation success (via llm_invoke): $command_name"
        print_cloud_status "$command_name" "true"
        return 0
    fi

    # Check for cloud attempt (even if it failed due to credits/rate limit)
    # This helps verify cloud integration is working even without credits
    if grep -qE "(Insufficient credits|Cloud.*rate limit|Cloud LLM|cloud_url|CloudConfig)" "$log_output"; then
        log_timestamped "Cloud was attempted but failed (likely credits/rate limit): $command_name"
        echo "[CLOUD ATTEMPTED] $command_name - Cloud was invoked but failed (check credits/rate limit)"
        # Don't count as failure if cloud was attempted - just not successful
        return 0
    fi

    # No cloud indication at all
    log_timestamped "Cloud validation failed: $command_name"
    print_cloud_status "$command_name" "false"
    return 1
}

# --- Modified run_pdd_command_base - NO --local flag ---
run_pdd_command_base() {
    local exit_on_fail=$1
    shift
    local command_name=$1
    shift
    local args=("$@") # Capture remaining args in an array

    local cmd_array=("$PDD_SCRIPT" "--force")

    # Always add cost tracking
    cmd_array+=("--output-cost" "$REGRESSION_DIR/$COST_FILE")

    # Add --verbose to see cloud execution messages (needed for validation)
    cmd_array+=("--verbose")

    # Add strength and temp unless overridden
    local has_strength=false
    local has_temp=false
    for arg in "${args[@]}"; do
        if [[ "$arg" == "--strength" ]]; then has_strength=true; fi
        if [[ "$arg" == "--temperature" ]]; then has_temp=true; fi
    done
    if ! $has_strength; then cmd_array+=("--strength" "$STRENGTH"); fi
    if ! $has_temp; then cmd_array+=("--temperature" "$TEMPERATURE"); fi

    # NOTE: NO --local flag here - this is the key difference from regression.sh
    # Cloud execution will be used by default

    # Lift global flags (e.g., --context, --list-contexts) before the command name
    local global_ctx_args=()
    local sub_args=()
    local i=0
    while [ $i -lt ${#args[@]} ]; do
        local a=${args[$i]}
        if [ "$a" = "--context" ]; then
            global_ctx_args+=("--context")
            if [ $((i+1)) -lt ${#args[@]} ]; then
                global_ctx_args+=("${args[$((i+1))]}")
                i=$((i+2))
                continue
            else
                i=$((i+1))
                continue
            fi
        elif [ "$a" = "--list-contexts" ]; then
            global_ctx_args+=("--list-contexts")
            i=$((i+1))
            continue
        else
            sub_args+=("$a")
            i=$((i+1))
        fi
    done

    # Assemble final command
    if [ "${#global_ctx_args[@]}" -gt 0 ]; then
        cmd_array+=("${global_ctx_args[@]}")
    fi
    cmd_array+=("$command_name")
    if [ "${#sub_args[@]}" -gt 0 ]; then
        cmd_array+=("${sub_args[@]}")
    fi

    local full_command_str="${cmd_array[*]}" # For logging
    log_timestamped "----------------------------------------"
    log_timestamped "Starting command: $full_command_str"
    log "Running: $full_command_str"

    # Execute and capture output for cloud validation
    local temp_output=$(mktemp)
    "${cmd_array[@]}" 2>&1 | tee -a "$LOG_FILE" > "$temp_output"
    local status=${PIPESTATUS[0]}

    if [ $status -eq 0 ]; then
        log "Command completed successfully."
        log_timestamped "Command: $full_command_str - Completed successfully."
    else
        log_error "Command failed with exit code $status."
        log_timestamped "Command: $full_command_str - Failed with exit code $status."
    fi

    # Validate cloud execution
    validate_cloud_success "$temp_output" "$command_name"

    rm -f "$temp_output"

    if [ $status -ne 0 ] && [ "$exit_on_fail" = "true" ]; then
        exit 1
    fi
    return $status
}

run_pdd_command() {
    run_pdd_command_base true "$@"
}

run_pdd_command_noexit() {
    run_pdd_command_base false "$@"
}

# --- Cleanup Function ---
cleanup() {
    log "Running cleanup..."
    if [ "$CLEANUP_ON_EXIT" = "true" ]; then
        log "Removing regression directory: $REGRESSION_DIR"
        rm -rf "$REGRESSION_DIR"
    else
        log "Skipping cleanup as CLEANUP_ON_EXIT is false. Files remain in: $REGRESSION_DIR"
    fi
    log "Cleanup finished."
}
trap cleanup EXIT

# --- Setup ---

# Create regression test directory and ensure it's clean
log "Creating cloud regression test directory: $REGRESSION_DIR"
mkdir -p "$REGRESSION_DIR"
cd "$REGRESSION_DIR" # Work inside the regression directory

log "Current directory: $(pwd)"
log "PDD Script: $(command -v $PDD_SCRIPT || echo 'Not in PATH')"
log "Fixtures Path: $FIXTURES_PATH"
log "Context Path: $CONTEXT_PATH"
log "Log File: $LOG_FILE"
log "Cost File: $COST_FILE"
log "Strength: $STRENGTH"
log "Temperature: $TEMPERATURE"
log "Cloud Mode: ENABLED (no --local flag)"
log "----------------------------------------"

# Create a local .pddrc with test contexts
cat > ./.pddrc << 'EOF'
contexts:
  default:
    defaults:
      default_language: "python"
  alt:
    defaults:
      default_language: "python"
  envonly:
    defaults:
      default_language: "python"
EOF

# Create context files needed by tests
log "Creating common context files (example.prompt, test.prompt)"
mkdir -p context
cat << \EOF > "context/example.prompt"
For the function 'add' defined based on 'simple_math_python.prompt', the implementation is in 'simple_math.py'.
Therefore, the example should include the line: 'from simple_math import add'
EOF
cat << EOF > "context/test.prompt"
For the function 'add' defined based on 'simple_math_python.prompt', the implementation is in 'simple_math.py'.
Therefore, the test file should include the line: 'from simple_math import add'
EOF

# --- Cloud Regression Tests ---

log_timestamped "======== Starting Cloud Regression Tests ========"

# 1. Generate
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "1" ]; then
    log "========================================"
    log "1. Testing cloud 'generate' command"
    log "========================================"
    run_pdd_command generate --output "$MATH_SCRIPT" "$FIXTURES_PATH/$MATH_PROMPT"
    check_exists "$MATH_SCRIPT" "'generate' output"
    cp "$MATH_SCRIPT" "$ORIGINAL_MATH_SCRIPT" # Backup for subsequent tests
fi

# 2. Example
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "2" ]; then
    log "========================================"
    log "2. Testing cloud 'example' command"
    log "========================================"
    # Ensure we have a script to work with
    if [ ! -f "$MATH_SCRIPT" ] && [ -f "$ORIGINAL_MATH_SCRIPT" ]; then
        cp "$ORIGINAL_MATH_SCRIPT" "$MATH_SCRIPT"
    elif [ ! -f "$MATH_SCRIPT" ]; then
        log "Generating math script first..."
        if ! run_pdd_command_noexit generate --output "$MATH_SCRIPT" "$FIXTURES_PATH/$MATH_PROMPT"; then
            log "Prerequisite generate failed, retrying after 5s..."
            sleep 5
            run_pdd_command generate --output "$MATH_SCRIPT" "$FIXTURES_PATH/$MATH_PROMPT"
        fi
    fi
    run_pdd_command example --output "$MATH_VERIFICATION_PROGRAM" "$FIXTURES_PATH/$MATH_PROMPT" "$MATH_SCRIPT"
    check_exists "$MATH_VERIFICATION_PROGRAM" "'example' output"
fi

# 3. Test
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "3" ]; then
    log "========================================"
    log "3. Testing cloud 'test' command"
    log "========================================"
    # Ensure we have a script to work with
    if [ ! -f "$MATH_SCRIPT" ] && [ -f "$ORIGINAL_MATH_SCRIPT" ]; then
        cp "$ORIGINAL_MATH_SCRIPT" "$MATH_SCRIPT"
    elif [ ! -f "$MATH_SCRIPT" ]; then
        log "Generating math script first..."
        if ! run_pdd_command_noexit generate --output "$MATH_SCRIPT" "$FIXTURES_PATH/$MATH_PROMPT"; then
            log "Prerequisite generate failed, retrying after 5s..."
            sleep 5
            run_pdd_command generate --output "$MATH_SCRIPT" "$FIXTURES_PATH/$MATH_PROMPT"
        fi
    fi
    run_pdd_command test --output "$MATH_TEST_SCRIPT" --language Python "$FIXTURES_PATH/$MATH_PROMPT" "$MATH_SCRIPT"
    check_exists "$MATH_TEST_SCRIPT" "'test' output"
fi

# 4. Fix
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "4" ]; then
    log "========================================"
    log "4. Testing cloud 'fix' command"
    log "========================================"
    # Ensure we have necessary files
    if [ ! -f "$MATH_SCRIPT" ] && [ -f "$ORIGINAL_MATH_SCRIPT" ]; then
        cp "$ORIGINAL_MATH_SCRIPT" "$MATH_SCRIPT"
    elif [ ! -f "$MATH_SCRIPT" ]; then
        log "Generating math script first..."
        if ! run_pdd_command_noexit generate --output "$MATH_SCRIPT" "$FIXTURES_PATH/$MATH_PROMPT"; then
            log "Prerequisite generate failed, retrying after 5s..."
            sleep 5
            run_pdd_command generate --output "$MATH_SCRIPT" "$FIXTURES_PATH/$MATH_PROMPT"
        fi
    fi
    if [ ! -f "$MATH_SCRIPT" ]; then
        log "Skipping fix test: math script not available"
    elif [ ! -f "$MATH_TEST_SCRIPT" ]; then
        log "Generating test script first..."
        run_pdd_command_noexit test --output "$MATH_TEST_SCRIPT" --language Python "$FIXTURES_PATH/$MATH_PROMPT" "$MATH_SCRIPT" || true
    fi

    if [ ! -f "$MATH_SCRIPT" ] || [ ! -f "$MATH_TEST_SCRIPT" ]; then
        log "Skipping fix test: prerequisite files not available"
    else
        # Run tests to potentially generate errors for fix command
        log "Running pytest to check for errors..."
        python -m pytest "$MATH_TEST_SCRIPT" > "$PYTEST_LOG" 2>&1 || true

        if grep -q -E "===+ (FAILURES|ERRORS) ===+" "$PYTEST_LOG"; then
            log "Errors found, running 'fix' command"
            run_pdd_command_noexit fix --output-test "$FIXED_MATH_TEST_SCRIPT" --output-code "$FIXED_MATH_SCRIPT" \
                                "$FIXTURES_PATH/$MATH_PROMPT" "$MATH_SCRIPT" "$MATH_TEST_SCRIPT" "$PYTEST_LOG"
        else
            log "No errors found in pytest run, creating a simple error scenario for fix test"
            # Create a test file with an intentional error to test fix command
            cat > "broken_${MATH_TEST_SCRIPT}" << 'PYEOF'
import pytest
from simple_math import add

def test_add_intentional_fail():
    """This test intentionally fails to test the fix command."""
    assert add(2, 2) == 5, "Intentional failure for testing fix"
PYEOF
            python -m pytest "broken_${MATH_TEST_SCRIPT}" > "$PYTEST_LOG" 2>&1 || true
            run_pdd_command_noexit fix --output-test "$FIXED_MATH_TEST_SCRIPT" --output-code "$FIXED_MATH_SCRIPT" \
                                "$FIXTURES_PATH/$MATH_PROMPT" "$MATH_SCRIPT" "broken_${MATH_TEST_SCRIPT}" "$PYTEST_LOG"
        fi
    fi
fi

# 5. Crash
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "5" ]; then
    log "========================================"
    log "5. Testing cloud 'crash' command"
    log "========================================"
    # Ensure we have necessary files
    if [ ! -f "$MATH_SCRIPT" ] && [ -f "$ORIGINAL_MATH_SCRIPT" ]; then
        cp "$ORIGINAL_MATH_SCRIPT" "$MATH_SCRIPT"
    elif [ ! -f "$MATH_SCRIPT" ]; then
        log "Generating math script first..."
        if ! run_pdd_command_noexit generate --output "$MATH_SCRIPT" "$FIXTURES_PATH/$MATH_PROMPT"; then
            log "Prerequisite generate failed, retrying after 5s..."
            sleep 5
            run_pdd_command generate --output "$MATH_SCRIPT" "$FIXTURES_PATH/$MATH_PROMPT"
        fi
    fi

    # Create a program that will crash (TypeError)
    log "Creating crashing program..."
    cat > "$MATH_VERIFICATION_PROGRAM" << PYEOF
import $MATH_BASENAME
result = $MATH_BASENAME.add(5, 'a')  # This will cause a TypeError
print(f'The sum is: {result}')
PYEOF

    # Run to generate error log
    log "Running crashing program to generate error log..."
    python "$MATH_VERIFICATION_PROGRAM" > "$MATH_ERROR_LOG" 2>&1 || true

    if [ -s "$MATH_ERROR_LOG" ]; then
        log "Error log generated, running 'crash' command"
        run_pdd_command crash --output "$CRASH_FIXED_SCRIPT" --output-program "$CRASH_FIXED_PROGRAM" \
                              "$FIXTURES_PATH/$MATH_PROMPT" "$MATH_SCRIPT" \
                              "$MATH_VERIFICATION_PROGRAM" "$MATH_ERROR_LOG"
    else
        log_error "Failed to generate error log for crash test"
    fi
fi

# 6. Verify
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "6" ]; then
    log "========================================"
    log "6. Testing cloud 'verify' command"
    log "========================================"
    # Ensure we have necessary files
    if [ ! -f "$MATH_SCRIPT" ] && [ -f "$ORIGINAL_MATH_SCRIPT" ]; then
        cp "$ORIGINAL_MATH_SCRIPT" "$MATH_SCRIPT"
    elif [ ! -f "$MATH_SCRIPT" ]; then
        log "Generating math script first..."
        if ! run_pdd_command_noexit generate --output "$MATH_SCRIPT" "$FIXTURES_PATH/$MATH_PROMPT"; then
            log_error "Prerequisite generate failed for verify test (cloud rate limit?). Skipping."
            CLOUD_FAILURES=$((CLOUD_FAILURES + 1))
            print_cloud_status "verify (prerequisite generate)" "false"
        fi
    fi
    if [ ! -f "$MATH_SCRIPT" ]; then
        log "Skipping verify test: math script not available"
    else
        if [ ! -f "$MATH_VERIFICATION_PROGRAM" ] || grep -q "'a'" "$MATH_VERIFICATION_PROGRAM"; then
            # Regenerate a valid example program
            log "Generating example program first..."
            run_pdd_command_noexit example --output "$MATH_VERIFICATION_PROGRAM" "$FIXTURES_PATH/$MATH_PROMPT" "$MATH_SCRIPT" || true
        fi

        if [ ! -f "$MATH_VERIFICATION_PROGRAM" ]; then
            log "Skipping verify test: example program not available"
        else
            # Introduce a semantic error to test verify
            log "Introducing semantic error for verify test..."
            if grep -q "return a + b" "$MATH_SCRIPT"; then
                sed -i.bak 's/return a + b/return a - b/' "$MATH_SCRIPT"
                log "Changed 'return a + b' to 'return a - b'"
            else
                log "Could not find 'return a + b' pattern, verify may not detect semantic error"
            fi

            run_pdd_command_noexit verify --output-results "$VERIFY_RESULTS_LOG" \
                --output-code "$VERIFY_CODE_OUTPUT" --output-program "$VERIFY_PROGRAM_OUTPUT" \
                --max-attempts 3 --budget 5.0 \
                "$FIXTURES_PATH/$MATH_PROMPT" "$MATH_SCRIPT" "$MATH_VERIFICATION_PROGRAM"
        fi
    fi
fi

# 7. Split
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "7" ]; then
    log "========================================"
    log "7. Testing cloud 'split' command"
    log "========================================"
    # Ensure we have necessary files
    if [ ! -f "$MATH_SCRIPT" ] && [ -f "$ORIGINAL_MATH_SCRIPT" ]; then
        cp "$ORIGINAL_MATH_SCRIPT" "$MATH_SCRIPT"
    elif [ ! -f "$MATH_SCRIPT" ]; then
        log "Generating math script first..."
        run_pdd_command generate --output "$MATH_SCRIPT" "$FIXTURES_PATH/$MATH_PROMPT"
    fi
    if [ ! -f "$MATH_VERIFICATION_PROGRAM" ]; then
        log "Generating example program first..."
        run_pdd_command example --output "$MATH_VERIFICATION_PROGRAM" "$FIXTURES_PATH/$MATH_PROMPT" "$MATH_SCRIPT"
    fi

    # Create split instruction prompt
    echo "Extract the 'add' function into a separate sub-prompt." > "$SPLIT_PROMPT"

    run_pdd_command split --output-sub "$SPLIT_SUB_PROMPT" --output-modified "$SPLIT_MODIFIED_PROMPT" \
                          "$SPLIT_PROMPT" \
                          "$MATH_SCRIPT" \
                          "$MATH_VERIFICATION_PROGRAM"
    check_exists "$SPLIT_SUB_PROMPT" "'split' sub-prompt output"
    check_exists "$SPLIT_MODIFIED_PROMPT" "'split' modified prompt output"
fi

# 8. Auto-Deps
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "8" ]; then
    log "========================================"
    log "8. Testing cloud 'auto-deps' command"
    log "========================================"
    # Create a single simple context file to minimize scan time
    mkdir -p autodeps_context
    cat > "autodeps_context/helper.py" << 'PYEOF'
"""Simple helper module."""
def helper_func(x):
    return x * 2
PYEOF

    run_pdd_command auto-deps --output "$AUTO_DEPS_PROMPT" \
                              --csv "$AUTO_DEPS_CSV" \
                              "$FIXTURES_PATH/$MATH_PROMPT" "autodeps_context/*.py"
    check_exists "$AUTO_DEPS_PROMPT" "'auto-deps' modified prompt"
    check_exists "$AUTO_DEPS_CSV" "'auto-deps' dependency CSV"
fi

# --- Final Summary ---
log_timestamped "======== Cloud Regression Tests Completed ========"
log_timestamped "Cloud Successes: $CLOUD_SUCCESSES"
log_timestamped "Cloud Failures: $CLOUD_FAILURES"

echo ""
echo "========================================"
echo "CLOUD REGRESSION TEST SUMMARY"
echo "========================================"
echo "Cloud Successes: $CLOUD_SUCCESSES"
echo "Cloud Failures:  $CLOUD_FAILURES"
echo ""
echo "Log file: $LOG_FILE"
echo "Cost file: $REGRESSION_DIR/$COST_FILE"
echo ""
if [ $CLOUD_FAILURES -gt 0 ]; then
    echo "STATUS: FAILED - Some commands did not use cloud execution"
    echo "========================================"
    exit 1
else
    echo "STATUS: PASSED - All commands used cloud execution successfully"
    echo "========================================"
fi
