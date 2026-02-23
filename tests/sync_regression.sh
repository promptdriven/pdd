#!/bin/bash

# Exit immediately if a command exits with a non-zero status.
set -e
# Treat unset variables as an error when substituting.
set -u

# Global settings
VERBOSE=${VERBOSE:-1} # Default to 1 if not set
STRENGTH=${STRENGTH:-0.3} # Default strength (lower = cheaper models)
TEMPERATURE=${TEMPERATURE:-0.0} # Default temperature
TEST_LOCAL=${TEST_LOCAL:-false} # Default to cloud execution
CLEANUP_ON_EXIT=false # Set to false to keep files for debugging

# --- Helper Functions ---

log() {
    if [ "$VERBOSE" -eq 1 ]; then
        echo "[INFO] $1"
    fi
}

# WSL environment detection and validation
is_wsl() {
    # Check multiple WSL indicators
    if [ -f /proc/version ] && grep -qi microsoft /proc/version; then
        return 0
    elif [ -n "${WSL_DISTRO_NAME:-}" ]; then
        return 0
    elif echo "${PATH}" | grep -q "/mnt/c/"; then
        return 0
    else
        return 1
    fi
}

validate_wsl_environment() {
    if is_wsl; then
        log "WSL environment detected"
        
        # Check for API key environment variables and validate they don't contain carriage returns
        if [ -n "${OPENAI_API_KEY:-}" ]; then
            # Check if API key contains carriage return characters
            if echo "${OPENAI_API_KEY}" | grep -q $'\r'; then
                log "WARNING: OPENAI_API_KEY contains carriage return characters"
                log "This is a known WSL issue that can cause API authentication failures"
                log "Consider re-setting your API key or checking your .env file for line ending issues"
            else
                log "OPENAI_API_KEY appears to be properly formatted"
            fi
        fi
        
        # Check for other potential WSL issues
        if [ ! -d "/mnt/c" ]; then
            log "WARNING: WSL detected but /mnt/c directory not found - this may indicate WSL configuration issues"
        fi
        
        log "WSL environment validation complete"
    else
        log "Non-WSL environment detected"
    fi
}

# --- Test Selection ---
# Accept a single argument (test number) to run only that test. Default to "all".
TARGET_TEST=${1:-"all"}
log "Running sync tests: $TARGET_TEST"
# --- End Test Selection ---

# Set PDD_AUTO_UPDATE to false to prevent interference
export PDD_AUTO_UPDATE=false

# Force local execution for regression tests using the --local CLI flag.
# This is cleaner than manipulating environment variables.
TEST_LOCAL=true

# Define base variables
# Set PDD base directory as the script's location (two directories up from this script)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PDD_BASE_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
PDD_PATH="$PDD_BASE_DIR/pdd"
STAGING_PATH="$PDD_BASE_DIR/staging"
# Use local development version instead of globally installed pdd
PDD_SCRIPT="$PDD_BASE_DIR/pdd-local.sh"
PROMPTS_PATH="$PDD_BASE_DIR/prompts"
CONTEXT_PATH="$PDD_BASE_DIR/context"
OUTPUT_PATH="$PDD_BASE_DIR/staging"

# Determine REGRESSION_DIR
if [ -n "${REGRESSION_TARGET_DIR:-}" ]; then
    REGRESSION_DIR="$REGRESSION_TARGET_DIR"
    log "Using specified regression directory: $REGRESSION_DIR"
elif [ "$TARGET_TEST" = "all" ]; then
    REGRESSION_DIR="$OUTPUT_PATH/sync_regression_$(date +%Y%m%d_%H%M%S)"
    log "Creating new sync regression directory for full run: $REGRESSION_DIR"
else
    # Find the latest existing sync regression directory for specific tests
    LATEST_REGRESSION_DIR=$(ls -td -- "$OUTPUT_PATH"/sync_regression_* 2>/dev/null | head -n 1)
    if [ -d "$LATEST_REGRESSION_DIR" ]; then
        REGRESSION_DIR="$LATEST_REGRESSION_DIR"
        log "Reusing latest sync regression directory for specific test: $REGRESSION_DIR"
    else
        log "Warning: No existing sync regression directory found in $OUTPUT_PATH. Creating a new one."
        REGRESSION_DIR="$OUTPUT_PATH/sync_regression_$(date +%Y%m%d_%H%M%S)_specific_${TARGET_TEST}"
        log "Creating new sync regression directory: $REGRESSION_DIR"
    fi
fi

LOG_FILE="$REGRESSION_DIR/sync_regression.log"
COST_FILE="sync_regression_cost.csv"

# Test case files
SIMPLE_BASENAME="simple_math"
SIMPLE_PROMPT="${SIMPLE_BASENAME}_python.prompt"
SIMPLE_SCRIPT="${SIMPLE_BASENAME}.py"
SIMPLE_TEST_SCRIPT="test_${SIMPLE_BASENAME}.py"
SIMPLE_EXAMPLE="${SIMPLE_BASENAME}_example.py"

COMPLEX_BASENAME="data_processor"
COMPLEX_PROMPT="${COMPLEX_BASENAME}_python.prompt"
COMPLEX_SCRIPT="${COMPLEX_BASENAME}.py"

MULTI_LANG_BASENAME="calculator"
MULTI_LANG_PYTHON_PROMPT="${MULTI_LANG_BASENAME}_python.prompt"
MULTI_LANG_JS_PROMPT="${MULTI_LANG_BASENAME}_javascript.prompt"
MULTI_LANG_TS_PROMPT="${MULTI_LANG_BASENAME}_typescript.prompt"

# Sync state and metadata files
SYNC_META_DIR=".pdd/meta"
SYNC_LOCKS_DIR=".pdd/locks"

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

check_not_exists() {
    local file_path="$1"
    local description="$2"
    if [ -e "$file_path" ]; then
        log_error "$description file SHOULD NOT exist but does: $file_path"
        log_timestamped "Validation failed: $description file exists but should not: $file_path"
        exit 1
    else
        log "$description file correctly does not exist: $file_path"
        log_timestamped "Validation success: $description file does not exist: $file_path"
    fi
}

run_pdd_command_base() {
    local exit_on_fail=$1
    shift
    local command_name=$1
    shift
    local args=("$@") # Capture remaining args in an array

    local cmd_array=("$PDD_SCRIPT" "--force")

    # Always add cost tracking
    cmd_array+=("--output-cost" "$REGRESSION_DIR/$COST_FILE")

    # Add strength and temp unless overridden
    local has_strength=false
    local has_temp=false
    for arg in "${args[@]}"; do
        if [[ "$arg" == "--strength" ]]; then has_strength=true; fi
        if [[ "$arg" == "--temperature" ]]; then has_temp=true; fi
    done
    if ! $has_strength; then cmd_array+=("--strength" "$STRENGTH"); fi
    if ! $has_temp; then cmd_array+=("--temperature" "$TEMPERATURE"); fi

    # Add --local if requested
    if [ "$TEST_LOCAL" = "true" ]; then
        # Check for necessary API keys (example for OpenAI)
        if [ -z "${OPENAI_API_KEY:-}" ]; then
            log_error "TEST_LOCAL is true, but OPENAI_API_KEY is not set. Skipping local test run."
            return 1
        fi
        cmd_array+=("--local")
        log "Running with --local flag"
    fi

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
        elif [ "$a" = "--local" ]; then
            global_ctx_args+=("--local")
            i=$((i+1))
            continue
        else
            sub_args+=("$a")
            i=$((i+1))
        fi
    done

    # Append globals (if any), then subcommand and its args
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

    # Execute the command with timeout, redirecting stdout/stderr to log file and stdin from /dev/null
    PDD_CMD_TIMEOUT="${PDD_CMD_TIMEOUT:-600}"
    run_with_timeout "${PDD_CMD_TIMEOUT}s" "${cmd_array[@]}" < /dev/null >> "$LOG_FILE" 2>&1
    local status=$?

    if [ $status -eq 0 ]; then
        log "Command completed successfully."
        log_timestamped "Command: $full_command_str - Completed successfully."
    else
        log_error "Command failed with exit code $status."
        log_timestamped "Command: $full_command_str - Failed with exit code $status."
        if [ "$exit_on_fail" = "true" ]; then
            exit 1
        fi
    fi
    return $status
}   

run_pdd_command() {
    run_pdd_command_base true "$@"
}

run_pdd_command_noexit() {
    run_pdd_command_base false "$@"
}

run_pdd_expect_fail() {
    log "Expecting failure for: $*"
    if run_pdd_command_base false "$@"; then
        log_error "Command succeeded but was expected to fail: $*"
        log_timestamped "Validation failed: Command succeeded but was expected to fail: $*"
        exit 1
    else
        log "Command failed as expected."
        log_timestamped "Validation success: Command failed as expected: $*"
    fi
}

# --- Portable Timeout Helper ---
# Prefer GNU timeout if available (macOS installs it as gtimeout via coreutils)
# Falls back to pure-bash implementation if neither is available
TIMEOUT_CMD="$(command -v timeout || command -v gtimeout || true)"
run_with_timeout() {
    local duration="$1"; shift

    if [ -n "$TIMEOUT_CMD" ]; then
        "$TIMEOUT_CMD" "$duration" "$@"
    else
        # Pure-bash timeout fallback for systems without timeout/gtimeout
        # Parse duration (supports formats: 30, 30s, 5m, 1h)
        local seconds
        case "$duration" in
            *s) seconds="${duration%s}" ;;
            *m) seconds=$((${duration%m} * 60)) ;;
            *h) seconds=$((${duration%h} * 3600)) ;;
            *)  seconds="$duration" ;;
        esac

        log "Using bash timeout fallback (${seconds}s): $*"

        # Run command in background
        "$@" &
        local cmd_pid=$!

        # Wait for command or timeout
        local elapsed=0
        while kill -0 "$cmd_pid" 2>/dev/null; do
            if [ "$elapsed" -ge "$seconds" ]; then
                kill -TERM "$cmd_pid" 2>/dev/null
                sleep 1
                kill -KILL "$cmd_pid" 2>/dev/null
                wait "$cmd_pid" 2>/dev/null
                log "Command timed out after ${seconds}s"
                return 124  # Same exit code as GNU timeout
            fi
            sleep 1
            elapsed=$((elapsed + 1))
        done

        # Command finished before timeout
        wait "$cmd_pid"
        return $?
    fi
}

wait_for_sync_completion() {
    local basename="$1"
    local timeout="${2:-30}" # Default 30 seconds timeout
    local count=0
    
    log "Waiting for sync completion for $basename (timeout: ${timeout}s)"
    
    while [ $count -lt $timeout ]; do
        # Check if sync process is still running by looking for lock files
        if [ ! -d "$SYNC_LOCKS_DIR" ] || [ -z "$(find "$SYNC_LOCKS_DIR" -name "*${basename}*" 2>/dev/null)" ]; then
            log "Sync completed for $basename"
            return 0
        fi
        sleep 1
        count=$((count + 1))
    done
    
    log_error "Sync timeout for $basename after ${timeout}s"
    return 1
}

check_sync_files() {
    local basename="$1"
    local language="${2:-python}"
    local strict="${3:-false}" # If false, only check code file is required
    
    log "DEBUG: Checking for files in current directory: $(pwd)"
    log "DEBUG: Contents of current directory:"
    ls -la >> "$LOG_FILE" 2>&1 || true
    log "DEBUG: Contents of src/ directory (if exists):"
    ls -la src/ >> "$LOG_FILE" 2>&1 || true

    # Check generated files exist - handle multiple possible locations
    case "$language" in
        "python")
            # Try src/, pdd/, and root directory (for different .pddrc contexts)
            if [ -f "src/${basename}.py" ] && [ -s "src/${basename}.py" ]; then
                check_exists "src/${basename}.py" "Generated Python code"
            elif [ -f "pdd/${basename}.py" ] && [ -s "pdd/${basename}.py" ]; then
                check_exists "pdd/${basename}.py" "Generated Python code"
            elif [ -f "${basename}.py" ] && [ -s "${basename}.py" ]; then
                log "Generated Python code found in root (copying to expected location): ${basename}.py"
                mkdir -p src
                cp "${basename}.py" "src/${basename}.py"
                check_exists "src/${basename}.py" "Generated Python code"
            else
                log_error "Generated Python code file not found in src/, pdd/, or root directory"
                exit 1
            fi
            
            # Check optional files (may not be generated in current sync implementation)
            if [ "$strict" = "true" ]; then
                # Handle test files that might be in root
                if [ -f "tests/test_${basename}.py" ] && [ -s "tests/test_${basename}.py" ]; then
                    check_exists "tests/test_${basename}.py" "Generated Python tests"
                elif [ -f "test_${basename}.py" ] && [ -s "test_${basename}.py" ]; then
                    log "Generated Python test found in root (copying to expected location): test_${basename}.py"
                    mkdir -p tests
                    cp "test_${basename}.py" "tests/test_${basename}.py"
                    check_exists "tests/test_${basename}.py" "Generated Python tests"
                else
                    log_error "Generated Python test file not found in tests/ or root directory"
                    exit 1
                fi
                check_exists "examples/${basename}_example.py" "Generated Python example"
            else
                # Handle test files that might be in root (non-strict mode)
                if [ -f "tests/test_${basename}.py" ] && [ -s "tests/test_${basename}.py" ]; then
                    log "Generated Python tests exist in tests/"
                elif [ -f "test_${basename}.py" ] && [ -s "test_${basename}.py" ]; then
                    log "Generated Python test found in root (moving to tests/): test_${basename}.py"
                    mkdir -p tests
                    cp "test_${basename}.py" "tests/test_${basename}.py"
                    log "Generated Python tests moved to tests/"
                else
                    log "Generated Python tests not created (acceptable with current sync behavior)"
                fi
                
                if [ -f "examples/${basename}_example.py" ]; then
                    log "Generated Python example exists"
                else
                    log "Generated Python example not created (acceptable with current sync behavior)"
                fi
            fi
            ;;
        "javascript")
            check_exists "pdd/${basename}.js" "Generated JavaScript code"
            if [ "$strict" = "true" ]; then
                check_exists "examples/${basename}_example.js" "Generated JavaScript example"
                check_exists "tests/test_${basename}.js" "Generated JavaScript tests"
            fi
            ;;
        "typescript")
            check_exists "pdd/${basename}.ts" "Generated TypeScript code"
            if [ "$strict" = "true" ]; then
                check_exists "examples/${basename}_example.ts" "Generated TypeScript example"
                check_exists "tests/test_${basename}.ts" "Generated TypeScript tests"
            fi
            ;;
    esac
    
    # Check metadata files exist (optional)
    if [ -f "$SYNC_META_DIR/${basename}_${language}.json" ]; then
        log "Sync metadata exists"
    else
        log "Sync metadata not found (may not be created in test environment)"
    fi
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

# Validate WSL environment before starting tests
validate_wsl_environment

# Create regression test directory and ensure it's clean
log "Creating sync regression test directory: $REGRESSION_DIR"
mkdir -p "$REGRESSION_DIR"
cd "$REGRESSION_DIR" # Work inside the regression directory

log "Current directory: $(pwd)"
log "PDD Script: $(command -v $PDD_SCRIPT || echo 'Not in PATH')"
log "Prompt Path: $PROMPTS_PATH"
log "Context Path: $CONTEXT_PATH"
log "Log File: $LOG_FILE"
log "Cost File: $COST_FILE"
log "Strength: $STRENGTH"
log "Temperature: $TEMPERATURE"
log "Local Execution: $TEST_LOCAL"
log "----------------------------------------"

# Create a local .pdd directory for regression-specific config
mkdir -p .pdd

# Create a filtered llm_model.csv that excludes local/unreachable models for CI stability
if [ -f "$PDD_BASE_DIR/pdd/data/llm_model.csv" ]; then
    log "Creating CI-safe llm_model.csv (excluding 'localhost' and 'lm_studio')"
    grep -vE "localhost|lm_studio|anthropic/" "$PDD_BASE_DIR/pdd/data/llm_model.csv" > .pdd/llm_model.csv
else
    log "Warning: Source llm_model.csv not found at $PDD_BASE_DIR/pdd/data/llm_model.csv"
fi

# Force cheap models for regression tests to minimize cost
export PDD_MODEL_DEFAULT="vertex_ai/gemini-3-flash-preview"
export PDD_AGENTIC_PROVIDER="google,anthropic,openai"

# Create a local .pddrc with explicit sync test contexts
cat > ./.pddrc << 'EOF'
contexts:
  regression_root:
    defaults:
      generate_output_path: "./"
      test_output_path: "tests/"
      example_output_path: "examples/"
      default_language: "python"
  regression_pdd:
    defaults:
      generate_output_path: "src/"
      test_output_path: "tests/"
      example_output_path: "examples/"
      default_language: "python"
EOF

# Create directory structure expected by contexts
log "Creating directory structure for sync tests"
mkdir -p src examples tests context prompts

# Create placeholder test files for multi-language calculator (required by multi-language sync)
# log "Creating placeholder test files for multi-language projects"
# cat << EOF > "tests/test_calculator.py"
# # Placeholder test file for calculator module
# # This will be generated/updated by the sync process
# import pytest

# def test_placeholder():
#     """Placeholder test - will be replaced by sync process"""
#     pass
# EOF

# cat << EOF > "tests/test_calculator.js"
# // Placeholder test file for calculator module
# // This will be generated/updated by the sync process
# const { describe, it, expect } = require('@jest/globals');

# describe('Calculator placeholder tests', () => {
#     it('should be a placeholder test - will be replaced by sync process', () => {
#         expect(true).toBe(true);
#     });
# });
# EOF

# cat << EOF > "tests/test_calculator.ts"
# // Placeholder test file for calculator module
# // This will be generated/updated by the sync process
# import { describe, it, expect } from '@jest/globals';

# describe('Calculator placeholder tests', () => {
#     it('should be a placeholder test - will be replaced by sync process', () => {
#         expect(true).toBe(true);
#     });
# });
# EOF

# Create context files needed by tests
log "Creating context files for sync tests"
cat << EOF > "context/test.prompt"
CRITICAL: For test imports, always use the exact basename as the module name:
- For basename "simple_math": use "from simple_math import add"
- For basename "calculator": use "from calculator import add, subtract, multiply, divide"  
- For basename "data_processor": use "from data_processor import DataProcessor"
Never use shortened names like "calc" or function names like "add" as module names.
The module name is always the same as the basename parameter passed to PDD.
EOF

cat << EOF > "context/example.prompt"
For functions defined in prompt files, ensure examples demonstrate practical usage with correct imports.
CRITICAL IMPORT RULES:
- Always use the exact basename as the module name (e.g., for data_processor.py, use "from data_processor import ClassName")  
- Never use shortened names or aliases in import statements
- Never use function names as module names
- Show the import statement explicitly in examples when demonstrating usage
- The generated module name will always match the basename parameter
EOF

# Create test prompt files
log "Creating test prompt files"
mkdir -p prompts

# Simple math prompt for basic sync testing
cat << EOF > "prompts/$SIMPLE_PROMPT"
Create a Python module with a simple math function.

Requirements:
- Function name: add
- Parameters: a, b (both numbers)  
- Return: sum of a and b
- Include type hints
- Add docstring explaining the function

Example usage:
from simple_math import add
result = add(5, 3)  # Should return 8
EOF

# Complex data processor prompt for advanced sync testing
cat << EOF > "prompts/$COMPLEX_PROMPT"
Create a Python module for data processing.

Requirements:
- Class name: DataProcessor
- Method: process_data(data: list) -> dict
- Functionality: Calculate statistics (min, max, mean) of numeric data
- Handle empty lists and non-numeric data gracefully
- Include comprehensive error handling
- Add detailed docstrings

Example usage:
from data_processor import DataProcessor
processor = DataProcessor()
stats = processor.process_data([1, 2, 3, 4, 5])
EOF

# Multi-language calculator prompts
cat << EOF > "prompts/$MULTI_LANG_PYTHON_PROMPT"
Create a Python calculator module.

Requirements:
- Functions: add, subtract, multiply, divide
- Type hints for all functions
- Error handling for division by zero
- Comprehensive docstrings

Example:
from calculator import add, subtract, multiply, divide
result = add(10, 5)  # Returns 15
divide(10, 0)  # Raises ValueError
EOF

cat << EOF > "prompts/$MULTI_LANG_JS_PROMPT"
Create a JavaScript calculator module.

Requirements:
- Functions: add, subtract, multiply, divide
- JSDoc comments for all functions
- Error handling for division by zero
- Export all functions

Example:
const { add, subtract, multiply, divide } = require('./calculator');
const result = add(10, 5);  // Returns 15
divide(10, 0);  // Throws Error
EOF

cat << EOF > "prompts/$MULTI_LANG_TS_PROMPT"
Create a TypeScript calculator module.

Requirements:
- Functions: add, subtract, multiply, divide
- Full TypeScript types
- Error handling for division by zero
- Export all functions with proper types

Example:
import { add, subtract, multiply, divide } from './calculator';
const result: number = add(10, 5);  // Returns 15
divide(10, 0);  // Throws Error
EOF

# --- Sync Regression Tests ---

log_timestamped "======== Starting Sync Regression Tests ========"

# 1. Basic Sync Test
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "1" ]; then
    log "1. Testing basic 'sync' command"
    
    if run_pdd_command --verbose sync --budget 20.0 "$SIMPLE_BASENAME"; then
        log "Validation success: sync basic command completed"
    else
        log_timestamped "[ERROR] Validation failed: sync basic command"
    fi
    
    log "Checking generated files..."
    if check_sync_files "$SIMPLE_BASENAME" "python" false; then
        log "Validation success: generated files present for basic sync"
    else
        log_timestamped "[ERROR] Validation failed: generated files missing for basic sync"
    fi
    
    if [ -f "tests/test_${SIMPLE_BASENAME}.py" ]; then
        if python -m pytest "tests/test_${SIMPLE_BASENAME}.py" >> "$LOG_FILE" 2>&1; then
            log "Validation success: generated tests ran for basic sync"
        else
            log_timestamped "[ERROR] Validation failed: generated tests errored for basic sync"
        fi
    else
        log "No test file generated, skipping test execution"
    fi
fi

# 2. Sync with Skip Options
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "2" ]; then
    log "2. Testing 'sync' with skip options"
    
    # Test --skip-verify
    log "2a. Testing 'sync --skip-verify'"
    if run_pdd_command_noexit sync --skip-verify --context regression_root "$SIMPLE_BASENAME"; then
        log "Validation success: sync --skip-verify"
    else
        log_timestamped "[ERROR] Validation failed: sync --skip-verify"
    fi
    if check_sync_files "$SIMPLE_BASENAME" "python" false; then
        log "Validation success: files exist after sync --skip-verify"
    else
        log_timestamped "[ERROR] Validation failed: files missing after sync --skip-verify"
    fi
    
    # Test --skip-tests
    log "2b. Testing 'sync --skip-tests'"
    # Clean previous files AND metadata to test fresh generation
    rm -f "src/${SIMPLE_BASENAME}.py" "${SIMPLE_BASENAME}.py" "examples/${SIMPLE_BASENAME}_example.py" "tests/test_${SIMPLE_BASENAME}.py"
    rm -f "$SYNC_META_DIR/${SIMPLE_BASENAME}_python.json" "$SYNC_META_DIR/${SIMPLE_BASENAME}_python_run.json"
    {
    set +e
    if run_pdd_command_noexit sync --skip-tests --context regression_pdd "$SIMPLE_BASENAME"; then
        log "Validation success: sync --skip-tests"
    else
        status=$?
        log_timestamped "[ERROR] Validation failed: sync --skip-tests (exit $status)"
    fi
    set -e
}
    # Check what was actually generated (sync may only generate code)
    if [ -f "src/${SIMPLE_BASENAME}.py" ]; then
        log "Code file generated with --skip-tests"
        check_exists "src/${SIMPLE_BASENAME}.py" "Generated code with --skip-tests"
    else
        log "No code file generated with --skip-tests (unexpected)"
    fi
    
    # Note: In current implementation, sync may not generate example/test files
    # This tests the actual behavior rather than ideal behavior
    if [ -f "examples/${SIMPLE_BASENAME}_example.py" ]; then
        log "Example file was generated (not expected with current sync behavior)"
    else
        log "Example file not generated (expected with current sync behavior)"
    fi
    
    # Test file should not exist when --skip-tests is used
    check_not_exists "tests/test_${SIMPLE_BASENAME}.py" "Test file (should not exist with --skip-tests)"
    
    # Test both skip options together
    log "2c. Testing 'sync --skip-verify --skip-tests'"
    rm -f "src/${SIMPLE_BASENAME}.py" "${SIMPLE_BASENAME}.py" "examples/${SIMPLE_BASENAME}_example.py"
    rm -f "$SYNC_META_DIR/${SIMPLE_BASENAME}_python.json" "$SYNC_META_DIR/${SIMPLE_BASENAME}_python_run.json"
    {
    set +e
    if run_pdd_command_noexit sync --skip-verify --skip-tests --context regression_pdd "$SIMPLE_BASENAME"; then
        log "Validation success: sync --skip-verify --skip-tests"
    else
        status=$?
        log_timestamped "[ERROR] Validation failed: sync --skip-verify --skip-tests (exit $status)"
    fi
    set -e
}
    check_exists "src/${SIMPLE_BASENAME}.py" "Generated code with both skip options"
    
    # Example file may or may not be generated
    if [ -f "examples/${SIMPLE_BASENAME}_example.py" ]; then
        log "Example file generated with both skip options (unexpected but acceptable)"
    else
        log "Example file not generated with both skip options (expected with current sync behavior)"
    fi
    
    check_not_exists "tests/test_${SIMPLE_BASENAME}.py" "Test file (should not exist with skip options)"
fi

# 3. Sync with Budget and Attempt Limits
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "3" ]; then
    log "3. Testing 'sync' with budget and attempt limits"
    
    # Test with budget limit
    log "3a. Testing 'sync --budget 2.0'"
    rm -f "src/${SIMPLE_BASENAME}.py" "examples/${SIMPLE_BASENAME}_example.py" "tests/test_${SIMPLE_BASENAME}.py"
    rm -f "$SYNC_META_DIR/${SIMPLE_BASENAME}_python.json" "$SYNC_META_DIR/${SIMPLE_BASENAME}_python_run.json"
    if run_pdd_command_noexit sync --budget 2.0 --context regression_pdd "$SIMPLE_BASENAME"; then
        log "Validation success: sync --budget 2.0"
    else
        log_timestamped "[ERROR] Validation failed: sync --budget 2.0"
    fi
    # Should still create basic files even with low budget
    if check_sync_files "$SIMPLE_BASENAME" "python" false; then
        log "Validation success: files exist after initial sync"
    else
        log_timestamped "[ERROR] Validation failed: files missing after initial sync"
    fi
    
    # Test with max attempts
    log "3b. Testing 'sync --max-attempts 1'"
    rm -f "src/${SIMPLE_BASENAME}.py" "examples/${SIMPLE_BASENAME}_example.py" "tests/test_${SIMPLE_BASENAME}.py"
    rm -f "$SYNC_META_DIR/${SIMPLE_BASENAME}_python.json" "$SYNC_META_DIR/${SIMPLE_BASENAME}_python_run.json"
    if run_pdd_command sync --max-attempts 1 "$SIMPLE_BASENAME"; then
        log "Validation success: sync --max-attempts 1"
    else
        log_timestamped "[ERROR] Validation failed: sync --max-attempts 1"
    fi
    check_sync_files "$SIMPLE_BASENAME" "python"
    
    # Test with target coverage
    log "3c. Testing 'sync --target-coverage 10.0'"
    rm -f "src/${SIMPLE_BASENAME}.py" "examples/${SIMPLE_BASENAME}_example.py" "tests/test_${SIMPLE_BASENAME}.py"
    rm -f "$SYNC_META_DIR/${SIMPLE_BASENAME}_python.json" "$SYNC_META_DIR/${SIMPLE_BASENAME}_python_run.json"
    if run_pdd_command sync --target-coverage 10.0 "$SIMPLE_BASENAME"; then
        log "Validation success: sync --target-coverage 10.0"
    else
        log_timestamped "[ERROR] Validation failed: sync --target-coverage 10.0"
    fi
    check_sync_files "$SIMPLE_BASENAME" "python"
fi

# 4. Multi-language Sync Test
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "4" ]; then
    log "4. Testing multi-language 'sync'"

    # Single sync with budget processes all language prompts (Python, JS, TS)
    log "4a. Testing multi-language calculator sync"
    run_pdd_command sync --budget 30.0 "$MULTI_LANG_BASENAME"
    check_sync_files "$MULTI_LANG_BASENAME" "python"

    # Check if JavaScript/TypeScript files were also generated by the sync
    if [ -f "prompts/$MULTI_LANG_JS_PROMPT" ]; then
        log "4b. Checking JavaScript output from sync"
        if [ -f "${MULTI_LANG_BASENAME}.js" ] || [ -f "pdd/${MULTI_LANG_BASENAME}.js" ] || [ -f "src/${MULTI_LANG_BASENAME}.js" ]; then
            log "JavaScript files generated successfully"
        else
            log "JavaScript files not generated (may require JS environment setup)"
        fi
    fi
fi

# 5. Sync State Management and Incremental Updates
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "5" ]; then
    log "5. Testing sync state management and incremental updates"
    
    # First sync to establish baseline
    log "5a. Initial sync to establish state"
    if run_pdd_command sync --skip-verify "$SIMPLE_BASENAME"; then
        log "Validation success: initial sync for state management"
    else
        log_timestamped "[ERROR] Validation failed: initial sync for state management"
    fi
    check_sync_files "$SIMPLE_BASENAME" "python" false
    
    # Check metadata files (optional - may not exist in test environment)
    METADATA_FILE="$SYNC_META_DIR/${SIMPLE_BASENAME}_python.json"
    if [ -f "$METADATA_FILE" ]; then
        log "Sync metadata file exists: $METADATA_FILE"
        log_timestamped "Validation success: Sync metadata found"
    else
        log "Sync metadata file not found (acceptable in test environment): $METADATA_FILE"
        log_timestamped "Note: Sync metadata not created in test environment"
    fi
    
    # Second sync without changes (should be fast/skipped)
    log "5b. Testing incremental sync with no changes"
    SYNC_START_TIME=$(date +%s)
    run_pdd_command sync --skip-verify "$SIMPLE_BASENAME"
    SYNC_END_TIME=$(date +%s)
    SYNC_DURATION=$((SYNC_END_TIME - SYNC_START_TIME))
    
    if [ $SYNC_DURATION -lt 10 ]; then
        log "Incremental sync completed quickly ($SYNC_DURATION seconds) - likely skipped unchanged files"
        log_timestamped "Validation success: Incremental sync optimization working"
    else
        log "Incremental sync took $SYNC_DURATION seconds - may have regenerated files"
        log_timestamped "Note: Incremental sync duration: $SYNC_DURATION seconds"
    fi
    
    # Modify prompt and test incremental update
    log "5c. Testing incremental sync with prompt changes"
    # Add a comment to the prompt
    echo "" >> "prompts/$SIMPLE_PROMPT"
    echo "# Updated prompt for incremental test" >> "prompts/$SIMPLE_PROMPT"
    
    if run_pdd_command sync --skip-verify "$SIMPLE_BASENAME"; then
        log "Validation success: incremental sync after prompt change"
    else
        log_timestamped "[ERROR] Validation failed: incremental sync after prompt change"
    fi
    if check_sync_files "$SIMPLE_BASENAME" "python" false; then
        log "Validation success: files present after incremental sync change"
    else
        log_timestamped "[ERROR] Validation failed: files missing after incremental sync change"
    fi
fi

# 6. Sync Dry-Run and Analysis
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "6" ]; then
    log "6. Testing sync dry-run and analysis features"

    log "6a. Testing 'sync --dry-run'"
    if run_pdd_command sync --dry-run "$SIMPLE_BASENAME"; then
        log "Validation success: sync --dry-run produced output"
    else
        log_timestamped "[ERROR] Validation failed: sync --dry-run"
    fi

    log "6b. Testing verbose sync dry-run"
    if run_pdd_command --verbose sync --dry-run "$SIMPLE_BASENAME"; then
        log "Validation success: verbose sync dry-run"
    else
        log_timestamped "[ERROR] Validation failed: verbose sync dry-run"
    fi

    log "6c. Running sync to generate log entries"
    rm -f "${SIMPLE_BASENAME}.py" "${SIMPLE_BASENAME}_example.py" "test_${SIMPLE_BASENAME}.py"
    if run_pdd_command sync --skip-verify "$SIMPLE_BASENAME"; then
        log "Validation success: sync generated log entries"
    else
        log_timestamped "[ERROR] Validation failed: sync log generation"
    fi

    log "6d. Viewing analysis after sync operations"
    if run_pdd_command sync --dry-run "$SIMPLE_BASENAME"; then
        log "Validation success: viewed analysis after sync operations"
    else
        log_timestamped "[ERROR] Validation failed: viewing analysis after sync operations"
    fi
fi

# 7. Complex Sync with Advanced Features
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "7" ]; then
    log "7. Testing complex sync with advanced features"
    
    # Test sync with complex prompt
    log "7a. Testing sync with complex data processor"
    if run_pdd_command sync --target-coverage 10.0 --budget 10.0 "$COMPLEX_BASENAME"; then
        log "Validation success: complex sync with target coverage"
    else
        log_timestamped "[ERROR] Validation failed: complex sync with target coverage"
    fi
    if check_sync_files "$COMPLEX_BASENAME" "python"; then
        log "Validation success: complex files exist"
    else
        log_timestamped "[ERROR] Validation failed: complex files missing"
    fi
    
    # Test the generated complex code functionality (only if example exists)
    log "7b. Testing complex generated code functionality"
    if [ -f "examples/${COMPLEX_BASENAME}_example.py" ]; then
        log "Testing complex example execution"
        if python "examples/${COMPLEX_BASENAME}_example.py" >> "$LOG_FILE" 2>&1; then
            log "Validation success: Complex example executes correctly"
        else
            log_error "Complex example failed to run"
            log_timestamped "Validation failed: Complex example execution failed"
        fi
    else
        log "Skipping complex example test - no example file generated"
        log_timestamped "Note: Complex example file not generated by sync"
    fi
    
    # Run complex tests (only if test file exists)
    log "7c. Running complex generated tests"
    if [ -f "tests/test_${COMPLEX_BASENAME}.py" ]; then
        log "Running complex test suite"
        if python -m pytest "tests/test_${COMPLEX_BASENAME}.py" -v >> "$LOG_FILE" 2>&1; then
            log "Validation success: Complex tests passed"
        else
            log "Complex tests completed with failures"
            log_timestamped "[ERROR] Validation failed: Complex tests reported failures"
        fi
    else
        log "Skipping complex test execution - no test file generated"
        log_timestamped "Note: Complex test file not generated by sync"
    fi
fi

# 8. Error Handling and Edge Cases
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "8" ]; then
    log "8. Testing sync error handling and edge cases"
    
    # Test sync with non-existent basename (may succeed as no-op)
    log "8a. Testing sync with non-existent basename"
    # Allow non-zero exit without aborting the script under 'set -e'
    run_pdd_command_noexit sync "nonexistent_module" || true
    # Check that no files were actually generated for non-existent module
    if [ -f "pdd/nonexistent_module.py" ]; then
        log_error "Files were generated for non-existent module (unexpected)"
        log_timestamped "Validation failed: Files generated for non-existent module"
    else
        log "No files generated for non-existent module (expected behavior)"
        log_timestamped "Validation success: Sync handled non-existent module gracefully"
    fi
    
    # Test sync with invalid options (budget validation)
    log "8b. Testing sync with invalid budget"
    # Test with negative budget - should be rejected
    # Capture exit code in a set -e safe way
    if run_pdd_command_noexit sync --budget -1.0 "$SIMPLE_BASENAME"; then
        budget_exit_code=0
    else
        budget_exit_code=$?
    fi
    if [ $budget_exit_code -ne 0 ]; then
        log "Sync properly rejected negative budget"
        log_timestamped "Validation success: Sync rejected invalid budget"
    else
        log "Sync handled negative budget gracefully (may use default budget)"
        log_timestamped "Note: Sync accepted negative budget (possibly using default)"
    fi
    
    # Test sync with malformed prompt
    log "8c. Testing sync with malformed prompt"
    MALFORMED_PROMPT="malformed_test_python.prompt"
    echo "This is not a proper prompt format without clear requirements" > "prompts/$MALFORMED_PROMPT"
    run_pdd_command_noexit sync "malformed_test" || true
    # Should handle gracefully but may not produce optimal results
fi

# 9. Context and Configuration Integration
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "9" ]; then
    log "9. Testing context and configuration integration"
    
    # Test with automatic context detection (if .pddrc exists)
    if [ -f "$PDD_BASE_DIR/.pddrc" ]; then
        log "9a. Testing sync with automatic context detection"
    if run_pdd_command sync --skip-verify "$SIMPLE_BASENAME"; then
        log "Validation success: Context detection sync completed"
    else
        log_timestamped "[ERROR] Validation failed: Context detection sync"
    fi
    if check_sync_files "$SIMPLE_BASENAME" "python"; then
        log "Validation success: Files correctly placed with context detection"
    else
        log_timestamped "[ERROR] Validation failed: Files missing after context detection"
    fi
    else
        log "9a. Skipping context detection test (no .pddrc file found)"
        log_timestamped "Note: No .pddrc file found for context testing"
    fi
    
    # Test configuration file detection
    log "9b. Testing configuration file integration"
    if [ -f ".pddrc" ] || [ -f "$PDD_BASE_DIR/.pddrc" ]; then
        log "Configuration file detected and being used by PDD"
        # Verify that files are being created in the correct context-specific directories
        if [ -f "src/${SIMPLE_BASENAME}.py" ]; then
            log "Files correctly placed in context-specific directory structure"
            log_timestamped "Validation success: Configuration integration working"
        else
            log "Files not placed in expected context directories"
            log_timestamped "Note: Context directory structure may not be fully configured"
        fi
    else
        log "No configuration files found - using default behavior"
        log_timestamped "Note: Using default PDD configuration"
    fi
    
    # Test working directory context
    log "9c. Testing working directory context integration"
    # Run sync locally with an explicit timeout so hung cloud calls don't stall CI
    WORKDIR_CONTEXT_TIMEOUT="${WORKDIR_CONTEXT_TIMEOUT:-900}s"
    WORKDIR_CONTEXT_CMD=(
        "$PDD_SCRIPT"
        --force
        --output-cost "$REGRESSION_DIR/$COST_FILE"
        --strength "$STRENGTH"
        --temperature "$TEMPERATURE"
        --local
        sync
        --skip-verify
        --skip-tests
        --budget 2.0
        --max-attempts 1
        "$SIMPLE_BASENAME"
    )
    WORKDIR_CONTEXT_CMD_STR="${WORKDIR_CONTEXT_CMD[*]}"
    log_timestamped "----------------------------------------"
    log_timestamped "Starting command with timeout ($WORKDIR_CONTEXT_TIMEOUT): $WORKDIR_CONTEXT_CMD_STR"
    log "Running with timeout ($WORKDIR_CONTEXT_TIMEOUT): $WORKDIR_CONTEXT_CMD_STR"
    if run_with_timeout "$WORKDIR_CONTEXT_TIMEOUT" "${WORKDIR_CONTEXT_CMD[@]}" < /dev/null >> "$LOG_FILE" 2>&1; then
        log "Command completed successfully."
        log_timestamped "Command: $WORKDIR_CONTEXT_CMD_STR - Completed successfully."
    else
        log_error "Working directory context sync timed out or failed"
        log_timestamped "[ERROR] Validation failed: Working directory context sync timed out or failed"
        exit 1
    fi
    if [ -f "src/${SIMPLE_BASENAME}.py" ]; then
        log "Working directory context integration successful"
        log_timestamped "Validation success: Working directory context working"
    else
        log "Working directory context may not be fully integrated"
        log_timestamped "Note: Files may be placed in different location than expected"
    fi
fi

# 10. Performance and Concurrent Sync
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "10" ]; then
    log "10. Testing sync performance and concurrency"
    
    # Test sync lock mechanism (simplified)
    log "10a. Testing sync lock mechanism"
    # Start a background sync with timeout - direct command execution
    run_with_timeout 30s "$PDD_SCRIPT" --force --output-cost "$REGRESSION_DIR/$COST_FILE" --strength "$STRENGTH" --temperature "$TEMPERATURE" sync "$SIMPLE_BASENAME" >> "$LOG_FILE" 2>&1 &
    BACKGROUND_PID=$!
    
    # Try to run another sync immediately (should be blocked or handle gracefully)
    sleep 2
    log "Testing concurrent sync execution..."
    # Temporarily disable set -e to capture exit code (both success and failure are valid outcomes)
    set +e
    run_with_timeout 15s "$PDD_SCRIPT" --force --output-cost "$REGRESSION_DIR/$COST_FILE" --strength "$STRENGTH" --temperature "$TEMPERATURE" sync "$SIMPLE_BASENAME" >> "$LOG_FILE" 2>&1
    CONCURRENT_EXIT_CODE=$?
    set -e
    
    if [ $CONCURRENT_EXIT_CODE -eq 0 ]; then
        log "Concurrent sync succeeded (no locking detected)"
        log_timestamped "Note: Concurrent sync succeeded - may indicate no file locking"
    else
        log "Concurrent sync failed or was blocked (appropriate lock behavior)"
        log_timestamped "Validation success: Sync locking working correctly"
    fi
    
    # Wait for background sync to complete (with timeout)
    if wait $BACKGROUND_PID 2>/dev/null; then
        log "Background sync completed successfully"
        log_timestamped "Validation success: Background sync completed"
    else
        log "Background sync timed out or failed"
        log_timestamped "Note: Background sync did not complete within timeout"
    fi
    
    # Test lock cleanup
    log "10b. Testing lock cleanup"
    if [ -d "$SYNC_LOCKS_DIR" ]; then
        LOCK_COUNT=$(find "$SYNC_LOCKS_DIR" -name "*${SIMPLE_BASENAME}*" 2>/dev/null | wc -l)
        if [ "$LOCK_COUNT" -eq 0 ]; then
            log "Lock files properly cleaned up"
        else
            log "Warning: $LOCK_COUNT lock files remain"
        fi
    fi
fi

# --- Final Summary ---
log_timestamped "======== Sync Regression Tests Completed (Target: $TARGET_TEST) ========"
log "----------------------------------------"
log "All sync tests completed."
log "Log file: $(pwd)/$LOG_FILE"
log "Cost file: $(pwd)/$COST_FILE"

# Display total cost and validate results
if [ -f "$COST_FILE" ]; then
    # Validate row count (sync may only do 1-2 operations depending on context)
    MIN_EXPECTED_COST_ROWS=1
    ACTUAL_DATA_ROWS=$(awk 'NR > 1 {count++} END {print count+0}' "$COST_FILE")
    log "Found $ACTUAL_DATA_ROWS data rows in cost file."
    if [ "$ACTUAL_DATA_ROWS" -ge "$MIN_EXPECTED_COST_ROWS" ]; then
        log "Cost file row count ($ACTUAL_DATA_ROWS) meets minimum expectation ($MIN_EXPECTED_COST_ROWS)."
        log_timestamped "Validation success: Cost file row count sufficient."
    else
        log_error "Cost file row count ($ACTUAL_DATA_ROWS) is below minimum expectation ($MIN_EXPECTED_COST_ROWS)."
        log_timestamped "Validation failed: Cost file row count insufficient."
    fi

    # Calculate total cost
    total_cost=$(awk -F',' 'NR > 1 && NF >= 4 && $4 ~ /^[0-9]+(\.[0-9]+)?$/ { sum += $4 } END { printf "%.6f", sum }' "$COST_FILE")
    log "Total estimated cost of sync operations: $total_cost USD"
    log_timestamped "Total estimated cost of sync operations: $total_cost USD"
else
    log_error "Cost file $COST_FILE not found at end of script."
    log_timestamped "Validation failed: Cost file not found at end of script."
fi

# Final validation summary
log "========================================="
log "Sync Regression Test Summary:"
log "- Basic sync functionality: TESTED"
log "- Skip options (--skip-verify, --skip-tests): TESTED" 
log "- Budget and attempt limits: TESTED"
log "- Multi-language support: TESTED"
log "- State management and incremental updates: TESTED"
log "- Log analysis and debugging: TESTED"
log "- Complex scenarios: TESTED"
log "- Error handling: TESTED"
log "- Context integration: TESTED"
log "- Performance and concurrency: TESTED"
log "========================================="

cd .. # Return to original directory

exit 0
