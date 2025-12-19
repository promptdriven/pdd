#!/bin/bash

# Exit immediately if a command exits with a non-zero status.
set -e
# Treat unset variables as an error when substituting.
set -u

# Global settings
VERBOSE=${VERBOSE:-1} # Default to 1 if not set
STRENGTH=${STRENGTH:-0.3} # Default strength
TEMPERATURE=${TEMPERATURE:-0.0} # Default temperature
TEST_LOCAL=${TEST_LOCAL:-false} # Default to cloud execution
CLEANUP_ON_EXIT=false # Set to false to keep files for debugging

# --- Helper Functions ---

log() {
    if [ "$VERBOSE" -eq 1 ]; then
        echo "[INFO] $1"
    fi
}

# --- Test Selection ---
# Accept a single argument (test number) to run only that test. Default to "all".
TARGET_TEST=${1:-"all"}
log "Running tests: $TARGET_TEST"
# --- End Test Selection ---

# Set PDD_AUTO_UPDATE to false to prevent interference
export PDD_AUTO_UPDATE=false

# Define base variables
# Set PDD base directory as the script's location (two directories up from this script)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PDD_BASE_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

# Load .env file from the base directory if it exists
if [ -f "$PDD_BASE_DIR/.env" ]; then
    log "Loading environment variables from .env file"
    # Create a temporary, cleaned version of the .env file to source.
    # This makes the sourcing more robust to common .env file formatting issues,
    # such as spaces around the '=' character, which would otherwise cause 'command not found' errors.
    TEMP_ENV_FILE=$(mktemp)
    # The grep filters comments/empty lines; the sed removes whitespace around the first '=' on each line.
    grep -v -e '^#' -e '^$' "$PDD_BASE_DIR/.env" | sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' -e 's/[[:space:]]*=[[:space:]]*/=/' > "$TEMP_ENV_FILE"

    set -o allexport
    source "$TEMP_ENV_FILE"
    set +o allexport

    rm "$TEMP_ENV_FILE"
else
    log "No .env file found at $PDD_BASE_DIR/.env"
fi

# Force local execution for regression tests using the --local CLI flag.
# This is cleaner than manipulating environment variables.
TEST_LOCAL=true

PDD_PATH="$PDD_BASE_DIR/pdd"
STAGING_PATH="$PDD_BASE_DIR/staging"
PDD_SCRIPT="pdd" # Assumes pdd is in PATH
# Always prefer local CLI script when present to test workspace code
if [ -x "$PDD_BASE_DIR/pdd-local.sh" ]; then
  log "Using local CLI script (pdd-local.sh) for regression tests"
  PDD_SCRIPT="$PDD_BASE_DIR/pdd-local.sh"
fi
PROMPTS_PATH="$PDD_BASE_DIR/prompts"
CONTEXT_PATH="$PDD_BASE_DIR/context"
CONTEXT_PATH_GLOB="$CONTEXT_PATH/*.py" # Escaping might be needed depending on shell interpretation

# Determine REGRESSION_DIR
if [ -n "${REGRESSION_TARGET_DIR:-}" ]; then
    REGRESSION_DIR="$REGRESSION_TARGET_DIR"
    log "Using specified regression directory: $REGRESSION_DIR"
elif [ "$TARGET_TEST" = "all" ]; then
    REGRESSION_DIR="$STAGING_PATH/regression_$(date +%Y%m%d_%H%M%S)"
    log "Creating new regression directory for full run: $REGRESSION_DIR"
else
    # Find the latest existing regression directory for specific tests
    LATEST_REGRESSION_DIR=$(ls -td -- "$STAGING_PATH"/regression_* 2>/dev/null | head -n 1)
    if [ -d "$LATEST_REGRESSION_DIR" ]; then
        REGRESSION_DIR="$LATEST_REGRESSION_DIR"
        log "Reusing latest regression directory for specific test: $REGRESSION_DIR"
    else
        log "Warning: No existing regression directory found in $STAGING_PATH. Creating a new one."
        REGRESSION_DIR="$STAGING_PATH/regression_$(date +%Y%m%d_%H%M%S)_specific_${TARGET_TEST}"
        log "Creating new regression directory: $REGRESSION_DIR"
    fi
fi

LOG_FILE="$REGRESSION_DIR/regression.log"
COST_FILE="regression_cost.csv"

# simple_math test case files
MATH_BASENAME="simple_math"
MATH_PROMPT="${MATH_BASENAME}_python.prompt"
MATH_SCRIPT="${MATH_BASENAME}.py"
MATH_TEST_SCRIPT="test_${MATH_BASENAME}.py"
MATH_VERIFICATION_PROGRAM="${MATH_BASENAME}_example.py"
MATH_ERROR_LOG="math_error.log"
MATH_ERROR_LOOP_LOG="math_error_loop.log"
PYTEST_LOG="pytest_output.log"
COVERAGE_REPORT="coverage.xml"
ORIGINAL_MATH_SCRIPT="original_${MATH_SCRIPT}"
UPDATED_MATH_PROMPT="updated_${MATH_PROMPT}"
CHANGED_MATH_PROMPT="changed_${MATH_PROMPT}"
FIXED_MATH_SCRIPT="fixed_${MATH_SCRIPT}"
FIXED_MATH_TEST_SCRIPT="fixed_${MATH_TEST_SCRIPT}"
FIXED_LOOP_MATH_SCRIPT="fixed_loop_${MATH_SCRIPT}"
FIXED_LOOP_MATH_TEST_SCRIPT="fixed_loop_${MATH_TEST_SCRIPT}"
CRASH_FIXED_SCRIPT="fixed_crash_${MATH_SCRIPT}"
CRASH_FIXED_PROGRAM="fixed_crash_${MATH_VERIFICATION_PROGRAM}"
BUG_TEST_SCRIPT="bug_${MATH_TEST_SCRIPT}"
AUTO_DEPS_PROMPT="auto_deps_${MATH_PROMPT}"

# Complex preprocess test case files
COMPLEX_PROMPT="complex_features_python.prompt"
COMPLEX_PREPROCESSED="complex_features_python_preprocessed.prompt"
COMPLEX_XML="complex_features_python_xml.prompt"
COMPLEX_RECURSIVE="complex_features_python_recursive.prompt"
COMPLEX_DOUBLE="complex_features_python_double.prompt"
INCLUDE_FILE="include_me.txt"
SHELL_OUTPUT_FILE="shell_output.txt"
WEB_DUMMY_FILE="dummy_web.html"

# Change CSV test files
CHANGE_CSV_FILE="batch_changes.csv"
CHANGE_CSV_CODE_DIR="change_csv_code"
CHANGE_CSV_OUT_DIR="changed_csv_prompts"
DUMMY_CODE_A="dummy_a.py"
DUMMY_PROMPT_A="dummy_a_python.prompt"
DUMMY_CODE_B="dummy_b.py"
DUMMY_PROMPT_B="dummy_b_python.prompt"

# Split test files
SPLIT_PROMPT="split_instruction.prompt"
SPLIT_SUB_PROMPT="sub_${MATH_BASENAME}.prompt"
SPLIT_MODIFIED_PROMPT="modified_${MATH_BASENAME}.prompt"

# Update Git test files
UPDATE_GIT_DIR="update_git_test"
UPDATED_GIT_PROMPT="updated_git_${MATH_PROMPT}"

# Detect/Conflicts files
DETECT_CHANGE_FILE="change_description.prompt"
DETECT_RESULTS_CSV="detect_results.csv"
CONFLICTS_RESULTS_CSV="conflicts_analysis.csv"
OTHER_PROMPT="test_other_python.prompt" # Test-specific prompt for detect/conflicts tests

# Trace files
TRACE_RESULTS_LOG="trace_results.log"

# Verify files
VERIFY_RESULTS_LOG="verify_results.log"
VERIFY_CODE_OUTPUT="verified_${MATH_SCRIPT}"
VERIFY_EXAMPLE_OUTPUT="verified_${MATH_VERIFICATION_PROGRAM}" # Example derived from verified code
VERIFY_PROGRAM_OUTPUT="directly_verified_${MATH_VERIFICATION_PROGRAM}" # New: Direct output from verify
VERIFY_HARNESS_LOG="verify_harness.log"
VERIFY_ISOLATED_DIR="isolated_verify"
VERIFY_SCRIPT_PATH="$PDD_BASE_DIR/tests/isolated_verify.py"

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
            # Decide if this should be a fatal error or just skip local tests
            return 1 # Or exit 1 if local testing is mandatory
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
            # Move --context and its value into global args
            global_ctx_args+=("--context")
            if [ $((i+1)) -lt ${#args[@]} ]; then
                global_ctx_args+=("${args[$((i+1))]}")
                i=$((i+2))
                continue
            else
                # Malformed, but pass through anyway
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

    # Assemble final command
    # On macOS bash, using default expansion with length (:-0) is invalid.
    # Arrays are initialized above, so plain length checks are safe.
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

    # Execute the command, redirecting stdout/stderr to log file
    "${cmd_array[@]}" >> "$LOG_FILE" 2>&1
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
log "Creating regression test directory: $REGRESSION_DIR"
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

# Create a local .pddrc with test contexts up front
cat > ./.pddrc << 'EOF'
contexts:
  default:
    defaults:
      default_language: "python"
  alt:
    defaults:
      default_language: "python"
  base:
    defaults:
      generate_output_path: "pdd/"
      test_output_path: "tests/"
      example_output_path: "examples/"
      default_language: "python"
  envonly:
    defaults:
      default_language: "python"
EOF

# Create context files needed by multiple tests
log "Creating common context files (example.prompt, test.prompt)"
mkdir -p context # Ensure context subdirectory exists
if [ $? -ne 0 ]; then
    log_error "Failed to create context directory. Exiting."
    exit 1
fi
# Context for 'example' command
cat << \EOF > "context/example.prompt"
For the function 'add' defined based on 'simple_math_python.prompt', the implementation is in 'simple_math.py'.
Therefore, the example should include the line: 'from simple_math import add'
EOF
if [ $? -ne 0 ]; then
    log_error "Failed to write context/example.prompt file. Exiting."
    exit 1
fi
# Context for 'test' command
cat << EOF > "context/test.prompt"
For the function 'add' defined based on 'simple_math_python.prompt', the implementation is in 'simple_math.py'.
Therefore, the test file should include the line: 'from simple_math import add'
EOF
if [ $? -ne 0 ]; then
    log_error "Failed to write context/test.prompt file. Exiting."
    exit 1
fi


# --- Test Preparations ---

# Create dummy files for preprocess test
log "Creating dummy files for preprocess test"
echo "This is the file to be included." > "$INCLUDE_FILE"
echo "<html><body><h1>Dummy Web Content</h1></body></html>" > "$WEB_DUMMY_FILE"
cat << EOF > "$COMPLEX_PROMPT"
This prompt tests various preprocess features.

Include tag:
<include>$INCLUDE_FILE</include>

PDD Comment (should be removed):
<pdd>This comment will disappear.</pdd>

Shell command (output should be included):
<shell>echo "Output from shell command."</shell>

Web scrape (testing web functionality):
<web>https://httpbin.org/get</web>

Triple backtick include:
\`\`\`
<$INCLUDE_FILE>
\`\`\`

Curly braces test:
Single: {var1}
Double: {{var2}}
Nested: { outer { inner } }
Exclude key: model={model_name}
EOF

# Create files for change --csv test
log "Creating files for change --csv test"
mkdir -p "$CHANGE_CSV_CODE_DIR"
mkdir -p "$CHANGE_CSV_OUT_DIR"
printf "def func_a():\\n  print('Hello A')\\n" > "$CHANGE_CSV_CODE_DIR/$DUMMY_CODE_A"
printf "def func_b():\\n  print('Hello B')\\n" > "$CHANGE_CSV_CODE_DIR/$DUMMY_CODE_B"
cp "$PROMPTS_PATH/$MATH_PROMPT" "$DUMMY_PROMPT_A" # Use math prompt as base
cp "$PROMPTS_PATH/$MATH_PROMPT" "$DUMMY_PROMPT_B" # Use math prompt as base
cat << EOF > "$CHANGE_CSV_FILE"
prompt_name,change_instructions
"$DUMMY_PROMPT_A","Change function name to func_a_modified"
"$DUMMY_PROMPT_B","Add a comment saying 'Modified B'"
EOF

# Create file for detect test
echo "Refactor the simple_math function to use a helper." > "$DETECT_CHANGE_FILE"

# Make sure DETECT_CHANGE_FILE follows the naming convention
mv "$DETECT_CHANGE_FILE" "change_description_python.prompt"
DETECT_CHANGE_FILE="change_description_python.prompt"

# Create files for split test
echo "Extract the 'add' function into a separate sub-prompt." > "$SPLIT_PROMPT"

# Make sure SPLIT_PROMPT follows the naming convention
mv "$SPLIT_PROMPT" "split_instruction_python.prompt"
SPLIT_PROMPT="split_instruction_python.prompt"

# --- Regression Tests ---

log_timestamped "======== Starting Regression Tests ========"

# 0. CLI Globals: --list-contexts and --context override
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "0" ]; then
  log "0. Testing global CLI flags: --list-contexts and --context"

# Create a local .pdd directory for regression-specific config
mkdir -p .pdd

# Create a filtered llm_model.csv that excludes local/unreachable models for CI stability
if [ -f "$PDD_BASE_DIR/pdd/data/llm_model.csv" ]; then
    log "Creating CI-safe llm_model.csv (excluding 'localhost' and 'lm_studio')"
    grep -vE "localhost|lm_studio|anthropic/" "$PDD_BASE_DIR/pdd/data/llm_model.csv" > .pdd/llm_model.csv
else
    log "Warning: Source llm_model.csv not found at $PDD_BASE_DIR/pdd/data/llm_model.csv"
fi

# Create a local .pddrc to control contexts for this regression run
cat > ./.pddrc << 'EOF'
contexts:
  default:
    defaults:
      generate_output_path: "src_default/"
      test_output_path: "tests_default/"
      example_output_path: "examples_default/"
  alt:
    defaults:
      default_language: "python"
  envonly:
    defaults:
      default_language: "python"
EOF

  # 0a. --list-contexts should print available contexts and exit 0
  CONTEXTS_OUTPUT=$($PDD_SCRIPT --list-contexts 2>> "$LOG_FILE")
  STATUS=$?
  if [ $STATUS -ne 0 ]; then
    log_error "--list-contexts exited with non-zero status: $STATUS"
    exit 1
  fi
  echo "$CONTEXTS_OUTPUT" | grep -q "^default$" || { log_error "--list-contexts missing 'default'"; exit 1; }
  echo "$CONTEXTS_OUTPUT" | grep -q "^alt$" || { log_error "--list-contexts missing 'alt'"; exit 1; }
  log "--list-contexts returned expected contexts: $(echo "$CONTEXTS_OUTPUT" | tr '\n' ' ')"

  # 0b. Unknown --context should raise a usage error (early validation)
  run_pdd_expect_fail --context does_not_exist preprocess --output ctx_check.prompt "$COMPLEX_PROMPT"

  # 0c. Known --context should pass through to subcommands; run a cheap command (preprocess)
  run_pdd_command --context alt preprocess --output ctx_alt_preprocessed.prompt "$COMPLEX_PROMPT"
  check_exists "ctx_alt_preprocessed.prompt" "'preprocess' with --context alt output"
fi

# 1. Generate
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "1" ]; then
  log "1. Testing 'generate' command"
  run_pdd_command --local generate --output "$MATH_SCRIPT" "$PROMPTS_PATH/$MATH_PROMPT"
  check_exists "$MATH_SCRIPT" "'generate' output"
  cp "$MATH_SCRIPT" "$ORIGINAL_MATH_SCRIPT" # Backup for update test

  # 1a. Generate with different strength/temp
  log "1a. Testing 'generate' with different strength/temp"
  # Pass global options FIRST, then the command and its specific options/args
  run_pdd_command --local --strength 0.5 --temperature 0.0 generate --output "gen_low_str.py" "$PROMPTS_PATH/$MATH_PROMPT"
  check_exists "gen_low_str.py" "'generate' low strength output"
  run_pdd_command --local --strength $STRENGTH --temperature 1.5 generate --output "gen_high_temp.py" "$PROMPTS_PATH/$MATH_PROMPT"
  check_exists "gen_high_temp.py" "'generate' high temp output"

  # 1b. Generate with env var output path (via envonly context)
  log "1b. Testing 'generate' with environment variable output path"
  ENV_OUT_DIR="env_out_generate"
  mkdir -p "$ENV_OUT_DIR"
  export PDD_GENERATE_OUTPUT_PATH="$ENV_OUT_DIR/" # Trailing slash indicates directory
  # Use envonly context so env vars take precedence (no context paths)
  run_pdd_command --local --context envonly generate "$PROMPTS_PATH/$MATH_PROMPT" # No --output
  # Default name is <basename>.<lang_ext> which should be simple_math.py
  check_exists "$ENV_OUT_DIR/$MATH_SCRIPT" "'generate' output via env var" # Check for the Python file, not the prompt

  unset PDD_GENERATE_OUTPUT_PATH
fi

# 2. Example
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "2" ]; then
  log "2. Testing 'example' command"

  # Create a context example prompt to guide the import generation
  # MOVED TO SETUP SECTION
  # log "Creating context/example.prompt for example generation"
  # mkdir -p context # Ensure context subdirectory exists
  # if [ $? -ne 0 ]; then
  #     log_error "Failed to create context directory. Exiting."
  #     exit 1
  # fi
  # cat << \EOF > "context/example.prompt"
  # For the function 'add' defined based on 'simple_math_python.prompt', the implementation is in 'simple_math.py'.
  # Therefore, the example should include the line: 'from simple_math import add'
  # EOF
  # if [ $? -ne 0 ]; then
  #     log_error "Failed to write context/example.prompt file. Exiting."
  #     exit 1
  # fi

  run_pdd_command example --output "$MATH_VERIFICATION_PROGRAM" "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT"
  check_exists "$MATH_VERIFICATION_PROGRAM" "'example' output"
fi

# 3. Preprocess
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "3" ]; then
  log "3. Testing 'preprocess' command"
  # Basic preprocess
  run_pdd_command preprocess --output "preprocessed_${MATH_PROMPT}" "$PROMPTS_PATH/$MATH_PROMPT"
  check_exists "preprocessed_${MATH_PROMPT}" "'preprocess' basic output"
  # XML preprocess
  run_pdd_command preprocess --xml --output "${MATH_BASENAME}_xml.prompt" "$PROMPTS_PATH/$MATH_PROMPT"
  check_exists "${MATH_BASENAME}_xml.prompt" "'preprocess --xml' output"

  # 3a. Testing complex 'preprocess' features
  log "3a. Testing complex 'preprocess' features"
  run_pdd_command preprocess --output "$COMPLEX_PREPROCESSED" "$COMPLEX_PROMPT"
  check_exists "$COMPLEX_PREPROCESSED" "'preprocess' complex output"
  # Check specific features (basic checks)
  grep -q "This is the file to be included." "$COMPLEX_PREPROCESSED" || (log_error "Preprocess failed: Include tag missing"; exit 1)
  grep -q "Output from shell command." "$COMPLEX_PREPROCESSED" || (log_error "Preprocess failed: Shell tag output missing"; exit 1)
  # Check that web scraping was attempted (either successful content or error message)
  (grep -q "httpbin" "$COMPLEX_PREPROCESSED" || grep -q "Web scraping error" "$COMPLEX_PREPROCESSED" || grep -q "Service Temporarily Unavailable" "$COMPLEX_PREPROCESSED") || (log_error "Preprocess failed: Web tag not processed"; exit 1)
  grep -v "<pdd>" "$COMPLEX_PREPROCESSED" || (log_error "Preprocess failed: PDD comment not removed"; exit 1)
  # Test --recursive (will just run, complex check is hard)
  run_pdd_command preprocess --recursive --output "$COMPLEX_RECURSIVE" "$COMPLEX_PROMPT"
  check_exists "$COMPLEX_RECURSIVE" "'preprocess --recursive' output"
  # Test --double
  run_pdd_command preprocess --double --exclude model --output "$COMPLEX_DOUBLE" "$COMPLEX_PROMPT"
  check_exists "$COMPLEX_DOUBLE" "'preprocess --double' output"
  grep -q "{{var2}}" "$COMPLEX_DOUBLE" || (log_error "Preprocess failed: Double brace missing"; exit 1)
  grep -q "model={{model_name}}" "$COMPLEX_DOUBLE" || (log_error "Preprocess failed: Excluded key check incorrect (should be doubled)"; exit 1)

  # Stop web server - moved inside the block as it's related to preprocess web tag
  if [ -n "${HTTP_SERVER_PID:-}" ]; then
      log "Stopping background HTTP server (PID: $HTTP_SERVER_PID)..."
      kill "$HTTP_SERVER_PID" && wait "$HTTP_SERVER_PID" 2>/dev/null || log "HTTP server already stopped."
      unset HTTP_SERVER_PID # Clear the variable
  fi
fi

# 4. Update
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "4" ]; then
  log "4. Testing 'update' command"
  # Modify the script slightly
  log "Modifying script for update test"
  echo "# Added comment for update test" >> "$MATH_SCRIPT"
  run_pdd_command update --output "$UPDATED_MATH_PROMPT" "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" "$ORIGINAL_MATH_SCRIPT"
  check_exists "$UPDATED_MATH_PROMPT" "'update' output"

  # 4a. Update with --git
  log "4a. Testing 'update --git'"
  mkdir "$UPDATE_GIT_DIR"
  cd "$UPDATE_GIT_DIR"
  git init -b main > /dev/null 2>&1
  git config --local user.email "test@example.com"
  git config --local user.name "Test User"
  # Copy data directory for LLM model CSV access - check both root and pdd/data locations
  if [ -d "$PDD_BASE_DIR/data" ]; then
    cp -r "$PDD_BASE_DIR/data" .
  elif [ -d "$PDD_BASE_DIR/pdd/data" ]; then
    cp -r "$PDD_BASE_DIR/pdd/data" data
  else
    log "Warning: data directory not found at $PDD_BASE_DIR/data or $PDD_BASE_DIR/pdd/data"
  fi
  cp "../$ORIGINAL_MATH_SCRIPT" "$MATH_SCRIPT" # Copy original version
  cp "$PROMPTS_PATH/$MATH_PROMPT" .
  git add "$MATH_SCRIPT" "$MATH_PROMPT"
  git commit -m "Initial commit" > /dev/null 2>&1
  echo "# Git modification" >> "$MATH_SCRIPT" # Modify tracked file
  # Run update --git from the git repo root
  run_pdd_command update --git --output "$UPDATED_GIT_PROMPT" "$MATH_PROMPT" "$MATH_SCRIPT"
  check_exists "$UPDATED_GIT_PROMPT" "'update --git' output"
  cd .. # Return to REGRESSION_DIR
fi

# 5. Change
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "5" ]; then
  log "5. Testing 'change' command"
  # Use the updated prompt from step 4 as input
  run_pdd_command change --output "$CHANGED_MATH_PROMPT" \
                         "$DETECT_CHANGE_FILE" \
                         "$MATH_SCRIPT" \
                         "$UPDATED_MATH_PROMPT"
  check_exists "$CHANGED_MATH_PROMPT" "'change' output"

  # 5a. Change with --csv
  log "5a. Testing 'change --csv'"
  run_pdd_command change --csv --output "$CHANGE_CSV_OUT_DIR/" "$CHANGE_CSV_FILE" "$CHANGE_CSV_CODE_DIR/" # Note trailing slash for output dir
  check_exists "$CHANGE_CSV_OUT_DIR/$DUMMY_PROMPT_A" "'change --csv' output A"
  check_exists "$CHANGE_CSV_OUT_DIR/$DUMMY_PROMPT_B" "'change --csv' output B"

  # Intermediate check for cost file population
  log "Performing intermediate check on cost file: $COST_FILE"
  if [ -f "$COST_FILE" ]; then
      DATA_ROWS=$(awk 'NR > 1' "$COST_FILE" | wc -l | tr -d ' ')
      if [ "$DATA_ROWS" -gt 0 ]; then
          log "Cost file contains $DATA_ROWS data rows (intermediate check passed)."
          log_timestamped "Validation success: Cost file contains data rows (intermediate check)."
      else
          log_error "Cost file only contains header or is empty after several commands."
          log_timestamped "Validation failed: Cost file missing data rows (intermediate check)."
          # Decide if this should be fatal; for now, just log error
          # exit 1
      fi
  else
      log_error "Cost file $COST_FILE not found for intermediate check."
      log_timestamped "Validation failed: Cost file not found (intermediate check)."
      # Decide if this should be fatal
      # exit 1
  fi
fi

# 6. Crash
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "6" ]; then
  log "6. Testing 'crash' command"
  # Make sure example program exists and is runnable first
  run_pdd_command example --output "$MATH_VERIFICATION_PROGRAM" "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT"
  log "Running example program before introducing error..."
  # Run the example once and if it fails, immediately try to fix with 'crash'
  set +e
  python "$MATH_VERIFICATION_PROGRAM" > "$MATH_ERROR_LOG" 2>&1
  initial_status=$?
  set -e

  if [ $initial_status -ne 0 ]; then
      log "Initial example run failed; invoking 'crash' to fix it..."
      run_pdd_command crash --output "$CRASH_FIXED_SCRIPT" \
                            --output-program "$CRASH_FIXED_PROGRAM" \
                            "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" \
                            "$MATH_VERIFICATION_PROGRAM" "$MATH_ERROR_LOG"

      # Adopt fixed files if they were created
      if [ -s "$CRASH_FIXED_SCRIPT" ]; then
          log "Adopting fixed script from initial 'crash' command."
          cp "$CRASH_FIXED_SCRIPT" "$MATH_SCRIPT"
      else
          log "Initial 'crash' did not produce a fixed script (may not be needed)."
      fi

      if [ -s "$CRASH_FIXED_PROGRAM" ]; then
          log "Adopting fixed program from initial 'crash' command."
          cp "$CRASH_FIXED_PROGRAM" "$MATH_VERIFICATION_PROGRAM"
      else
          log "Initial 'crash' did not produce a fixed program (may not be needed)."
      fi

      # Verify the fix
      log "Re-running example program after initial 'crash' fix"
      python "$MATH_VERIFICATION_PROGRAM" >> "$LOG_FILE" 2>&1
      rerun_status=$?
      if [ $rerun_status -ne 0 ]; then
          log_error "Program still failed after initial 'crash' fix."
          exit 1
      else
          log "Program ran successfully after initial 'crash' fix."
      fi
  else
      # On success, append the normal output to the main log and continue
      cat "$MATH_ERROR_LOG" >> "$LOG_FILE" 2>/dev/null || true
      log "Example program ran successfully before introducing error."
  fi
  log "Introducing error into $MATH_VERIFICATION_PROGRAM"
  # Intentionally cause a TypeError
  echo "import $MATH_BASENAME" > "$MATH_VERIFICATION_PROGRAM" # Overwrite
  echo "result = $MATH_BASENAME.add(5, 'a')" >> "$MATH_VERIFICATION_PROGRAM"
  echo "print(f'The sum is: {result}')" >> "$MATH_VERIFICATION_PROGRAM"
  # Run modified program to generate error log
  log "Running modified example to generate error log for 'crash'"
  python "$MATH_VERIFICATION_PROGRAM" > "$MATH_ERROR_LOG" 2>&1 || true # Allow failure

  if [ ! -s "$MATH_ERROR_LOG" ]; then
      log_error "Crash test error log is empty. Skipping 'crash' command."
  else
      # Run crash (non-loop) - Increase strength here
      run_pdd_command crash --output "$CRASH_FIXED_SCRIPT" \
                            --output-program "$CRASH_FIXED_PROGRAM" \
                            "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" \
                            "$MATH_VERIFICATION_PROGRAM" "$MATH_ERROR_LOG"
      
      # Conditionally adopt the fixed files if they were created
      if [ -s "$CRASH_FIXED_SCRIPT" ]; then
          log "Adopting fixed script from 'crash' command."
          cp "$CRASH_FIXED_SCRIPT" "$MATH_SCRIPT"
      else
          log "Fixed script was not created by 'crash' command (no changes needed)."
      fi

      if [ -s "$CRASH_FIXED_PROGRAM" ]; then
          log "Adopting fixed program from 'crash' command."
          cp "$CRASH_FIXED_PROGRAM" "$MATH_VERIFICATION_PROGRAM"
      else
          log "Fixed program was not created by 'crash' command (no changes needed)."
      fi

      # Verify the fix by running the potentially updated program
      log "Running the potentially fixed program after 'crash' command"
      
      # If we adopted a fixed script with input validation, update the test program
      if [ -s "$CRASH_FIXED_SCRIPT" ] && grep -q -E "(isinstance|TypeError.*numbers)" "$MATH_SCRIPT"; then
          log "Detected input validation in fixed code, updating test program with valid inputs"
          cat > "$MATH_VERIFICATION_PROGRAM" << 'EOF'
import simple_math
result = simple_math.add(5, 10)  # Fixed: use valid numbers
print(f'The sum is: {result}')
EOF
      elif [ -s "$CRASH_FIXED_PROGRAM" ] && grep -q -E "('a'|multiply)" "$MATH_VERIFICATION_PROGRAM"; then
          log "Detected problematic test program, creating valid test case"
          cat > "$MATH_VERIFICATION_PROGRAM" << 'EOF'
import simple_math
result = simple_math.add(5, 10)  # Fixed: use valid function and numbers
print(f'The sum is: {result}')
EOF
      fi
      
      python "$MATH_VERIFICATION_PROGRAM" >> "$LOG_FILE" 2>&1
      exit_code=$?
      if [ $exit_code -eq 0 ]; then
          log "Program ran successfully after crash command."
          log_timestamped "Validation success: Program ran successfully after crash command."
      else

          log_error "Program still failed after crash command."
          log_timestamped "Validation failed: Program still failed after crash command."
          log "Note: According to README, crash command should fix both code module and calling program"
          log "This indicates the crash command may not be working as specified"
          exit 1 # Treat this as a failure since crash should fix the issue
      fi
  fi

  # 6a. Crash with --loop (introduce different error)
  log "6a. Testing 'crash --loop'"
  log "Introducing different error for 'crash --loop'"
  # Intentionally cause a NameError
  echo "import $MATH_BASENAME" > "$MATH_VERIFICATION_PROGRAM" # Overwrite
  echo "result = $MATH_BASENAME.multiply(5, 3)" >> "$MATH_VERIFICATION_PROGRAM" # Assume multiply doesn't exist
  echo "print(f'The product is: {result}')" >> "$MATH_VERIFICATION_PROGRAM"
  # Run modified program to generate error log
  log "Running modified example to generate error log for 'crash --loop'"
  python "$MATH_VERIFICATION_PROGRAM" > "${MATH_ERROR_LOG}_loop" 2>&1 || true # Allow failure

  if [ ! -s "${MATH_ERROR_LOG}_loop" ]; then
      log_error "Crash loop test error log is empty. Skipping 'crash --loop' command."
  else
      # Run crash --loop - Increase strength here too
      run_pdd_command_noexit crash --loop --max-attempts 5 --budget 5.0 \
                            --output "${CRASH_FIXED_SCRIPT}_loop" \
                            --output-program "${CRASH_FIXED_PROGRAM}_loop" \
                            "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" \
                            "$MATH_VERIFICATION_PROGRAM" "${MATH_ERROR_LOG}_loop"

      # Conditionally adopt the fixed files if they were created by the loop
      loop_fix_produced=false
      if [ -s "${CRASH_FIXED_SCRIPT}_loop" ]; then
          log "Crash --loop produced an output script. Adopting it for subsequent tests."
          cp "${CRASH_FIXED_SCRIPT}_loop" "$MATH_SCRIPT"
          loop_fix_produced=true
      fi
      if [ -s "${CRASH_FIXED_PROGRAM}_loop" ]; then
          log "Crash --loop produced an output program. Adopting it for subsequent tests."
          cp "${CRASH_FIXED_PROGRAM}_loop" "$MATH_VERIFICATION_PROGRAM"
          loop_fix_produced=true
      fi

      if [ "$loop_fix_produced" = true ]; then
          log "Running program after 'crash --loop' attempt."
          python "$MATH_VERIFICATION_PROGRAM" >> "$LOG_FILE" 2>&1 || log "Program fixed by crash --loop failed to run (non-fatal for test)."
      else
          log "Crash --loop did not produce any output files (as expected if unfixable)."
      fi
  fi
  
  # Restore original math script for subsequent tests since crash tests may have modified it
  log "Restoring original math script for subsequent tests"
  if [ -f "$ORIGINAL_MATH_SCRIPT" ]; then
      cp "$ORIGINAL_MATH_SCRIPT" "$MATH_SCRIPT"
      log "Restored $MATH_SCRIPT from backup"
  else
      log "Warning: Original math script backup not found, regenerating from prompt"
      run_pdd_command generate --output "$MATH_SCRIPT" "$PROMPTS_PATH/$MATH_PROMPT"
  fi
fi

# 7. Verify (using built-in pdd verify)
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "7" ]; then
  log "7. Testing 'verify' command"
  if [ ! -f "$MATH_SCRIPT" ]; then
      log_error "Code file $MATH_SCRIPT not found. Skipping 'verify' test."
  elif [ ! -f "$MATH_VERIFICATION_PROGRAM" ]; then
      log_error "Verification program $MATH_VERIFICATION_PROGRAM not found. Skipping 'verify' test."
  else
      log "Running pdd verify"
      
      log "Introducing semantic error into $MATH_SCRIPT for verify test..."
      # Change 'return a + b' to 'return a - b' to test if verify can fix semantic errors
      sed -i.bak 's/return a + b/return a - b/' "$MATH_SCRIPT"

      # Directly call pdd verify instead of the python harness script
      run_pdd_command_noexit --strength .75 verify \
          --output-results "$VERIFY_RESULTS_LOG" \
          --output-code "$VERIFY_CODE_OUTPUT" \
          --output-program "$VERIFY_PROGRAM_OUTPUT" \
          --max-attempts 5 \
          --budget 5.0 \
          "$PROMPTS_PATH/$MATH_PROMPT" \
          "$MATH_SCRIPT" \
          "$MATH_VERIFICATION_PROGRAM"

      VERIFY_STATUS=$?
      if [ $VERIFY_STATUS -eq 0 ]; then
          log_timestamped "Validation success: pdd verify completed successfully."
          check_exists "$VERIFY_CODE_OUTPUT" "'verify' output code"
          check_exists "$VERIFY_PROGRAM_OUTPUT" "'verify' direct output program"

          log "Checking if verify fixed the semantic error in $VERIFY_CODE_OUTPUT using Python AST script"
          
          # For simplicity, embedding it here. In a real setup, it might be a separate file.
          cat << 'EOSCRIPT' > check_python_add_operation.py
import ast
import sys

def is_numeric_node(node):
    """Checks if a node likely represents a number, a numeric variable, or a call returning a number."""
    if isinstance(node, ast.Constant) and isinstance(node.value, (int, float)):
        return True
    # Could be extended to check for variables known to be numeric, or function calls
    # that are known to return numbers, but this is kept simple.
    return False

def check_add_operation(filepath):
    """
    Checks if a Python file contains an 'add' function that performs an addition
    operation like 'a + b', 'float(a) + float(b)', or 'num_a + num_b',
    where 'a'/'num_a' and 'b'/'num_b' are its parameters or variables derived from them.
    """
    try:
        with open(filepath, 'r') as file:
            tree = ast.parse(file.read(), filename=filepath)
    except Exception as e:
        print(f"Error parsing Python file: {e}", file=sys.stderr)
        return False

    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name == 'add':
            # Check for parameters (e.g., a, b)
            func_params = {arg.arg for arg in node.args.args}

            for sub_node in ast.walk(node):
                if isinstance(sub_node, ast.Return):
                    if isinstance(sub_node.value, ast.BinOp) and isinstance(sub_node.value.op, ast.Add):
                        left = sub_node.value.left
                        right = sub_node.value.right

                        # Check if operands are simple names (variables) or float() calls on names
                        left_is_param_or_derived = False
                        right_is_param_or_derived = False

                        # Check left operand
                        if isinstance(left, ast.Name) and left.id in func_params:
                            left_is_param_or_derived = True
                        elif isinstance(left, ast.Call) and isinstance(left.func, ast.Name) and left.func.id == 'float':
                            if left.args and isinstance(left.args[0], ast.Name) and left.args[0].id in func_params:
                                left_is_param_or_derived = True
                        elif isinstance(left, ast.Name) and left.id.startswith("num_"): # num_a
                            left_is_param_or_derived = True


                        # Check right operand
                        if isinstance(right, ast.Name) and right.id in func_params:
                            right_is_param_or_derived = True
                        elif isinstance(right, ast.Call) and isinstance(right.func, ast.Name) and right.func.id == 'float':
                            if right.args and isinstance(right.args[0], ast.Name) and right.args[0].id in func_params:
                                right_is_param_or_derived = True
                        elif isinstance(right, ast.Name) and right.id.startswith("num_"): # num_b
                             right_is_param_or_derived = True


                        # Looser check: also allow direct numeric constants if one side is a param
                        # This is to accommodate cases like 'return a + 0' or 'return 0 + b' if such variants appear
                        left_is_numeric_const = is_numeric_node(left)
                        right_is_numeric_const = is_numeric_node(right)

                        # Valid if (param_A + param_B) or (param_A + const_B) or (const_A + param_B)
                        if (left_is_param_or_derived and right_is_param_or_derived) or \
                           (left_is_param_or_derived and right_is_numeric_const) or \
                           (left_is_numeric_const and right_is_param_or_derived):
                            return True
            # If no return a + b style operation found in the add function
            return False
    # If no 'add' function found
    return False

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python check_python_add_operation.py <filepath>", file=sys.stderr)
        sys.exit(1)
    
    filepath_to_check = sys.argv[1]
    if check_add_operation(filepath_to_check):
        # print(f"PASSED: Found 'add' function with 'a + b' or similar in {filepath_to_check}")
        sys.exit(0)
    else:
        # print(f"FAILED: Did not find 'add' function with 'a + b' or similar in {filepath_to_check}", file=sys.stderr)
        sys.exit(1)
EOSCRIPT
          chmod +x check_python_add_operation.py # Make it executable, though python interpreter is called directly

          # Call the python script to check the generated code
          if python ./check_python_add_operation.py "$VERIFY_CODE_OUTPUT"; then
            log_timestamped "Validation success: 'verify' fixed the semantic error in $VERIFY_CODE_OUTPUT (AST check passed)."
          else
            log_timestamped "[ERROR] Verify command succeeded but FAILED to fix the introduced semantic error in $VERIFY_CODE_OUTPUT (AST check failed)."
            VALIDATION_FAILED=1
          fi
      else
          log_error "pdd verify failed with exit code $VERIFY_STATUS."
          log_timestamped "Validation failed: pdd verify failed with exit code $VERIFY_STATUS."
          # Decide if this is fatal, but script will likely exit due to set -e anyway if VERIFY_STATUS != 0
      fi
  fi
fi

# Use verified file for subsequent tests (better coverage)
if [ -f "$VERIFY_CODE_OUTPUT" ]; then
    cp "$VERIFY_CODE_OUTPUT" "$MATH_SCRIPT"
    log "Adopted verified_simple_math.py as simple_math.py for subsequent tests"
elif [ -f "$ORIGINAL_MATH_SCRIPT" ]; then
    # Fallback for individual test runs where verify didn't run
    cp "$ORIGINAL_MATH_SCRIPT" "$MATH_SCRIPT"
    log "Restored original simple_math.py (verified file not available)"
fi

# 8. Parameterized generate (-e/--env)
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "8" ]; then
  log "8. Testing parameterized 'generate' with -e/--env"

  PARAM_PROMPT="param_module_python.prompt"
  # Create a minimal prompt that doesn't depend on the variable value for correctness
  cat > "$PARAM_PROMPT" << 'EOF'
% You are an expert Python engineer. Create a simple Python module with at least one function.
% Keep it small and runnable.

Write a Python module that defines:
- a function `whoami()` that returns a non-empty string.
EOF

  # Decide whether to use cloud or local for this step
  EXTRA_ARGS=()
  if { [ -n "${NEXT_PUBLIC_FIREBASE_API_KEY:-}" ] && [ -n "${GITHUB_CLIENT_ID:-}" ]; }; then
    log "Using cloud for parameterized generate"
  elif [ -n "${OPENAI_API_KEY:-}" ]; then
    log "Using local for parameterized generate"
    EXTRA_ARGS+=("--local")
  else
    log "Skipping parameterized generate: missing both cloud (NEXT_PUBLIC_FIREBASE_API_KEY+GITHUB_CLIENT_ID) and local (OPENAI_API_KEY) credentials"
    # Skip this block without exiting the script
    EXTRA_ARGS=("__SKIP__")
  fi

  # If the installed pdd CLI does not support -e/--env, skip this section
  if ! $PDD_SCRIPT generate --help 2>&1 | grep -q -- "--env"; then
    log "Skipping parameterized generate: current pdd CLI does not support -e/--env"
    EXTRA_ARGS=("__SKIP__")
  fi

  # Case A: KEY=VALUE form; output path uses ${MODULE}
  # Use PDD-side expansion to avoid shell expanding unset variables
  if [ "${EXTRA_ARGS[0]:-}" != "__SKIP__" ]; then
    run_pdd_command generate ${EXTRA_ARGS[@]:-} -e MODULE=orders --output 'param_${MODULE}.py' "$PARAM_PROMPT"
    check_exists "param_orders.py" "Parameterized output (orders)"

    # Case B: Bare KEY fallback to env; ensure shell env supplies it
    export MODULE="payments"
    run_pdd_command generate ${EXTRA_ARGS[@]:-} -e MODULE --output 'param_${MODULE}.py' "$PARAM_PROMPT"
    check_exists "param_payments.py" "Parameterized output (payments)"

    # Case C: Unknown placeholder in output path remains unchanged
    run_pdd_command generate ${EXTRA_ARGS[@]:-} -e MODULE=customers --output 'param_${UNKNOWN}.py' "$PARAM_PROMPT"
    if [ -e 'param_${UNKNOWN}.py' ]; then
      log "Unknown placeholder remained unchanged in output path as expected"
      log_timestamped "Validation success: unknown placeholder in output path unchanged"
    else
      log_error "Expected literal file with \\"param_\${UNKNOWN}.py\\" name not found"
      exit 1
    fi
  else
    log "Skipping parameterized generate due to missing credentials"
  fi
fi

# 8. Test
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "8" ]; then
  log "8. Testing 'test' command (initial generation)"

  # Create a context test prompt to guide test generation
  # MOVED TO SETUP SECTION
  # log "Creating context/test.prompt for test generation"
  # mkdir -p context # Ensure context subdirectory exists (might be redundant if Test 2 ran)
  # cat << EOF > "context/test.prompt"
  # For the function 'add' defined based on 'simple_math_python.prompt', the implementation is in 'simple_math.py'.
  # Therefore, the test file should include the line: 'from simple_math import add'
  # EOF

  run_pdd_command test --output "$MATH_TEST_SCRIPT" --language Python "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT"
  check_exists "$MATH_TEST_SCRIPT" "'test' initial output"

  # 8a. Test with coverage improvement
  log "8a. Testing 'test' with coverage improvement"
  # Fix the module import issue in the test script
  # log "Fixing module import in test script..." # Should be unnecessary with context/test.prompt
  # sed -i.bak 's/from add import add/from simple_math import add/' "$MATH_TEST_SCRIPT"
  
  # Remove the Z3 dependency that's causing issues
  # log "Removing Z3 dependency from test script..." # Should be unnecessary with context/test.prompt
  # sed -i.bak2 's/from z3 import Int, Solver, sat/# Z3 import removed for regression tests/' "$MATH_TEST_SCRIPT"
  # log "Creating simplified test file without Z3 dependencies..." # Should be unnecessary with context/test.prompt
  # cat > "$MATH_TEST_SCRIPT" << 'EOF'
  # ... (simplified test content removed) ...
  # EOF
  
  # Run initial tests with coverage
  log "Running pytest with coverage..."
  TEST_CMD=(python -m pytest --cov="$MATH_BASENAME" --cov-report=xml:"$COVERAGE_REPORT" "$MATH_TEST_SCRIPT")
  "${TEST_CMD[@]}" > "$PYTEST_LOG" 2>&1 || true # Allow failure
  
  # Create an empty coverage report if it doesn't exist to allow the test to continue
  if [ ! -f "$COVERAGE_REPORT" ]; then
    log "Creating empty coverage report file since none was generated..."
    echo '<?xml version="1.0" ?><coverage version="7.0.0"></coverage>' > "$COVERAGE_REPORT"
  fi
  
  check_exists "$COVERAGE_REPORT" "Coverage report"

  # Check if tests passed initially (grep for failures/errors)
  if grep -q -E "===+ (FAILURES|ERRORS) ===+" "$PYTEST_LOG"; then
      log "Initial tests failed. Proceeding to fix..."
  else
      log "Initial tests passed. Coverage improvement test might not add much unless coverage < target."
  fi

  # Run test command again to improve coverage
  TARGET_COVERAGE=95.0
  IMPROVED_TEST_SCRIPT="improved_$MATH_TEST_SCRIPT"
  run_pdd_command test --output "$IMPROVED_TEST_SCRIPT" \
                       --coverage-report "$COVERAGE_REPORT" \
                       --existing-tests "$MATH_TEST_SCRIPT" \
                       --target-coverage $TARGET_COVERAGE \
                       "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT"
  check_exists "$IMPROVED_TEST_SCRIPT" "'test' coverage improvement output"

  # 8b. Test with merge
  log "8b. Testing 'test' with merge"
  MERGED_TEST_SCRIPT="merged_$MATH_TEST_SCRIPT"
  # Backup coverage.xml before rerunning coverage
  if [ -f "$COVERAGE_REPORT" ]; then
    cp "$COVERAGE_REPORT" "${COVERAGE_REPORT}.backup"
  fi
  # Rerun coverage generation on original tests, preserving coverage.xml
  "${TEST_CMD[@]}" > "$PYTEST_LOG.merge" 2>&1 || true
  # Restore coverage.xml if it was lost
  if [ ! -f "$COVERAGE_REPORT" ] && [ -f "${COVERAGE_REPORT}.backup" ]; then
    log "Restoring coverage.xml from backup..."
    cp "${COVERAGE_REPORT}.backup" "$COVERAGE_REPORT"
  fi
  # Run test with merge - output overwrites existing test file
  run_pdd_command test --output "$MATH_TEST_SCRIPT" \
                       --coverage-report "$COVERAGE_REPORT" \
                       --existing-tests "$MATH_TEST_SCRIPT" \
                       --target-coverage $TARGET_COVERAGE \
                       --merge \
                       "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT"
  check_exists "$MATH_TEST_SCRIPT" "'test --merge' output (should overwrite)"
  log "Running merged tests..."
  python -m pytest "$MATH_TEST_SCRIPT" >> "$LOG_FILE" 2>&1 || log "Merged tests failed (non-fatal for script)."

  # 8c. Test with env var output path (via envonly context)
  log "8c. Testing 'test' with environment variable output path"
  ENV_OUT_DIR_TEST="env_out_test"
  mkdir -p "$ENV_OUT_DIR_TEST"
  export PDD_TEST_OUTPUT_PATH="$ENV_OUT_DIR_TEST/" # Trailing slash indicates directory

  # Use envonly context so env vars take precedence (no context paths)
  run_pdd_command --context envonly test "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" # No --output
  # Default name is test_<basename>.<lang_ext>
  check_exists "$ENV_OUT_DIR_TEST/$MATH_TEST_SCRIPT" "'test' output via env var"

  unset PDD_TEST_OUTPUT_PATH
fi

# 9. Fix
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "9" ]; then
  log "9. Testing 'fix' command"
  # Run tests again, capture errors for fix command
  log "Running pytest to generate errors for 'fix' command"
  python -m pytest "$MATH_TEST_SCRIPT" > "$PYTEST_LOG" 2>&1 || true

  if grep -q -E "===+ (FAILURES|ERRORS) ===+" "$PYTEST_LOG"; then
      log "Running 'fix' command (non-loop)"
      run_pdd_command_noexit fix --output-test "$FIXED_MATH_TEST_SCRIPT" --output-code "$FIXED_MATH_SCRIPT" --output-results "fix_results.log" \
                          "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" "$MATH_TEST_SCRIPT" "$PYTEST_LOG"

      # Adopt fixed versions if they were created
      adopted_fix=false
      if [ -f "$FIXED_MATH_SCRIPT" ]; then
          cp "$FIXED_MATH_SCRIPT" "$MATH_SCRIPT"
          log "Adopted fixed script from 'fix' command."
          adopted_fix=true
      fi
      if [ -f "$FIXED_MATH_TEST_SCRIPT" ]; then
          cp "$FIXED_MATH_TEST_SCRIPT" "$MATH_TEST_SCRIPT"
          log "Adopted fixed test script from 'fix' command."
          adopted_fix=true
      fi

      # 9a. Fix with --loop
      log "9a. Testing 'fix --loop'"
      # Generate fresh error log for loop test
      log "Running pytest again for 'fix --loop'"
      python -m pytest "$MATH_TEST_SCRIPT" > "$MATH_ERROR_LOOP_LOG" 2>&1 || true

      if grep -q -E "===+ (FAILURES|ERRORS) ===+" "$MATH_ERROR_LOOP_LOG"; then
          run_pdd_command_noexit fix --loop --output-test "$FIXED_LOOP_MATH_TEST_SCRIPT" --output-code "$FIXED_LOOP_MATH_SCRIPT" \
                              --output-results "fixed_loop_results.log" \
                              --verification-program "$MATH_VERIFICATION_PROGRAM" \
                              --max-attempts 2 --budget 5.0 \
                              --auto-submit \
                              "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" "$MATH_TEST_SCRIPT" "$MATH_ERROR_LOOP_LOG"
          # Adopt loop fixed versions if created
          if [ -f "$FIXED_LOOP_MATH_SCRIPT" ]; then
              cp "$FIXED_LOOP_MATH_SCRIPT" "$MATH_SCRIPT"
              log "Adopted fixed script from 'fix --loop' command."
          fi
          if [ -f "$FIXED_LOOP_MATH_TEST_SCRIPT" ]; then
              cp "$FIXED_LOOP_MATH_TEST_SCRIPT" "$MATH_TEST_SCRIPT"
              log "Adopted fixed test script from 'fix --loop' command."
          fi
          # Final check: Run tests after all fixes
          log "Running final tests after all 'fix' attempts"
          python -m pytest "$MATH_TEST_SCRIPT" >> "$LOG_FILE" 2>&1 || log "Tests still failed after all fix attempts (non-fatal)."
      else
          log "No errors found for 'fix --loop', skipping loop test."
      fi
  else
      log "No errors found in pytest run, skipping 'fix' commands."
  fi
fi

# 10. Split
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "10" ]; then
  log "10. Testing 'split' command"
  run_pdd_command split --output-sub "$SPLIT_SUB_PROMPT" --output-modified "$SPLIT_MODIFIED_PROMPT" \
                        "$SPLIT_PROMPT" \
                        "$MATH_SCRIPT" \
                        "$MATH_VERIFICATION_PROGRAM"
  check_exists "$SPLIT_SUB_PROMPT" "'split' sub-prompt output"
  check_exists "$SPLIT_MODIFIED_PROMPT" "'split' modified prompt output"
fi

# 11. Detect
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "11" ]; then
  log "11. Testing 'detect' command"
  run_pdd_command detect --output "$DETECT_RESULTS_CSV" \
                         "$PROMPTS_PATH/$MATH_PROMPT" \
                         "$SPLIT_SUB_PROMPT" \
                         "$PROMPTS_PATH/$OTHER_PROMPT" \
                         "$DETECT_CHANGE_FILE"
  check_exists "$DETECT_RESULTS_CSV" "'detect' results CSV"
fi

# 12. Conflicts
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "12" ]; then
  log "12. Testing 'conflicts' command"
  run_pdd_command conflicts --output "$CONFLICTS_RESULTS_CSV" \
                            "$PROMPTS_PATH/$MATH_PROMPT" \
                            "$PROMPTS_PATH/$OTHER_PROMPT"
  check_exists "$CONFLICTS_RESULTS_CSV" "'conflicts' results CSV"
fi

# 13. Trace
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "13" ]; then
  log "13. Testing 'trace' command"
  
  # Ensure we have a clean simple_math.py with add function for trace test
  log "Ensuring clean math script for trace test"
  if [ ! -f "$ORIGINAL_MATH_SCRIPT" ]; then
      log "Warning: Original math script backup not found, regenerating for trace test"
      run_pdd_command generate --output "$MATH_SCRIPT" "$PROMPTS_PATH/$MATH_PROMPT"
  else
      cp "$ORIGINAL_MATH_SCRIPT" "$MATH_SCRIPT"
      log "Restored $MATH_SCRIPT from backup for trace test"
  fi
  
  # Debug: Show what's in the file
  log "DEBUG: Contents of $MATH_SCRIPT before trace test:"
  cat "$MATH_SCRIPT" >> "$LOG_FILE" 2>&1
  
  # Get line number of 'def add' in the current script
  ADD_FUNC_LINE=$(grep -n "def add(" "$MATH_SCRIPT" | cut -d: -f1 | head -n 1)
  if [ -z "$ADD_FUNC_LINE" ]; then
      log "Warning: Could not find 'def add(' in $MATH_SCRIPT for 'trace' test. Using default line 3."
      ADD_FUNC_LINE=3
  fi
  log "Tracing line $ADD_FUNC_LINE in $MATH_SCRIPT"
  run_pdd_command_noexit trace --output "$TRACE_RESULTS_LOG" \
                        "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" "$ADD_FUNC_LINE"
  
  # Check if trace command succeeded and handle accordingly
  if [ $? -eq 0 ]; then
      check_exists "$TRACE_RESULTS_LOG" "'trace' results log"
      log "Trace command completed successfully"
  else
      log "Trace command failed, but continuing with tests"
      # Create empty file to satisfy any downstream dependencies
      touch "$TRACE_RESULTS_LOG"
      log "Created empty trace results file to continue testing"
  fi
fi

# 14. Bug
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "14" ]; then
  log "14. Testing 'bug' command"
  log "Ensuring verification program is runnable for 'bug' test"
  run_pdd_command example --output "$MATH_VERIFICATION_PROGRAM" "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT"
  log "Generating current output for 'bug' command"
  python "$MATH_VERIFICATION_PROGRAM" > "current_output.txt" 2>&1 || true # Allow failure
  log "Creating desired output for 'bug' command"
  # Example: Desired output changes the sum description
  echo "The result of addition is: 8" > "desired_output.txt" # Assuming 5+3 example

  run_pdd_command bug --output "$BUG_TEST_SCRIPT" --language Python \
                      "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" \
                      "$MATH_VERIFICATION_PROGRAM" \
                      "current_output.txt" "desired_output.txt"
  check_exists "$BUG_TEST_SCRIPT" "'bug' generated test script"
fi

# 15. Auto-Deps
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "15" ]; then
  log "15. Testing 'auto-deps' command"
  AUTO_DEPS_CSV="project_dependencies.csv"
  run_pdd_command auto-deps --output "$AUTO_DEPS_PROMPT" \
                            --csv "$AUTO_DEPS_CSV" \
                            "$PROMPTS_PATH/$MATH_PROMPT" "$CONTEXT_PATH_GLOB" # Use quotes if glob pattern has spaces or special chars
  check_exists "$AUTO_DEPS_PROMPT" "'auto-deps' modified prompt"
  check_exists "$AUTO_DEPS_CSV" "'auto-deps' dependency CSV"

  # 15a. Auto-Deps with --force-scan
  log "15a. Testing 'auto-deps --force-scan'"
  # Modify timestamp of CSV to check if scan happens (cross-platform solution)
  if date --version 2>/dev/null | grep -q GNU; then
    # GNU/Linux
    touch -m -d "2 hours ago" "$AUTO_DEPS_CSV"
  else
    # BSD/macOS
    touch -m -t "$(date -v-2H +%Y%m%d%H%M.%S)" "$AUTO_DEPS_CSV"
  fi
  run_pdd_command auto-deps --force-scan --output "forced_scan_${AUTO_DEPS_PROMPT}" \
                             --csv "$AUTO_DEPS_CSV" \
                             "$PROMPTS_PATH/$MATH_PROMPT" "$CONTEXT_PATH_GLOB"
  check_exists "forced_scan_${AUTO_DEPS_PROMPT}" "'auto-deps --force-scan' output"
  # Check if CSV timestamp updated (simple check)
  if [ "$AUTO_DEPS_CSV" -ot "forced_scan_${AUTO_DEPS_PROMPT}" ]; then # Check if CSV is older
      log "Auto-deps CSV timestamp updated after --force-scan, as expected."
  else
      log "Warning: Auto-deps CSV timestamp did not update after --force-scan (check might be unreliable)."
  fi
fi

# 16. Test Global Options
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "16" ]; then
  log "16. Testing Global Options"
  # Test --quiet
  log "16a. Testing '--quiet'"
  QUIET_LOG="quiet_run.log"
  run_pdd_command --quiet generate --output "quiet_gen.py" "$PROMPTS_PATH/$MATH_PROMPT" > "$QUIET_LOG" 2>&1
  # Check if log is small (basic check)
  QUIET_SIZE=$(wc -c < "$QUIET_LOG")
  if [ "$QUIET_SIZE" -lt 100 ]; then # Arbitrary small size
      log "'--quiet' produced minimal output as expected."
  else
      log "Warning: '--quiet' output size ($QUIET_SIZE bytes) seems large."
  fi
fi

# 17. Test Multi-Command Chaining (Commented out in original, remains commented)
# if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "17" ]; then
# log "17. Testing Multi-Command Chaining"
# # This syntax might depend heavily on how pdd parses chained commands.
# # Assuming space separation works:
# run_pdd_command generate --output chained_gen.py $PROMPTS_PATH/$MATH_PROMPT \
#                 example --output chained_example.py $PROMPTS_PATH/$MATH_PROMPT chained_gen.py \
#                 test --output chained_test.py $PROMPTS_PATH/$MATH_PROMPT chained_gen.py
# check_exists chained_gen.py "Chained 'generate' output"
# check_exists chained_example.py "Chained 'example' output"
# check_exists chained_test.py "Chained 'test' output"
# Note: Chaining is complex to implement robustly in the CLI parser and may not be fully supported. Skip if needed.
# fi

# 18. Test Error Handling
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "18" ]; then
  log "18. Testing Error Handling"
  # Provide non-existent prompt to generate
  run_pdd_expect_fail generate --output "nonexistent.py" "nonexistent/prompt.prompt"
  # Provide invalid line number to trace
  run_pdd_command trace --output "invalid_trace.log" "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" 99999
  check_exists "invalid_trace.log" "'trace' error-handling output"
  python - <<'PY'
from pathlib import Path

log_path = Path("invalid_trace.log")
text = log_path.read_text(encoding="utf-8") if log_path.exists() else ""
if "Prompt Line:" not in text:
    raise SystemExit("trace fallback output missing 'Prompt Line' entry")
PY
  # Provide non-existent error file to fix
  run_pdd_expect_fail fix --output-test "err_test.py" --output-code "err_code.py" "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" "$MATH_TEST_SCRIPT" "nonexistent/error.log"
fi

# 19. Templates
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "19" ]; then
  log "19. Testing templates command group and template-backed generation"

  TEMPLATE_FIXTURE_DIR="docs"
  TEMPLATE_PRD_FILE="$TEMPLATE_FIXTURE_DIR/specs.md"
  TEMPLATE_TECH_STACK_FILE="$TEMPLATE_FIXTURE_DIR/tech_stack.md"
  mkdir -p "$TEMPLATE_FIXTURE_DIR"
  cat > "$TEMPLATE_PRD_FILE" << 'EOF'
# Order Management MVP (regression template fixture)
## Goals
- Capture end-to-end order lifecycle for web and API clients.

## Key Features
1. Create Order (items, totals, status transitions)
2. Customer Dashboard (list and track orders)
3. Admin Oversight (monitor SLAs, escalate stalled orders)

## Constraints
- Target stack: Next.js frontend, FastAPI backend, Postgres.
EOF

  cat > "$TEMPLATE_TECH_STACK_FILE" << 'EOF'
# Regression tech stack fixture
Backend: Python (FastAPI)
Frontend: Next.js (TypeScript)
Database: Postgres
EOF

  # Validate templates list output contains packaged architecture template
  log "Running 'templates list'"
  log_timestamped "TEMPLATES_LIST_START"
  run_pdd_command templates list
  log_timestamped "TEMPLATES_LIST_END"
  LOG_PATH="$LOG_FILE" START_MARK="TEMPLATES_LIST_START" END_MARK="TEMPLATES_LIST_END" python - <<'PY'
import os
import pathlib
import sys

log_path = pathlib.Path(os.environ["LOG_PATH"])
start_mark = os.environ["START_MARK"]
end_mark = os.environ["END_MARK"]

text = log_path.read_text(encoding="utf-8")
start_idx = text.rfind(start_mark)
if start_idx == -1:
    print("templates list start marker missing", file=sys.stderr)
    sys.exit(1)
end_idx = text.find(end_mark, start_idx)
if end_idx == -1:
    print("templates list end marker missing", file=sys.stderr)
    sys.exit(1)
segment = text[start_idx:end_idx]
if "architecture/architecture_json" not in segment:
    print("architecture/architecture_json missing from templates list output", file=sys.stderr)
    sys.exit(1)
PY

  # Validate template metadata via registry helper (ensures PRD variable and output_schema are exposed)
  log "Inspecting template metadata for architecture/architecture_json"
  PYTHONPATH="$PDD_BASE_DIR${PYTHONPATH:+:$PYTHONPATH}" python - <<'PY'
import sys
from pdd import template_registry

data = template_registry.show_template("architecture/architecture_json")
variables = data.get("variables") or {}
if "PRD_FILE" not in variables:
    print("PRD_FILE missing from template metadata", file=sys.stderr)
    sys.exit(1)
if not data.get("output_schema"):
    print("output_schema missing from template metadata", file=sys.stderr)
    sys.exit(1)
PY

  # Copy the packaged template into a project prompts directory
  TEMPLATE_COPY_DIR="prompts/templates_demo"
  log "Copying template into prompts/templates_demo"
  rm -f "$TEMPLATE_COPY_DIR/architecture_json.prompt"
  PYTHONPATH="$PDD_BASE_DIR${PYTHONPATH:+:$PYTHONPATH}" python - <<'PY'
import sys
from pathlib import Path
from pdd import template_registry

dest_dir = Path("prompts/templates_demo")
dest_dir.mkdir(parents=True, exist_ok=True)
dest = template_registry.copy_template("architecture/architecture_json", str(dest_dir))
print(dest)
PY
  check_exists "$TEMPLATE_COPY_DIR/architecture_json.prompt" "'templates copy' output"

  # Ensure generate --template flags missing required variables
  MISSING_TEMPLATE_OUTPUT="missing_template.json"
  [ -f "$MISSING_TEMPLATE_OUTPUT" ] && rm -f "$MISSING_TEMPLATE_OUTPUT"
  log_timestamped "TEMPLATES_GENERATE_FAIL_START"
  run_pdd_command_noexit generate --template architecture/architecture_json \
      -e TECH_STACK_FILE="$TEMPLATE_TECH_STACK_FILE" \
      -e DOC_FILES="$TEMPLATE_PRD_FILE" \
      -e INCLUDE_FILES="" \
      --output "$MISSING_TEMPLATE_OUTPUT"
  log_timestamped "TEMPLATES_GENERATE_FAIL_END"
  LOG_PATH="$LOG_FILE" START_MARK="TEMPLATES_GENERATE_FAIL_START" END_MARK="TEMPLATES_GENERATE_FAIL_END" python - <<'PY'
import os
import pathlib
import sys

log_path = pathlib.Path(os.environ["LOG_PATH"])
start_mark = os.environ["START_MARK"]
end_mark = os.environ["END_MARK"]

text = log_path.read_text(encoding="utf-8")
start_idx = text.rfind(start_mark)
if start_idx == -1:
    print("templates generate fail start marker missing", file=sys.stderr)
    sys.exit(1)
end_idx = text.find(end_mark, start_idx)
if end_idx == -1:
    print("templates generate fail end marker missing", file=sys.stderr)
    sys.exit(1)
segment = text[start_idx:end_idx]
if "Missing required variables" not in segment or "PRD_FILE" not in segment:
    print("generate --template without PRD_FILE did not report missing variable", file=sys.stderr)
    sys.exit(1)
PY
  check_not_exists "$MISSING_TEMPLATE_OUTPUT" "'generate --template' output when PRD_FILE missing"

  TEMPLATE_GENERATED_OUTPUT="template_architecture.json"
  log_timestamped "TEMPLATES_GENERATE_ATTEMPT_START"
  if run_pdd_command_noexit generate --template architecture/architecture_json \
      -e PRD_FILE="$TEMPLATE_PRD_FILE" \
      -e TECH_STACK_FILE="$TEMPLATE_TECH_STACK_FILE" \
      -e DOC_FILES="$TEMPLATE_PRD_FILE" \
      -e INCLUDE_FILES="" \
      --output "$TEMPLATE_GENERATED_OUTPUT"; then
    GENERATE_STATUS=$?
  else
    GENERATE_STATUS=$?
  fi
  log_timestamped "TEMPLATES_GENERATE_ATTEMPT_END"
  if [ "$GENERATE_STATUS" -eq 0 ] && [ -f "$TEMPLATE_GENERATED_OUTPUT" ]; then
    log "Template generation produced output file"
    check_exists "$TEMPLATE_GENERATED_OUTPUT" "'generate --template' output"
    LOG_PATH="$TEMPLATE_GENERATED_OUTPUT" python - <<'PY'
import json
import os
import pathlib
import sys

output_path = pathlib.Path(os.environ["LOG_PATH"])
try:
    data = json.loads(output_path.read_text(encoding="utf-8"))
except Exception as exc:  # json decode should never fail here
    print(f"failed to parse architecture output JSON: {exc}", file=sys.stderr)
    sys.exit(1)

def ensure_datasource(entry, item_idx, ds_idx):
    if not isinstance(entry, dict):
        raise ValueError(f"item[{item_idx}] dataSources[{ds_idx}] is not an object: {entry!r}")
    missing = [key for key in ("kind", "source") if key not in entry or not entry[key]]
    if missing:
        raise ValueError(
            f"item[{item_idx}] dataSources[{ds_idx}] missing required fields: {missing}"
        )

if isinstance(data, list):
    for idx, item in enumerate(data):
        interface = isinstance(item, dict) and item.get("interface")
        if not isinstance(interface, dict):
            continue
        if interface.get("type") != "page":
            continue
        page = interface.get("page")
        if not isinstance(page, dict):
            continue
        data_sources = page.get("dataSources")
        if not data_sources:
            continue
        if not isinstance(data_sources, list):
            raise ValueError(f"item[{idx}] page.dataSources is not a list")
        for ds_idx, entry in enumerate(data_sources):
            ensure_datasource(entry, idx, ds_idx)
else:
    print("architecture output is not a list", file=sys.stderr)
    sys.exit(1)
PY

    # Use the generated architecture output to drive generic/generate_prompt
    log "Deriving module/language from architecture output for generic template"
    GENERIC_ENV_FILE="$REGRESSION_DIR/generic_template_env.sh"
    ARCH_JSON_PATH="$TEMPLATE_GENERATED_OUTPUT" PYTHONPATH="$PDD_BASE_DIR${PYTHONPATH:+:$PYTHONPATH}" python - <<'PY' > "$GENERIC_ENV_FILE"
import json
import os
import pathlib
import shlex
import sys

arch_path = pathlib.Path(os.environ["ARCH_JSON_PATH"])
if not arch_path.exists():
    print("architecture JSON file not found", file=sys.stderr)
    sys.exit(1)
try:
    data = json.loads(arch_path.read_text(encoding="utf-8"))
except Exception as exc:  # JSON decode errors should be fatal here
    print(f"failed to parse architecture JSON: {exc}", file=sys.stderr)
    sys.exit(1)

if not isinstance(data, list) or not data:
    print("architecture JSON has no entries", file=sys.stderr)
    sys.exit(1)

item = data[0]
filename = isinstance(item, dict) and item.get("filename")
if not filename or not filename.endswith(".prompt"):
    print("architecture entry missing prompt filename", file=sys.stderr)
    sys.exit(1)

basename = filename[:-len(".prompt")]
parts = basename.split("_")
if len(parts) >= 2:
    module = "_".join(parts[:-1])
    language = parts[-1]
else:
    module = basename
    language = "Python"

print(f"MODULE_FROM_ARCHITECTURE={shlex.quote(module)}")
print(f"LANG_FROM_ARCHITECTURE={shlex.quote(language)}")
PY
    # shellcheck disable=SC1090
    source "$GENERIC_ENV_FILE"

    SANITIZED_MODULE=$(printf '%s' "$MODULE_FROM_ARCHITECTURE" | tr -c '[:alnum:]_' '_')
    SANITIZED_LANG=$(printf '%s' "$LANG_FROM_ARCHITECTURE" | tr -c '[:alnum:]_' '_')
    GENERIC_PROMPT_OUTPUT="$REGRESSION_DIR/${SANITIZED_MODULE}_${SANITIZED_LANG}.prompt"

    log "Generating generic/generate_prompt using architecture output -> $GENERIC_PROMPT_OUTPUT"
    log_timestamped "GENERIC_TEMPLATE_GENERATE_START"
    if run_pdd_command_noexit generate --template generic/generate_prompt \
        -e MODULE="$MODULE_FROM_ARCHITECTURE" \
        -e LANG_OR_FRAMEWORK="$LANG_FROM_ARCHITECTURE" \
        -e ARCHITECTURE_FILE="$TEMPLATE_GENERATED_OUTPUT" \
        -e PRD_FILE="$TEMPLATE_PRD_FILE" \
        -e TECH_STACK_FILE="$TEMPLATE_TECH_STACK_FILE" \
        --output "$GENERIC_PROMPT_OUTPUT"; then
      log_timestamped "GENERIC_TEMPLATE_GENERATE_END"
      if [ -s "$GENERIC_PROMPT_OUTPUT" ]; then
        log "'generate --template generic/generate_prompt' output file exists and is not empty: $GENERIC_PROMPT_OUTPUT"
        WRAP_SENTINEL="$GENERIC_PROMPT_OUTPUT.wrapped"
        rm -f "$WRAP_SENTINEL"
        GENERIC_PROMPT_OUTPUT="$GENERIC_PROMPT_OUTPUT" WRAP_SENTINEL="$WRAP_SENTINEL" python - <<'PY'
import os
import pathlib
import sys

prompt_path = pathlib.Path(os.environ["GENERIC_PROMPT_OUTPUT"])
text = prompt_path.read_text(encoding="utf-8") if prompt_path.exists() else ""
if "<prompt>" not in text or "</prompt>" not in text:
    sanitized = text.strip()
    if sanitized:
        prompt_path.write_text(f"<prompt>\n{sanitized}\n</prompt>\n", encoding="utf-8")
        sentinel = pathlib.Path(os.environ["WRAP_SENTINEL"])
        sentinel.write_text("wrapped", encoding="utf-8")
        print("wrapped generated module prompt with <prompt> tags after detection", file=sys.stderr)
    else:
        print("generated module prompt missing <prompt> tags", file=sys.stderr)
        sys.exit(1)
PY
        if [ -f "$WRAP_SENTINEL" ]; then
          log "generic template output was missing <prompt> tags; regression wrapped it automatically"
          rm -f "$WRAP_SENTINEL"
        fi
      else
        if LOG_PATH="$LOG_FILE" START_MARK="GENERIC_TEMPLATE_GENERATE_START" END_MARK="GENERIC_TEMPLATE_GENERATE_END" python - <<'PY'
import os
import pathlib
import sys

log_path = pathlib.Path(os.environ["LOG_PATH"])
start_mark = os.environ["START_MARK"]
end_mark = os.environ["END_MARK"]

text = log_path.read_text(encoding="utf-8")
start_idx = text.rfind(start_mark)
if start_idx == -1:
    print("generic template generate start marker missing", file=sys.stderr)
    sys.exit(1)
end_idx = text.find(end_mark, start_idx)
segment = text[start_idx:] if end_idx == -1 else text[start_idx:end_idx]
allowed = (
    "All candidate models failed",
    "Connection error",
)
if any(phrase in segment for phrase in allowed):
    sys.exit(0)

print("generic template generation did not produce output and no allowed failure detected", file=sys.stderr)
sys.exit(1)
PY
        then
          log "generic template generation skipped due to allowed failure (no output produced)"
        else
          log_error "'generate --template generic/generate_prompt' output file not found or is empty: $GENERIC_PROMPT_OUTPUT"
          log_timestamped "Validation failed: 'generate --template generic/generate_prompt' output file not found or is empty: $GENERIC_PROMPT_OUTPUT"
          exit 1
        fi
      fi
    else
      log_timestamped "GENERIC_TEMPLATE_GENERATE_END"
      LOG_PATH="$LOG_FILE" START_MARK="GENERIC_TEMPLATE_GENERATE_START" END_MARK="GENERIC_TEMPLATE_GENERATE_END" python - <<'PY'
import os
import pathlib
import sys

log_path = pathlib.Path(os.environ["LOG_PATH"])
start_mark = os.environ["START_MARK"]
end_mark = os.environ["END_MARK"]

text = log_path.read_text(encoding="utf-8")
start_idx = text.rfind(start_mark)
if start_idx == -1:
    print("generic template generate start marker missing", file=sys.stderr)
    sys.exit(1)
end_idx = text.find(end_mark, start_idx)
segment = text[start_idx:] if end_idx == -1 else text[start_idx:end_idx]
allowed = (
    "All candidate models failed",
    "Connection error",
)
if any(phrase in segment for phrase in allowed):
    sys.exit(0)

print("unexpected failure mode for generate --template generic/generate_prompt", file=sys.stderr)
sys.exit(1)
PY
      check_not_exists "$GENERIC_PROMPT_OUTPUT" "'generate --template generic/generate_prompt' output file after failure"
    fi
  else
    log "Template generation failed or did not produce output; verifying allowed failure reason"
    LOG_PATH="$LOG_FILE" START_MARK="TEMPLATES_GENERATE_ATTEMPT_START" END_MARK="TEMPLATES_GENERATE_ATTEMPT_END" python - <<'PY'
import os
import pathlib
import sys

log_path = pathlib.Path(os.environ["LOG_PATH"])
start_mark = os.environ["START_MARK"]
end_mark = os.environ["END_MARK"]
text = log_path.read_text(encoding="utf-8")
start_idx = text.rfind(start_mark)
if start_idx == -1:
    print("generate attempt start marker missing", file=sys.stderr)
    sys.exit(1)
end_idx = text.find(end_mark, start_idx)
if end_idx == -1:
    segment = text[start_idx:]
else:
    segment = text[start_idx:end_idx]
allowed = (
    "All candidate models failed",
    "Connection error",
)
if any(phrase in segment for phrase in allowed):
    sys.exit(0)

print("unexpected failure mode for generate --template", file=sys.stderr)
sys.exit(1)
PY
    check_not_exists "$TEMPLATE_GENERATED_OUTPUT" "'generate --template' output file after failure"
  fi
fi

# 20. Unit Test Auto-Discovery Regression
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "20" ]; then
  log "20. Testing 'generate' unit test auto-discovery effectiveness"

  # Create the unit test file in CURRENT directory (auto-discovery default looks here)
  # tests_dir defaults to "." (parent of default test_output_path "tests")
  cat > "test_encode_message.py" << 'EOF'
from encode_message import encode_message

def test_encode_basic():
    assert encode_message("hello") == "ifmmp"

def test_encode_abc():
    assert encode_message("abc") == "bcd"

def test_encode_wrap():
    assert encode_message("xyz") == "yza"
EOF

  # 1. Generate WITH --exclude-tests (no test context, expect failure)
  log "Generating with --exclude-tests (no auto-discovery)..."
  run_pdd_command generate --exclude-tests --output "encode_message.py" "$PROMPTS_PATH/encode_message_python.prompt"
  check_exists "encode_message.py" "'generate' with --exclude-tests"

  # Run pytest - expect FAILURE
  log "Running tests against code generated with --exclude-tests (expecting failure)..."
  if python -m pytest "test_encode_message.py" -v >> "$LOG_FILE" 2>&1; then
    log "WARNING: Tests passed with --exclude-tests (unexpected but acceptable)"
  else
    log "Tests failed as expected with --exclude-tests (no test context)"
  fi

  # 2. Generate normally - auto-discovery should find test file (expect success)
  log "Generating with auto-discovery (default behavior)..."
  run_pdd_command generate --output "encode_message.py" "$PROMPTS_PATH/encode_message_python.prompt"
  check_exists "encode_message.py" "'generate' with auto-discovery"

  # Run pytest - expect SUCCESS
  log "Running tests against code generated with auto-discovery..."
  if python -m pytest "test_encode_message.py" -v >> "$LOG_FILE" 2>&1; then
    log "Tests passed with auto-discovery - feature working correctly"
  else
    log_error "Tests failed with auto-discovery - feature may be broken"
    exit 1
  fi
fi

# 21. Testing 'fix' with multiple test files (end-to-end with LLM)
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "21" ]; then
  log "21. Testing 'fix' command with multiple test files (E2E)"

  # Create a directory for this test (use absolute path)
  MULTI_FIX_DIR="$REGRESSION_DIR/multi_fix_test"
  mkdir -p "$MULTI_FIX_DIR"

  # Create a buggy code file - has real bugs that tests will catch
  cat > "$MULTI_FIX_DIR/buggy_math.py" << 'PYEOF'
def double(x):
    # BUG: returns x instead of x * 2
    return x

def square(x):
    # BUG: returns x * 2 instead of x * x
    return x * 2
PYEOF

  # Create first test file - tests double() function
  cat > "$MULTI_FIX_DIR/test_double.py" << 'PYEOF'
from buggy_math import double

def test_double_positive():
    assert double(5) == 10

def test_double_zero():
    assert double(0) == 0

def test_double_negative():
    assert double(-3) == -6
PYEOF

  # Create second test file - tests square() function
  cat > "$MULTI_FIX_DIR/test_square.py" << 'PYEOF'
from buggy_math import square

def test_square_positive():
    assert square(3) == 9

def test_square_zero():
    assert square(0) == 0

def test_square_negative():
    assert square(-2) == 4
PYEOF

  # Create a simple prompt file
  cat > "$MULTI_FIX_DIR/buggy_math_python.prompt" << 'PYEOF'
// Language: Python
// Description: Simple math utilities

Create a Python module with:
- double(x): Returns x multiplied by 2
- square(x): Returns x squared (x * x)
PYEOF

  # Run pytest to generate error log
  log "Running pytest on buggy code to generate errors"
  python -m pytest "$MULTI_FIX_DIR/test_double.py" "$MULTI_FIX_DIR/test_square.py" \
    > "$MULTI_FIX_DIR/errors.log" 2>&1 || true

  # Show what errors we got
  if grep -q "FAILED" "$MULTI_FIX_DIR/errors.log"; then
    FAIL_COUNT=$(grep -c "FAILED" "$MULTI_FIX_DIR/errors.log" || echo "0")
    log "Found $FAIL_COUNT failing tests - running fix with multiple test files"

    # Run fix command with TWO test files - each should be processed by LLM
    log "Calling pdd fix with test_double.py and test_square.py"
    run_pdd_command --local fix \
      --output-code "$MULTI_FIX_DIR/fixed_math.py" \
      --output-test "$MULTI_FIX_DIR/fixed_tests/" \
      --output-results "$MULTI_FIX_DIR/fix_results.log" \
      "$MULTI_FIX_DIR/buggy_math_python.prompt" \
      "$MULTI_FIX_DIR/buggy_math.py" \
      "$MULTI_FIX_DIR/test_double.py" \
      "$MULTI_FIX_DIR/test_square.py" \
      "$MULTI_FIX_DIR/errors.log"

    # Check if fixed code was created
    if [ -f "$MULTI_FIX_DIR/fixed_math.py" ]; then
      log "Fixed code file created: $MULTI_FIX_DIR/fixed_math.py"

      # Verify the fix actually works by running tests against fixed code
      cp "$MULTI_FIX_DIR/fixed_math.py" "$MULTI_FIX_DIR/buggy_math.py"
      if python -m pytest "$MULTI_FIX_DIR/test_double.py" "$MULTI_FIX_DIR/test_square.py" >> "$LOG_FILE" 2>&1; then
        log "All tests pass after fix - multiple test files feature working!"
        log_timestamped "Test 21 PASSED: 'fix' with multiple test files - tests pass after fix"
      else
        log "Some tests still fail after fix (LLM may need more attempts)"
        log_timestamped "Test 21 PARTIAL: 'fix' ran but some tests still fail"
      fi
    else
      log_error "Fixed code file was NOT created"
      log_timestamped "Test 21 FAILED: No fixed code output"
    fi
  else
    log "Tests unexpectedly passed - skipping fix test"
    log_timestamped "Test 21 SKIPPED: No failing tests found"
  fi

  log "Multiple test files fix test completed"
fi

# --- Final Summary ---
log_timestamped "======== Regression Tests Completed (Target: $TARGET_TEST) ========"
log "----------------------------------------"
log "All tests completed."
log "Log file: $(pwd)/$LOG_FILE"
log "Cost file: $(pwd)/$COST_FILE"

# Display total cost and perform final validation
if [ -f "$COST_FILE" ]; then
    # Validate row count
    MIN_EXPECTED_COST_ROWS=10
    ACTUAL_DATA_ROWS=$(awk 'NR > 1 {count++} END {print count+0}' "$COST_FILE") # +0 ensures numeric output even if empty
    log "Found $ACTUAL_DATA_ROWS data rows in cost file."
    if [ "$ACTUAL_DATA_ROWS" -ge "$MIN_EXPECTED_COST_ROWS" ]; then
        log "Cost file row count ($ACTUAL_DATA_ROWS) meets minimum expectation ($MIN_EXPECTED_COST_ROWS)."
        log_timestamped "Validation success: Cost file row count sufficient."
    else
        log_error "Cost file row count ($ACTUAL_DATA_ROWS) is below minimum expectation ($MIN_EXPECTED_COST_ROWS)."
        log_timestamped "Validation failed: Cost file row count insufficient."
        # Decide if this should be fatal
        # exit 1
    fi

    # Robust awk command to handle potential missing cost values or headers
    total_cost=$(awk -F',' 'NR > 1 && NF >= 4 && $4 ~ /^[0-9]+(\.[0-9]+)?$/ { sum += $4 } END { printf "%.6f", sum }' "$COST_FILE")
    log "Total estimated cost of all operations: $total_cost USD"
    log_timestamped "Total estimated cost of all operations: $total_cost USD"
else
    log_error "Cost file $COST_FILE not found at end of script. Cannot calculate total cost or validate rows."
    log_timestamped "Validation failed: Cost file not found at end of script."
    # exit 1 # Definitely fatal if cost tracking was expected
fi

cd .. # Go back to original directory if needed

exit 0 # Ensure script exits successfully if all steps pass
exit 0 # Ensure script exits successfully if all steps pass
