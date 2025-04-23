#!/bin/bash

# Exit immediately if a command exits with a non-zero status.
set -e
# Treat unset variables as an error when substituting.
set -u

# Global settings
VERBOSE=${VERBOSE:-1} # Default to 1 if not set
STRENGTH=${STRENGTH:-0.85} # Default strength
TEMPERATURE=${TEMPERATURE:-1.0} # Default temperature
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
# Assuming PDD_PATH is set externally, pointing to the pdd source directory
if [ -z "${PDD_PATH:-}" ]; then
  echo "Error: PDD_PATH environment variable is not set."
  exit 1
fi
STAGING_PATH="$PDD_PATH/../staging"
PDD_SCRIPT="pdd" # Assumes pdd is in PATH or use "$PDD_PATH/pdd/cli.py" etc.
PROMPTS_PATH="$PDD_PATH/../prompts"
CONTEXT_PATH="$PDD_PATH/../context"
CONTEXT_PATH_GLOB="$CONTEXT_PATH/*.py" # Escaping might be needed depending on shell interpretation
REGRESSION_DIR="$STAGING_PATH/regression_$(date +%Y%m%d_%H%M%S)" # Unique dir per run
LOG_FILE="$REGRESSION_DIR/regression.log"
COST_FILE="regression_cost.csv"

# simple_math test case files
MATH_BASENAME="simple_math"
MATH_PROMPT="${MATH_BASENAME}.prompt"
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
COMPLEX_PROMPT="complex_features.prompt"
COMPLEX_PREPROCESSED="complex_features_preprocessed.prompt"
COMPLEX_XML="complex_features_xml.prompt"
COMPLEX_RECURSIVE="complex_features_recursive.prompt"
COMPLEX_DOUBLE="complex_features_double.prompt"
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
OTHER_PROMPT="get_extension_python.prompt" # Assumed exists in PROMPTS_PATH

# Trace files
TRACE_RESULTS_LOG="trace_results.log"

# Verify files
VERIFY_RESULTS_LOG="verify_results.log"
VERIFY_CODE_OUTPUT="verified_${MATH_SCRIPT}"
VERIFY_EXAMPLE_OUTPUT="verified_${MATH_VERIFICATION_PROGRAM}" # Example derived from verified code
VERIFY_HARNESS_LOG="verify_harness.log"
VERIFY_ISOLATED_DIR="isolated_verify"
VERIFY_SCRIPT_PATH="$PDD_PATH/../tests/isolated_verify.py"

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

    # Add cost tracking only if the file doesn't exist yet
    if [ ! -f "$REGRESSION_DIR/$COST_FILE" ]; then
      cmd_array+=("--output-cost" "$REGRESSION_DIR/$COST_FILE")
    fi

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

    cmd_array+=("$command_name")
    cmd_array+=("${args[@]}")

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
    # Kill web server if running
    if [ -n "${HTTP_SERVER_PID:-}" ]; then
        log "Stopping background HTTP server (PID: $HTTP_SERVER_PID)..."
        kill "$HTTP_SERVER_PID" || log "HTTP server already stopped."
    fi
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

# Create cost file header if it doesn't exist
if [ ! -f "$COST_FILE" ]; then
    echo "timestamp,model,command,cost,input_files,output_files" > "$COST_FILE"
fi

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

Web scrape (requires local server):
<web>https://www.google.com</web>

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
echo "def func_a():\n  print('Hello A')" > "$CHANGE_CSV_CODE_DIR/$DUMMY_CODE_A"
echo "def func_b():\n  print('Hello B')" > "$CHANGE_CSV_CODE_DIR/$DUMMY_CODE_B"
cp "$PROMPTS_PATH/$MATH_PROMPT" "$DUMMY_PROMPT_A" # Use math prompt as base
cp "$PROMPTS_PATH/$MATH_PROMPT" "$DUMMY_PROMPT_B" # Use math prompt as base
cat << EOF > "$CHANGE_CSV_FILE"
prompt_name,change_instructions
"$DUMMY_PROMPT_A","Change function name to func_a_modified"
"$DUMMY_PROMPT_B","Add a comment saying 'Modified B'"
EOF

# Create file for detect test
echo "Refactor the simple_math function to use a helper." > "$DETECT_CHANGE_FILE"

# Create files for split test
echo "Extract the 'add' function into a separate sub-prompt." > "$SPLIT_PROMPT"

# --- Regression Tests ---

log_timestamped "======== Starting Regression Tests ========"

# 1. Generate
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "1" ]; then
  log "1. Testing 'generate' command"
  run_pdd_command generate --output "$MATH_SCRIPT" "$PROMPTS_PATH/$MATH_PROMPT"
  check_exists "$MATH_SCRIPT" "'generate' output"
  cp "$MATH_SCRIPT" "$ORIGINAL_MATH_SCRIPT" # Backup for update test

  # 1a. Generate with different strength/temp
  log "1a. Testing 'generate' with different strength/temp"
  # Pass global options FIRST, then the command and its specific options/args
  run_pdd_command --strength 0.1 --temperature 0.0 generate --output "gen_low_str.py" "$PROMPTS_PATH/$MATH_PROMPT"
  check_exists "gen_low_str.py" "'generate' low strength output"
  run_pdd_command --strength $STRENGTH --temperature 1.5 generate --output "gen_high_temp.py" "$PROMPTS_PATH/$MATH_PROMPT"
  check_exists "gen_high_temp.py" "'generate' high temp output"

  # 1b. Generate with env var output path
  log "1b. Testing 'generate' with environment variable output path"
  ENV_OUT_DIR="env_out_generate"
  mkdir "$ENV_OUT_DIR"
  export PDD_GENERATE_OUTPUT_PATH="$ENV_OUT_DIR/" # Trailing slash indicates directory
  run_pdd_command generate "$PROMPTS_PATH/$MATH_PROMPT" # No --output
  # Default name is <basename>.<lang_ext> which should be simple_math.py
  check_exists "$ENV_OUT_DIR/$MATH_PROMPT" "'generate' output via env var" # Note: Check file name based on prompt name
  unset PDD_GENERATE_OUTPUT_PATH
fi

# 2. Example
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "2" ]; then
  log "2. Testing 'example' command"
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
  grep -q "Google" "$COMPLEX_PREPROCESSED" || (log_error "Preprocess failed: Web tag output missing (Google check)"; exit 1)
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
  check_exists "$CHANGE_CSV_OUT_DIR/modified_$DUMMY_PROMPT_A" "'change --csv' output A"
  check_exists "$CHANGE_CSV_OUT_DIR/modified_$DUMMY_PROMPT_B" "'change --csv' output B"
fi

# 6. Crash
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "6" ]; then
  log "6. Testing 'crash' command"
  # Make sure example program exists and is runnable first
  run_pdd_command example --output "$MATH_VERIFICATION_PROGRAM" "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT"
  log "Running example program before introducing error..."
  python "$MATH_VERIFICATION_PROGRAM" >> "$LOG_FILE" 2>&1
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
      # Run crash (non-loop)
      run_pdd_command crash --output "$CRASH_FIXED_SCRIPT" \
                            --output-program "$CRASH_FIXED_PROGRAM" \
                            "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" \
                            "$MATH_VERIFICATION_PROGRAM" "$MATH_ERROR_LOG"
      check_exists "$CRASH_FIXED_SCRIPT" "'crash' fixed script output"
      check_exists "$CRASH_FIXED_PROGRAM" "'crash' fixed program output"
      # Verify the fix
      log "Running the fixed program after 'crash' command"
      python "$CRASH_FIXED_PROGRAM" >> "$LOG_FILE" 2>&1
      if [ $? -eq 0 ]; then
          log "Fixed program ran successfully after crash command."
          log_timestamped "Validation success: Fixed program ran successfully after crash command."
          # Adopt fixed versions for subsequent tests
          cp "$CRASH_FIXED_SCRIPT" "$MATH_SCRIPT"
          cp "$CRASH_FIXED_PROGRAM" "$MATH_VERIFICATION_PROGRAM"
      else
          log_error "Fixed program still failed after crash command."
          log_timestamped "Validation failed: Fixed program still failed after crash command."
          exit 1 # Treat this as a failure
      fi
  fi

  # 6a. Crash with --loop (introduce different error)
  log "6a. Testing 'crash --loop'"
  log "Introducing different error for 'crash --loop'"
  # Intentionally cause NameError
  echo "import $MATH_BASENAME" > "$MATH_VERIFICATION_PROGRAM" # Overwrite
  echo "result = $MATH_BASENAME.multiply(5, 3)" >> "$MATH_VERIFICATION_PROGRAM" # Assume multiply doesn't exist
  echo "print(f'The product is: {result}')" >> "$MATH_VERIFICATION_PROGRAM"
  # Run modified program to generate error log
  log "Running modified example to generate error log for 'crash --loop'"
  python "$MATH_VERIFICATION_PROGRAM" > "${MATH_ERROR_LOG}_loop" 2>&1 || true # Allow failure

  if [ ! -s "${MATH_ERROR_LOG}_loop" ]; then
      log_error "Crash loop test error log is empty. Skipping 'crash --loop' command."
  else
      # Run crash --loop
      run_pdd_command_noexit crash --loop --max-attempts 2 --budget 5.0 \
                            --output "${CRASH_FIXED_SCRIPT}_loop" \
                            --output-program "${CRASH_FIXED_PROGRAM}_loop" \
                            "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" \
                            "$MATH_VERIFICATION_PROGRAM" "${MATH_ERROR_LOG}_loop"
      # Check if output exists (don't check runtime as fix might not succeed)
      if [ -f "${CRASH_FIXED_SCRIPT}_loop" ]; then
          log "Crash --loop produced an output script."
          # Optionally try running the output program and log result
          if [ -f "${CRASH_FIXED_PROGRAM}_loop" ]; then
               log "Running program fixed by crash --loop"
               python "${CRASH_FIXED_PROGRAM}_loop" >> "$LOG_FILE" 2>&1 || log "Program fixed by crash --loop failed to run (non-fatal)."
          fi
          # Adopt latest fixed versions if produced
          cp "${CRASH_FIXED_SCRIPT}_loop" "$MATH_SCRIPT"
          if [ -f "${CRASH_FIXED_PROGRAM}_loop" ]; then
             cp "${CRASH_FIXED_PROGRAM}_loop" "$MATH_VERIFICATION_PROGRAM"
          fi
      else
          log "Crash --loop did not produce an output script (might be expected if unfixable)."
      fi
  fi
fi

# 7. Verify (using isolated harness)
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "7" ]; then
  log "7. Testing 'verify' command"
  if [ ! -f "$VERIFY_SCRIPT_PATH" ]; then
      log_error "Verification harness script not found at $VERIFY_SCRIPT_PATH. Skipping 'verify' test."
  else
      mkdir -p "$VERIFY_ISOLATED_DIR"
      log "Running isolated verification harness"
      python "$VERIFY_SCRIPT_PATH" \
          --prompt-file "$PROMPTS_PATH/$MATH_PROMPT" \
          --code-file "$MATH_SCRIPT" \
          --program-file "$MATH_VERIFICATION_PROGRAM" \
          --output-results "$VERIFY_RESULTS_LOG" \
          --output-code "$VERIFY_CODE_OUTPUT" \
          --output-dir "$VERIFY_ISOLATED_DIR" \
          --max-attempts 3 \
          --budget 5.0 \
          --strength $STRENGTH \
          --temperature $TEMPERATURE \
          --force \
          --verbose \
          ${TEST_LOCAL:+--local} \
          > "$VERIFY_HARNESS_LOG" 2>&1

      cat "$VERIFY_HARNESS_LOG" >> "$LOG_FILE"
      VERIFY_STATUS=$?
      if [ $VERIFY_STATUS -eq 0 ]; then
          log "Verification harness completed successfully."
          log_timestamped "Validation success: Verification harness completed successfully."
          check_exists "$VERIFY_CODE_OUTPUT" "'verify' output code"
          # Adopt verified code
          cp "$VERIFY_CODE_OUTPUT" "$MATH_SCRIPT"
          # Regenerate example program based on verified code
          run_pdd_command example --output "$VERIFY_EXAMPLE_OUTPUT" \
              "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT"
          check_exists "$VERIFY_EXAMPLE_OUTPUT" "'example' from verified code"
          cp "$VERIFY_EXAMPLE_OUTPUT" "$MATH_VERIFICATION_PROGRAM"
          log "Running example program generated from verified code"
          python "$MATH_VERIFICATION_PROGRAM" >> "$LOG_FILE" 2>&1
          if [ $? -ne 0 ]; then
              log_error "Verified code example program failed."
              log_timestamped "Validation failed: Verified code example program failed."
              # Decide if this is fatal
          else
              log "Verified code example program ran successfully."
              log_timestamped "Validation success: Verified code example program ran successfully."
          fi
      else
          log_error "Verification harness failed with exit code $VERIFY_STATUS."
          log_timestamped "Validation failed: Verification harness failed with exit code $VERIFY_STATUS."
          # Decide if this is fatal
      fi
  fi
fi

# 8. Test
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "8" ]; then
  log "8. Testing 'test' command (initial generation)"
  run_pdd_command test --output "$MATH_TEST_SCRIPT" --language Python "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT"
  check_exists "$MATH_TEST_SCRIPT" "'test' initial output"

  # 8a. Test with coverage improvement
  log "8a. Testing 'test' with coverage improvement"
  # Run initial tests with coverage
  log "Running pytest with coverage..."
  TEST_CMD=(python -m pytest --cov="$MATH_SCRIPT" --cov-branch --cov-report=xml:"$COVERAGE_REPORT" "$MATH_TEST_SCRIPT")
  "${TEST_CMD[@]}" > "$PYTEST_LOG" 2>&1 || true # Allow failure
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
  # Rerun coverage generation on original tests
  "${TEST_CMD[@]}" > /dev/null 2>&1 || true
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

  # 8c. Test with env var output path
  log "8c. Testing 'test' with environment variable output path"
  ENV_OUT_DIR_TEST="env_out_test"
  mkdir "$ENV_OUT_DIR_TEST"
  export PDD_TEST_OUTPUT_PATH="$ENV_OUT_DIR_TEST/" # Trailing slash indicates directory
  run_pdd_command test "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" # No --output
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
      local adopted_fix=false
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
  # Get line number of 'def add' in the current script
  ADD_FUNC_LINE=$(grep -n "def add(" "$MATH_SCRIPT" | cut -d: -f1 | head -n 1)
  if [ -z "$ADD_FUNC_LINE" ]; then
      log "Warning: Could not find 'def add(' in $MATH_SCRIPT for 'trace' test. Using default line 3."
      ADD_FUNC_LINE=3
  fi
  log "Tracing line $ADD_FUNC_LINE in $MATH_SCRIPT"
  run_pdd_command trace --output "$TRACE_RESULTS_LOG" \
                        "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" "$ADD_FUNC_LINE"
  check_exists "$TRACE_RESULTS_LOG" "'trace' results log"
fi

# 14. Bug
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "14" ]; then
  log "14. Testing 'bug' command"
  log "Ensuring verification program is runnable for 'bug' test"
  run_pdd_command example --output "$MATH_VERIFICATION_PROGRAM" "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT"
  log "Generating current output for 'bug' command"
  python "$MATH_VERIFICATION_PROGRAM" > "current_output.txt" 2>&1
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
  # Modify timestamp of CSV to check if scan happens
  touch -m -d "2 hours ago" "$AUTO_DEPS_CSV"
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
  run_pdd_expect_fail trace --output "invalid_trace.log" "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" 99999
  # Provide non-existent error file to fix
  run_pdd_expect_fail fix --output-test "err_test.py" --output-code "err_code.py" "$PROMPTS_PATH/$MATH_PROMPT" "$MATH_SCRIPT" "$MATH_TEST_SCRIPT" "nonexistent/error.log"
fi

# --- Final Summary ---
log_timestamped "======== Regression Tests Completed (Target: $TARGET_TEST) ========"
log "----------------------------------------"
log "All tests completed."
log "Log file: $(pwd)/$LOG_FILE"
log "Cost file: $(pwd)/$COST_FILE"

# Display total cost
if [ -f "$COST_FILE" ]; then
    # Robust awk command to handle potential missing cost values or headers
    total_cost=$(awk -F',' 'NR > 1 && NF >= 4 && $4 ~ /^[0-9]+(\.[0-9]+)?$/ { sum += $4 } END { printf "%.6f", sum }' "$COST_FILE")
    log "Total estimated cost of all operations: $total_cost USD"
    log_timestamped "Total estimated cost of all operations: $total_cost USD"
else
    log "Cost file not found or invalid. Unable to calculate total cost."
    log_timestamped "Cost file not found or invalid. Unable to calculate total cost."
fi

cd .. # Go back to original directory if needed

exit 0 # Ensure script exits successfully if all steps pass