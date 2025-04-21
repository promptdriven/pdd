#!/bin/bash

# Set PDD_AUTO_UPDATE to false
export PDD_AUTO_UPDATE=false

# Define variables for commonly used paths
STAGING_PATH="$PDD_PATH/../staging"
PDD_SCRIPT="pdd"
PROMPTS_PATH="$PDD_PATH/../prompts"
CONTEXT_PATH="$PDD_PATH/../context"
CONTEXT_PATH_GLOB="$CONTEXT_PATH/*.py"
LOG_FILE="$STAGING_PATH/regression/regression.log"
COST_FILE="regression_cost.csv"

# Define variables for commonly used filenames
EXTENSION_PROMPT="get_extension_python.prompt"
EXTENSION_SCRIPT="get_extension.py"
EXTENSION_TEST="test_get_extension.py"
EXTENSION_ERROR_LOG="error.log"
EXTENSION_ERROR_LOOP_LOG="error_loop.log"
EXTENSION_VERIFICATION_PROGRAM="get_extension_example.py"
XML_OUTPUT_PROMPT="get_extension_python_xml.prompt"

CHANGE_PROMPT="initial_code_generator_python.prompt"
CHANGE_SCRIPT="initial_code_generator.py"
CHANGE_CONTEXT_PROMPT="change.prompt"

SPLIT_PROMPT="initial_construct_paths_python.prompt"
SPLIT_SCRIPT="construct_paths.py"
SPLIT_EXAMPLE_SCRIPT="split_construct_paths_generate_output_filename.py"

# New filenames for verify workflow
VERIFY_RESULTS_LOG="verify_results.log"
VERIFY_CODE_OUTPUT="verified_$EXTENSION_SCRIPT"
VERIFY_EXAMPLE_OUTPUT="verified_$EXTENSION_VERIFICATION_PROGRAM"

# Enable verbose output (1 for true, 0 for false)
VERBOSE=1

# Set the strength variable
STRENGTH=0.85

# Set the temperature variable
TEMPERATURE=1

# Remove regression.log if it exists
if [ -f "$LOG_FILE" ]; then
    rm "$LOG_FILE"
fi

# Function to print messages if verbose is enabled
log() {
    if [ $VERBOSE -eq 1 ]; then
        echo "$1"
    fi
}

# Function to log timestamped entries
log_timestamped() {
    echo "[$(date +'%Y-%m-%d %H:%M:%S')] $1" >> "$LOG_FILE"
}

# Function to run PDD command, print progress, and log output
run_pdd_command() {
    local command=$1
    local args="${@:2}"
    local full_command="$PDD_SCRIPT --force --strength $STRENGTH --temperature $TEMPERATURE --output-cost $STAGING_PATH/regression/$COST_FILE $command $args"
    log_timestamped "----------------------------------------" # Separator before command start
    log_timestamped "Starting command: $full_command" # Log the command starting
    log "Running: $full_command"
    $full_command >> "$LOG_FILE" 2>&1
    if [ $? -eq 0 ]; then
        log "Command completed successfully."
        log_timestamped "Command: $full_command - Completed successfully."
    else
        log "Command failed."
        log_timestamped "Command: $full_command - Failed."
        exit 1
    fi
    # Removed separator from the end as it's now at the start
}

# Helper to run PDD command but NOT exit on failure (used for verify)
run_pdd_command_noexit() {
    local command=$1
    shift
    local args="$@"
    local full_command="$PDD_SCRIPT --force --strength $STRENGTH --temperature $TEMPERATURE --output-cost $STAGING_PATH/regression/$COST_FILE $command $args"
    log_timestamped "----------------------------------------"
    log_timestamped "Starting command (non-fatal): $full_command"
    log "Running (non-fatal): $full_command"
    $full_command >> "$LOG_FILE" 2>&1
    local status=$?
    if [ $status -eq 0 ]; then
        log "Command completed successfully."
        log_timestamped "Command: $full_command - Completed successfully."
    else
        log "Command failed, continuing."
        log_timestamped "Command: $full_command - Failed (continuing)."
    fi
    return $status
}

# Create regression test directory
log "Creating regression test directory"
mkdir -p "$STAGING_PATH/regression"
log "Current directory: $(pwd)"
log "----------------------------------------"

# Run regression tests
log "Running regression tests"

# Generate extension script from its prompt
run_pdd_command generate --output "$STAGING_PATH/regression/$EXTENSION_SCRIPT" "$PROMPTS_PATH/$EXTENSION_PROMPT"

# Backup the originally generated extension script for update comparison
cp "$STAGING_PATH/regression/$EXTENSION_SCRIPT" "$STAGING_PATH/regression/original_$EXTENSION_SCRIPT"

# Modify the extension script slightly to trigger an update (adding a print statement)
if [[ $(uname) == "Darwin" ]]; then
  sed -i '' '1i\\
print("Hello World")\\
' "$STAGING_PATH/regression/$EXTENSION_SCRIPT"
else
  sed -i '1i print("Hello World")\n' "$STAGING_PATH/regression/$EXTENSION_SCRIPT"
fi

# Continue with the rest of the regression test commands
run_pdd_command example --output  "$STAGING_PATH/regression/$EXTENSION_VERIFICATION_PROGRAM"  "$PROMPTS_PATH/$EXTENSION_PROMPT" "$STAGING_PATH/regression/$EXTENSION_SCRIPT"

# Create a wrapper module that imports from the local file
cat > "$STAGING_PATH/regression/pdd_wrapper.py" << 'EOF'
# Simple wrapper to import get_extension from the local directory
import os
import sys

# Get the absolute path of the directory containing this script
current_dir = os.path.dirname(os.path.abspath(__file__))

# Import the get_extension function from the local file
from get_extension import get_extension
EOF

# Modify the test file to use the wrapper instead of importing from pdd package
if [[ $(uname) == "Darwin" ]]; then
  # macOS sed syntax
  sed -i '' 's/from pdd.get_extension import get_extension/from pdd_wrapper import get_extension/' "$STAGING_PATH/regression/$EXTENSION_TEST"
else
  # Linux/GNU sed syntax
  sed -i 's/from pdd.get_extension import get_extension/from pdd_wrapper import get_extension/' "$STAGING_PATH/regression/$EXTENSION_TEST"
fi

run_pdd_command preprocess --output "$STAGING_PATH/regression/preprocessed_$EXTENSION_PROMPT" "$PROMPTS_PATH/$EXTENSION_PROMPT"
run_pdd_command preprocess --xml --output "$STAGING_PATH/regression/$XML_OUTPUT_PROMPT" "$PROMPTS_PATH/$EXTENSION_PROMPT"

# Updated update command now uses both the modified and original version of the extension script
run_pdd_command update --output "$STAGING_PATH/regression/updated_$EXTENSION_PROMPT" "$PROMPTS_PATH/$EXTENSION_PROMPT" "$STAGING_PATH/regression/$EXTENSION_SCRIPT" "$STAGING_PATH/regression/original_$EXTENSION_SCRIPT"

# Run change command
log "Running change command"
run_pdd_command change --output "$STAGING_PATH/regression/changed_$CHANGE_PROMPT" \
                       "$CONTEXT_PATH/change/11/$CHANGE_PROMPT" \
                       "$CONTEXT_PATH/change/11/$CHANGE_SCRIPT" \
                       "$CONTEXT_PATH/change/11/$CHANGE_CONTEXT_PROMPT"

# Run crash command
log "Running crash command"
python "$STAGING_PATH/regression/$EXTENSION_VERIFICATION_PROGRAM" >& "$STAGING_PATH/regression/$EXTENSION_ERROR_LOG"
run_pdd_command crash --output "$STAGING_PATH/regression/fixed_crash_$EXTENSION_SCRIPT" \
                      --output-program "$STAGING_PATH/regression/fixed_crash_$EXTENSION_VERIFICATION_PROGRAM" \
                      "$PROMPTS_PATH/$EXTENSION_PROMPT" "$STAGING_PATH/regression/$EXTENSION_SCRIPT" \
                      "$STAGING_PATH/regression/$EXTENSION_VERIFICATION_PROGRAM" "$STAGING_PATH/regression/$EXTENSION_ERROR_LOG"

# If there are files (from output and/or output program) created by the crash command, use them for the fix command, otherwise, use the current files
if [ -f "$STAGING_PATH/regression/fixed_crash_$EXTENSION_SCRIPT" ]; then
    cp "$STAGING_PATH/regression/fixed_crash_$EXTENSION_SCRIPT" "$STAGING_PATH/regression/$EXTENSION_SCRIPT"
fi

if [ -f "$STAGING_PATH/regression/fixed_crash_$EXTENSION_VERIFICATION_PROGRAM" ]; then
    cp "$STAGING_PATH/regression/fixed_crash_$EXTENSION_VERIFICATION_PROGRAM" "$STAGING_PATH/regression/$EXTENSION_VERIFICATION_PROGRAM"
fi

# ---------------- Verify command using isolated harness ----------------
log "Running isolated verify command"

# Create isolated_verify directory if it doesn't exist
ISOLATED_DIR="$STAGING_PATH/regression/isolated_verify"
mkdir -p "$ISOLATED_DIR"

# Run the isolated verify harness
log "Running isolated verification with a custom harness that ensures code consistency"
log_timestamped "Starting isolated verification harness"

# Save the command output to a separate log file for easier debugging
VERIFY_HARNESS_LOG="$STAGING_PATH/regression/verify_harness.log"

python "$PDD_PATH/../tests/isolated_verify.py" \
    --prompt-file "$PROMPTS_PATH/$EXTENSION_PROMPT" \
    --code-file "$STAGING_PATH/regression/$EXTENSION_SCRIPT" \
    --program-file "$STAGING_PATH/regression/$EXTENSION_VERIFICATION_PROGRAM" \
    --output-results "$STAGING_PATH/regression/$VERIFY_RESULTS_LOG" \
    --output-code "$STAGING_PATH/regression/$VERIFY_CODE_OUTPUT" \
    --output-dir "$ISOLATED_DIR" \
    --max-attempts 3 \
    --budget 5.0 \
    --strength $STRENGTH \
    --temperature $TEMPERATURE \
    --force \
    --verbose \
    --keep-temp \
    > "$VERIFY_HARNESS_LOG" 2>&1

# Also add key information to the main log file
cat "$VERIFY_HARNESS_LOG" >> "$LOG_FILE"

VERIFY_STATUS=$?
if [ $VERIFY_STATUS -eq 0 ]; then
    log "Verification successful"
    log_timestamped "Verification successful"
else
    log "Verification failed with exit code $VERIFY_STATUS"
    log_timestamped "Verification failed with exit code $VERIFY_STATUS"
fi

# If verify produced a new code file, adopt it and regenerate example
if [ -f "$STAGING_PATH/regression/$VERIFY_CODE_OUTPUT" ]; then
    cp "$STAGING_PATH/regression/$VERIFY_CODE_OUTPUT" "$STAGING_PATH/regression/$EXTENSION_SCRIPT"
    run_pdd_command example --output "$STAGING_PATH/regression/$VERIFY_EXAMPLE_OUTPUT" \
        "$PROMPTS_PATH/$EXTENSION_PROMPT" "$STAGING_PATH/regression/$EXTENSION_SCRIPT"
    cp "$STAGING_PATH/regression/$VERIFY_EXAMPLE_OUTPUT" "$STAGING_PATH/regression/$EXTENSION_VERIFICATION_PROGRAM"
    
    log "Testing verified code with enhanced example program"
    # Verify that the example program works with the verified code
    python "$STAGING_PATH/regression/$EXTENSION_VERIFICATION_PROGRAM" > "$STAGING_PATH/regression/verification_test_output.log" 2>&1
    if [ $? -ne 0 ]; then
        log "Warning: Verified code example program failed. Check verification_test_output.log"
        log_timestamped "Warning: Verified code example program failed."
    else
        log "Verified code example program ran successfully"
        log_timestamped "Verified code example program ran successfully."
    fi
fi

# Regenerate unit tests after verification to ensure they align with verified code
run_pdd_command test --output "$STAGING_PATH/regression/$EXTENSION_TEST" "$PROMPTS_PATH/$EXTENSION_PROMPT" "$STAGING_PATH/regression/$EXTENSION_SCRIPT"

# Update regenerated test to use local wrapper instead of pdd package
if [[ $(uname) == "Darwin" ]]; then
  sed -i '' 's/from pdd.get_extension import get_extension/from pdd_wrapper import get_extension/' "$STAGING_PATH/regression/$EXTENSION_TEST"
else
  sed -i 's/from pdd.get_extension import get_extension/from pdd_wrapper import get_extension/' "$STAGING_PATH/regression/$EXTENSION_TEST"
fi

# Run fix commands
log "Running fix commands"
python -m pytest "$STAGING_PATH/regression/$EXTENSION_TEST" > "$STAGING_PATH/regression/pytest_output.log"
run_pdd_command fix --output-test "$STAGING_PATH/regression/fixed_$EXTENSION_TEST" --output-code "$STAGING_PATH/regression/fixed_$EXTENSION_SCRIPT"  --output-results "$STAGING_PATH/regression/get_extension_fix_results.log" \
                    "$PROMPTS_PATH/$EXTENSION_PROMPT" "$STAGING_PATH/regression/$EXTENSION_SCRIPT" "$STAGING_PATH/regression/$EXTENSION_TEST" "$STAGING_PATH/regression/pytest_output.log"

# Create a comprehensive standalone test file for the fix --loop command
log "Creating comprehensive standalone test for fix --loop"
STANDALONE_TEST="$STAGING_PATH/regression/standalone_test.py"

cat > "$STANDALONE_TEST" << 'EOF'
import pytest
import os
import sys
import importlib.util
from unittest.mock import patch, mock_open
from pathlib import Path

# Dynamically import the local get_extension.py file
def import_module_from_file(file_path):
    module_name = os.path.basename(file_path).replace('.py', '')
    spec = importlib.util.spec_from_file_location(module_name, file_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

# Get the directory of this script
current_dir = os.path.dirname(os.path.abspath(__file__))

# Import the local get_extension module
get_extension_module = import_module_from_file(os.path.join(current_dir, "get_extension.py"))
get_extension = get_extension_module.get_extension

class TestGetExtension:
    def test_empty_language(self):
        """Test that empty string input returns empty string."""
        assert get_extension("") == ""

    def test_none_language(self):
        """Test that None input returns empty string with error message."""
        # Expect empty string for None, matching how the verification program uses it
        result = get_extension(None)
        assert result == ""
            
    @patch.dict(os.environ, {"PDD_PATH": "/mock/path"})
    @patch("builtins.open", new_callable=mock_open, read_data="language,extension\nPython,.py\n")
    def test_valid_language(self, mock_file):
        """Test that a valid language returns the correct extension."""
        assert get_extension("Python") == ".py"

    @patch.dict(os.environ, {})
    def test_missing_env_variable(self):
        """Test behavior when PDD_PATH environment variable is missing."""
        # The exact behavior depends on your implementation
        result = get_extension("Python")
        assert isinstance(result, str)  # Should return some kind of string (probably empty)

    @patch("builtins.open", side_effect=FileNotFoundError)
    @patch.dict(os.environ, {"PDD_PATH": "/mock/path"})
    def test_file_not_found(self, mock_open):
        """Test behavior when CSV file is not found."""
        result = get_extension("Python")
        assert isinstance(result, str)  # Should return some kind of string (probably empty)
        
    def test_case_insensitivity(self):
        """Test that the function works with different case inputs."""
        # Mock environment and file operations
        with patch.dict(os.environ, {"PDD_PATH": "/mock/path"}):
            with patch("builtins.open", new_callable=mock_open, 
                      read_data="language,extension\nPython,.py\nJava,.java\n"):
                # Should be case-insensitive
                assert get_extension("python") == ".py"
                assert get_extension("JAVA") == ".java"
EOF

# Run fix command with loop using the standalone test
run_pdd_command fix --loop --output-test "$STAGING_PATH/regression/fixed_loop_$EXTENSION_TEST" --output-code "$STAGING_PATH/regression/fixed_loop_$EXTENSION_SCRIPT" \
                    --output-results "$STAGING_PATH/regression/fixed_loop_results.log" \
                    --verification-program "$STAGING_PATH/regression/$EXTENSION_VERIFICATION_PROGRAM" --max-attempts 2 --budget 5.0 \
                    "$PROMPTS_PATH/$EXTENSION_PROMPT" "$STAGING_PATH/regression/$EXTENSION_SCRIPT" "$STANDALONE_TEST" "$STAGING_PATH/regression/$EXTENSION_ERROR_LOOP_LOG"

# Run split command
log "Running split command"
run_pdd_command split --output-sub "$STAGING_PATH/regression/sub_$SPLIT_PROMPT" --output-modified "$STAGING_PATH/regression/modified_$SPLIT_PROMPT" \
                      "$CONTEXT_PATH/split/4/$SPLIT_PROMPT" \
                      "$CONTEXT_PATH/split/4/$SPLIT_SCRIPT" \
                      "$CONTEXT_PATH/split/4/$SPLIT_EXAMPLE_SCRIPT"

# Run detect command
log "Running detect command"
run_pdd_command detect --output "$STAGING_PATH/regression/detect_results.csv" \
                       "$PROMPTS_PATH/$EXTENSION_PROMPT" "$CONTEXT_PATH/change/11/$CHANGE_PROMPT" "$CONTEXT_PATH/split/4/$SPLIT_PROMPT" \
                       "$CONTEXT_PATH/change/11/$CHANGE_CONTEXT_PROMPT"

# Run conflicts command
log "Running conflicts command"
run_pdd_command conflicts --output "$STAGING_PATH/regression/conflicts_analysis.csv" \
                          "$PROMPTS_PATH/$EXTENSION_PROMPT" "$CONTEXT_PATH/change/11/$CHANGE_PROMPT"

# Run trace command
log "Running trace command"
run_pdd_command trace --output "$STAGING_PATH/regression/trace_results.log" \
                      "$PROMPTS_PATH/$EXTENSION_PROMPT" "$STAGING_PATH/regression/$EXTENSION_SCRIPT" 31

# Run bug command
log "Running bug command"
echo "The file extension for 'Python' is: '.py'" > "$STAGING_PATH/regression/current_output.txt"
echo "The file extension for 'Python' is: 'py'" > "$STAGING_PATH/regression/desired_output.txt"
run_pdd_command bug --output "$STAGING_PATH/regression/bug_$EXTENSION_TEST" \
                    "$PROMPTS_PATH/$EXTENSION_PROMPT" "$STAGING_PATH/regression/$EXTENSION_SCRIPT" \
                    "$STAGING_PATH/regression/$EXTENSION_VERIFICATION_PROGRAM" \
                    "$STAGING_PATH/regression/current_output.txt" "$STAGING_PATH/regression/desired_output.txt"

# Run auto-deps command
log "Running auto-deps command"
run_pdd_command auto-deps --output "$STAGING_PATH/regression/auto_deps_$EXTENSION_PROMPT" \
                          --csv "project_dependencies.csv" \
                          "$PROMPTS_PATH/$EXTENSION_PROMPT" \""$CONTEXT_PATH_GLOB"\"

log "Regression tests completed. Check regression.log for detailed results."
log_timestamped "Regression tests completed."

# Display total cost
if [ -f "$STAGING_PATH/regression/$COST_FILE" ]; then
    total_cost=$(awk -F',' '{sum += $4} END {print sum}' "$STAGING_PATH/regression/$COST_FILE")
    log "Total cost of all operations: $total_cost"
    log_timestamped "Total cost of all operations: $total_cost"
else
    log "Cost file not found. Unable to calculate total cost."
    log_timestamped "Cost file not found. Unable to calculate total cost."
fi