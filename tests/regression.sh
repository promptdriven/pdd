#!/bin/bash
#
# regression.sh - Comprehensive regression script for pdd CLI
#
# This script exercises all major pdd CLI commands in a single automated run.
# It creates output in the $STAGING_PATH/regression directory but does NOT
# change the current directory. All commands are invoked with a fixed AI model
# strength (0.5) and temperature (0.0). Auto-updates are disabled.

###############################################################################
# Environment Setup
###############################################################################
export PDD_AUTO_UPDATE=false  # Disable auto-updates for regression testing
VERBOSE=1                     # Enable verbose logging: 1 (on), 0 (off)
PDD_SCRIPT="pdd"              # The pdd executable name

# Commonly used directories
STAGING_PATH="${PDD_PATH}/staging"
PROMPTS_PATH="${PDD_PATH}/prompts"
CONTEXT_PATH="${PDD_PATH}/context"

# Create the staging directory for regression output
mkdir -p "$STAGING_PATH/regression"

###############################################################################
# Variables for Filenames and Logging
###############################################################################
LOG_FILE="regression.log"
COST_FILE="regression_cost.csv"

# Primary test prompt files and their outputs
EXTENSION_PROMPT="get_extension_python.prompt"
EXTENSION_SCRIPT="get_extension.py"
EXTENSION_TEST="test_get_extension.py"
EXTENSION_VERIFICATION_PROGRAM="get_extension_example.py"
EXTENSION_ERROR_LOG="error.log"
EXTENSION_ERROR_LOOP_LOG="error_loop.log"
XML_OUTPUT_PROMPT="get_extension_python_xml.prompt"

# Change command prompt files
CHANGE_PROMPT="initial_code_generator_python.prompt"
CHANGE_SCRIPT="initial_code_generator.py"
CHANGE_CONTEXT_PROMPT="change.prompt"

# Split command prompt files
SPLIT_PROMPT="initial_construct_paths_python.prompt"
SPLIT_SCRIPT="construct_paths.py"
SPLIT_EXAMPLE_SCRIPT="split_construct_paths_generate_output_filename.py"

# Outputs for the "bug" command
CURRENT_OUTPUT="The extension is .tx"
DESIRED_OUTPUT="The extension is .txt"

###############################################################################
# Logging Functions
###############################################################################
log() {
    # Print messages if verbose is enabled
    if [ "$VERBOSE" -eq 1 ]; then
        echo "$1"
    fi
}

log_timestamped() {
    # Append timestamped entries to the regression log
    echo "[$(date +'%Y-%m-%d %H:%M:%S')] $1" >> "$LOG_FILE"
}

###############################################################################
# Function to Run pdd Commands with Uniform Options
###############################################################################
run_pdd_command() {
    local command=$1
    shift
    # Always use --strength=0.5 --temperature=0.0 and cost tracking
    local cmd="$PDD_SCRIPT --strength=0.5 --temperature=0.0 --force --output-cost $COST_FILE $command $*"

    log "Running: $cmd"
    $cmd >> "$LOG_FILE" 2>&1
    if [ $? -eq 0 ]; then
        log "Command completed successfully."
        log_timestamped "Command: $cmd - Completed successfully."
    else
        log "Command failed."
        log_timestamped "Command: $cmd - Failed."
        exit 1
    fi
    log "----------------------------------------"
}

###############################################################################
# Regression Tests
###############################################################################
log "Starting regression tests..."
log_timestamped "Regression tests started."

# 1) generate
run_pdd_command generate \
    --output "$STAGING_PATH/regression/$EXTENSION_SCRIPT" \
    "$PROMPTS_PATH/$EXTENSION_PROMPT"

# 2) example
run_pdd_command example \
    --output "$STAGING_PATH/regression/$EXTENSION_VERIFICATION_PROGRAM" \
    "$PROMPTS_PATH/$EXTENSION_PROMPT" \
    "$STAGING_PATH/regression/$EXTENSION_SCRIPT"

# 3) test
run_pdd_command test \
    --output "$STAGING_PATH/regression/$EXTENSION_TEST" \
    "$PROMPTS_PATH/$EXTENSION_PROMPT" \
    "$STAGING_PATH/regression/$EXTENSION_SCRIPT"

# 4) preprocess (no XML)
run_pdd_command preprocess \
    --output "$STAGING_PATH/regression/preprocessed_$EXTENSION_PROMPT" \
    "$PROMPTS_PATH/$EXTENSION_PROMPT"

# 5) preprocess with --xml
run_pdd_command preprocess \
    --xml \
    --output "$STAGING_PATH/regression/$XML_OUTPUT_PROMPT" \
    "$PROMPTS_PATH/$EXTENSION_PROMPT"

# 6) update
run_pdd_command update \
    --output "$STAGING_PATH/regression/updated_$EXTENSION_PROMPT" \
    "$PROMPTS_PATH/$EXTENSION_PROMPT" \
    "$PDD_PATH/pdd/$EXTENSION_SCRIPT" \
    "$STAGING_PATH/regression/$EXTENSION_SCRIPT"

# 7) change
run_pdd_command change \
    --output "$STAGING_PATH/regression/changed_$CHANGE_PROMPT" \
    "$CONTEXT_PATH/change/11/$CHANGE_PROMPT" \
    "$CONTEXT_PATH/change/11/$CHANGE_SCRIPT" \
    "$CONTEXT_PATH/change/11/$CHANGE_CONTEXT_PROMPT"

# 8) fix
python -m pytest "$STAGING_PATH/regression/$EXTENSION_TEST" > "$STAGING_PATH/regression/pytest_output.log"
run_pdd_command fix \
    --output-test "$STAGING_PATH/regression/fixed_$EXTENSION_TEST" \
    --output-code "$STAGING_PATH/regression/fixed_$EXTENSION_SCRIPT" \
    "$PROMPTS_PATH/$EXTENSION_PROMPT" \
    "$STAGING_PATH/regression/$EXTENSION_SCRIPT" \
    "$STAGING_PATH/regression/$EXTENSION_TEST" \
    "$STAGING_PATH/regression/pytest_output.log"

# 9) fix with --loop
run_pdd_command fix \
    --loop \
    --output-test "$STAGING_PATH/regression/fixed_loop_$EXTENSION_TEST" \
    --output-code "$STAGING_PATH/regression/fixed_loop_$EXTENSION_SCRIPT" \
    --output-results "$STAGING_PATH/regression/fixed_loop_results.log" \
    --verification-program "$STAGING_PATH/regression/$EXTENSION_VERIFICATION_PROGRAM" \
    --max-attempts 2 \
    --budget 5.0 \
    "$PROMPTS_PATH/$EXTENSION_PROMPT" \
    "$STAGING_PATH/regression/$EXTENSION_SCRIPT" \
    "$STAGING_PATH/regression/$EXTENSION_TEST" \
    "$STAGING_PATH/regression/$EXTENSION_ERROR_LOOP_LOG"

# 10) split
run_pdd_command split \
    --output-sub "$STAGING_PATH/regression/sub_$SPLIT_PROMPT" \
    --output-modified "$STAGING_PATH/regression/modified_$SPLIT_PROMPT" \
    "$CONTEXT_PATH/split/4/$SPLIT_PROMPT" \
    "$CONTEXT_PATH/split/4/$SPLIT_SCRIPT" \
    "$CONTEXT_PATH/split/4/$SPLIT_EXAMPLE_SCRIPT"

# 11) detect
run_pdd_command detect \
    --output "$STAGING_PATH/regression/detect_results.csv" \
    "$PROMPTS_PATH/$EXTENSION_PROMPT" \
    "$CONTEXT_PATH/change/11/$CHANGE_PROMPT" \
    "$CONTEXT_PATH/split/4/$SPLIT_PROMPT" \
    "$CONTEXT_PATH/change/11/$CHANGE_CONTEXT_PROMPT"

# 12) conflicts
run_pdd_command conflicts \
    --output "$STAGING_PATH/regression/conflicts_analysis.csv" \
    "$PROMPTS_PATH/$EXTENSION_PROMPT" \
    "$CONTEXT_PATH/change/11/$CHANGE_PROMPT"

# 13) crash
python "$STAGING_PATH/regression/$EXTENSION_VERIFICATION_PROGRAM" >& "$STAGING_PATH/regression/$EXTENSION_ERROR_LOG"
run_pdd_command crash \
    --output "$STAGING_PATH/regression/fixed_crash_$EXTENSION_SCRIPT" \
    "$PROMPTS_PATH/$EXTENSION_PROMPT" \
    "$STAGING_PATH/regression/$EXTENSION_SCRIPT" \
    "$STAGING_PATH/regression/$EXTENSION_VERIFICATION_PROGRAM" \
    "$STAGING_PATH/regression/$EXTENSION_ERROR_LOG"

# 14) trace
run_pdd_command trace \
    --output "$STAGING_PATH/regression/trace_results.log" \
    "$PROMPTS_PATH/$EXTENSION_PROMPT" \
    "$STAGING_PATH/regression/$EXTENSION_SCRIPT" \
    31

# 15) bug
run_pdd_command bug \
    --output "$STAGING_PATH/regression/bug_$EXTENSION_TEST" \
    "$PROMPTS_PATH/$EXTENSION_PROMPT" \
    "$STAGING_PATH/regression/$EXTENSION_SCRIPT" \
    "$STAGING_PATH/regression/$EXTENSION_VERIFICATION_PROGRAM" \
    "\"$CURRENT_OUTPUT\"" \
    "\"$DESIRED_OUTPUT\""

# 16) auto-deps
run_pdd_command auto-deps \
    --output "$STAGING_PATH/regression/auto_deps_$EXTENSION_PROMPT" \
    "$PROMPTS_PATH/$EXTENSION_PROMPT" \
    "$STAGING_PATH/regression"

log "Regression tests completed."
log_timestamped "Regression tests completed."

###############################################################################
# Display Total Cost
###############################################################################
if [ -f "$COST_FILE" ]; then
    total_cost=$(awk -F',' '{sum += $4} END {print sum}' "$COST_FILE")
    log "Total cost of all operations: $total_cost"
    log_timestamped "Total cost of all operations: $total_cost"
else
    log "Cost file not found. Unable to calculate total cost."
    log_timestamped "Cost file not found. Unable to calculate total cost."
fi

exit 0