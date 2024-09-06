#!/bin/bash

# Define variables for commonly used paths
STAGING_PATH="$PDD_PATH/staging"
PDD_SCRIPT="pdd"
PROMPTS_PATH="$PDD_PATH/prompts"
CONTEXT_PATH="$PDD_PATH/context"
LOG_FILE="regression.log"
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
SPLIT_EXAMPLE_SCRIPT="construct_paths_example.py"

# Enable verbose output (1 for true, 0 for false)
VERBOSE=1

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
    log "Running: $PDD_SCRIPT --output-cost $COST_FILE $command $args"
    $PDD_SCRIPT --output-cost $COST_FILE $command $args >> "$LOG_FILE" 2>&1
    if [ $? -eq 0 ]; then
        log "Command completed successfully."
        log_timestamped "Command: $PDD_SCRIPT --output-cost $COST_FILE $command $args - Completed successfully."
    else
        log "Command failed."
        log_timestamped "Command: $PDD_SCRIPT --output-cost $COST_FILE $command $args - Failed."
        exit 1
    fi
    log "----------------------------------------"
}

# Create and navigate to the regression test directory
log "Creating and entering regression test directory"
mkdir -p "$STAGING_PATH/regression"
cd "$STAGING_PATH/regression" || { log "Failed to enter regression directory"; exit 1; }
log "Current directory: $(pwd)"
log "----------------------------------------"

# Run regression tests
log "Running regression tests"
run_pdd_command generate --output "$EXTENSION_SCRIPT" "$PROMPTS_PATH/$EXTENSION_PROMPT"
run_pdd_command example --output  "$EXTENSION_VERIFICATION_PROGRAM"  "$PROMPTS_PATH/$EXTENSION_PROMPT" "$EXTENSION_SCRIPT"
run_pdd_command test --output "$EXTENSION_TEST" "$PROMPTS_PATH/$EXTENSION_PROMPT" "$EXTENSION_SCRIPT"
run_pdd_command preprocess --output "preprocessed_$EXTENSION_PROMPT" "$PROMPTS_PATH/$EXTENSION_PROMPT"
run_pdd_command preprocess --xml --output "$XML_OUTPUT_PROMPT" "$PROMPTS_PATH/$EXTENSION_PROMPT"
run_pdd_command update --output "updated_$EXTENSION_PROMPT" "$PROMPTS_PATH/$EXTENSION_PROMPT" "$PDD_PATH/pdd/$EXTENSION_SCRIPT" "$EXTENSION_SCRIPT"

# Run change command
log "Running change command"
run_pdd_command change --output "changed_$CHANGE_PROMPT" \
                       "$CONTEXT_PATH/change/11/$CHANGE_PROMPT" \
                       "$CONTEXT_PATH/change/11/$CHANGE_SCRIPT" \
                       "$CONTEXT_PATH/change/11/$CHANGE_CONTEXT_PROMPT"

# Run fix commands
log "Running fix commands"
python -m pytest $EXTENSION_TEST > pytest_output.log
run_pdd_command fix --output-test "fixed_$EXTENSION_TEST" --output-code "fixed_$EXTENSION_SCRIPT" \
                    "$PROMPTS_PATH/$EXTENSION_PROMPT" "$EXTENSION_SCRIPT" "$EXTENSION_TEST" pytest_output.log
run_pdd_command fix --loop --output-test "fixed_loop_$EXTENSION_TEST" --output-code "fixed_loop_$EXTENSION_SCRIPT" \
                    --verification-program "$EXTENSION_VERIFICATION_PROGRAM" --max-attempts 2 --budget 5.0 \
                    "$PROMPTS_PATH/$EXTENSION_PROMPT" "$EXTENSION_SCRIPT" "$EXTENSION_TEST" "$EXTENSION_ERROR_LOOP_LOG"

# Run split command
log "Running split command"
run_pdd_command split --output-sub "sub_$SPLIT_PROMPT" --output-modified "modified_$SPLIT_PROMPT" \
                      "$CONTEXT_PATH/split/4/$SPLIT_PROMPT" \
                      "$CONTEXT_PATH/split/4/$SPLIT_SCRIPT" \
                      "$CONTEXT_PATH/split/4/$SPLIT_EXAMPLE_SCRIPT"

# Run detect command
log "Running detect command"
run_pdd_command detect --output "detect_results.csv" \
                       "$PROMPTS_PATH/$EXTENSION_PROMPT" "$PROMPTS_PATH/$CHANGE_PROMPT" "$PROMPTS_PATH/$SPLIT_PROMPT" \
                       "$CONTEXT_PATH/change/11/$CHANGE_CONTEXT_PROMPT"

# Run conflicts command
log "Running conflicts command"
run_pdd_command conflicts --output "conflicts_analysis.csv" \
                          "$PROMPTS_PATH/$EXTENSION_PROMPT" "$PROMPTS_PATH/$CHANGE_PROMPT"

# Run crash command
log "Running crash command"
run_pdd_command crash --output "fixed_crash_$EXTENSION_SCRIPT" \
                      "$PROMPTS_PATH/$EXTENSION_PROMPT" "$EXTENSION_SCRIPT" \
                      "$EXTENSION_VERIFICATION_PROGRAM" "$EXTENSION_ERROR_LOG"

log "Regression tests completed. Check regression.log for detailed results."
log_timestamped "Regression tests completed."

# Display total cost
if [ -f "$COST_FILE" ]; then
    total_cost=$(awk -F',' '{sum += $4} END {print sum}' "$COST_FILE")
    log "Total cost of all operations: $total_cost"
    log_timestamped "Total cost of all operations: $total_cost"
else
    log "Cost file not found. Unable to calculate total cost."
    log_timestamped "Cost file not found. Unable to calculate total cost."
fi