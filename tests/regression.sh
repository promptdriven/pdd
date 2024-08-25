#!/bin/bash

# Define variables for commonly used paths
STAGING_PATH="$PDD_PATH/staging"
PDD_SCRIPT="pdd.cli"
PROMPTS_PATH="$PDD_PATH/prompts"
CONTEXT_PATH="$PDD_PATH/context"
LOG_FILE="regression.log"

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
SPLIT_OUTPUT_FILENAME="split_construct_paths_generate_output_filename.py"

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
    log "Running: python -m $PDD_SCRIPT $command $args"
    PYTHONPATH=$STAGING_PATH python -m "$PDD_SCRIPT" $command $args >> "$LOG_FILE" 2>&1
    if [ $? -eq 0 ]; then
        log "Command completed successfully."
        log_timestamped "Command: python -m $PDD_SCRIPT $command $args - Completed successfully."
    else
        log "Command failed."
        log_timestamped "Command: python -m $PDD_SCRIPT $command $args - Failed."
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
run_pdd_command generate "$PROMPTS_PATH/$EXTENSION_PROMPT"
run_pdd_command example "$EXTENSION_SCRIPT" "$PROMPTS_PATH/$EXTENSION_PROMPT"
run_pdd_command test "$EXTENSION_SCRIPT" "$PROMPTS_PATH/$EXTENSION_PROMPT"
run_pdd_command preprocess "$PROMPTS_PATH/$EXTENSION_PROMPT"
run_pdd_command preprocess --xml --output "$XML_OUTPUT_PROMPT" "$PROMPTS_PATH/$EXTENSION_PROMPT"
run_pdd_command update "$PROMPTS_PATH/$EXTENSION_PROMPT" "$PDD_PATH/pdd/$EXTENSION_SCRIPT" "$EXTENSION_SCRIPT"

# Run change command
log "Running change command"
run_pdd_command change "$CONTEXT_PATH/change/11/$CHANGE_PROMPT" \
                       "$CONTEXT_PATH/change/11/$CHANGE_SCRIPT" \
                       "$CONTEXT_PATH/change/11/$CHANGE_CONTEXT_PROMPT"

# Run fix commands
log "Running fix commands"
run_pdd_command fix "$EXTENSION_TEST" "$EXTENSION_SCRIPT" "$EXTENSION_ERROR_LOG"
run_pdd_command fix --loop --output-test test.py --output-code code.py \
                    --verification-program "$EXTENSION_VERIFICATION_PROGRAM" --max-attempts 2 \
                    "$EXTENSION_TEST" "$EXTENSION_SCRIPT" "$EXTENSION_ERROR_LOOP_LOG"

# Run split command
log "Running split command"
run_pdd_command split "$CONTEXT_PATH/split/4/$SPLIT_PROMPT" \
                      "$CONTEXT_PATH/split/4/$SPLIT_SCRIPT" \
                      "$CONTEXT_PATH/split/4/$SPLIT_OUTPUT_FILENAME"

log "Regression tests completed. Check regression.log for detailed results."
log_timestamped "Regression tests completed."