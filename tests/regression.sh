#!/bin/bash

################################################################################
# regression.sh
#
# Comprehensive regression test script for the PDD (Prompt-Driven Development)
# Command Line Interface (CLI). This script executes all `pdd` commands to ensure
# their proper functionality. All output files are directed to the
# "$STAGING_PATH/regression" directory while the commands run in the current
# directory.
#
# Usage:
#   ./regression.sh
#
# Ensure that the following environment variables are set before running the script:
#   PDD_PATH - Base path where PDD resources are located.
#
################################################################################

# Exit immediately if a command exits with a non-zero status.
set -e

# ------------------------------ Configuration ----------------------------------

# Define variables for commonly used paths
STAGING_PATH="${PDD_PATH}/staging"
REGRESSION_DIR="${STAGING_PATH}/regression"
PDD_SCRIPT="pdd"
PROMPTS_PATH="${PDD_PATH}/prompts"
CONTEXT_PATH="${PDD_PATH}/context"
TESTS_DIR="${STAGING_PATH}/tests"
LOG_FILE="${REGRESSION_DIR}/regression.log"
COST_FILE="${REGRESSION_DIR}/regression_cost.csv"

# Define variables for commonly used filenames

# Example 1: Extension
EXTENSION_PROMPT="get_extension_python.prompt"
EXTENSION_SCRIPT="get_extension.py"
EXTENSION_TEST="test_get_extension.py"
EXTENSION_ERROR_LOG="${REGRESSION_DIR}/error.log"
EXTENSION_ERROR_LOOP_LOG="${REGRESSION_DIR}/error_loop.log"
EXTENSION_VERIFICATION_PROGRAM="${REGRESSION_DIR}/get_extension_example.py"
XML_OUTPUT_PROMPT="${REGRESSION_DIR}/get_extension_python_xml.prompt"

# Example 2: Change
CHANGE_PROMPT="initial_code_generator_python.prompt"
CHANGE_SCRIPT="initial_code_generator.py"
CHANGE_DESCRIPTION_PROMPT="change.prompt"
CHANGE_CONTEXT_PROMPT="${CONTEXT_PATH}/change/11/${CHANGE_PROMPT}"
CHANGE_DESCRIPTION_FILE="${CONTEXT_PATH}/change/11/${CHANGE_DESCRIPTION_PROMPT}"

# Example 3: Split
SPLIT_PROMPT="initial_construct_paths_python.prompt"
SPLIT_SCRIPT="construct_paths.py"
SPLIT_EXAMPLE_SCRIPT="split_construct_paths_generate_output_filename.py"

# Example 4: Trace
TRACE_PROMPT="factorial_calculator_python.prompt"
TRACE_SCRIPT="src/factorial_calculator.py"
TRACE_LINE=10  # Example line number

# Example 5: Bug
BUG_PROMPT="bug_report_python.prompt"
BUG_SCRIPT="buggy_script.py"
BUG_PROGRAM="run_buggy_program.py"
CURRENT_OUTPUT="Incorrect output"
DESIRED_OUTPUT="Correct output"

# General Variables
VERBOSE=1

# ------------------------------ Functions ---------------------------------------

# Function to print messages if verbose is enabled
log() {
    if [ "$VERBOSE" -eq 1 ]; then
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
    shift
    local args=("$@")

    log "Running: $PDD_SCRIPT ${GLOBAL_OPTIONS[*]} $command ${args[*]}"
    echo "Running: $PDD_SCRIPT ${GLOBAL_OPTIONS[*]} $command ${args[*]}" >> "$LOG_FILE"
    
    # Execute the pdd command
    $PDD_SCRIPT "${GLOBAL_OPTIONS[@]}" "$command" "${args[@]}" >> "$LOG_FILE" 2>&1

    if [ $? -eq 0 ]; then
        log "Command '$command' completed successfully."
        log_timestamped "Command: $PDD_SCRIPT ${GLOBAL_OPTIONS[*]} $command ${args[*]} - Completed successfully."
    else
        log "Command '$command' failed. Check $LOG_FILE for details."
        log_timestamped "Command: $PDD_SCRIPT ${GLOBAL_OPTIONS[*]} $command ${args[*]} - Failed."
        exit 1
    fi
    log "----------------------------------------" >> "$LOG_FILE"
}

# ------------------------------ Setup ------------------------------------------

# Create the regression test directory
log "Creating regression test directory at $REGRESSION_DIR"
mkdir -p "$REGRESSION_DIR"

# Initialize log file
echo "Regression Test Log - $(date)" > "$LOG_FILE"
echo "----------------------------------------" >> "$LOG_FILE"

# Initialize cost file header if it doesn't exist
if [ ! -f "$COST_FILE" ]; then
    echo "timestamp,model,command,cost,input_files,output_files" > "$COST_FILE"
fi

# ------------------------------ Environment -------------------------------------

# Define global options for pdd commands
GLOBAL_OPTIONS=(
    "--force"                 # Overwrite existing files without confirmation
    "--strength" "0.7"        # Example strength value
    "--temperature" "0.3"     # Example temperature value
    "--verbose"               # Increase verbosity
    "--output-cost" "$COST_FILE"  # Enable cost tracking
)

# ------------------------------ Regression Tests -------------------------------

# Run regression tests for all PDD commands

# 1. Generate
log "Running 'generate' command"
run_pdd_command generate --output "${REGRESSION_DIR}/${EXTENSION_SCRIPT}" "${PROMPTS_PATH}/${EXTENSION_PROMPT}"

# 2. Example
log "Running 'example' command"
run_pdd_command example --output "${EXTENSION_VERIFICATION_PROGRAM}" "${PROMPTS_PATH}/${EXTENSION_PROMPT}" "${REGRESSION_DIR}/${EXTENSION_SCRIPT}"

# 3. Test
log "Running 'test' command"
run_pdd_command test --output "${REGRESSION_DIR}/${EXTENSION_TEST}" "${PROMPTS_PATH}/${EXTENSION_PROMPT}" "${REGRESSION_DIR}/${EXTENSION_SCRIPT}"

# 4. Preprocess
log "Running 'preprocess' command"
run_pdd_command preprocess --output "${REGRESSION_DIR}/preprocessed_${EXTENSION_PROMPT}" "${PROMPTS_PATH}/${EXTENSION_PROMPT}"

# 5. Preprocess with XML
log "Running 'preprocess' command with --xml option"
run_pdd_command preprocess --xml --output "${XML_OUTPUT_PROMPT}" "${PROMPTS_PATH}/${EXTENSION_PROMPT}"

# 6. Update
log "Running 'update' command"
run_pdd_command update --output "${REGRESSION_DIR}/updated_${EXTENSION_PROMPT}" "${PROMPTS_PATH}/${EXTENSION_PROMPT}" "${REGRESSION_DIR}/${EXTENSION_SCRIPT}" "${REGRESSION_DIR}/${EXTENSION_SCRIPT}"

# 7. Change
log "Running 'change' command"

# Ensure that the change description prompt exists
if [ ! -f "${CHANGE_DESCRIPTION_FILE}" ]; then
    log "Change description prompt file '${CHANGE_DESCRIPTION_FILE}' does not exist. Creating a default change prompt."
    echo "% Describe the changes to be applied to the 'initial_code_generator_python.prompt'." > "${CHANGE_DESCRIPTION_FILE}"
fi

run_pdd_command change --output "${REGRESSION_DIR}/changed_${CHANGE_PROMPT}" \
                       "${CHANGE_CONTEXT_PROMPT}" \
                       "${CONTEXT_PATH}/change/11/${CHANGE_SCRIPT}" \
                       "${CHANGE_DESCRIPTION_FILE}"

# 8. Fix
log "Running 'fix' command"
# Assuming pytest is set up correctly
python -m pytest "${REGRESSION_DIR}/${EXTENSION_TEST}" > "${REGRESSION_DIR}/pytest_output.log" || true
run_pdd_command fix --output-test "${REGRESSION_DIR}/fixed_${EXTENSION_TEST}" \
                    --output-code "${REGRESSION_DIR}/fixed_${EXTENSION_SCRIPT}" \
                    "${PROMPTS_PATH}/${EXTENSION_PROMPT}" "${REGRESSION_DIR}/${EXTENSION_SCRIPT}" "${REGRESSION_DIR}/${EXTENSION_TEST}" "${REGRESSION_DIR}/pytest_output.log"

# 9. Fix with Loop
log "Running 'fix' command with --loop option"
run_pdd_command fix --loop \
                    --output-test "${REGRESSION_DIR}/fixed_loop_${EXTENSION_TEST}" \
                    --output-code "${REGRESSION_DIR}/fixed_loop_${EXTENSION_SCRIPT}" \
                    --output-results "${REGRESSION_DIR}/fixed_loop_results.log" \
                    --verification-program "${EXTENSION_VERIFICATION_PROGRAM}" \
                    --max-attempts 2 \
                    --budget 5.0 \
                    "${PROMPTS_PATH}/${EXTENSION_PROMPT}" "${REGRESSION_DIR}/${EXTENSION_SCRIPT}" "${REGRESSION_DIR}/${EXTENSION_TEST}" "${REGRESSION_DIR}/fix_loop_error.log"

# 10. Split
log "Running 'split' command"
run_pdd_command split --output-sub "${REGRESSION_DIR}/sub_${SPLIT_PROMPT}" \
                      --output-modified "${REGRESSION_DIR}/modified_${SPLIT_PROMPT}" \
                      "${CONTEXT_PATH}/split/4/${SPLIT_PROMPT}" \
                      "${CONTEXT_PATH}/split/4/${SPLIT_SCRIPT}" \
                      "${CONTEXT_PATH}/split/4/${SPLIT_EXAMPLE_SCRIPT}"

# 11. Detect
log "Running 'detect' command"
run_pdd_command detect --output "${REGRESSION_DIR}/detect_results.csv" \
                       "${PROMPTS_PATH}/${EXTENSION_PROMPT}" \
                       "${CONTEXT_PATH}/change/11/${CHANGE_PROMPT}" \
                       "${CONTEXT_PATH}/split/4/${SPLIT_PROMPT}" \
                       "${CHANGE_DESCRIPTION_FILE}"

# 12. Conflicts
log "Running 'conflicts' command"
run_pdd_command conflicts --output "${REGRESSION_DIR}/conflicts_analysis.csv" \
                          "${PROMPTS_PATH}/${EXTENSION_PROMPT}" \
                          "${CONTEXT_PATH}/change/11/${CHANGE_PROMPT}"

# 13. Crash
log "Running 'crash' command"
# Simulate a crash by running a faulty program
python "${EXTENSION_VERIFICATION_PROGRAM}" >& "${EXTENSION_ERROR_LOG}" || true
run_pdd_command crash --output "${REGRESSION_DIR}/fixed_crash_${EXTENSION_SCRIPT}" \
                      "${PROMPTS_PATH}/${EXTENSION_PROMPT}" \
                      "${REGRESSION_DIR}/${EXTENSION_SCRIPT}" \
                      "${TRACE_PROGRAM}" \
                      "${EXTENSION_ERROR_LOG}"

# 14. Trace
log "Running 'trace' command"
run_pdd_command trace --output "${REGRESSION_DIR}/trace_results.log" \
                      "${PROMPTS_PATH}/${TRACE_PROMPT}" \
                      "${REGRESSION_DIR}/${TRACE_SCRIPT}" \
                      "${TRACE_LINE}"

# 15. Bug
log "Running 'bug' command"
run_pdd_command bug --output "${REGRESSION_DIR}/test_${BUG_PROMPT}" \
                   "${PROMPTS_PATH}/${BUG_PROMPT}" \
                   "${REGRESSION_DIR}/${BUG_SCRIPT}" \
                   "${REGRESSION_DIR}/${BUG_PROGRAM}" \
                   "${CURRENT_OUTPUT}" \
                   "${DESIRED_OUTPUT}"

# ------------------------------ Completion -------------------------------------

log "Regression tests completed. Check ${LOG_FILE} for detailed results."
log_timestamped "Regression tests completed."

# Display total cost
if [ -f "$COST_FILE" ]; then
    total_cost=$(awk -F',' 'NR>1 {sum += $4} END {printf "%.2f", sum}' "$COST_FILE")
    log "Total cost of all operations: \$${total_cost}"
    log_timestamped "Total cost of all operations: \$${total_cost}"
else
    log "Cost file not found. Unable to calculate total cost."
    log_timestamped "Cost file not found. Unable to calculate total cost."
fi
