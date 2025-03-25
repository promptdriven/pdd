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
    log "Running: $PDD_SCRIPT --force --strength $STRENGTH --temperature $TEMPERATURE --output-cost $STAGING_PATH/regression/$COST_FILE $command $args"
    $PDD_SCRIPT --force --strength $STRENGTH --temperature $TEMPERATURE --output-cost $STAGING_PATH/regression/$COST_FILE $command $args >> "$LOG_FILE" 2>&1
    if [ $? -eq 0 ]; then
        log "Command completed successfully."
        log_timestamped "Command: $PDD_SCRIPT --force --strength $STRENGTH --temperature $TEMPERATURE --output-cost $STAGING_PATH/regression/$COST_FILE $command $args - Completed successfully."
    else
        log "Command failed."
        log_timestamped "Command: $PDD_SCRIPT --force --strength $STRENGTH --temperature $TEMPERATURE --output-cost $STAGING_PATH/regression/$COST_FILE $command $args - Failed."
        exit 1
    fi
    log "----------------------------------------"
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
  # macOS - BSD sed requires backslash after 'i' and newline before the text
  # Need to add the print and a blank line to ensure proper spacing
  sed -i '' '1i\
print("Hello World")\

' "$STAGING_PATH/regression/$EXTENSION_SCRIPT"
else
  # Linux/Others - GNU sed
  sed -i '1i print("Hello World")\n' "$STAGING_PATH/regression/$EXTENSION_SCRIPT"
fi

# Continue with the rest of the regression test commands
run_pdd_command example --output  "$STAGING_PATH/regression/$EXTENSION_VERIFICATION_PROGRAM"  "$PROMPTS_PATH/$EXTENSION_PROMPT" "$STAGING_PATH/regression/$EXTENSION_SCRIPT"
run_pdd_command test --output "$STAGING_PATH/regression/$EXTENSION_TEST" "$PROMPTS_PATH/$EXTENSION_PROMPT" "$STAGING_PATH/regression/$EXTENSION_SCRIPT"
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

# Run fix commands
log "Running fix commands"
python -m pytest "$STAGING_PATH/regression/$EXTENSION_TEST" > "$STAGING_PATH/regression/pytest_output.log"
run_pdd_command fix --output-test "$STAGING_PATH/regression/fixed_$EXTENSION_TEST" --output-code "$STAGING_PATH/regression/fixed_$EXTENSION_SCRIPT"  --output-results "$STAGING_PATH/regression/get_extension_fix_results.log" \
                    "$PROMPTS_PATH/$EXTENSION_PROMPT" "$STAGING_PATH/regression/$EXTENSION_SCRIPT" "$STAGING_PATH/regression/$EXTENSION_TEST" "$STAGING_PATH/regression/pytest_output.log"

# Run fix command with loop
run_pdd_command fix --loop --output-test "$STAGING_PATH/regression/fixed_loop_$EXTENSION_TEST" --output-code "$STAGING_PATH/regression/fixed_loop_$EXTENSION_SCRIPT" \
                    --output-results "$STAGING_PATH/regression/fixed_loop_results.log" \
                    --verification-program "$STAGING_PATH/regression/$EXTENSION_VERIFICATION_PROGRAM" --max-attempts 2 --budget 5.0 \
                    "$PROMPTS_PATH/$EXTENSION_PROMPT" "$STAGING_PATH/regression/$EXTENSION_SCRIPT" "$STAGING_PATH/regression/$EXTENSION_TEST" "$STAGING_PATH/regression/$EXTENSION_ERROR_LOOP_LOG"

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