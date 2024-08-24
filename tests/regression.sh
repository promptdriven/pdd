#!/bin/bash

# Define variables for commonly used paths
STAGING_PATH="$PDD_PATH/staging"
PDD_SCRIPT="$STAGING_PATH/pdd/pdd.py"
PROMPTS_PATH="$PDD_PATH/prompts"
CONTEXT_PATH="$PDD_PATH/context"

# Function to run PDD command, print progress, and log output
run_pdd_command() {
    local command=$1
    local args="${@:2}"
    echo "Running: python $PDD_SCRIPT $command $args"
    python "$PDD_SCRIPT" $command $args >> regression.log
    echo "Command completed. Output logged to regression.log"
    echo "----------------------------------------"
}

# Create and navigate to the regression test directory
echo "Creating and entering regression test directory"
mkdir -p "$STAGING_PATH/tests/regression"
cd "$STAGING_PATH/tests/regression"
echo "Current directory: $(pwd)"
echo "----------------------------------------"

# Run regression tests
run_pdd_command generate "$PROMPTS_PATH/get_extension_python.prompt"
run_pdd_command example get_extension.py
run_pdd_command test get_extension.py "$PROMPTS_PATH/get_extension_python.prompt"
run_pdd_command preprocess "$PROMPTS_PATH/get_extension_python.prompt"
run_pdd_command preprocess --xml --output get_extension_python_xml.prompt "$PROMPTS_PATH/get_extension_python.prompt"
run_pdd_command update get_extension.py "$PROMPTS_PATH/get_extension_python.prompt" "$PDD_PATH/pdd/get_extension.py"

# Run change command
echo "Running change command"
run_pdd_command change "$CONTEXT_PATH/change/11/initial_code_generator_python.prompt" \
                       "$CONTEXT_PATH/change/11/initial_code_generator.py" \
                       "$CONTEXT_PATH/change/11/change.prompt"

# Run fix commands
echo "Running fix commands"
run_pdd_command fix test_get_extension.py get_extension.py error.log
run_pdd_command fix --loop --output-test test.py --output-code code.py \
                    --verification-program get_extension_example.py --max-attempts 2 \
                    test_get_extension.py get_extension.py error.log

# Run split command
echo "Running split command"
run_pdd_command split "$CONTEXT_PATH/split/4/initial_construct_paths_python.prompt" \
                      "$CONTEXT_PATH/split/4/construct_paths.py" \
                      "$CONTEXT_PATH/split/4/split_construct_paths_generate_output_filename.py"

echo "Regression tests completed. Check regression.log for detailed results."