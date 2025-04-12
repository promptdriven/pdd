#!/bin/bash

# Check if the module argument is provided
if [ -z "$1" ]; then
  echo "Error: Please provide a module name as an argument."
  exit 1
fi

MODULE=$1
CSV_FILE="prompts/io_dependencies.csv"

# Step 1: Look up the path from the CSV file
echo "Looking up the path for module: $MODULE..."
# Use awk to find the line where the first field exactly matches "module_name.py"
# or ends with "/module_name.py\""
PATH_COLUMN=$(awk -F',' -v mod=""$MODULE.py"" -v suffix="/$MODULE.py\"" '
    $1 == mod {print $1; exit}
    substr($1, length($1)-length(suffix)+1) == suffix {print $1; exit}
' "$CSV_FILE")

# Check if the path was found
if [ -z "$PATH_COLUMN" ]; then
  echo "Error: Module '$MODULE' not found in the CSV file."
  exit 1
fi

# Step 2: Remove double quotes from the path
PATH_COLUMN=$(echo "$PATH_COLUMN" | tr -d '"')
echo "Found path: $PATH_COLUMN"

# Extract the directory part from the path
DIR_PATH=$(dirname "$PATH_COLUMN")
echo "Directory path: $DIR_PATH"

# Step 3: Generate code from the prompt
echo "Generating code for module: $MODULE..."
pdd --strength .865 --temperature 0 generate --output "$PATH_COLUMN" "prompts/${MODULE}_python.prompt"

# Step 4: Generate example code
echo "Generating example code for module: $MODULE..."
pdd --strength .85 --temperature 1 example --output context "prompts/${MODULE}_python.prompt" "$PATH_COLUMN"

# Step 5: Verify the generated code using the crash command
echo "Verifying the generated code for module: $MODULE..."
python context/${MODULE}_example.py >& crash_error.log
pdd --strength .85 --temperature 1 crash --loop --output "$PATH_COLUMN" --output-program context/${MODULE}_example.py "prompts/${MODULE}_python.prompt" "$PATH_COLUMN" context/${MODULE}_example.py crash_error.log

# Step 6: Generate unit tests
echo "Generating unit tests for module: $MODULE..."
pdd --strength .85 --temperature 1 --verbose test --output backend/tests "prompts/${MODULE}_python.prompt" "$PATH_COLUMN"

# Step 7: Fix any issues in the code and tests
echo "Fixing any issues in the code and tests for module: $MODULE..."

pdd --verbose --strength .85 --verbose --temperature 1 fix --auto-submit --loop --output-test backend/tests/test_${MODULE}.py --output-code "$PATH_COLUMN" --verification-program context/${MODULE}_example.py --max-attempts 5 "prompts/${MODULE}_python.prompt" "$PATH_COLUMN" backend/tests/test_${MODULE}.py fix_error.log

# Step 8: Print success message
echo "All commands executed successfully for module: $MODULE!"