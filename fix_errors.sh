# Here's a Bash script named `fix_errors.sh` that implements the specified functionality. This script will run unit tests, capture errors, and use the PDD CLI to fix the code and tests iteratively until the specified limit is reached.

# ```bash
#!/bin/bash

# fix_errors.sh
# A script to fix errors in unit tests and code files using PDD CLI.

# Function to pretty print messages
pretty_print() {
    echo -e "\033[1;34m$1\033[0m"  # Blue color for messages
}

# Check for the correct number of arguments
if [ "$#" -ne 3 ]; then
    echo "Usage: $0 <unit_test_file> <code_file> <max_attempts>"
    exit 1
fi

UNIT_TEST_FILE="$1"
CODE_FILE="$2"
MAX_ATTEMPTS="$3"
ATTEMPT=0

# Loop until the maximum attempts are reached
while [ "$ATTEMPT" -lt "$MAX_ATTEMPTS" ]; do
    pretty_print "Running unit tests..."
    
    # Step 1: Run the unit test file and capture output
    python -m unittest -v "$UNIT_TEST_FILE" > error.log 2>&1
    TEST_RESULT=$?

    # If the test passes, exit the loop
    if [ $TEST_RESULT -eq 0 ]; then
        pretty_print "All tests passed successfully!"
        exit 0
    fi

    # Step 2: Print out the error message from error.log
    pretty_print "Tests failed. Here are the error messages:"
    cat error.log

    # Step 3: Run the PDD fix command
    pretty_print "Attempting to fix errors using PDD..."
    python staging/pdd/pdd.py --strength .9 fix --output-test "$UNIT_TEST_FILE" --output-code "$CODE_FILE" "$UNIT_TEST_FILE" "$CODE_FILE" error.log

    # Increment the attempt counter
    ATTEMPT=$((ATTEMPT + 1))
    pretty_print "Attempt $ATTEMPT of $MAX_ATTEMPTS completed."
done

pretty_print "Maximum attempts reached. Please check the error.log for details."
exit 1
# ```

# ### Explanation of the Script:

# 1. **Function Definition**: A `pretty_print` function is defined to format console output in blue for better readability.

# 2. **Argument Check**: The script checks if exactly three arguments are provided. If not, it prints usage instructions and exits.

# 3. **Loop for Attempts**: The script enters a loop that will run until the maximum number of attempts is reached.

# 4. **Running Unit Tests**: It runs the unit tests using `python -m unittest` and captures the output in `error.log`. The exit status is checked to determine if the tests passed.

# 5. **Error Handling**: If the tests fail, it prints the error messages from `error.log`.

# 6. **Fixing Errors**: The script calls the PDD CLI to fix the errors in the unit test and code files, using the error log as input.

# 7. **Attempt Counter**: The attempt counter is incremented after each iteration, and the loop continues until the maximum attempts are reached.

# 8. **Completion Message**: If the maximum attempts are reached without passing the tests, a message is printed to inform the user.

# ### Usage:
# To use the script, make it executable and run it with the required arguments:
# ```bash
# chmod +x fix_errors.sh
# ./fix_errors.sh <unit_test_file> <code_file> <max_attempts>
# ```

# Replace `<unit_test_file>`, `<code_file>`, and `<max_attempts>` with the appropriate values.