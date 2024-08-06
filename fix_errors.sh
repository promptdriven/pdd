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
CUMULATIVE_LOG="cumulative_error.log"

# Clear the cumulative log at the start
> "$CUMULATIVE_LOG"

# Loop until the maximum attempts are reached
while [ "$ATTEMPT" -lt "$MAX_ATTEMPTS" ]; do
    pretty_print "Running unit tests..."
    
    # Step 1: Run the unit test file and capture output
    echo "==================== ATTEMPT $((ATTEMPT + 1)) - PYTEST OUTPUT ====================" >> "$CUMULATIVE_LOG"
    python -m pytest -v "$UNIT_TEST_FILE" >> "$CUMULATIVE_LOG" 2>&1
    TEST_RESULT=$?
    echo "" >> "$CUMULATIVE_LOG"  # Add a blank line for readability
    
    # If the test passes, exit the loop
    if [ $TEST_RESULT -eq 0 ]; then
        pretty_print "All tests passed successfully!"
        exit 0
    fi
    
    # Step 2: Print out the error message from the cumulative log
    pretty_print "Tests failed. Here are the error messages:"
    tail -n +$(grep -n "ATTEMPT $((ATTEMPT + 1)) - PYTEST OUTPUT" "$CUMULATIVE_LOG" | cut -d: -f1) "$CUMULATIVE_LOG"
    
    # Step 3: Run the PDD fix command
    pretty_print "Attempting to fix errors using PDD..."
    echo "==================== ATTEMPT $((ATTEMPT + 1)) - PDD OUTPUT ====================" >> "$CUMULATIVE_LOG"
    python staging/pdd/pdd.py --strength .9 fix --output-test "$UNIT_TEST_FILE" --output-code "$CODE_FILE" "$UNIT_TEST_FILE" "$CODE_FILE" "$CUMULATIVE_LOG" >> "$CUMULATIVE_LOG" 2>&1
    echo "" >> "$CUMULATIVE_LOG"  # Add a blank line for readability
    
    # Increment the attempt counter
    ATTEMPT=$((ATTEMPT + 1))
    pretty_print "Attempt $ATTEMPT of $MAX_ATTEMPTS completed."
done

pretty_print "Maximum attempts reached. Please check the cumulative_error.log for details."
exit 1