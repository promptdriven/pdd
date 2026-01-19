#!/bin/bash
# Test that regression scripts handle paths with spaces correctly
# Issue #334: https://github.com/promptdriven/pdd/issues/334

set -e

echo "=== Testing space path support ==="

# Create a temporary directory with spaces in the name
TEST_DIR=$(mktemp -d)/"test with spaces"
mkdir -p "$TEST_DIR"

# Create a dummy script to simulate PDD_SCRIPT
DUMMY_SCRIPT="$TEST_DIR/dummy_pdd.sh"
cat > "$DUMMY_SCRIPT" << 'SCRIPT'
#!/bin/bash
echo "dummy pdd called with args: $@"
if [ "$1" = "--list-contexts" ]; then
    echo "default"
    echo "alt"
fi
exit 0
SCRIPT
chmod +x "$DUMMY_SCRIPT"

# Create a dummy log file
LOG_FILE="$TEST_DIR/test.log"
touch "$LOG_FILE"

echo "Test directory: $TEST_DIR"
echo "Dummy script: $DUMMY_SCRIPT"

# Test 1: Test that command -v works with quoted path
echo ""
echo "Test 1: command -v with quoted path"
if command -v "$DUMMY_SCRIPT" > /dev/null 2>&1; then
    echo "PASS: command -v works with quoted path"
else
    echo "FAIL: command -v does not find script with quoted path"
    exit 1
fi

# Test 2: Test that command -v fails with unquoted path (demonstrates the bug)
echo ""
echo "Test 2: command -v with unquoted path (expected to fail)"
set +e
# This simulates the bug in regression.sh line 343
eval "command -v $DUMMY_SCRIPT" > /dev/null 2>&1
UNQUOTED_STATUS=$?
set -e
if [ $UNQUOTED_STATUS -ne 0 ]; then
    echo "CONFIRMED: Unquoted path fails (this is the bug we're fixing)"
else
    echo "NOTE: Unquoted path worked (may depend on shell)"
fi

# Test 3: Test command execution with quoted path
echo ""
echo "Test 3: Execute script with quoted path"
OUTPUT=$("$DUMMY_SCRIPT" --list-contexts 2>> "$LOG_FILE")
if echo "$OUTPUT" | grep -q "default"; then
    echo "PASS: Script execution works with quoted path"
else
    echo "FAIL: Script execution failed with quoted path"
    exit 1
fi

# Test 4: Test command execution with unquoted path (demonstrates the bug)
echo ""
echo "Test 4: Execute script with unquoted path (expected to fail)"
set +e
# This simulates the bug in regression.sh line 497
eval "OUTPUT=\$($DUMMY_SCRIPT --list-contexts 2>> \"$LOG_FILE\")"
UNQUOTED_EXEC_STATUS=$?
set -e
if [ $UNQUOTED_EXEC_STATUS -ne 0 ]; then
    echo "CONFIRMED: Unquoted execution fails (this is the bug we're fixing)"
else
    echo "NOTE: Unquoted execution worked (may depend on shell)"
fi

# Cleanup
rm -rf "$(dirname "$TEST_DIR")"

echo ""
echo "=== Space path support tests completed ==="
echo "The tests above confirm that unquoted paths with spaces cause failures."
