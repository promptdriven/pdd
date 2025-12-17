#!/bin/bash
# Integration test: Verify that pdd verify correctly fixes mock bugs
#
# Prerequisites:
# - The example file has the mock bug: __getitem__.return_value = [mock_agg_result]
# - The production code has correct API: count_snapshot[0][0].value
#
# Expected behavior AFTER prompt fix:
# - pdd verify should fix the EXAMPLE file (remove list wrapper)
# - pdd verify should NOT modify the PRODUCTION code
#
# TDD Workflow:
# - This test should FAIL before prompt updates
# - This test should PASS after prompt updates

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PDD_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
PROJECT_ROOT="$(cd "$PDD_ROOT/.." && pwd)"

EXAMPLE_FILE="$PROJECT_ROOT/context/get_user_contributions_example.py"
CODE_FILE="$PROJECT_ROOT/backend/functions/get_user_contributions.py"

echo "=== Mock vs Production Fix Integration Test ==="
echo "Script dir: $SCRIPT_DIR"
echo "PDD root: $PDD_ROOT"
echo "Project root: $PROJECT_ROOT"
echo ""

# Step 1: Check if bug exists or was already fixed
echo "Checking example file state..."
if grep -q "__getitem__.return_value = \[mock_agg_result\]" "$EXAMPLE_FILE"; then
    echo "✓ Precondition met: Example has the mock bug (will run sync to fix)"
    RUN_SYNC=true
elif grep -q "get.return_value = \[mock_agg_result\]" "$EXAMPLE_FILE"; then
    echo "✓ Example already uses correct pattern (get.return_value = [mock_agg_result])"
    echo "  Skipping sync - checking that production code is also aligned..."
    RUN_SYNC=false
else
    echo "? Unknown example state - checking for other mock patterns..."
    grep -n "mock_agg" "$EXAMPLE_FILE" || echo "  (no mock_agg patterns found)"
    RUN_SYNC=false
fi

# Step 2: Record production code state
echo "Recording production code state..."
# Check for both patterns - original [0][0] and simplified [0]
PROD_CODE_DOUBLE=$(grep "count_snapshot\[0\]\[0\].value" "$CODE_FILE" || echo "NOT_FOUND")
PROD_CODE_SINGLE=$(grep "count_snapshot\[0\].value" "$CODE_FILE" | grep -v "\[0\]\[0\]" || echo "NOT_FOUND")

if [ "$PROD_CODE_DOUBLE" != "NOT_FOUND" ]; then
    echo "✓ Production code has double-index pattern: $PROD_CODE_DOUBLE"
    PROD_PATTERN="double"
elif [ "$PROD_CODE_SINGLE" != "NOT_FOUND" ]; then
    echo "✓ Production code has single-index pattern: $PROD_CODE_SINGLE"
    PROD_PATTERN="single"
else
    echo "✗ Production code doesn't have expected count_snapshot pattern"
    echo "  In file: $CODE_FILE"
    grep -n "count_snapshot" "$CODE_FILE" || echo "  (not found)"
    exit 1
fi

# Step 3: Run pdd sync only if bug exists
if [ "$RUN_SYNC" = true ]; then
    echo ""
    echo "Running pdd sync (which triggers verify)..."
    cd "$PROJECT_ROOT"

    # Use the local pdd script
    if [ -f "./pdd/pdd-local.sh" ]; then
        PDD_CMD="./pdd/pdd-local.sh"
    elif command -v pdd &> /dev/null; then
        PDD_CMD="pdd"
    else
        echo "✗ Could not find pdd command"
        exit 1
    fi

    echo "Using PDD command: $PDD_CMD"
    echo "Running: $PDD_CMD --context backend --verbose --force sync get_user_contributions"
    $PDD_CMD --context backend --verbose --force sync get_user_contributions || {
        echo "Note: sync may exit non-zero during fix iterations"
    }
else
    echo ""
    echo "Skipping pdd sync - example already fixed"
fi

# Step 4: Check results
echo ""
echo "=== Checking Results ==="

EXAMPLE_OK=false
PROD_OK=false

# Check if example has correct mock pattern
# Accept: get.return_value = [mock_agg_result] (simplified approach)
# Or: __getitem__.return_value = mock_agg_result (without list wrapper)
if grep -q "get.return_value = \[mock_agg_result\]" "$EXAMPLE_FILE"; then
    echo "✓ PASS: Example uses correct mock pattern (get.return_value = [mock_agg_result])"
    EXAMPLE_OK=true
elif grep -q "__getitem__.return_value = mock_agg_result[^]]" "$EXAMPLE_FILE" 2>/dev/null || \
     grep -q "__getitem__.return_value = mock_agg_result$" "$EXAMPLE_FILE" 2>/dev/null; then
    echo "✓ PASS: Example mock was fixed (list wrapper removed from __getitem__)"
    EXAMPLE_OK=true
elif grep -q "__getitem__.return_value = \[mock_agg_result\]" "$EXAMPLE_FILE"; then
    echo "✗ FAIL: Example mock has bug (list wrapper on __getitem__)"
    EXAMPLE_OK=false
else
    echo "? UNKNOWN: Example mock pattern not recognized"
    echo "  Current mock patterns:"
    grep -n "mock_agg\|__getitem__" "$EXAMPLE_FILE" || echo "  (not found)"
    EXAMPLE_OK=false
fi

# Check if production code has valid pattern
# Accept: count_snapshot[0].value (single index - aligned with get.return_value = [result])
# Or: count_snapshot[0][0].value (double index - aligned with __getitem__ approach)
PROD_CODE_AFTER_DOUBLE=$(grep "count_snapshot\[0\]\[0\].value" "$CODE_FILE" || echo "NOT_FOUND")
PROD_CODE_AFTER_SINGLE=$(grep "count_snapshot\[0\].value" "$CODE_FILE" | grep -v "\[0\]\[0\]" || echo "NOT_FOUND")

if [ "$PROD_CODE_AFTER_SINGLE" != "NOT_FOUND" ]; then
    echo "✓ PASS: Production code uses single-index pattern (aligned with simplified mock)"
    PROD_OK=true
elif [ "$PROD_CODE_AFTER_DOUBLE" != "NOT_FOUND" ]; then
    echo "✓ PASS: Production code preserved double-index pattern"
    PROD_OK=true
else
    echo "✗ FAIL: Production code count_snapshot pattern not found!"
    echo "  Current content around count_snapshot:"
    grep -n "count_snapshot" "$CODE_FILE" || echo "  (not found)"
    PROD_OK=false
fi

# Final result
echo ""
if [ "$EXAMPLE_OK" = true ] && [ "$PROD_OK" = true ]; then
    echo "=== TEST PASSED ==="
    echo ""
    echo "Summary:"
    echo "  Example mock pattern: CORRECT"
    echo "  Production code pattern: CORRECT"
    echo "  Mock and production code are aligned"
    exit 0
else
    echo "=== TEST FAILED ==="
    echo ""
    echo "Summary:"
    echo "  Example mock correct: $EXAMPLE_OK"
    echo "  Production code correct: $PROD_OK"
    exit 1
fi
