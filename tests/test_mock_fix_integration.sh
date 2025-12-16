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

# Step 1: Verify the bug exists in example (precondition)
echo "Checking precondition: example has mock bug..."
if grep -q "__getitem__.return_value = \[mock_agg_result\]" "$EXAMPLE_FILE"; then
    echo "✓ Precondition met: Example has the mock bug"
else
    echo "✗ Precondition failed: Example doesn't have expected bug pattern"
    echo "  Looking for: __getitem__.return_value = [mock_agg_result]"
    echo "  In file: $EXAMPLE_FILE"
    exit 1
fi

# Step 2: Record production code state (should not change)
echo "Recording production code state..."
PROD_CODE_BEFORE=$(grep "count_snapshot\[0\]\[0\].value" "$CODE_FILE" || echo "NOT_FOUND")
if [ "$PROD_CODE_BEFORE" = "NOT_FOUND" ]; then
    echo "✗ Production code doesn't have expected pattern: count_snapshot[0][0].value"
    echo "  In file: $CODE_FILE"
    exit 1
fi
echo "✓ Production code has correct pattern: $PROD_CODE_BEFORE"

# Step 3: Run pdd verify
echo ""
echo "Running pdd verify..."
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
$PDD_CMD --context backend verify get_user_contributions || {
    echo "Note: verify may exit non-zero during fix iterations"
}

# Step 4: Check results
echo ""
echo "=== Checking Results ==="

EXAMPLE_FIXED=false
PROD_PRESERVED=false

# Check if example was fixed
if grep -q "__getitem__.return_value = mock_agg_result[^]]" "$EXAMPLE_FILE" 2>/dev/null || \
   grep -q "__getitem__.return_value = mock_agg_result$" "$EXAMPLE_FILE" 2>/dev/null; then
    echo "✓ PASS: Example mock was fixed (list wrapper removed)"
    EXAMPLE_FIXED=true
elif grep -q "__getitem__.return_value = \[mock_agg_result\]" "$EXAMPLE_FILE"; then
    echo "✗ FAIL: Example mock was NOT fixed (still has list wrapper)"
    EXAMPLE_FIXED=false
else
    echo "? UNKNOWN: Example mock pattern changed unexpectedly"
    echo "  Current content around __getitem__:"
    grep -n "__getitem__" "$EXAMPLE_FILE" || echo "  (not found)"
    EXAMPLE_FIXED=false
fi

# Check if production code was preserved
PROD_CODE_AFTER=$(grep "count_snapshot\[0\]\[0\].value" "$CODE_FILE" || echo "NOT_FOUND")
if [ "$PROD_CODE_AFTER" != "NOT_FOUND" ]; then
    echo "✓ PASS: Production code preserved ([0][0] pattern intact)"
    PROD_PRESERVED=true
else
    echo "✗ FAIL: Production code was incorrectly modified!"
    echo "  Looking for: count_snapshot[0][0].value"
    echo "  Current content around count_snapshot:"
    grep -n "count_snapshot" "$CODE_FILE" || echo "  (not found)"
    PROD_PRESERVED=false
fi

# Final result
echo ""
if [ "$EXAMPLE_FIXED" = true ] && [ "$PROD_PRESERVED" = true ]; then
    echo "=== TEST PASSED ==="
    exit 0
else
    echo "=== TEST FAILED ==="
    echo ""
    echo "Summary:"
    echo "  Example mock fixed: $EXAMPLE_FIXED"
    echo "  Production code preserved: $PROD_PRESERVED"
    exit 1
fi
