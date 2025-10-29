#!/bin/bash
#
# Local testing script for public PR testing workflow
# This simulates what GitHub Actions does
#

set -e  # Exit on error

echo "============================================"
echo "Local PR Testing Simulation"
echo "============================================"
echo ""

# Check arguments
if [ -z "$1" ]; then
    echo "Error: PR number required"
    echo "Usage: ./scripts/test_pr_workflow_local.sh 123"
    exit 1
fi

PR_NUMBER=$1
PUBLIC_REPO="https://github.com/promptdriven/pdd.git"
PR_URL="https://github.com/promptdriven/pdd/pull/${PR_NUMBER}"

echo "Testing public PR #${PR_NUMBER}"
echo "URL: ${PR_URL}"
echo ""

# Step 1: Save current state
echo "Step 1: Saving current state..."
ORIGINAL_BRANCH=$(git branch --show-current)
echo "Current branch: ${ORIGINAL_BRANCH}"
echo ""

# Step 2: Create test branch
TEST_BRANCH="test-public-pr-${PR_NUMBER}-$(date +%s)"
echo "Step 2: Creating test branch: ${TEST_BRANCH}"
git checkout -b "${TEST_BRANCH}"
echo ""

# Step 3: Add public remote if not exists
echo "Step 3: Adding public remote..."
if git remote | grep -q "^public$"; then
    echo "Remote 'public' already exists"
    git remote set-url public "${PUBLIC_REPO}"
else
    git remote add public "${PUBLIC_REPO}"
fi
echo ""

# Step 4: Fetch the PR
echo "Step 4: Fetching PR #${PR_NUMBER} from public repo..."
git fetch public "pull/${PR_NUMBER}/head:pr-${PR_NUMBER}" || {
    echo "Error: Failed to fetch PR #${PR_NUMBER}"
    echo "Make sure the PR number is valid"
    git checkout "${ORIGINAL_BRANCH}"
    git branch -D "${TEST_BRANCH}" 2>/dev/null || true
    exit 1
}
echo ""

# Step 5: Show what we fetched
echo "Step 5: PR details:"
git log --oneline -1 "pr-${PR_NUMBER}"
echo ""

# Step 6: Merge the PR
echo "Step 6: Merging PR locally (not pushing)..."
if git merge --no-ff "pr-${PR_NUMBER}" -m "Test merge of public PR #${PR_NUMBER}"; then
    echo "Merge successful!"
else
    echo ""
    echo "=========================================="
    echo "MERGE CONFLICT DETECTED"
    echo "=========================================="
    echo ""
    echo "The PR has conflicts with your codebase."
    echo "This PR would fail in GitHub Actions too."
    echo ""
    echo "Aborting merge and cleaning up..."
    git merge --abort 2>/dev/null || true
    git checkout "${ORIGINAL_BRANCH}"
    git branch -D "${TEST_BRANCH}" 2>/dev/null || true
    git branch -D "pr-${PR_NUMBER}" 2>/dev/null || true
    exit 1
fi
echo ""

# Step 7: Show merge summary
echo "Step 7: Merge summary:"
echo "Files changed:"
git diff --name-status "${ORIGINAL_BRANCH}"..HEAD | head -20
echo ""

# Step 8: Check conda environment
echo "Step 8: Checking conda environment..."
if conda info --envs | grep -q "^pdd "; then
    echo "Conda environment 'pdd' found ✓"
else
    echo "Warning: Conda environment 'pdd' not found"
    echo "Create it with: conda create -n pdd python=3.12"
fi
echo ""

# Step 9: Ask about running tests
echo "=========================================="
echo "Merge successful! Ready to run tests."
echo "=========================================="
echo ""
echo "The PR has been merged locally in branch: ${TEST_BRANCH}"
echo "Original branch: ${ORIGINAL_BRANCH}"
echo ""
read -p "Do you want to run tests now? (y/n) " -n 1 -r
echo ""

if [[ $REPLY =~ ^[Yy]$ ]]; then
    echo ""
    echo "Step 10: Running tests with Infisical..."
    echo "=========================================="
    
    # Check if infisical is available
    if ! command -v infisical &> /dev/null; then
        echo "Error: Infisical CLI not found"
        echo "Install with: npm install -g @infisical/cli"
        echo ""
        echo "Skipping test execution"
    else
        # Run tests
        echo "Running: infisical run -- conda run -n pdd python scripts/run_all_tests_with_results.py --pr-number ${PR_NUMBER} --pr-url ${PR_URL}"
        echo ""
        
        if infisical run -- conda run -n pdd python scripts/run_all_tests_with_results.py \
            --pr-number "${PR_NUMBER}" \
            --pr-url "${PR_URL}"; then
            echo ""
            echo "=========================================="
            echo "TESTS PASSED ✓"
            echo "=========================================="
            echo ""
            echo "View results:"
            echo "  cat test_results/latest_comment.md"
            echo "  cat test_results/latest_results.json"
        else
            echo ""
            echo "=========================================="
            echo "TESTS FAILED ✗"
            echo "=========================================="
            echo ""
            echo "View results:"
            echo "  cat test_results/latest_comment.md"
            echo "  cat test_results/latest_results.json"
        fi
    fi
fi

echo ""
echo "=========================================="
echo "Cleanup"
echo "=========================================="
echo ""
echo "Returning to original branch: ${ORIGINAL_BRANCH}"
git checkout "${ORIGINAL_BRANCH}"

echo "Deleting test branches..."
git branch -D "${TEST_BRANCH}" 2>/dev/null || true
git branch -D "pr-${PR_NUMBER}" 2>/dev/null || true

echo ""
echo "Done! Your repository is back to its original state."
echo ""
echo "Summary:"
echo "  - PR #${PR_NUMBER} was fetched and merged successfully"
echo "  - Tests were run (if you chose to)"
echo "  - No changes were pushed to any remote"
echo "  - All test branches cleaned up"
echo ""

