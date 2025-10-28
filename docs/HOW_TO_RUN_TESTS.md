# How to Run Tests Manually

The test automation is **fully manual** - you control when tests run via the GitHub Actions UI.

## Running Tests on GitHub Actions

### Step-by-Step Instructions

1. **Go to Actions Tab**
   ```
   https://github.com/gltanaka/pdd/actions
   ```

2. **Select Workflow**
   - Click on "Manual Test Execution" in the left sidebar

3. **Click "Run workflow"** (top right)

4. **Fill in the Form:**
   
   **Option A: Test a PR**
   - **PR number:** `123` (enter the PR number)
   - **Branch:** (leave empty or enter PR branch name)
   - **PR URL:** (optional - auto-generated if you provide PR number)
   
   **Option B: Test a Branch**
   - **PR number:** (leave empty)
   - **Branch:** `feat/my-feature`
   - **PR URL:** (leave empty)
   
   **Option C: Test Main Branch**
   - **PR number:** (leave empty)
   - **Branch:** `main` (or leave as default)
   - **PR URL:** (leave empty)

5. **Click "Run workflow"** (green button)

6. **Wait for Results**
   - Watch progress in Actions tab
   - Takes ~15-30 minutes
   - Results appear when complete

## Examples

### Example 1: Test PR #45

```
Go to: https://github.com/gltanaka/pdd/actions
Click: "Manual Test Execution" → "Run workflow"

Fill in:
  PR number: 45
  Branch: (leave empty)
  PR URL: (leave empty)

Click: "Run workflow"
```

**Result:** 
- Tests run on PR #45
- Comment posted to PR #45 with results
- PR link included in comment

### Example 2: Test Feature Branch

```
Go to: https://github.com/gltanaka/pdd/actions
Click: "Manual Test Execution" → "Run workflow"

Fill in:
  PR number: (leave empty)
  Branch: feat/automate-regression-unit-tests
  PR URL: (leave empty)

Click: "Run workflow"
```

**Result:**
- Tests run on the feature branch
- Results saved as artifact
- No PR comment (since no PR number provided)

### Example 3: Test with Custom PR URL

```
Go to: https://github.com/gltanaka/pdd/actions
Click: "Manual Test Execution" → "Run workflow"

Fill in:
  PR number: 45
  Branch: feat/my-feature
  PR URL: https://github.com/gltanaka/pdd/pull/45

Click: "Run workflow"
```

**Result:**
- Tests run on specified branch
- Custom PR URL included in comment
- Comment posted to PR #45

## Where to Find Results

### 1. In the Actions Tab

Go to: `https://github.com/gltanaka/pdd/actions`

- See all workflow runs
- Click on a run to view logs
- Real-time progress updates

### 2. In PR Comments (if PR number provided)

Go to the PR page:
- Automated comment posted with results
- Shows pass/fail counts
- Lists failed test numbers
- Includes PR link back to itself

Example comment:
```markdown
## Test Results - PASS

**Pull Request:** https://github.com/gltanaka/pdd/pull/45

**Overall Summary:**
- Passed: 150
- Failed: 0
```

### 3. In Artifacts

Download detailed logs:
1. Go to workflow run
2. Scroll to bottom → "Artifacts" section
3. Download `test-results-{number}`
4. Extract and view JSON/logs

## Via GitHub CLI

If you have GitHub CLI installed:

```bash
# Test a branch
gh workflow run pr-tests.yml \
  -f branch=feat/my-feature

# Test a PR
gh workflow run pr-tests.yml \
  -f pr_number=45 \
  -f branch=feat/my-feature

# List recent runs
gh run list --workflow=pr-tests.yml

# Watch a running workflow
gh run watch

# View logs
gh run view <run-id> --log
```

## Via API

Using curl or other HTTP clients:

```bash
# Get your GitHub token
export GITHUB_TOKEN="your_token_here"

# Trigger workflow for a branch
curl -X POST \
  -H "Authorization: token $GITHUB_TOKEN" \
  -H "Accept: application/vnd.github.v3+json" \
  https://api.github.com/repos/gltanaka/pdd/actions/workflows/pr-tests.yml/dispatches \
  -d '{"ref":"main","inputs":{"branch":"feat/my-feature"}}'

# Trigger workflow for a PR
curl -X POST \
  -H "Authorization: token $GITHUB_TOKEN" \
  -H "Accept: application/vnd.github.v3+json" \
  https://api.github.com/repos/gltanaka/pdd/actions/workflows/pr-tests.yml/dispatches \
  -d '{"ref":"main","inputs":{"pr_number":"45","branch":"feat/my-feature"}}'
```

## Who Can Trigger Tests

**Anyone with repository access can trigger tests:**
- Contributors
- Collaborators
- Organization members
- Repository admins

**No API keys required** - they're stored in GitHub secrets!

## When to Run Tests

**Before merging a PR:**
```
Trigger: PR #45 on branch feat/my-feature
Result: Ensures code quality before merge
```

**After making changes:**
```
Trigger: Branch feat/my-feature
Result: Validates changes work correctly
```

**Before release:**
```
Trigger: Branch main
Result: Final validation before deployment
```

**To reproduce an issue:**
```
Trigger: Specific branch with known issue
Result: Debug with full logs in artifacts
```

## Troubleshooting

### Workflow Not Found

- Ensure branch with `.github/workflows/pr-tests.yml` is pushed
- Check you're in the right repository (pdd_cloud)
- Verify you have repository access

### Can't Trigger Workflow

- Check you're logged into GitHub
- Verify you have contributor/write access
- Ensure Actions are enabled for the repository

### Tests Don't Run

1. Check Actions tab for error logs
2. Verify GitHub secrets are set:
   - `INFISICAL_TOKEN`
   - `INFISICAL_PROJECT_ID`
3. Check Infisical token is valid
4. Ensure branch name is correct

### No PR Comment Posted

- Did you provide a PR number?
- Check the workflow logs for errors
- Verify `pull-requests: write` permission is set
- Ensure GITHUB_TOKEN has required permissions

## Best Practices

1. **Test Before Merging**
   - Always run tests before approving PRs
   - Review test results in PR comment

2. **Use Branch Names**
   - Enter full branch names
   - Double-check spelling

3. **Provide PR Numbers**
   - To get results posted as comments
   - Makes tracking easier

4. **Download Artifacts**
   - For detailed debugging
   - Keep for historical reference

5. **Monitor Usage**
   - Check GitHub Actions minutes
   - Stay within free tier limits

## Summary

**Manual Workflow Control:**
- ✅ You decide when tests run
- ✅ Anyone with access can trigger
- ✅ No automatic PR triggers
- ✅ Test any branch or PR
- ✅ Results posted to PR (if number provided)
- ✅ Artifacts always saved

**To Run Tests:**
1. Go to: https://github.com/gltanaka/pdd/actions
2. Click: "Manual Test Execution" → "Run workflow"
3. Enter: PR number or branch name
4. Click: "Run workflow"
5. Wait: ~15-30 minutes
6. View: Results in Actions or PR comment

