# Testing Public PRs Against Private Codebase

## Overview

This system allows you to test pull requests from the **public repository** (`promptdriven/pdd`) against your **private codebase** (`gltanaka/pdd`) without merging or exposing private code.

## Architecture

```
┌──────────────────────────────────────────────────────┐
│   You (Local Machine)                                │
│                                                      │
│  $ make pr-test pr-url=https://github.com/..../123  │
└────────────┬─────────────────────────────────────────┘
             │
             │ Triggers GitHub Actions
             │ (via gh workflow run)
             ▼
┌────────────────────────────────────────────────┐
│       GitHub Actions (gltanaka/pdd)            │
│       Runs in PRIVATE repo                     │
│                                                │
│  1. Clone gltanaka/pdd (private)          ✓   │
│  2. Add promptdriven/pdd as remote        ✓   │
│  3. Fetch PR from public repo             ✓   │
│  4. Merge PR locally (NOT pushed)         ✓   │
│  5. Run tests with Infisical              ✓   │
│  6. Parse results & extract failures      ✓   │
│  7. Post comment → promptdriven/pdd PR    ✓   │
└────────────────────────────────────────────────┘
             │
             │ Posts test results
             ▼
┌────────────────────────────────────────────────┐
│   promptdriven/pdd (PUBLIC)                    │
│   PR #123                                      │
│   └─ Comment: "Test Results - PASS/FAIL"      │
└────────────────────────────────────────────────┘
```

## Security Model

### What Stays Private
- Your private codebase (`gltanaka/pdd`)
- API keys and secrets (via Infisical)
- Test infrastructure and setup
- Internal testing data

### What Gets Exposed
- Test results (pass/fail counts)
- Failed test names and numbers
- Error messages from public code
- Duration and summary statistics

### Key Security Features
1. **No code push**: PR is merged locally only, never pushed anywhere
2. **Private execution**: All tests run in your private GitHub Actions environment
3. **Secrets via Infisical**: API keys fetched securely at runtime
4. **Controlled output**: Only test results are posted, not internal code/data
5. **Token isolation**: Separate tokens for private repo access and public repo commenting

## Prerequisites

### 1. GitHub CLI
```bash
# macOS
brew install gh

# Linux
# See: https://github.com/cli/cli/blob/trunk/docs/install_linux.md

# Authenticate
gh auth login

# Set default repo to private repo
gh repo set-default gltanaka/pdd
```

### 2. GitHub Secrets (in gltanaka/pdd)

You need to configure these secrets in your private repo:

| Secret | Description | How to get it |
|--------|-------------|---------------|
| `INFISICAL_TOKEN` | Service token for Infisical | [Infisical Dashboard](https://app.infisical.com) → Project Settings → Service Tokens |
| `INFISICAL_PROJECT_ID` | Your Infisical project ID | Infisical Dashboard → Project Settings |
| `INFISICAL_CLIENT_ID` | Machine identity client ID | Infisical Dashboard → Project Settings → Machine Identities |
| `INFISICAL_CLIENT_SECRET` | Machine identity secret | Generated when creating machine identity |
| `PUBLIC_REPO_TOKEN` | GitHub PAT with public repo access | [GitHub Settings](https://github.com/settings/tokens) → New Token → `public_repo` scope |

#### Creating PUBLIC_REPO_TOKEN

This token is used to post comments on the public repository PRs.

1. Go to https://github.com/settings/tokens
2. Click "Generate new token" → "Generate new token (classic)"
3. Set note: "Public PR Testing - Comment Access"
4. Select scope: **`public_repo`** (Access public repositories)
5. Generate token and copy it
6. Add to gltanaka/pdd secrets as `PUBLIC_REPO_TOKEN`

### 3. GitHub Actions Workflow

The workflow file `.github/workflows/pr-tests.yml` must be on the **main branch** of your private repo (`gltanaka/pdd`) before you can trigger it.

## Usage

### Basic Command

```bash
make pr-test pr-url=https://github.com/promptdriven/pdd/pull/123
```

Where `123` is the PR number from `promptdriven/pdd`. You can use any GitHub PR URL.

### What Happens

1. **Makefile** validates inputs and triggers GitHub Actions:
   ```bash
   gh workflow run pr-tests.yml \
     --repo gltanaka/pdd \
     --field public_pr_number=123 \
     --field public_pr_url=https://github.com/promptdriven/pdd/pull/123
   ```

2. **GitHub Actions** (in private repo):
   - Checks out `gltanaka/pdd` (private codebase)
   - Adds `promptdriven/pdd` as a remote named "public"
   - Fetches the PR: `git fetch public pull/123/head:pr-123`
   - Merges locally: `git merge --no-ff pr-123`
   - Sets up Python 3.12 and Conda environment
   - Installs Infisical CLI
   - Installs all dependencies
   - Runs all test suites:
     - Unit tests (`make test`)
     - Regression tests (`make regression`)
     - Sync regression tests (`make sync-regression`)
   - Parses results and extracts failed test numbers
   - Posts formatted comment to `promptdriven/pdd` PR #123

3. **Public PR** receives a comment with results:
   ```markdown
   ## Test Results - PASS
   
   **Pull Request:** https://github.com/promptdriven/pdd/pull/123
   
   **Overall Summary:**
   - Passed: 205
   - Failed: 0
   - Skipped: 3
   - Duration: 342.5s
   
   ### Unit Tests - PASS
   - Passed: 145
   - Failed: 0
   - Skipped: 3
   - Duration: 45.2s
   
   ### Regression Tests - PASS
   - Passed: 48
   - Failed: 0
   - Skipped: 0
   - Duration: 245.1s
   
   ### Sync Regression Tests - PASS
   - Passed: 12
   - Failed: 0
   - Skipped: 0
   - Duration: 52.2s
   ```

## Advanced Usage

### Test Against Different Base Branch

By default, PRs are tested against the `main` branch of your private repo. To test against a different branch:

```bash
# Via GitHub UI
Go to: https://github.com/gltanaka/pdd/actions/workflows/pr-tests.yml
Click: "Run workflow"
Set:
  - public_pr_number: 123
  - branch: feature-branch
  - public_pr_url: (optional)

# Or manually with gh CLI
gh workflow run pr-tests.yml \
  --repo gltanaka/pdd \
  --field public_pr_number=123 \
  --field branch=feature-branch \
  --field public_pr_url=https://github.com/promptdriven/pdd/pull/123
```

### Monitor Test Execution

```bash
# Watch the workflow run in real-time
gh run watch

# List recent runs
gh run list --workflow=pr-tests.yml --repo gltanaka/pdd

# View logs of specific run
gh run view RUN_ID --log --repo gltanaka/pdd

# Or visit web UI
open https://github.com/gltanaka/pdd/actions
```

### Download Test Artifacts

```bash
# List artifacts from a run
gh run view RUN_ID --repo gltanaka/pdd

# Download artifacts
gh run download RUN_ID --repo gltanaka/pdd

# Artifacts include:
# - test-results-public-pr-123/
#   ├── latest_results.json
#   ├── latest_comment.md
#   ├── unit_tests.log
#   ├── regression_tests.log
#   └── sync_regression_tests.log
```

## Workflow Details

### Workflow File Location
`.github/workflows/pr-tests.yml` (in `gltanaka/pdd` main branch)

### Workflow Inputs
```yaml
public_pr_number:
  description: 'PR number from public repo (promptdriven/pdd)'
  required: true
  type: string

public_pr_url:
  description: 'PR URL from public repo'
  required: false
  type: string

branch:
  description: 'Base branch in private repo to test against'
  required: false
  default: 'main'
  type: string
```

### Test Script
`scripts/run_all_tests_with_results.py`

This script:
- Runs all three test suites sequentially
- Captures stdout/stderr for each suite
- Parses pytest/test output to extract:
  - Pass/fail/skip counts
  - Test durations
  - Failed test names and numbers
  - Error messages
- Generates JSON results file
- Generates markdown comment
- Prints summary to console

## Troubleshooting

### Error: "workflow pr-tests.yml not found"

**Problem:** The workflow file doesn't exist on the main branch of your private repo.

**Solution:**
```bash
# Ensure the workflow is on main branch
git checkout main
git pull origin main

# Check if .github/workflows/pr-tests.yml exists
ls -la .github/workflows/pr-tests.yml

# If not, merge your feature branch
git merge feat/automate-regression-unit-tests
git push origin main
```

### Error: "gh: command not found"

**Problem:** GitHub CLI not installed.

**Solution:**
```bash
# macOS
brew install gh

# Linux (Ubuntu/Debian)
curl -fsSL https://cli.github.com/packages/githubcli-archive-keyring.gpg | sudo dd of=/usr/share/keyrings/githubcli-archive-keyring.gpg
echo "deb [arch=$(dpkg --print-architecture) signed-by=/usr/share/keyrings/githubcli-archive-keyring.gpg] https://cli.github.com/packages stable main" | sudo tee /etc/apt/sources.list.d/github-cli.list > /dev/null
sudo apt update
sudo apt install gh

# Authenticate
gh auth login
```

### Error: "Resource not accessible by integration"

**Problem:** The `PUBLIC_REPO_TOKEN` doesn't have the right permissions or isn't set.

**Solution:**
1. Create a new Personal Access Token with `public_repo` scope
2. Add it to `gltanaka/pdd` secrets as `PUBLIC_REPO_TOKEN`
3. Ensure the token hasn't expired

### Error: "Merge conflict"

**Problem:** The public PR conflicts with your private codebase.

**Solution:**
This is expected behavior! The workflow will fail and post an error comment. Options:
1. Ask the PR author to resolve conflicts
2. Manually test the PR locally:
   ```bash
   git checkout -b test-pr-123
   git fetch https://github.com/promptdriven/pdd.git pull/123/head:pr-123
   git merge pr-123
   # Resolve conflicts
   make test-all-with-infisical
   ```

### No Comment Posted to Public PR

**Problem:** Tests ran but no comment appeared.

**Possible causes:**
1. `PUBLIC_REPO_TOKEN` not set or expired
2. Token doesn't have `public_repo` scope
3. Test results file wasn't generated

**Debug:**
```bash
# Check workflow logs
gh run view --log --repo gltanaka/pdd

# Look for "Comment on public repo PR" step
# Check if results_available was 'true'

# Download artifacts to see if results exist
gh run download RUN_ID --repo gltanaka/pdd
cat test-results-public-pr-123/latest_comment.md
```

### Tests Failing Due to Missing Secrets

**Problem:** Tests fail with "API key not found" or similar errors.

**Solution:**
Ensure all Infisical secrets are configured:
```bash
# Test Infisical locally
infisical login
infisical secrets

# Verify GitHub secrets are set
gh secret list --repo gltanaka/pdd

# Required:
# - INFISICAL_TOKEN
# - INFISICAL_PROJECT_ID  
# - INFISICAL_CLIENT_ID
# - INFISICAL_CLIENT_SECRET
```

## Security Considerations

### What to Review Before Merging Public PRs

Even though tests pass, always review:

1. **Dependency changes**: New packages could have vulnerabilities
2. **File access patterns**: Ensure PR doesn't try to read sensitive files
3. **Network calls**: Verify PR doesn't exfiltrate data
4. **Test modifications**: Don't let PRs weaken test coverage
5. **Prompt changes**: Ensure prompts don't expose internal logic

### Automated Checks (TODO)

Consider adding:
- Dependency security scanning (Dependabot, Snyk)
- Code quality gates (pylint, mypy)
- License compliance checks
- Secrets scanning (git-secrets, trufflehog)

### Rate Limiting

GitHub Actions has usage limits:
- Free tier: 2,000 minutes/month for private repos
- Each test run takes ~5-10 minutes
- ~200-400 PR tests per month on free tier

Consider:
- Upgrading to paid plan for more minutes
- Only testing PRs that look serious/complete
- Asking contributors to run tests locally first

## Example Workflow

### Scenario: New PR from External Contributor

1. **PR Submitted** to `promptdriven/pdd`:
   ```
   PR #456: "Add support for Python 3.13"
   by @external-contributor
   ```

2. **You Review** the PR briefly:
   - Changes look reasonable
   - Want to see if it passes tests

3. **Trigger Tests** from your machine:
   ```bash
   make pr-test pr-url=https://github.com/promptdriven/pdd/pull/456
   ```

4. **GitHub Actions Runs** (5-10 minutes):
   - Clones your private repo
   - Merges PR #456 locally
   - Runs all tests
   - Posts results

5. **Review Results** on public PR:
   - All tests pass ✓
   - Or some fail → see which tests and why

6. **Decision**:
   - If passing: Deeper code review → approve/merge
   - If failing: Comment with specific failures → ask author to fix

## Comparison with Alternatives

### Alternative 1: Manual Testing

**Before:**
```bash
# Clone public PR
git clone https://github.com/promptdriven/pdd.git public-pdd
cd public-pdd
gh pr checkout 123

# Copy to private repo
cd ../pdd-11
git checkout -b test-pr-123
cp -r ../public-pdd/* .

# Set up secrets manually
export OPENAI_API_KEY="..."
export ANTHROPIC_API_KEY="..."
# ... etc

# Run tests
make test
make regression
make sync-regression

# Clean up
cd ..
rm -rf public-pdd
cd pdd-11
git checkout main
git branch -D test-pr-123
```

**Now:**
```bash
make pr-test pr-url=https://github.com/promptdriven/pdd/pull/123
```

### Alternative 2: Separate CI on Public Repo

**Problem:** Can't run tests on public repo because:
- Requires private API keys
- Reveals internal test structure
- Exposes private dependencies

**This solution:** Tests run in private environment, only results are public

### Alternative 3: Contributor Testing

**Problem:** Asking contributors to test doesn't verify against:
- Your specific environment
- Your private code dependencies
- Your complete test suite

**This solution:** Tests against actual production environment

## Related Documentation

- [CI/CD Setup](./CI_CD_SETUP.md) - General CI/CD configuration
- [Manual Test Trigger](./MANUAL_TEST_TRIGGER.md) - Manual testing workflows  
- [Quick Start CI](./QUICK_START_CI.md) - Quick setup guide
- [Automation Summary](../AUTOMATION_SUMMARY.md) - Complete system overview

## Support

Issues with this workflow? Check:

1. **GitHub Actions logs**: https://github.com/gltanaka/pdd/actions
2. **Makefile**: `Makefile` (pr-test target)
3. **Workflow file**: `.github/workflows/pr-tests.yml`
4. **Test script**: `scripts/run_all_tests_with_results.py`

## Future Enhancements

Potential improvements:
- [ ] Automatic triggering on PR labels (e.g., "test-ready")
- [ ] PR comment command (e.g., "/test-pr" in comment)
- [ ] Multiple platform testing (Linux, macOS, Windows)
- [ ] Performance benchmarking
- [ ] Security scanning integration
- [ ] Automatic dependency updates testing

