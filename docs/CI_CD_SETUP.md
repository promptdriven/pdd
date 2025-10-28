# CI/CD Test Automation Setup Guide

This guide explains how to set up automated test execution for PDD using GitHub Actions and Infisical for secrets management.

## Overview

The automated testing system:
- ✅ Runs unit tests, regression tests, and sync regression tests
- ✅ Captures pass/fail counts and detailed error messages
- ✅ Posts results as GitHub PR comments
- ✅ Uses Infisical for secure credential management
- ✅ Runs on GitHub Actions cloud runners (free tier)
- ✅ Supports both PR triggers and manual workflow dispatch

## Architecture

```
┌─────────────┐
│  GitHub PR  │
└──────┬──────┘
       │
       ▼
┌────────────────────┐
│ GitHub Actions     │
│ - Checkout code    │
│ - Setup environment│
│ - Fetch secrets    │
└─────────┬──────────┘
          │
          ▼
┌─────────────────────┐
│  Infisical          │
│  Secrets Management │
└─────────┬───────────┘
          │
          ▼
┌──────────────────────┐
│  Test Execution      │
│  - Unit tests        │
│  - Regression tests  │
│  - Sync regression   │
└─────────┬────────────┘
          │
          ▼
┌─────────────────────┐
│  Results Processing │
│  - Parse outputs    │
│  - Generate comment │
│  - Upload artifacts │
└─────────┬───────────┘
          │
          ▼
┌──────────────────┐
│  GitHub Comment  │
│  with Results    │
└──────────────────┘
```

## Quick Setup (10 Minutes)

### 1. Infisical Setup

**Create Infisical Account:**
- Visit: https://infisical.com
- Sign up for free account
- Create a new project for PDD

**Add API Keys to Infisical:**

Required secrets in your Infisical project:
- `ANTHROPIC_API_KEY` - Claude API key
- `OPENAI_API_KEY` - OpenAI API key
- `GOOGLE_API_KEY` - Google API key (optional)
- Any other API keys your tests need

**Create Service Token:**
1. Go to Project Settings → Service Tokens
2. Click "Create Token"
3. Name: `GitHub Actions`
4. Copy the token (starts with `st.`)

### 2. GitHub Repository Secrets

Add these secrets in your GitHub repository:

**Go to:** `Settings → Secrets and variables → Actions`

**Add these two secrets:**

| Secret Name | Value | Where to Get |
|-------------|-------|--------------|
| `INFISICAL_TOKEN` | `st.xxxxx...` | From Infisical (step 1) |
| `INFISICAL_PROJECT_ID` | `proj_xxxxx` | Infisical Project Settings |

**That's it!** Only two secrets needed.

### 3. Test the Setup

**Automatic Testing:**
- Create or update a PR
- Tests run automatically
- Results posted as PR comment

**Manual Testing:**
1. Go to Actions tab
2. Select "PR Test Automation"
3. Click "Run workflow"
4. Enter branch name
5. Click "Run workflow"

## Usage

### Automated PR Testing

Tests automatically run when:
- New PR is opened
- PR is updated (new commits pushed)
- PR is reopened

**What happens:**
1. GitHub Actions triggers
2. Sets up Python 3.12 + Conda environment
3. Installs Infisical CLI
4. Fetches secrets from Infisical
5. Runs all test suites
6. Posts results to PR

**Result:** Comment posted with pass/fail counts, test numbers, errors

### Manual Test Execution

**Via GitHub UI:**
1. Go to: `Actions` tab
2. Select: `PR Test Automation`
3. Click: `Run workflow`
4. Enter: Branch or PR number
5. Click: `Run workflow`

**Via GitHub CLI:**
```bash
gh workflow run pr-tests.yml -f branch=feat/my-feature
```

### Local Testing

```bash
# Install Infisical CLI
npm install -g @infisical/cli
infisical login

# Run all tests with Infisical
conda activate pdd
make test-all-with-infisical

# Or run individual suites
infisical run -- make test
infisical run -- make regression
infisical run -- make sync-regression
```

## Test Result Format

### Example PR Comment

```markdown
## Test Results - PASS

**Overall Summary:**
- Passed: 150
- Failed: 0
- Skipped: 5
- Duration: 245.3s

**FAILED TEST NUMBERS:** (none)

---

### Unit Tests (pytest) - PASS
**Results:**
- Passed: 120
- Failed: 0
- Duration: 45.2s

### Regression Tests - PASS
**Results:**
- Passed: 28
- Failed: 0
- Duration: 180.5s

### Sync Regression Tests - PASS
**Results:**
- Passed: 2
- Failed: 0
- Duration: 20.0s
```

### JSON Output

Results are saved to `test_results/latest_results.json`:

```json
{
  "timestamp": "2025-01-15T10:30:00",
  "test_suites": {
    "unit_tests": {
      "name": "Unit Tests (pytest)",
      "exit_code": 0,
      "passed": 120,
      "failed": 0,
      "duration_seconds": 45.2
    },
    "regression_tests": {
      "name": "Regression Tests",
      "exit_code": 0,
      "passed": 28,
      "failed": 0,
      "duration_seconds": 180.5
    }
  },
  "summary": {
    "total_passed": 150,
    "total_failed": 0,
    "all_passed": true
  }
}
```

## Troubleshooting

### Tests Not Running

**Check GitHub Actions logs:**
- Go to: `Actions` tab → Failed run → View logs

**Common issues:**
- Infisical secrets not set
- Token expired
- Workflow file syntax error

**Fix:**
```bash
# Verify secrets are set
Go to: Settings → Secrets → Actions
Should see: INFISICAL_TOKEN, INFISICAL_PROJECT_ID

# Test locally
infisical whoami  # Check if logged in
infisical secrets  # List secrets
```

### Authentication Failures

**Error:** `Failed to authenticate with Infisical`

**Fix:**
1. Check token is valid in Infisical
2. Regenerate service token if needed
3. Update GitHub secret with new token

**Test:**
```bash
# Test token locally
export INFISICAL_TOKEN="your_token"
infisical export --format=dotenv
```

### Test Failures

**View detailed logs:**
1. Go to Actions → Failed run
2. Download artifacts
3. Check `test_results/latest_results.json`

**Rerun specific tests:**
```bash
# If test #5 failed
make regression TEST_NUM=5

# If sync test #3 failed
make sync-regression TEST_NUM=3
```

## Maintenance

### Updating Test Runner

1. Modify `scripts/run_all_tests_with_results.py`
2. Commit and push
3. Tests use updated script automatically

### Rotating Secrets

**In Infisical:**
1. Update API keys
2. No code changes needed
3. Next test run uses new keys

**In GitHub:**
1. Regenerate Infisical service token
2. Update `INFISICAL_TOKEN` secret
3. Tests use new token on next run

### Upgrading Dependencies

```bash
# Update requirements
pip list --outdated
pip install --upgrade package_name
pip freeze > requirements.txt

# Update conda environment
conda env update -f environment.yml
```

## Cost Considerations

### GitHub Actions
- **Free tier:** 2000 minutes/month (private repos)
- **Estimated usage:** ~30 minutes per PR
- **Monthly capacity:** ~65 PRs on free tier
- **Overage:** $0.008/minute beyond free tier

### Infisical
- **Free tier:** Unlimited secrets
- **Sufficient for:** Most teams
- **Paid tier:** $18/user/month (advanced features)

### Monitoring Usage

**GitHub Actions:**
```
Settings → Billing → Actions usage
```

**Set spending limit:**
```
Settings → Billing → Set spending limit
```

## Security Best Practices

1. ✅ **Never commit secrets** to repository
2. ✅ **Use Infisical** for all API keys
3. ✅ **Rotate secrets** regularly (every 90 days)
4. ✅ **Limit service account** permissions
5. ✅ **Enable branch protection** rules
6. ✅ **Review PR changes** before merging
7. ✅ **Monitor access logs** in Infisical
8. ✅ **Use least privilege** for tokens

## Advanced Configuration

### Adjust Workflow Settings

In `.github/workflows/pr-tests.yml`:

**Timeout:**
```yaml
jobs:
  run-tests:
    timeout-minutes: 90  # Increase for long tests
```

**Concurrency:**
```yaml
concurrency:
  group: ${{ github.workflow }}-${{ github.ref }}
  cancel-in-progress: true  # Cancel old runs
```

**Resource Limits:**
```yaml
runs-on: ubuntu-latest  # Standard (2 CPU, 7GB RAM)
# Or:
runs-on: ubuntu-latest-4-cores  # More CPU
runs-on: ubuntu-latest-8-cores  # Maximum
```

### Custom Test Selection

**Run specific test suites:**
```yaml
# Only unit tests
make test

# Only regression
make regression TEST_NUM=5

# Only sync
make sync-regression TEST_NUM=3
```

### Conditional Execution

**Skip tests on draft PRs:**
```yaml
if: github.event.pull_request.draft == false
```

**Run on specific branches:**
```yaml
on:
  pull_request:
    branches:
      - main
      - develop
      - release/*
```

## Support

### Getting Help

1. **Check documentation:**
   - [Quick Start](QUICK_START_CI.md)
   - [Manual Trigger Guide](MANUAL_TEST_TRIGGER.md)

2. **Review logs:**
   - GitHub Actions logs
   - Test result artifacts
   - Infisical audit logs

3. **Test locally:**
   - Run `make test-all-with-infisical`
   - Check for same errors

4. **Open GitHub Issue:**
   - Include error logs
   - Workflow run link
   - Steps to reproduce

---

**Setup Time:** ~10 minutes
**Monthly Cost:** Free (within limits)
**Maintenance:** Minimal (rotate secrets quarterly)
