# Manual Test Trigger Guide

This guide shows **any authorized team member** how to trigger tests without needing API keys or credentials.

## 🎯 Goal

Anyone with repository access can trigger tests on any branch or PR **without knowing or storing API keys**.

Keys are stored once in GitHub secrets by the admin, then anyone can trigger tests.

---

## 🚀 How to Trigger Tests (For Any Team Member)

### Method 1: Via GitHub UI (Easiest)

1. Go to your repository on GitHub
2. Click the **Actions** tab
3. Select **"PR Test Automation"** workflow from the left sidebar
4. Click **"Run workflow"** button (top right)
5. Fill in the form:
   - **Branch to test**: `main` or `feat/my-feature`
   - **PR number**: (optional) leave empty for branch test
6. Click **"Run workflow"** green button

**That's it!** Tests will run and post results.

### Method 2: Via GitHub CLI

```bash
# Test a specific branch
gh workflow run pr-tests.yml -f branch=feat/my-feature

# Test a PR
gh workflow run pr-tests.yml -f pr_number=123

# Test main branch (default)
gh workflow run pr-tests.yml
```

### Method 3: Via API Call

```bash
# Get your GitHub token from: https://github.com/settings/tokens
export GITHUB_TOKEN="your_token_here"

curl -X POST \
  -H "Authorization: token $GITHUB_TOKEN" \
  -H "Accept: application/vnd.github.v3+json" \
  https://api.github.com/repos/gltanaka/pdd/actions/workflows/pr-tests.yml/dispatches \
  -d '{"ref":"main","inputs":{"branch":"feat/my-feature"}}'
```

---

## 📊 View Test Results

After triggering:

1. **Actions Tab**: See real-time progress
   - Repository → Actions → Your workflow run
   
2. **PR Comments**: (if testing a PR)
   - Automated comment posted with results
   
3. **Artifacts**: Download full logs
   - Workflow run → Artifacts section
   
4. **Email**: (if enabled)
   - GitHub sends notifications on completion

---

## 🔒 Security Model

### What Team Members Need
- GitHub repository access (read permission)
- Ability to trigger Actions (standard for contributors)

### What Team Members DON'T Need
- ❌ API keys (stored in GitHub secrets)
- ❌ Infisical login
- ❌ Cloud credentials
- ❌ Direct access to secrets

### One-Time Admin Setup
Admin configures GitHub secrets once:
- `INFISICAL_TOKEN`
- `INFISICAL_PROJECT_ID`

Then **anyone** can trigger tests.

---

## 🎮 Use Cases

### Use Case 1: Test Before Creating PR
```bash
# You're working on a feature branch
git checkout feat/new-feature
git push

# Trigger tests on your branch before creating PR
# Go to Actions → Run workflow → branch: feat/new-feature
```

### Use Case 2: Re-run Failed Tests
```bash
# Tests failed on PR #45, you made fixes locally
git push

# Manually trigger tests again
# Go to Actions → Run workflow → pr_number: 45
```

### Use Case 3: Test Someone Else's PR
```bash
# You want to verify PR #67 from a colleague
# Go to Actions → Run workflow → pr_number: 67
```

### Use Case 4: Scheduled Testing
Set up a cron schedule in the workflow to run tests nightly.

---

## 💡 Comparison: Manual Login vs Service Tokens

### ❌ Manual Login (Won't Work for CI/CD)
```bash
# This only works locally, not in GitHub Actions
infisical login
make test-all-with-infisical
```

**Problem**: 
- GitHub Actions containers are ephemeral
- Can't do interactive login
- Session doesn't persist

### ✅ Service Tokens (Works for CI/CD)
```yaml
# Stored once in GitHub secrets
INFISICAL_TOKEN: ${{ secrets.INFISICAL_TOKEN }}
```

**Benefits**:
- Set up once by admin
- Anyone can trigger
- Automatic authentication
- No key sharing needed

---

## 🔧 Admin: How to Set Up (One-Time)

### 1. Create Infisical Service Token

```bash
# In Infisical dashboard:
# 1. Go to Project Settings
# 2. Service Tokens → Create Token
# 3. Copy the token (starts with 'st.')
```

### 2. Add to GitHub Secrets

```bash
# Go to repository settings:
# Settings → Secrets and variables → Actions → New secret

Name: INFISICAL_TOKEN
Value: st.xxxxx...  (paste your token)

Name: INFISICAL_PROJECT_ID  
Value: proj_xxxxx...  (your project ID)
```

### 3. Done!

Now any team member can trigger tests without knowing these values.

---

## 🐛 Troubleshooting

### "Workflow not found"
- Check you're in the Actions tab
- Look for "PR Test Automation" in the left sidebar
- Ensure the workflow file is on your default branch

### "Unable to trigger workflow"
- Check you have repository access
- Ensure Actions are enabled for the repo
- Contact admin to verify permissions

### "Tests fail with authentication error"
- Admin needs to check GitHub secrets are set
- Verify Infisical token hasn't expired
- Check Infisical project ID is correct

### "No results posted"
- Check the workflow run logs
- Look for errors in the "Run tests" step
- Download artifacts for detailed logs

---

## 📝 Example Workflow

**Team Member**: "I want to test my feature branch"

1. Push your branch to GitHub
2. Go to Actions tab
3. Click "Run workflow"
4. Enter your branch name
5. Click "Run workflow" button
6. Wait 15-30 minutes
7. Check results in Actions or PR comment

**No keys or credentials needed!**

---

## 🎓 Best Practices

1. **Test Before PR**: Run tests on your branch first
2. **Check Results**: Review the full output before merging
3. **Download Artifacts**: Save logs for debugging
4. **Don't Share Tokens**: Use the UI, not tokens
5. **Report Issues**: If tests fail unexpectedly, notify team

---

## 📚 Related Documentation

- [Quick Start Guide](QUICK_START_CI.md) - Local testing
- [Complete Setup](CI_CD_SETUP.md) - Full configuration
- [CI/CD Overview](../README_CI.md) - Architecture

---

**Summary**: 
✅ Admin sets up secrets once
✅ Anyone can trigger tests anytime
✅ No key sharing required
✅ Secure and auditable

