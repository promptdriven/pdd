# Automated Testing System for PDD

[![Tests](https://github.com/YOUR_ORG/pdd-11/actions/workflows/pr-tests.yml/badge.svg)](https://github.com/YOUR_ORG/pdd-11/actions/workflows/pr-tests.yml)

Automated test execution system that runs unit tests, regression tests, and sync regression tests on every PR, posting results as comments.

## 🎯 Features

- ✅ **Automatic PR Testing** - Tests run automatically on PR creation/updates
- ✅ **Comprehensive Coverage** - Unit tests, regression tests, sync regression tests
- ✅ **Secure Secrets** - Infisical integration for credential management
- ✅ **Cloud Execution** - Optional Google Cloud Run for consistent environment
- ✅ **Detailed Results** - Pass/fail counts, error messages, execution time
- ✅ **PR Comments** - Results posted directly to PR with formatting
- ✅ **Artifact Upload** - Full logs saved as GitHub Actions artifacts

## 🚀 Quick Start

### For Developers

```bash
# 1. Install Infisical CLI
npm install -g @infisical/cli
infisical login

# 2. Run tests locally
conda activate pdd
make test-all-with-infisical

# 3. Create a PR and watch tests run automatically
git checkout -b feature/my-feature
git commit -am "Add new feature"
git push origin feature/my-feature
# Open PR on GitHub → Tests run automatically
```

### For Administrators

See [docs/CI_CD_SETUP.md](docs/CI_CD_SETUP.md) for complete setup instructions including:
- GitHub Actions secrets configuration
- Google Cloud setup
- Infisical project setup
- Service account creation

## 📋 What Gets Tested

### Unit Tests (pytest)
- Location: `tests/test_*.py`
- Duration: ~1-2 minutes
- Coverage: Core functionality, utilities, CLI commands

### Regression Tests  
- Location: `tests/regression.sh`
- Duration: ~5-10 minutes
- Coverage: All PDD commands, edge cases, error handling

### Sync Regression Tests
- Location: `tests/sync_regression.sh`
- Duration: ~5-10 minutes  
- Coverage: Sync functionality, state management, multi-language support

## 💬 PR Comment Format

After tests complete, a comment is automatically posted:

```markdown
## ✅ Test Results

**Overall Summary:**
- ✅ Passed: 150
- ❌ Failed: 2
- ⏭️ Skipped: 5
- ⏱️ Duration: 245.3s

---

### ✅ Unit Tests (pytest)
**Results:**
- Passed: 120
- Failed: 0
- Duration: 45.2s

### ❌ Regression Tests  
**Results:**
- Passed: 28
- Failed: 2
- Duration: 180.5s

**Errors:**
- Validation failed: Complex example execution failed
- Validation failed: Cost file row count insufficient
```

## 🛠️ Local Development

### Run All Tests

```bash
# With Infisical (recommended)
make test-all-with-infisical

# Without Infisical (using .env)
make test              # Unit tests
make regression        # Regression tests
make sync-regression   # Sync regression tests
```

### Run Specific Tests

```bash
# Specific regression test
TEST_NUM=5 make regression

# Specific sync regression test  
TEST_NUM=3 make sync-regression

# With custom settings
STRENGTH=0.9 TEST_LOCAL=true make regression
```

### View Results

```bash
# Latest test results
cat test_results/latest_comment.md

# JSON format
cat test_results/latest_results.json
jq '.summary' test_results/latest_results.json
```

## 🔧 Configuration

### Makefile Targets

| Target | Description |
|--------|-------------|
| `test-all-with-infisical` | Run all tests with Infisical secrets |
| `test-all-ci` | Run all tests with result capture |
| `test` | Run pytest unit tests |
| `regression` | Run regression test suite |
| `sync-regression` | Run sync regression tests |
| `all-regression` | Run all regression suites |

### Environment Variables

Set in Infisical or `.env`:
- `ANTHROPIC_API_KEY` - Claude API key
- `OPENAI_API_KEY` - OpenAI API key
- `GOOGLE_API_KEY` - Google/Vertex AI key
- `VERTEX_AI_PROJECT` - GCP project ID
- `VERTEX_AI_LOCATION` - Vertex AI region

## 📊 GitHub Actions Workflows

### PR Test Automation (`.github/workflows/pr-tests.yml`)
- Triggers: PR opened, synchronized, reopened
- Runs: All test suites
- Posts: Results as PR comment
- Uploads: Test artifacts

### Cloud Run Deployment (`.github/workflows/cloud-run-deploy.yml`)
- Triggers: Push to main, manual dispatch
- Deploys: Test runner to Google Cloud Run
- Updates: Docker image in Artifact Registry

### Manual Test Trigger (`.github/workflows/trigger-cloud-run-tests.yml`)
- Triggers: Workflow call, manual dispatch
- Executes: Tests on Cloud Run
- Posts: Results to PR

## 📂 Project Structure

```
pdd-11/
├── .github/
│   └── workflows/
│       ├── pr-tests.yml              # Main PR testing workflow
│       ├── cloud-run-deploy.yml      # Deploy to Cloud Run
│       └── trigger-cloud-run-tests.yml # Cloud Run test trigger
├── scripts/
│   └── run_all_tests_with_results.py # Test orchestration script
├── tests/
│   ├── test_*.py                     # Unit tests
│   ├── regression.sh                 # Regression test suite
│   └── sync_regression.sh            # Sync regression suite
├── docs/
│   ├── CI_CD_SETUP.md                # Detailed setup guide
│   ├── QUICK_START_CI.md             # Quick start guide
│   └── README_CI.md                  # This file
├── Dockerfile.cloud-test             # Cloud Run container
├── environment.yml                   # Conda environment
└── Makefile                          # Build targets
```

## 🐛 Troubleshooting

### Tests Not Running on PR

1. Check GitHub Actions tab for error logs
2. Verify `INFISICAL_TOKEN` secret is set
3. Ensure PR is from a branch in the same repository (not a fork)
4. Check branch protection rules

### Authentication Failures

```bash
# Re-authenticate with Infisical
infisical login

# Verify secrets are accessible
infisical secrets

# Test locally
make test-all-with-infisical
```

### Cloud Run Deployment Issues

```bash
# Check Cloud Run logs
gcloud run services logs read pdd-test-runner --region=us-central1

# Rebuild and deploy manually
docker build -f Dockerfile.cloud-test -t test-runner .
gcloud run deploy pdd-test-runner --image test-runner --region us-central1
```

## 🔐 Security

- ✅ Secrets managed via Infisical
- ✅ No credentials in code or environment files
- ✅ GitHub Actions uses service tokens
- ✅ Cloud Run uses Secret Manager
- ✅ Workload Identity for GCP authentication
- ✅ Least privilege access controls

## 📈 Monitoring

### View Test History

```bash
# GitHub Actions runs
https://github.com/YOUR_ORG/pdd-11/actions

# Download artifacts
gh run download <run-id> -n test-results-<pr-number>

# Cloud Run logs
gcloud run jobs executions logs read <execution-id>
```

### Track Costs

- **GitHub Actions**: Repository Settings → Billing → Actions usage
- **Google Cloud Run**: Cloud Console → Billing → Reports
- **Infisical**: Free for unlimited secrets

## 🤝 Contributing

When contributing code that affects tests:

1. Run tests locally first: `make test-all-with-infisical`
2. Create PR with descriptive title
3. Wait for automated tests to complete  
4. Review test results in PR comment
5. Fix any failures before requesting review
6. Tests must pass before merging

## 📚 Documentation

- [Quick Start Guide](docs/QUICK_START_CI.md) - Get started in 5 minutes
- [Complete Setup Guide](docs/CI_CD_SETUP.md) - Full configuration details
- [Test Writing Guide](docs/TESTING.md) - How to write effective tests
- [Infisical Setup](examples/edit_file_tool_example/INFISICAL_SETUP.md) - Secrets management

## 🆘 Support

- **Issues**: Create GitHub issue with `ci-cd` label
- **Questions**: Use GitHub Discussions
- **Urgent**: Contact @devops-team

---

**Status**: ✅ Automated testing enabled
**Last Updated**: 2025-01-15
**Maintainer**: DevOps Team

