# Quick Start: Automated Testing with CI/CD

This guide helps you quickly set up and use the automated testing system.

## 🚀 Quick Setup (5 Minutes)

### 1. Install Infisical CLI
```bash
npm install -g @infisical/cli
infisical login
```

### 2. Add GitHub Secrets

Go to your GitHub repository → Settings → Secrets and variables → Actions

Add these secrets:
- `INFISICAL_TOKEN` - Get from Infisical project settings
- `INFISICAL_PROJECT_ID` - Your Infisical project ID

### 3. Test Locally

```bash
# Make sure you're in the pdd conda environment
conda activate pdd

# Run all tests with Infisical
make test-all-with-infisical
```

That's it! Now every PR will automatically run tests and post results as comments.

## 📝 Usage Examples

### Run Tests Locally

```bash
# All test suites with Infisical
make test-all-with-infisical

# Individual test suites with Infisical
infisical run -- make test
infisical run -- make regression  
infisical run -- make sync-regression

# Without Infisical (using local .env)
make test
make regression
make sync-regression
```

### View Test Results

After running tests, check:
```bash
# View latest results
cat test_results/latest_comment.md

# View JSON results
cat test_results/latest_results.json

# View all results
ls -lt test_results/
```

### Test a Specific PR

Create a PR and the GitHub Actions workflow will automatically:
1. Checkout your PR code
2. Set up the environment
3. Fetch secrets from Infisical
4. Run all test suites
5. Post results as a PR comment
6. Upload detailed logs as artifacts

## 🔍 Understanding Test Results

### Example PR Comment

```markdown
## ✅ Test Results

**Overall Summary:**
- ✅ Passed: 150
- ❌ Failed: 0  
- ⏭️ Skipped: 5
- ⏱️ Duration: 245.3s
```

Status icons:
- ✅ = All tests passed
- ❌ = Some tests failed
- ⏭️ = Tests were skipped

### What Gets Tested

1. **Unit Tests (pytest)**
   - All tests in `tests/test_*.py`
   - Fast, focused unit tests
   - ~1-2 minutes

2. **Regression Tests**
   - Full regression suite in `tests/regression.sh`
   - Tests all CLI commands
   - ~5-10 minutes

3. **Sync Regression Tests**
   - Sync-specific tests in `tests/sync_regression.sh`
   - Tests sync functionality
   - ~5-10 minutes

## 🐛 Troubleshooting

### "Infisical CLI not found"
```bash
npm install -g @infisical/cli
```

### "Command 'conda' not found"
```bash
# Install miniconda or anaconda first
conda create -n pdd python=3.12
conda activate pdd
```

### "API key appears too short"
- Check your Infisical secrets
- Verify token hasn't expired
- Run: `infisical login` to re-authenticate

### Tests Failing Locally But Pass in CI
- Check your local environment
- Ensure conda env is activated
- Try: `conda env update -f environment.yml`

### PR Comment Not Appearing
- Check GitHub Actions logs
- Verify GITHUB_TOKEN permissions
- Ensure workflow has `pull-requests: write` permission

## 📊 Advanced Features

### Custom Test Runs

Run specific test numbers:
```bash
# Run only regression test #5
TEST_NUM=5 make regression

# Run only sync regression test #3
TEST_NUM=3 make sync-regression
```

### Save Results to Specific Location

```bash
# Custom output directory
mkdir my_test_results
python scripts/run_all_tests_with_results.py
# Results saved to test_results/ by default
```

### Parse Results Programmatically

```python
import json

with open('test_results/latest_results.json') as f:
    results = json.load(f)
    
print(f"Total passed: {results['summary']['total_passed']}")
print(f"Total failed: {results['summary']['total_failed']}")

for suite_name, suite_data in results['test_suites'].items():
    print(f"{suite_name}: {suite_data['passed']} passed, {suite_data['failed']} failed")
```

## 🔐 Security Notes

- Never commit API keys or secrets
- All secrets managed through Infisical
- Service tokens rotate automatically
- Cloud Run uses Secret Manager for credentials

## 📚 Next Steps

1. ✅ Set up Infisical - [See CI_CD_SETUP.md](./CI_CD_SETUP.md)
2. ✅ Configure GitHub Actions - Already done!
3. ⏭️ Optional: Set up Google Cloud Run - [See CI_CD_SETUP.md](./CI_CD_SETUP.md)
4. ⏭️ Optional: Configure GCS for test history - [See CI_CD_SETUP.md](./CI_CD_SETUP.md)

## 💡 Tips

- **Run tests before pushing** to catch issues early
- **Check PR comments** for detailed failure information  
- **Download artifacts** from GitHub Actions for full logs
- **Monitor test duration** to optimize slow tests
- **Update Infisical secrets** rather than code when rotating keys

## 🆘 Getting Help

1. Check [CI_CD_SETUP.md](./CI_CD_SETUP.md) for detailed setup
2. Review GitHub Actions logs
3. Check Infisical dashboard for secret issues
4. Open a GitHub issue with:
   - Error message
   - GitHub Actions run link
   - Steps to reproduce

---

**Ready to go!** Just create a PR and watch the magic happen ✨

