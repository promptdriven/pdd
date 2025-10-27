# CI/CD Test Automation Setup Guide

This guide explains how to set up automated test execution for PDD using GitHub Actions, Google Cloud Run, and Infisical for secrets management.

## Overview

The automated testing system:
- ✅ Runs unit tests, regression tests, and sync regression tests
- ✅ Captures pass/fail counts and detailed error messages
- ✅ Posts results as GitHub PR comments
- ✅ Uses Infisical for secure credential management
- ✅ Runs on Google Cloud for consistent execution environment
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

## Prerequisites

### 1. Infisical Setup

1. **Create Infisical Account**
   ```bash
   # Visit https://infisical.com and create account
   ```

2. **Install Infisical CLI**
   ```bash
   npm install -g @infisical/cli
   infisical login
   ```

3. **Create Project and Add Secrets**
   
   Required secrets:
   - `ANTHROPIC_API_KEY` - Claude API key
   - `OPENAI_API_KEY` - OpenAI API key  
   - `GOOGLE_API_KEY` - Google API key
   - `VERTEX_AI_PROJECT` - GCP project ID
   - `VERTEX_AI_LOCATION` - Vertex AI region
   - `GOOGLE_APPLICATION_CREDENTIALS` - Path to service account JSON

4. **Create Service Token**
   ```bash
   # In Infisical console:
   # Project Settings > Service Tokens > Create Token
   # Copy the token for GitHub secrets
   ```

### 2. GitHub Repository Secrets

Add the following secrets in GitHub Repository Settings > Secrets and variables > Actions:

#### Infisical Secrets
- `INFISICAL_TOKEN` - Service token from Infisical
- `INFISICAL_PROJECT_ID` - Your Infisical project ID
- `INFISICAL_CLIENT_ID` - Universal Auth Client ID (for Cloud Run)
- `INFISICAL_CLIENT_SECRET` - Universal Auth Client Secret

#### Google Cloud Secrets (for Cloud Run deployment)
- `GCP_PROJECT_ID` - Your GCP project ID
- `GCP_REGION` - Region for Cloud Run (e.g., `us-central1`)
- `GCP_WORKLOAD_IDENTITY_PROVIDER` - Workload Identity Provider
- `GCP_SERVICE_ACCOUNT` - Service account email
- `GCS_TEST_RESULTS_BUCKET` - GCS bucket for test results (optional)

### 3. Google Cloud Setup

1. **Create GCP Project**
   ```bash
   gcloud projects create pdd-testing --name="PDD Testing"
   gcloud config set project pdd-testing
   ```

2. **Enable Required APIs**
   ```bash
   gcloud services enable \
     run.googleapis.com \
     cloudbuild.googleapis.com \
     artifactregistry.googleapis.com \
     secretmanager.googleapis.com
   ```

3. **Create Artifact Registry**
   ```bash
   gcloud artifacts repositories create pdd-images \
     --repository-format=docker \
     --location=us-central1 \
     --description="PDD test runner images"
   ```

4. **Set up Workload Identity Federation**
   ```bash
   # Create workload identity pool
   gcloud iam workload-identity-pools create "github-pool" \
     --location="global" \
     --description="Pool for GitHub Actions"
   
   # Create provider
   gcloud iam workload-identity-pools providers create-oidc "github-provider" \
     --location="global" \
     --workload-identity-pool="github-pool" \
     --issuer-uri="https://token.actions.githubusercontent.com" \
     --attribute-mapping="google.subject=assertion.sub,attribute.repository=assertion.repository"
   
   # Create service account
   gcloud iam service-accounts create github-actions \
     --display-name="GitHub Actions Service Account"
   
   # Grant permissions
   gcloud projects add-iam-policy-binding PROJECT_ID \
     --member="serviceAccount:github-actions@PROJECT_ID.iam.gserviceaccount.com" \
     --role="roles/run.admin"
   
   gcloud projects add-iam-policy-binding PROJECT_ID \
     --member="serviceAccount:github-actions@PROJECT_ID.iam.gserviceaccount.com" \
     --role="roles/storage.admin"
   
   # Allow GitHub Actions to impersonate service account
   gcloud iam service-accounts add-iam-policy-binding \
     github-actions@PROJECT_ID.iam.gserviceaccount.com \
     --member="principalSet://iam.googleapis.com/projects/PROJECT_NUMBER/locations/global/workloadIdentityPools/github-pool/attribute.repository/YOUR_ORG/pdd" \
     --role="roles/iam.workloadIdentityUser"
   ```

5. **Store Infisical Credentials in Secret Manager**
   ```bash
   echo -n "YOUR_CLIENT_ID" | gcloud secrets create infisical-client-id \
     --data-file=- \
     --replication-policy=automatic
   
   echo -n "YOUR_CLIENT_SECRET" | gcloud secrets create infisical-client-secret \
     --data-file=- \
     --replication-policy=automatic
   
   # Grant Cloud Run access
   gcloud secrets add-iam-policy-binding infisical-client-id \
     --member="serviceAccount:github-actions@PROJECT_ID.iam.gserviceaccount.com" \
     --role="roles/secretmanager.secretAccessor"
   
   gcloud secrets add-iam-policy-binding infisical-client-secret \
     --member="serviceAccount:github-actions@PROJECT_ID.iam.gserviceaccount.com" \
     --role="roles/secretmanager.secretAccessor"
   ```

## Usage

### Automated PR Testing

Tests automatically run when:
- New PR is opened
- PR is updated (new commits pushed)
- PR is reopened

Results are posted as a comment on the PR with:
- Pass/fail counts for each test suite
- Duration of test execution
- Detailed failure messages
- Links to full logs

### Manual Test Execution

#### Local with Infisical
```bash
# Run all tests with Infisical
make test-all-with-infisical

# Or directly
infisical run -- make test
infisical run -- make regression
infisical run -- make sync-regression
```

#### Cloud Run Job
```bash
# Trigger test run on Cloud Run
gcloud run jobs execute pdd-test-job \
  --region us-central1 \
  --wait
```

#### Manual Workflow Dispatch
1. Go to GitHub Actions tab
2. Select "PR Test Automation" workflow
3. Click "Run workflow"
4. Enter PR number
5. Click "Run workflow"

### Viewing Results

#### GitHub PR Comments
- Automatically posted to PR
- Updated on each new run
- Shows summary and detailed failures

#### GitHub Actions Artifacts
- Full logs available as artifacts
- Retained for 30 days
- Download from Actions run page

#### Google Cloud Storage (if configured)
- Historical results stored in GCS
- Organized by PR number and timestamp
- Access via Cloud Console or gsutil

## Test Result Format

### GitHub Comment Example
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
- Passed: 25
- Failed: 2
- Duration: 180.5s

**Errors:**
- Validation failed: Complex example execution failed
- Validation failed: Cost file row count insufficient

---
```

### JSON Output Format
```json
{
  "timestamp": "2025-01-15T10:30:00",
  "test_suites": {
    "unit_tests": {
      "name": "Unit Tests (pytest)",
      "exit_code": 0,
      "passed": 120,
      "failed": 0,
      "duration_seconds": 45.2,
      "failures": []
    },
    "regression_tests": {
      "name": "Regression Tests",
      "exit_code": 1,
      "passed": 25,
      "failed": 2,
      "duration_seconds": 180.5,
      "errors": ["Error message 1", "Error message 2"]
    }
  },
  "summary": {
    "total_passed": 145,
    "total_failed": 2,
    "all_passed": false
  }
}
```

## Troubleshooting

### Tests Not Running
- Check GitHub Actions logs for errors
- Verify Infisical token is valid
- Ensure required secrets are set

### Authentication Failures
- Check Infisical project ID
- Verify API keys in Infisical
- Test locally: `infisical run -- make test`

### Cloud Run Deployment Issues
- Verify GCP project ID
- Check service account permissions
- Review Cloud Build logs

### Test Failures
- Download artifacts from GitHub Actions
- Check full logs in `test_results/` directory
- Run locally to reproduce

## Maintenance

### Updating Test Runner
1. Modify `scripts/run_all_tests_with_results.py`
2. Commit and push changes
3. Workflow automatically deploys to Cloud Run (if configured)

### Rotating Secrets
1. Update secrets in Infisical
2. No code changes required
3. Next test run will use new secrets

### Upgrading Dependencies
1. Update `requirements.txt` or `environment.yml`
2. Rebuild Docker image: `docker build -f Dockerfile.cloud-test .`
3. Test locally before deploying

## Cost Considerations

### GitHub Actions
- Free tier: 2000 minutes/month for private repos
- Estimated usage: ~30 minutes per PR
- Monitor usage in billing settings

### Google Cloud Run
- Free tier: 2 million requests/month
- Pay per execution time beyond free tier
- Set budget alerts in GCP console

### Infisical
- Free tier: Unlimited secrets
- Team plan: $18/user/month for advanced features

## Security Best Practices

1. **Never commit secrets** to repository
2. **Use Infisical** for all API keys
3. **Rotate secrets** regularly
4. **Limit service account** permissions
5. **Enable branch protection** rules
6. **Review PR changes** before merging
7. **Monitor access logs** in Infisical

## Support

For issues or questions:
1. Check existing GitHub Issues
2. Review test logs and artifacts
3. Contact team lead or DevOps
4. Create new GitHub Issue with details

