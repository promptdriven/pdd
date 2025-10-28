# Google Cloud Run Setup for Test Execution

This guide shows how to set up tests to run on Google Cloud Run instead of GitHub Actions runners.

## Why Use Google Cloud Run?

| Feature | GitHub Actions | Google Cloud Run |
|---------|---------------|------------------|
| **Environment** | GitHub's runners | Your isolated GCP environment |
| **Consistency** | Good | Better (same Docker image) |
| **Control** | Limited | Full control over resources |
| **Debugging** | Logs in GitHub | Full Cloud Logging access |
| **Cost** | Free tier: 2000 min/month | Pay per use (~$5-10/month) |
| **Timeout** | 6 hours max | Configurable (up to 24h) |
| **Resources** | 2 CPU, 7GB RAM | 1-8 CPU, up to 32GB RAM |

## Quick Setup Options

### Option A: Automated Setup with GitHub Actions (Easiest - 10 Minutes)

**No `gcloud` installation needed!** Let GitHub Actions set up everything:

1. **Create GCP Project** (in browser):
   - Go to: https://console.cloud.google.com/projectcreate
   - Create project: `pdd-testing`
   - Enable billing: https://console.cloud.google.com/billing
   - Note your project ID

2. **Set up Workload Identity** (one-time, see section below)

3. **Add GitHub Secrets**:
   - `GCP_PROJECT_ID` = your project ID
   - `GCP_REGION` = `us-central1`
   - `GCP_WORKLOAD_IDENTITY_PROVIDER` = (from workload identity setup)
   - `GCP_SERVICE_ACCOUNT` = (from workload identity setup)
   - `INFISICAL_TOKEN` = your Infisical service token
   - `INFISICAL_PROJECT_ID` = your Infisical project ID

4. **Run the Setup Workflow**:
   - Go to: Actions → Setup Cloud Run Infrastructure → Run workflow
   - Enter your project ID
   - Click "Run workflow"
   - Wait ~10 minutes for automated setup

5. **Done!** All infrastructure is created automatically.

### Option B: Manual Setup with gcloud CLI (30 Minutes)

If you prefer manual control or need to debug:

```bash
# Install gcloud CLI first
brew install --cask google-cloud-sdk

# Create project
gcloud projects create pdd-testing --name="PDD Testing"
gcloud config set project pdd-testing

# Enable billing (required)
# Go to: https://console.cloud.google.com/billing

# Enable required APIs
gcloud services enable \
  run.googleapis.com \
  cloudbuild.googleapis.com \
  artifactregistry.googleapis.com \
  secretmanager.googleapis.com \
  logging.googleapis.com
```

### 2. Create Artifact Registry

```bash
# Create Docker repository
gcloud artifacts repositories create pdd-images \
  --repository-format=docker \
  --location=us-central1 \
  --description="PDD test runner images"
```

### 3. Store Infisical Token in Secret Manager

```bash
# Create secret for Infisical token
echo -n "YOUR_INFISICAL_SERVICE_TOKEN" | \
  gcloud secrets create infisical-token \
    --data-file=- \
    --replication-policy=automatic
```

### 4. Set Up Workload Identity Federation

```bash
# Get your project number
PROJECT_NUMBER=$(gcloud projects describe pdd-testing --format='value(projectNumber)')

# Create workload identity pool
gcloud iam workload-identity-pools create "github-pool" \
  --location="global" \
  --description="Pool for GitHub Actions"

# Create provider
gcloud iam workload-identity-pools providers create-oidc "github-provider" \
  --location="global" \
  --workload-identity-pool="github-pool" \
  --issuer-uri="https://token.actions.githubusercontent.com" \
  --attribute-mapping="google.subject=assertion.sub,attribute.repository=assertion.repository,attribute.actor=assertion.actor" \
  --attribute-condition="assertion.repository_owner == 'gltanaka'"

# Create service account
gcloud iam service-accounts create github-actions \
  --display-name="GitHub Actions Service Account"

# Grant permissions to service account
gcloud projects add-iam-policy-binding pdd-testing \
  --member="serviceAccount:github-actions@pdd-testing.iam.gserviceaccount.com" \
  --role="roles/run.admin"

gcloud projects add-iam-policy-binding pdd-testing \
  --member="serviceAccount:github-actions@pdd-testing.iam.gserviceaccount.com" \
  --role="roles/artifactregistry.writer"

gcloud projects add-iam-policy-binding pdd-testing \
  --member="serviceAccount:github-actions@pdd-testing.iam.gserviceaccount.com" \
  --role="roles/secretmanager.secretAccessor"

gcloud projects add-iam-policy-binding pdd-testing \
  --member="serviceAccount:github-actions@pdd-testing.iam.gserviceaccount.com" \
  --role="roles/logging.viewer"

# Allow GitHub Actions to impersonate service account
gcloud iam service-accounts add-iam-policy-binding \
  github-actions@pdd-testing.iam.gserviceaccount.com \
  --member="principalSet://iam.googleapis.com/projects/${PROJECT_NUMBER}/locations/global/workloadIdentityPools/github-pool/attribute.repository/gltanaka/pdd" \
  --role="roles/iam.workloadIdentityUser"
```

### 5. Add GitHub Secrets

Go to: `https://github.com/gltanaka/pdd/settings/secrets/actions`

Add these secrets:

| Secret Name | Value | How to Get |
|-------------|-------|------------|
| `GCP_PROJECT_ID` | `pdd-testing` | Your project ID |
| `GCP_REGION` | `us-central1` | Your preferred region |
| `GCP_WORKLOAD_IDENTITY_PROVIDER` | `projects/PROJECT_NUMBER/locations/global/workloadIdentityPools/github-pool/providers/github-provider` | From step 4 |
| `GCP_SERVICE_ACCOUNT` | `github-actions@pdd-testing.iam.gserviceaccount.com` | From step 4 |

Get workload identity provider:
```bash
gcloud iam workload-identity-pools providers describe github-provider \
  --location=global \
  --workload-identity-pool=github-pool \
  --format='value(name)'
```

### 6. Enable the Cloud Run Workflow

The workflow is in `.github/workflows/pr-tests-cloud-run.yml`

**To use Cloud Run by default:**
1. Rename `pr-tests.yml` to `pr-tests-github.yml` (disable)
2. Rename `pr-tests-cloud-run.yml` to `pr-tests.yml` (enable)

**Or keep both:**
- `pr-tests.yml` - Runs on GitHub Actions (fast, free)
- `pr-tests-cloud-run.yml` - Runs on Cloud Run (isolated, controlled)

## Testing the Setup

### Test Locally First

```bash
# Build Docker image
docker build -f Dockerfile.cloud-test -t pdd-test-runner:local .

# Run tests in Docker (simulates Cloud Run)
docker run --rm \
  -e INFISICAL_TOKEN="your_token_here" \
  -e INFISICAL_PROJECT_ID="your_project_id" \
  pdd-test-runner:local test
```

### Test on Cloud Run

```bash
# Push your branch
git push origin feat/automate-regression-unit-tests

# Create a PR or trigger manually:
# Go to Actions → PR Tests on Google Cloud Run → Run workflow
```

## How It Works

```
1. PR Created/Updated
   ↓
2. GitHub Actions Triggers Cloud Run Workflow
   ↓
3. Build Docker Image with Current Code
   ↓
4. Push Image to Artifact Registry
   ↓
5. Create/Update Cloud Run Job
   ↓
6. Execute Job (runs tests in container)
   ↓
7. Wait for Completion (up to 1 hour)
   ↓
8. Fetch Logs from Cloud Logging
   ↓
9. Parse Test Results
   ↓
10. Post Comment to PR
```

## Viewing Results

### In PR Comments

```markdown
## Test Results (Google Cloud Run) - PASS

**Execution:** pdd-test-runner-abc123
**Region:** us-central1

**Summary:**
- Passed: 150
- Failed: 0
- Skipped: 5

**FAILED TEST NUMBERS:** (none)

---

**View Details:**
- [Cloud Run Console](...)
- [Cloud Logs](...)
```

### In Cloud Console

1. **Cloud Run Jobs:**
   ```
   https://console.cloud.google.com/run/jobs
   ```

2. **Execution Logs:**
   ```
   https://console.cloud.google.com/logs/query?project=pdd-testing
   ```

3. **Cost Dashboard:**
   ```
   https://console.cloud.google.com/billing
   ```

## Configuration

### Adjust Resources

In `.github/workflows/pr-tests-cloud-run.yml`:

```yaml
--memory 4Gi \     # Increase for memory-intensive tests
--cpu 2 \          # Increase for CPU-intensive tests
--task-timeout 3600 # Increase for longer tests
```

### Change Region

```yaml
env:
  GCP_REGION: 'us-east1'  # Change to your preferred region
```

### Set Concurrency Limits

```yaml
--max-retries 0 \      # Don't retry failed tests
--parallelism 1        # Run one task at a time
```

## Cost Management

### Estimate Costs

**Cloud Run Jobs:**
- $0.00002400 per vCPU-second
- $0.00000250 per GiB-second
- First 2M requests free per month

**Example:**
- 4 vCPU, 4GB RAM
- 30 minute test run
- Cost: ~$0.05 per run
- 100 PR runs/month = ~$5/month

### Set Budget Alerts

```bash
# Create budget alert
gcloud billing budgets create \
  --billing-account=YOUR_BILLING_ACCOUNT \
  --display-name="PDD Testing Budget" \
  --budget-amount=20 \
  --threshold-rule=percent=50 \
  --threshold-rule=percent=90 \
  --threshold-rule=percent=100
```

## Troubleshooting

### Job Fails to Start

```bash
# Check service account permissions
gcloud projects get-iam-policy pdd-testing \
  --flatten="bindings[].members" \
  --filter="bindings.members:github-actions@"

# Check if secret exists
gcloud secrets describe infisical-token
```

### Can't Access Secrets

```bash
# Grant secret accessor role
gcloud secrets add-iam-policy-binding infisical-token \
  --member="serviceAccount:github-actions@pdd-testing.iam.gserviceaccount.com" \
  --role="roles/secretmanager.secretAccessor"
```

### Docker Build Fails

```bash
# Test build locally
docker build -f Dockerfile.cloud-test -t test .

# Check Artifact Registry permissions
gcloud artifacts repositories get-iam-policy pdd-images \
  --location=us-central1
```

### Tests Timeout

Increase timeout in workflow:
```yaml
--task-timeout 7200  # 2 hours
```

Or in job config:
```yaml
timeout-minutes: 120  # GitHub Actions timeout
```

## Switching Back to GitHub Actions

If you want to go back to GitHub Actions runners:

1. Rename workflows:
   ```bash
   mv .github/workflows/pr-tests.yml .github/workflows/pr-tests-github.yml
   mv .github/workflows/pr-tests-cloud-run.yml .github/workflows/pr-tests.yml
   ```

2. Or just disable Cloud Run workflow:
   ```yaml
   # Add to top of pr-tests-cloud-run.yml
   on:
     workflow_dispatch:  # Only manual triggers
   ```

## Best Practices

1. **Use GitHub Actions for:**
   - Quick feedback on small PRs
   - Unit tests only
   - Development branches

2. **Use Cloud Run for:**
   - Full regression suites
   - Release candidates
   - Production merges
   - Long-running tests

3. **Hybrid Approach:**
   - Keep both workflows
   - GitHub Actions runs on every push
   - Cloud Run runs on PR ready for review

## Support

- **GCP Issues:** Check Cloud Run logs and service account permissions
- **GitHub Issues:** Verify workload identity federation setup
- **Infisical Issues:** Test token validity locally first

## Next Steps

1. Complete GCP setup (steps 1-5)
2. Add GitHub secrets (step 5)
3. Test locally with Docker (step 6)
4. Create test PR to verify
5. Monitor costs in GCP console
6. Adjust resources as needed

---

**Total Setup Time:** ~30 minutes
**Monthly Cost:** ~$5-20 depending on usage
**Benefits:** Isolated environment, full control, better debugging

