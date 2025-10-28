# Cloud Run Quick Start (No gcloud CLI Needed!)

Set up Google Cloud Run test execution using **only GitHub Actions** - no local CLI installation required.

## Prerequisites (5 minutes)

1. **Google Cloud Account** - Free tier available
2. **GCP Project with Billing** - Required for Cloud Run
3. **GitHub Repository Access** - Admin permissions

## Step-by-Step Setup

### 1. Create GCP Project (Browser Only)

Go to Google Cloud Console:

```
https://console.cloud.google.com/projectcreate
```

1. Click "New Project"
2. Project name: `PDD Testing`
3. Project ID: `pdd-testing` (or choose your own)
4. Click "Create"
5. **Enable Billing**: https://console.cloud.google.com/billing
   - Link a billing account (required for Cloud Run)
   - Free tier includes $300 credit

### 2. Set Up Workload Identity Federation (One-Time)

This allows GitHub Actions to access your GCP project securely.

**In Cloud Console:**

1. Go to **IAM & Admin → Workload Identity Federation**
   ```
   https://console.cloud.google.com/iam-admin/workload-identity-pools
   ```

2. Click **"Create Pool"**:
   - Name: `github-pool`
   - ID: `github-pool`
   - Click "Continue"

3. Click **"Add Provider"**:
   - Provider type: `OpenID Connect (OIDC)`
   - Provider name: `github-provider`
   - Issuer URL: `https://token.actions.githubusercontent.com`
   - Audiences: `Default audience`
   - Attribute mappings:
     ```
     google.subject = assertion.sub
     attribute.repository = assertion.repository
     attribute.actor = assertion.actor
     ```
   - Attribute conditions:
     ```
     assertion.repository_owner == 'gltanaka'
     ```
   - Click "Save"

4. **Create Service Account**:
   - Go to: IAM & Admin → Service Accounts
   - Click "Create Service Account"
   - Name: `github-actions`
   - Role: `Cloud Run Admin`
   - Role: `Artifact Registry Writer`
   - Role: `Secret Manager Secret Accessor`
   - Role: `Logging Viewer`
   - Click "Done"

5. **Link Service Account to Workload Identity**:
   - Click on the service account
   - Go to "Permissions" tab
   - Click "Grant Access"
   - New principal: 
     ```
     principalSet://iam.googleapis.com/projects/PROJECT_NUMBER/locations/global/workloadIdentityPools/github-pool/attribute.repository/gltanaka/pdd
     ```
   - Role: `Workload Identity User`
   - Click "Save"

**Get your Project Number:**
```
https://console.cloud.google.com/home/dashboard?project=pdd-testing
```
(Shows in top section)

### 3. Add GitHub Secrets

Go to your repository settings:
```
https://github.com/gltanaka/pdd/settings/secrets/actions
```

Click **"New repository secret"** for each:

| Secret Name | Value | Where to Find |
|-------------|-------|---------------|
| `GCP_PROJECT_ID` | `pdd-testing` | Your project ID |
| `GCP_REGION` | `us-central1` | Your preferred region |
| `GCP_WORKLOAD_IDENTITY_PROVIDER` | `projects/PROJECT_NUM/locations/global/workloadIdentityPools/github-pool/providers/github-provider` | From step 2 |
| `GCP_SERVICE_ACCOUNT` | `github-actions@pdd-testing.iam.gserviceaccount.com` | From step 2 |
| `INFISICAL_TOKEN` | `st.xxxxx...` | Your Infisical service token |
| `INFISICAL_PROJECT_ID` | `proj_xxxxx` | Your Infisical project ID |

### 4. Run Automated Setup

Now let GitHub Actions do all the work!

1. **Go to Actions tab** in your repository:
   ```
   https://github.com/gltanaka/pdd/actions
   ```

2. **Find workflow** "Setup Cloud Run Infrastructure"

3. **Click "Run workflow"**:
   - Branch: `feat/automate-regression-unit-tests`
   - Project ID: `pdd-testing`
   - Region: `us-central1`
   - Click "Run workflow"

4. **Wait ~10 minutes** while it:
   - Enables GCP APIs
   - Creates Artifact Registry
   - Stores Infisical token
   - Builds Docker image
   - Creates Cloud Run Job
   - Runs test execution

5. **Check the logs** to see progress

### 5. Verify Setup

After the workflow completes:

1. **Check Cloud Run Jobs**:
   ```
   https://console.cloud.google.com/run/jobs?project=pdd-testing
   ```
   - Should see: `pdd-test-runner`

2. **Check Artifact Registry**:
   ```
   https://console.cloud.google.com/artifacts?project=pdd-testing
   ```
   - Should see: `pdd-images` repository

3. **Check Secrets**:
   ```
   https://console.cloud.google.com/security/secret-manager?project=pdd-testing
   ```
   - Should see: `infisical-token`

### 6. Test with a PR

Create a test PR to trigger automated testing:

```bash
# Make a small change
echo "# Test" >> README.md
git add README.md
git commit -m "test: trigger cloud run tests"
git push

# Create PR on GitHub
```

The `PR Tests on Google Cloud Run` workflow will:
1. Build Docker image with your code
2. Push to Artifact Registry
3. Execute tests on Cloud Run
4. Post results to PR

## What Gets Created Automatically

The setup workflow creates:

```
✅ Artifact Registry repository (pdd-images)
✅ Secret Manager secret (infisical-token)
✅ Service Account (cloud-run-test-runner)
✅ Cloud Run Job (pdd-test-runner)
✅ Initial Docker image
✅ Test execution (validates setup)
```

## Troubleshooting

### "Workflow not found"
- Make sure you've pushed the branch with the workflows
- Check in `.github/workflows/` directory

### "Permission denied"
- Verify Workload Identity Federation is set up correctly
- Check service account has required roles
- Verify attribute conditions match your repository

### "API not enabled"
- The workflow enables APIs automatically
- Wait a few minutes after first run
- Check: https://console.cloud.google.com/apis/dashboard

### "Billing not enabled"
- Cloud Run requires billing account
- Enable at: https://console.cloud.google.com/billing
- Link to your project

## Cost Estimate

**Setup:** Free (one-time, ~10 minutes)

**Per test run:**
- 4 CPU, 4GB RAM
- 30 minutes
- ~$0.05 per run

**Monthly (100 PR tests):**
- ~$5/month
- First $300 credit covers ~6000 test runs

## Next Steps

1. ✅ Setup complete (via GitHub Actions)
2. ✅ Cloud Run infrastructure ready
3. ➡️ Create test PR to validate
4. ➡️ Monitor costs in GCP console
5. ➡️ Adjust resources if needed

## Switching Between GitHub Actions and Cloud Run

### Use GitHub Actions (Free)
Rename workflows:
```bash
mv .github/workflows/pr-tests-cloud-run.yml .github/workflows/pr-tests-cloud-run.yml.disabled
mv .github/workflows/pr-tests.yml .github/workflows/pr-tests.yml.enabled
```

### Use Cloud Run (Isolated)
Rename workflows:
```bash
mv .github/workflows/pr-tests.yml .github/workflows/pr-tests.yml.disabled
mv .github/workflows/pr-tests-cloud-run.yml .github/workflows/pr-tests-cloud-run.yml.enabled
```

### Use Both (Recommended)
Keep both workflows active - get results from both!

## Support

- **GCP Issues:** Check Cloud Run logs and IAM permissions
- **GitHub Issues:** Verify secrets are set correctly
- **Workflow Issues:** Check Actions logs for errors

---

**Total Time:** ~15 minutes (mostly waiting)
**No CLI Installation:** Everything via browser + GitHub
**Automated:** GitHub Actions handles the setup

