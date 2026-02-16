#!/usr/bin/env bash
set -euo pipefail

# ── Configuration ──────────────────────────────────────────────────────────
PROJECT_ID="${GCP_PROJECT_ID:-prompt-driven-development-stg}"
REGION="${GCP_REGION:-us-central1}"
BUCKET="${GCS_BUCKET:-pdd-ci-results}"
SA_NAME="pdd-ci-batch"
SA_EMAIL="${SA_NAME}@${PROJECT_ID}.iam.gserviceaccount.com"
AR_REPO="pdd-ci"

echo "=== Setting up Cloud Batch CI infrastructure ==="
echo "Project: ${PROJECT_ID}"
echo "Region:  ${REGION}"
echo ""

# ── Enable APIs ───────────────────────────────────────────────────────────
echo "=== Enabling required APIs ==="
gcloud services enable \
    batch.googleapis.com \
    artifactregistry.googleapis.com \
    cloudbuild.googleapis.com \
    secretmanager.googleapis.com \
    logging.googleapis.com \
    storage.googleapis.com \
    aiplatform.googleapis.com \
    --project="${PROJECT_ID}"

# ── Create Artifact Registry repository ───────────────────────────────────
echo "=== Creating Artifact Registry repo: ${AR_REPO} ==="
gcloud artifacts repositories create "${AR_REPO}" \
    --repository-format=docker \
    --location="${REGION}" \
    --project="${PROJECT_ID}" \
    --description="PDD CI test images" \
    2>/dev/null || echo "  (already exists)"

# ── Create GCS bucket ────────────────────────────────────────────────────
echo "=== Creating GCS bucket: ${BUCKET} ==="
gsutil mb -p "${PROJECT_ID}" -l "${REGION}" "gs://${BUCKET}" 2>/dev/null || echo "  (already exists)"

# Set lifecycle policy: auto-delete objects after 30 days
cat > /tmp/pdd-ci-lifecycle.json <<'EOF'
{
    "rule": [
        {
            "action": { "type": "Delete" },
            "condition": { "age": 30 }
        }
    ]
}
EOF
gsutil lifecycle set /tmp/pdd-ci-lifecycle.json "gs://${BUCKET}"
rm /tmp/pdd-ci-lifecycle.json

# ── Create service account ────────────────────────────────────────────────
echo "=== Creating service account: ${SA_EMAIL} ==="
gcloud iam service-accounts create "${SA_NAME}" \
    --display-name="PDD CI Batch Runner" \
    --project="${PROJECT_ID}" \
    2>/dev/null || echo "  (already exists)"

# ── Grant IAM roles ──────────────────────────────────────────────────────
echo "=== Granting IAM roles ==="
ROLES=(
    "roles/batch.agentReporter"
    "roles/logging.logWriter"
    "roles/storage.objectAdmin"
    "roles/secretmanager.secretAccessor"
    "roles/aiplatform.user"
    "roles/artifactregistry.reader"
)

for ROLE in "${ROLES[@]}"; do
    echo "  Granting ${ROLE}"
    gcloud projects add-iam-policy-binding "${PROJECT_ID}" \
        --member="serviceAccount:${SA_EMAIL}" \
        --role="${ROLE}" \
        --condition=None \
        --quiet \
        2>/dev/null || true
done

# ── Create Secret Manager secrets (empty, user adds values later) ─────────
echo "=== Creating Secret Manager secrets ==="
SECRETS=(
    "openai-api-key"
    "pdd-jwt-token"
    "firebase-api-key"
    "github-client-id"
)

for SECRET in "${SECRETS[@]}"; do
    echo "  Creating secret: ${SECRET}"
    gcloud secrets create "${SECRET}" \
        --project="${PROJECT_ID}" \
        --replication-policy="automatic" \
        2>/dev/null || echo "    (already exists)"
done

# ── Summary ───────────────────────────────────────────────────────────────
echo ""
echo "=============================================="
echo "  Setup complete!"
echo ""
echo "  Next steps:"
echo "  1. Add secret values:"
echo "     echo -n 'sk-...' | gcloud secrets versions add openai-api-key --data-file=- --project=${PROJECT_ID}"
echo "     echo -n '...' | gcloud secrets versions add pdd-jwt-token --data-file=- --project=${PROJECT_ID}"
echo "     echo -n '...' | gcloud secrets versions add firebase-api-key --data-file=- --project=${PROJECT_ID}"
echo "     echo -n '...' | gcloud secrets versions add github-client-id --data-file=- --project=${PROJECT_ID}"
echo ""
echo "  2. Build and push Docker image (via Cloud Build):"
echo "     make cloud-test-build"
echo ""
echo "  3. Run tests:"
echo "     make cloud-test-quick"
echo "=============================================="
