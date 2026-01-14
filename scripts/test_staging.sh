#!/bin/bash
set -e

echo "=== Testing Staging Configuration ==="
echo ""

# Ensure PDD_ENV is staging
export PDD_ENV=staging

# Run with Infisical to inject secrets
infisical run --env=staging -- bash -c '
    echo "Loaded Environment Variables:"
    echo "  PDD_ENV: $PDD_ENV"
    echo "  PDD_CLOUD_URL: $PDD_CLOUD_URL"
    echo "  GITHUB_CLIENT_ID_STAGING: ${GITHUB_CLIENT_ID_STAGING:0:10}..."
    echo "  NEXT_PUBLIC_FIREBASE_API_KEY_STAGING: ${NEXT_PUBLIC_FIREBASE_API_KEY_STAGING:0:20}..."
    echo ""

    # Export staging variables (Infisical injects _STAGING versions)
    export GITHUB_CLIENT_ID=$GITHUB_CLIENT_ID_STAGING
    export NEXT_PUBLIC_FIREBASE_API_KEY=$NEXT_PUBLIC_FIREBASE_API_KEY_STAGING

    echo "=== Starting PDD Connect (Staging) ==="
    echo "y" | pdd connect --allow-remote --no-browser
'
