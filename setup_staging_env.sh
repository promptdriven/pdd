#!/bin/bash
# Setup script for PDD staging environment
# This configures your environment to use PDD Cloud staging instead of production

echo "🔧 Configuring PDD for staging environment..."

# Staging cloud URL
export PDD_CLOUD_URL="https://us-central1-prompt-driven-development-stg.cloudfunctions.net"

# Staging Firebase API key
export NEXT_PUBLIC_FIREBASE_API_KEY="AIzaSyC7rX6OLGVDlzkU8q7nK_i14ggOqjNz2N4"

# Optional: Set GitHub client ID if you have one for staging
# export GITHUB_CLIENT_ID="your-staging-github-client-id"

echo "✓ Environment configured:"
echo "  PDD_CLOUD_URL=$PDD_CLOUD_URL"
echo "  NEXT_PUBLIC_FIREBASE_API_KEY=${NEXT_PUBLIC_FIREBASE_API_KEY:0:20}..."

echo ""
echo "📝 Next steps:"
echo "  1. Clear old authentication: rm -f ~/.pdd/jwt_cache"
echo "  2. Authenticate with staging: pdd auth login"
echo "  3. Start remote session: pdd connect"
echo ""
echo "⚠️  To make this permanent, add these exports to your ~/.zshrc or ~/.bashrc"
