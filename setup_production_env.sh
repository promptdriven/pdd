#!/bin/bash
# Setup script for PDD production environment (recommended for testing)
# Production has properly configured GitHub OAuth

echo "🔧 Configuring PDD for production environment..."

# Use production cloud (has working GitHub OAuth)
# Note: We'll deploy submitCommand to production too
unset PDD_CLOUD_URL  # Use default production URL

# Production Firebase API key (from your existing production setup)
export NEXT_PUBLIC_FIREBASE_API_KEY="AIzaSyBqbF-P9R7jLW8gXVPZqQMxI71FjUE9-lI"

echo "✓ Environment configured for production:"
echo "  PDD_CLOUD_URL: (default) https://us-central1-prompt-driven-development.cloudfunctions.net"
echo "  NEXT_PUBLIC_FIREBASE_API_KEY: ${NEXT_PUBLIC_FIREBASE_API_KEY:0:20}..."

echo ""
echo "📝 Next steps:"
echo "  1. Clear staging auth: rm -f ~/.pdd/jwt_cache"
echo "  2. Authenticate: pdd auth login"
echo "  3. Start remote session: pdd connect"
echo ""
echo "💡 This uses production Firebase which has working GitHub OAuth"
