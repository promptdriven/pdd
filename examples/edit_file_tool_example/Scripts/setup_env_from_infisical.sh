#!/bin/bash
# Setup environment variables from Infisical
# Usage: source scripts/setup_env_from_infisical.sh

# Check if infisical CLI is installed
if ! command -v infisical &> /dev/null; then
    echo "Error: Infisical CLI not found. Please install it first:"
    echo "npm install -g @infisical/cli"
    exit 1
fi

# Check if already logged in to Infisical
if ! infisical whoami &> /dev/null; then
    echo "Please login to Infisical first:"
    echo "infisical login"
    exit 1
fi

echo "Fetching secrets from Infisical..."

# Export environment variables from Infisical
# Adjust the project ID and environment as needed
export $(infisical secrets --env=prod --format=dotenv | xargs)

echo "Environment variables loaded from Infisical successfully!"

# Verify key variables are set
echo "Verifying key variables:"
echo "ANTHROPIC_API_KEY: ${ANTHROPIC_API_KEY:0:10}..."
echo "OPENAI_API_KEY: ${OPENAI_API_KEY:0:10}..."
echo "GOOGLE_API_KEY: ${GOOGLE_API_KEY:0:10}..."
echo "VERTEX_AI_PROJECT: ${VERTEX_AI_PROJECT}"
echo "VERTEX_AI_LOCATION: ${VERTEX_AI_LOCATION}"