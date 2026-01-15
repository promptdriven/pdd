# Infisical Setup for PDD

This guide shows how to use Infisical for centralized secret management with PDD, eliminating the intermittent authentication issues.

## Benefits

- **Consistent Authentication**: No more "API key appears too short" warnings
- **Centralized Secrets**: All API keys managed in one secure location
- **Team Sharing**: Easy to share configurations across team members
- **Environment Isolation**: Separate configs for dev/staging/prod

## Prerequisites

1. Install Infisical CLI:
   ```bash
   npm install -g @infisical/cli
   ```

2. Login to Infisical:
   ```bash
   infisical login
   ```

## Required Environment Variables

Store these variables in your Infisical project:

### Core Authentication
- `ANTHROPIC_API_KEY` - Claude API key
- `OPENAI_API_KEY` - OpenAI API key
- `GOOGLE_API_KEY` - Google API key for Vertex AI
- `VERTEX_AI_PROJECT` - Google Cloud project ID
- `VERTEX_AI_LOCATION` - Vertex AI location (e.g., us-central1)
- `GOOGLE_APPLICATION_CREDENTIALS` - Path to service account JSON

### Optional API Keys
- `GROQ_API_KEY`
- `TOGETHER_API_KEY`
- `DEEPSEEK_API_KEY`
- `CEREBRAS_API_KEY`
- `XAI_API_KEY`
- `FIREWORKS_API_KEY`

## Usage Methods

### Method 1: Using Scripts (Recommended)

```bash
# Build single component
./scripts/pdd_with_infisical.sh utils

# Build with flags
./scripts/pdd_with_infisical.sh utils --clean --no-log
```

### Method 2: Using Makefile

```bash
# Build single component
make infisical-component utils

# Build with additional arguments
make infisical-component utils --clean

# Run any command with Infisical
make infisical-run COMMAND="pdd sync utils"
```

### Method 3: Manual Environment Loading

```bash
# Load environment and run commands
source scripts/setup_env_from_infisical.sh
python Scripts/PDD_workflow.py utils
```

## Configuration

Edit `scripts/setup_env_from_infisical.sh` to customize:
- Project ID
- Environment name (prod/dev/staging)
- Additional validation checks

## Troubleshooting

1. **Login Issues**: Run `infisical login` and verify access
2. **Missing Secrets**: Check your Infisical project has all required variables
3. **Permission Issues**: Ensure script is executable: `chmod +x scripts/*.sh`

## Migration from .env

1. Copy existing `.env` values to Infisical
2. Test with: `./scripts/pdd_with_infisical.sh utils`
3. Remove or rename `.env` file once confirmed working
4. Update any CI/CD pipelines to use Infisical

This setup eliminates the authentication inconsistencies and provides better security management.