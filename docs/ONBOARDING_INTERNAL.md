# PDD Internal Onboarding

For PDD employees with access to shared infrastructure.

> **Note**: This guide supplements the main [ONBOARDING.md](ONBOARDING.md). Complete steps 1-6 from that guide first, then return here for secrets management setup.

## Infisical Setup

PDD employees use Infisical for centralized secrets management instead of local `.env` files for API keys.

### 1. Accept the Invitation

Check your email for an Infisical invitation from the PDD team. Accept it and verify you can see the project in your Infisical dashboard.

### 2. Install the Infisical CLI

Choose the command for your operating system:

**macOS:**
```bash
brew install infisical
```

**Windows (PowerShell):**
```powershell
winget install infisical
```

**Linux:**
```bash
curl -1sLf 'https://artifacts-cli.infisical.com/setup.deb.sh' | sudo -E bash
```

### 3. Authenticate and Link Your Repository

From the root of the `pdd` repository:

```bash
# Log in to your Infisical account
infisical login

# Link your local repo to the Infisical project
infisical init
```

## Local Configuration

Even with Infisical, you need one local setting in your `.env` file:

```bash
# Add to .env (file path can't be stored in Infisical)
VERTEX_CREDENTIALS=/path/to/service-account.json
```

**To get the service account JSON:**
- Ask your team lead for access to the shared GCP service account, or
- Create your own following the Vertex AI setup steps in ONBOARDING.md

## Running Commands

Always use the `infisical run --` prefix to inject secrets:

```bash
# Run tests
infisical run -- make test

# Generate code
infisical run -- pdd generate module_name

# Sync a module
infisical run -- pdd sync module_name
```

## What's in Infisical

The following secrets are managed centrally:

| Category | Variables |
|----------|-----------|
| LLM API Keys | `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, `GOOGLE_API_KEY`, etc. |
| Vertex AI | `VERTEX_PROJECT`, `VERTEX_LOCATION` |
| GCS Caching | `GCS_BUCKET_NAME`, `GCS_HMAC_ACCESS_KEY_ID`, `GCS_HMAC_SECRET_ACCESS_KEY` |

**Not in Infisical** (must be set locally):
- `VERTEX_CREDENTIALS` - path to your local service account JSON file
- `PDD_PATH` - path to your local PDD installation

## Troubleshooting

**"Secret not found" errors:**
- Ensure you ran `infisical init` in the repo root
- Verify you have access to the project in your Infisical dashboard

**"API key appears too short" warnings:**
- This usually means Infisical secrets aren't being loaded
- Check that you're using `infisical run --` prefix

**Conflicts with local `.env`:**
- Infisical values take precedence over `.env` when there's a name conflict
- Keep only `VERTEX_CREDENTIALS` and `PDD_PATH` in your local `.env`

## Cost-Efficient CLI Usage

PDD has Google Cloud credits and limited Claude Max seats. Use AI CLI tools in this order to maximize value:

| Tier | Model | CLI Tool | Cost |
|------|-------|----------|------|
| 1st | Gemini Flash 3.0 | Gemini CLI | Free (GCP credits) |
| 2nd | Gemini Pro 3.0 | Gemini CLI | Free (GCP credits) |
| 3rd | Claude Opus 4.5 | Claude Code CLI | Limited (Max subscription) |

### Try and Escalate

1. **Start with Gemini Flash 3.0** for all tasks
2. **Escalate to Gemini Pro 3.0** if Flash struggles or produces poor results
3. **Use Claude Opus 4.5** only for truly complex problems that Gemini can't handle

This approach leverages our GCP credits while conserving limited Claude Max usage for when it's really needed.
