# PDD Setup Guide

This guide covers the comprehensive `pdd setup` command, which helps you configure PDD with API keys, local LLMs, custom providers, and project settings.

## Overview

The `pdd setup` wizard provides an interactive menu-driven interface for configuring your PDD installation. It automatically:

- **Scans your environment** for API keys from all sources (shell, .env, ~/.pdd files)
- **Validates API keys** with real test requests to ensure they work
- **Manages providers** - add, fix, or remove LLM providers
- **Configures local LLMs** - Ollama, LM Studio, or custom endpoints
- **Selects model tiers** - with cost transparency and guidance
- **Detects agentic CLIs** - checks for claude, gemini, codex and offers installation
- **Creates .pddrc** - project configuration with sensible defaults

## Quick Start

```bash
pdd setup
```

After installation, run the setup wizard. It will scan your environment and present an interactive menu.

## The Setup Flow

### 1. Environment Scan

When you run `pdd setup`, it first scans for API keys:

```
═══════════════════════════════════════════════════════
Scanning for API keys...
═══════════════════════════════════════════════════════

  ANTHROPIC_API_KEY    ✓ Valid   (shell environment)
  OPENAI_API_KEY       ✓ Valid   (.env file)
  GROQ_API_KEY         ✗ Invalid (shell environment)
  GEMINI_API_KEY       — Not found
  FIREWORKS_API_KEY    — Not found
```

The scan shows:
- **✓ Valid**: Key found and validated with a test request
- **✗ Invalid**: Key found but failed validation
- **— Not found**: No key found in any source

**Source transparency:** Each key shows where it's loaded from:
- `(shell environment)` - From your shell's environment variables
- `(.env file)` - From the project's .env file
- `(~/.pdd/api-env.zsh)` - From PDD's managed key file

### 2. Interactive Menu

After the scan, you see the main menu:

```
What would you like to do?
  1. Add or fix API keys
  2. Add a local LLM (Ollama, LM Studio)
  3. Add a custom provider
  4. Remove a provider
  5. Continue →
```

#### Option 1: Add or Fix API Keys

This option shows only providers that are missing or invalid:

```
GROQ_API_KEY (currently: invalid):
  Enter new key: gsk_abc...
  Testing with groq/mixtral-8x7b-32768... ✓ Valid

GEMINI_API_KEY (currently: not set):
  Enter key (or press Enter to skip): AIza...
  Testing with gemini/gemini-1.5-flash... ✓ Valid
```

**Smart key storage:**
- Keys you **enter during setup** are saved to `~/.pdd/api-env.{{shell}}`
- Keys **already in your environment** are not duplicated

After adding keys, you return to the main menu with an updated scan.

#### Option 2: Add a Local LLM

Local models (Ollama, LM Studio) don't need API keys - they need a `base_url` and model name:

```
What tool are you using?
  1. LM Studio (default: localhost:1234)
  2. Ollama (default: localhost:11434)
  3. Other (custom base URL)
  Choice: 2

Querying Ollama at http://localhost:11434...
Found installed models:
  1. llama3:70b
  2. codellama:34b
  3. mistral:7b

Which models do you want to add? [1,2,3]: 1,2
✓ Added ollama_chat/llama3:70b and ollama_chat/codellama:34b to llm_model.csv
```

**Features:**
- **Ollama auto-detection**: Queries the API to list installed models
- **LM Studio defaults**: Pre-fills localhost:1234 base URL
- **Custom endpoints**: For any LiteLLM-compatible provider
- **Zero cost**: Local models are set to $0 or $0.0001 costs

#### Option 3: Add a Custom Provider

For LiteLLM-compatible providers not in the default CSV (Together AI, Deepinfra, Mistral, etc.):

```
Provider prefix (e.g. together_ai, deepinfra, mistral): together_ai
Model name: meta-llama/Llama-3-70b-chat
API key env var name: TOGETHERAI_API_KEY
Base URL (press Enter if standard):
Cost per 1M input tokens (optional): 0.90
Cost per 1M output tokens (optional): 0.90

Testing together_ai/meta-llama/Llama-3-70b-chat... ✓ Valid
✓ Added to llm_model.csv
```

This lets you add any provider without manually editing the CSV.

#### Option 4: Remove a Provider

Shows configured providers and lets you safely remove one:

```
Configured providers:
  1. ANTHROPIC_API_KEY   (3 models)
  2. OPENAI_API_KEY      (5 models)
  3. GROQ_API_KEY        (1 model)
  4. TOGETHERAI_API_KEY  (1 model)  [custom]

Remove which provider? 4

  # Commented out by pdd setup on 2026-02-09
  # export TOGETHERAI_API_KEY='tok_abc...'

  Removed 1 model from llm_model.csv
✓ TOGETHERAI_API_KEY removed
```

**Safe removal:**
- Keys are **commented out**, never deleted (easy to recover)
- Model rows are removed from `llm_model.csv`
- Prevents orphaned models in the CSV

#### Option 5: Continue

Proceeds to model selection, CLI detection, and .pddrc creation.

### 3. Model Tier Selection

After configuring providers (option 5), the wizard shows available models grouped by cost tier:

```
Models available for ANTHROPIC_API_KEY:

  #  Model                          Input    Output   ELO
  1. anthropic/claude-opus-4-5       $5.00    $25.00   1474
  2. anthropic/claude-sonnet-4-5     $3.00    $15.00   1370
  3. anthropic/claude-haiku-4-5      $1.00    $5.00    1270

Tip: pdd uses --strength (0.0–1.0) to pick models by cost/quality at runtime.
Adding all models gives you the full range.

Include which models? [1,2,3] (default: all): 2,3
```

**Cost transparency:**
- Shows input/output token costs per million
- Displays ELO ratings for quality comparison
- Explains how `--strength` controls model selection

**Smart defaults:**
- Press Enter to include all models (recommended)
- Or select specific tiers (e.g., just Haiku + Sonnet to avoid Opus costs)

### 4. Agentic CLI Detection

After model selection, setup checks for agentic CLI tools:

```
Checking agentic CLI harnesses...
(Required for: pdd fix, pdd change, pdd bug)

  Claude CLI   ✓ Found at /usr/local/bin/claude
  Codex CLI    ✗ Not found
  Gemini CLI   ✗ Not found

You have OPENAI_API_KEY but Codex CLI is not installed.
  Install with: npm install -g @openai/codex
  Install now? [y/N]
```

This proactive detection prevents errors when running `pdd fix` or `pdd change`.

### 5. .pddrc Initialization

Finally, setup offers to create a `.pddrc` configuration:

```
No .pddrc found in current project.

Would you like to create one with default settings?
  Default language: python
  Output path: pdd/
  Test output path: tests/

Create .pddrc? [Y/n]
```

**Auto-detection:**
- Detects language from project files (setup.py, package.json, go.mod)
- Sets conventional paths for that language
- Creates properly formatted YAML configuration

## API Key Loading Priority

PDD checks for API keys in this order (highest priority first):

1. **Shell environment variables** - `export ANTHROPIC_API_KEY=...`
2. **`.env` file** - In the project root
3. **`~/.pdd/api-env.{{shell}}`** - PDD's managed key file

**Why this order?**
- Shell vars override .env (industry standard with `load_dotenv(override=False)`)
- Allows .env for development defaults, shell vars for production secrets
- Prevents .env from accidentally overwriting intentional shell configs

**Source transparency:** The setup scan shows exactly which source provides each key.

## Saving Keys: Smart Storage

The setup wizard uses smart storage rules:

- **Keys entered during setup** → Saved to `~/.pdd/api-env.{{shell}}`
- **Keys already in shell/environment** → Not saved (avoids duplicates)

This prevents duplicating keys managed by Infisical, .env, shell profiles, etc.

Example:
```
Saving keys...
  GROQ_API_KEY        → saved to ~/.pdd/api-env.zsh (entered during setup)
  GEMINI_API_KEY      → saved to ~/.pdd/api-env.zsh (entered during setup)
  ANTHROPIC_API_KEY   → skipped (already in shell environment)
  OPENAI_API_KEY      → skipped (already in .env file)
```

## Re-running Setup

You can run `pdd setup` at any time to:

- Add new providers or fix invalid keys
- Add local LLM endpoints
- Remove providers
- Update model selections
- Reinstall shell completion

The wizard always starts with a fresh environment scan, so you see the current state.

## Manual Configuration (Alternative)

If you prefer not to use the wizard, you can configure PDD manually:

### Manual API Key Setup

Create `~/.pdd/api-env.zsh` (or `.bash`):

```bash
export ANTHROPIC_API_KEY='sk-ant-...'
export OPENAI_API_KEY='sk-...'
export GEMINI_API_KEY='AIza...'
```

Source it from your shell profile (~/.zshrc or ~/.bashrc):

```bash
# Load PDD API keys
[ -f ~/.pdd/api-env.zsh ] && source ~/.pdd/api-env.zsh
```

### Manual .pddrc Setup

Create `.pddrc` in your project root:

```yaml
version: "1.0"

contexts:
  default:
    defaults:
      generate_output_path: "pdd/"
      test_output_path: "tests/"
      example_output_path: "context/"
      default_language: "python"
      target_coverage: 80.0
      strength: 1.0
      temperature: 0.0
      budget: 10.0
      max_attempts: 3
```

### Manual llm_model.csv

See [SETUP_WITH_GEMINI.md](../SETUP_WITH_GEMINI.md) for full manual configuration instructions.

## Troubleshooting

### "API key not found"

Run the setup wizard:
```bash
pdd setup
```

It will scan all sources and show you exactly which keys are missing and where existing keys are loaded from.

### "Invalid API key"

The setup wizard tests keys immediately with `llm_invoke`. If validation fails:

1. Check the error message for details (authentication vs network vs config)
2. Verify the key format (some providers have format requirements)
3. Check your account/quota status with the provider

### Keys in multiple sources

If a key exists in both .env and shell:

- **Shell environment takes precedence** (industry standard)
- The setup scan shows which source is active: `(shell environment)`
- This prevents .env from overwriting intentional shell configs

### Missing Ollama models

If Ollama auto-detection fails:

1. Check that Ollama is running: `ollama serve`
2. Verify the API is accessible: `curl http://localhost:11434/api/tags`
3. Fall back to manual model name entry in the wizard

## Advanced Topics

### Vertex AI Configuration

For Google Vertex AI with service accounts:

1. Create a service account JSON file from Google Cloud Console
2. Set `VERTEX_CREDENTIALS=/path/to/service-account.json`
3. Run `pdd setup` and add Vertex AI models when prompted

### Multiple Projects

- **Global keys**: Store in `~/.pdd/api-env.{{shell}}` for all projects
- **Project keys**: Store in project `.env` for project-specific overrides
- **Model preferences**: Each project can have its own `llm_model.csv` in `.pdd/`

### CI/CD Integration

For CI/CD pipelines:

1. Don't use the interactive wizard (it requires user input)
2. Set API keys as environment variables in your CI system
3. Copy a pre-configured `llm_model.csv` to the project or user directory
4. Set `PDD_SKIP_SETUP=1` to bypass setup checks

## Related Documentation

- [README.md](../README.md) - Main PDD documentation
- [SETUP_WITH_GEMINI.md](../SETUP_WITH_GEMINI.md) - Manual setup guide
- [ONBOARDING.md](ONBOARDING.md) - Developer onboarding guide
- [whitepaper.md](whitepaper.md) - PDD concepts and architecture
