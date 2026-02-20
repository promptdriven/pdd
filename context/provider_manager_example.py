from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.provider_manager import (
    add_provider_from_registry,
    add_custom_provider,
    remove_models_by_provider,
    remove_individual_models,
    parse_api_key_vars,
    is_multi_credential,
)


def main() -> None:
    """
    Demonstrates how to use the provider_manager module to:
    1. Browse the reference CSV to add a provider and its models
    2. Add a custom LiteLLM-compatible provider
    3. Remove all models for a provider (comments out the key)
    4. Remove individual models from the user CSV
    5. Add GitHub Copilot provider (OAuth device flow)
    6. Parse pipe-delimited api_key fields
    """

    # Example 1: Browse providers from the bundled reference CSV
    # Shows numbered provider list with model counts, enter API key
    # add_provider_from_registry()  # Uncomment to run interactively

    # Interactive flow:
    #   Add a provider
    #
    #     1. Anthropic               (5 models)
    #     2. Google Vertex AI        (8 models)
    #     3. OpenAI                  (12 models)
    #     ...
    #   Enter number (empty to cancel): 3
    #
    #   OPENAI_API_KEY: sk-proj-...
    #   ✓ Saved OPENAI_API_KEY to ~/.pdd/api-env.zsh
    #   ✓ Added source line to ~/.zshrc
    #   Key is available now for this session.
    #   ✓ Added 12 model(s) for OpenAI to ~/.pdd/llm_model.csv
    #
    # NOTE: The API key is immediately available in the current session via os.environ,
    # so you can test the model right away. New terminal sessions will also have the
    # key automatically because `source ~/.pdd/api-env.zsh` was added to ~/.zshrc.

    # Example 2: Add a custom provider (Together AI, Deepinfra, etc.)
    # Prompts for prefix, model name, API key var, base URL, costs
    # add_custom_provider()  # Uncomment to run interactively

    # Example 3: Remove all models for a provider
    # Groups by api_key, removes CSV rows, comments out key in api-env
    # remove_models_by_provider()  # Uncomment to run interactively

    # Example 4: Remove individual models
    # Lists all models, user picks by number, removes selected rows
    # remove_individual_models()  # Uncomment to run interactively

    # Example 5: Add GitHub Copilot provider (OAuth device flow)
    # When selecting "Github Copilot" from the registry, pdd setup triggers
    # litellm's interactive OAuth device flow instead of prompting for an API key.
    # add_provider_from_registry()  # Uncomment to run interactively

    # Interactive flow:
    #   Add a provider
    #
    #     ...
    #     5. Github Copilot          (9 models)
    #     ...
    #   Enter number (empty to cancel): 5
    #
    #   Github Copilot Setup
    #
    #   GitHub Copilot authenticates via OAuth device flow.
    #   This will open a browser to authenticate with GitHub.
    #
    #   Authenticate now? [Y/n]: Y
    #   Starting device flow authentication...
    #   <litellm displays a device code and verification URL>
    #   <user visits URL, enters code, authorizes>
    #   ✓ GitHub Copilot authenticated successfully!
    #   ✓ Added 9 model(s) for Github Copilot to ~/.pdd/llm_model.csv
    #
    # NOTE: The OAuth token is cached by litellm at
    # ~/.config/litellm/github_copilot/api-key.json (customizable via
    # GITHUB_COPILOT_TOKEN_DIR and GITHUB_COPILOT_API_KEY_FILE env vars).
    # In --force/CI mode, GitHub Copilot models are skipped if no token exists.

    # Example 6: Utility functions for api_key field parsing
    # Useful when working with CSV rows that have pipe-delimited api_key fields
    single = parse_api_key_vars("OPENAI_API_KEY")
    print(f"Single key vars: {single}")  # ['OPENAI_API_KEY']

    multi = parse_api_key_vars("AWS_ACCESS_KEY_ID|AWS_SECRET_ACCESS_KEY|AWS_REGION_NAME")
    print(f"Multi key vars: {multi}")  # ['AWS_ACCESS_KEY_ID', 'AWS_SECRET_ACCESS_KEY', 'AWS_REGION_NAME']

    print(f"Is multi-credential? {is_multi_credential('A|B')}")  # True
    print(f"Is multi-credential? {is_multi_credential('OPENAI_API_KEY')}")  # False


if __name__ == "__main__":
    main()
