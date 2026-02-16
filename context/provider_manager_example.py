from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.setup.provider_manager import (
    add_provider_from_registry,
    add_custom_provider,
    remove_models_by_provider,
    remove_individual_models,
)


def main() -> None:
    """
    Demonstrates how to use the provider_manager module to:
    1. Search/browse litellm's registry to add a provider and specific models
    2. Add a custom LiteLLM-compatible provider
    3. Remove all models for a provider (comments out the key)
    4. Remove individual models from the user CSV
    """

    # Example 1: Search/browse providers from litellm's registry
    # Shows top ~10 providers, lets you search, pick models, enter API key
    # add_provider_from_registry()  # Uncomment to run interactively

    # Interactive flow:
    #   Top providers:
    #     1. OpenAI         (102 chat models)
    #     2. Anthropic       (29 chat models)
    #     ...
    #   Enter number, or type to search: anthropic
    #
    #   Chat models for Anthropic:
    #     1. claude-opus-4-5-20251101    $5.00  $25.00  200,000
    #     2. claude-sonnet-4-5-20250929  $3.00  $15.00  200,000
    #     ...
    #   Select models: 1,2
    #
    #   ANTHROPIC_API_KEY: sk-ant-...
    #   ✓ Added 2 model(s) to ~/.pdd/llm_model.csv

    # Example 2: Add a custom provider (Together AI, Deepinfra, etc.)
    # Prompts for prefix, model name, API key var, base URL, costs
    # add_custom_provider()  # Uncomment to run interactively

    # Example 3: Remove all models for a provider
    # Groups by api_key, removes CSV rows, comments out key in api-env
    # remove_models_by_provider()  # Uncomment to run interactively

    # Example 4: Remove individual models
    # Lists all models, user picks by number, removes selected rows
    # remove_individual_models()  # Uncomment to run interactively


if __name__ == "__main__":
    main()
