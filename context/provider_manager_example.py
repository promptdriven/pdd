from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.setup.provider_manager import (
    add_api_key,
    add_custom_provider,
    remove_models_by_provider,
    remove_individual_models,
)
from pdd.setup.api_key_scanner import scan_environment


def main() -> None:
    """
    Demonstrates how to use the provider_manager module to:
    1. Add an API key and auto-load all models for that provider
    2. Add a custom LiteLLM-compatible provider
    3. Remove all models for a provider (comments out the key)
    4. Remove individual models from the user CSV
    """

    # First, scan the environment to see what's configured
    scan_results = scan_environment()

    # Example 1: Add an API key (auto-loads all models for that provider)
    # Shows missing keys, prompts for one, saves to api-env, copies CSV rows
    # add_api_key(scan_results)  # Uncomment to run interactively

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
