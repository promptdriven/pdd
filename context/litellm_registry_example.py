from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.setup.litellm_registry import (
    is_litellm_available,
    get_api_key_env_var,
    get_top_providers,
    search_providers,
    get_models_for_provider,
    ProviderInfo,
    ModelInfo,
)


def main() -> None:
    """
    Demonstrates how to use the litellm_registry module to:
    1. Check if litellm data is available
    2. Browse top providers
    3. Search for a provider by name
    4. List chat models for a provider with pricing
    5. Look up API key env var for a provider
    """

    # Check availability
    if not is_litellm_available():
        print("litellm is not installed or has no model data.")
        return

    # Browse top providers (curated list of ~10 major cloud providers)
    print("Top providers:")
    for p in get_top_providers():
        print(f"  {p.display_name:20s}  {p.model_count:3d} chat models  key: {p.api_key_env_var}")
    print()

    # Search for a provider by substring
    results = search_providers("anth")
    print(f"Search 'anth': {len(results)} result(s)")
    for p in results:
        print(f"  {p.display_name} ({p.model_count} models)")
    print()

    # List models for a specific provider
    models = get_models_for_provider("anthropic")
    print(f"Anthropic chat models ({len(models)}):")
    for m in models[:5]:
        print(
            f"  {m.litellm_id:40s}  ${m.input_cost_per_million:>7.2f} in  "
            f"${m.output_cost_per_million:>7.2f} out  "
            f"ctx: {m.max_input_tokens}"
        )
    print()

    # Look up API key env var
    env_var = get_api_key_env_var("anthropic")
    print(f"Anthropic API key env var: {env_var}")

    env_var_unknown = get_api_key_env_var("some_unknown_provider")
    print(f"Unknown provider env var: {env_var_unknown}")


if __name__ == "__main__":
    main()
