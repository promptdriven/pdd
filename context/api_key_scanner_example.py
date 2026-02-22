from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.api_key_scanner import scan_environment, get_provider_key_names, KeyInfo


def main() -> None:
    """
    Demonstrates how to use the api_key_scanner module to:
    1. Discover all API key variable names from the user's ~/.pdd/llm_model.csv
    2. Scan multiple sources (shell env, .env file, ~/.pdd/api-env.*)
    3. Report existence and source without storing key values

    Note: The scanner reads from the user's configured models, not a hardcoded
    master list. If no models have been added via `pdd setup`, both functions
    return empty results.
    """

    # Get all provider key names from the user's configured CSV
    all_keys = get_provider_key_names()
    print(f"Provider key names from user CSV: {all_keys}\n")

    if not all_keys:
        print("No models configured yet. Use `pdd setup` to add providers.")
        return

    # Scan the environment for all API keys
    print("Scanning environment for API keys...\n")
    scan_results = scan_environment()

    # Display results — note: KeyInfo only has source and is_set, no value
    for key_name, key_info in scan_results.items():
        if key_info.is_set:
            print(f"  {key_name:25s} ✓ Found  ({key_info.source})")
        else:
            print(f"  {key_name:25s} — Not found")

    found = sum(1 for k in scan_results.values() if k.is_set)
    missing = sum(1 for k in scan_results.values() if not k.is_set)
    print(f"\nFound: {found}  Missing: {missing}")


if __name__ == "__main__":
    main()
