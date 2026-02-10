from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.setup.provider_manager import add_or_fix_keys, add_custom_provider, remove_provider
from pdd.setup.api_key_scanner import scan_environment


def main() -> None:
    """
    Demonstrates how to use the provider_manager module to:
    1. Add or fix API keys for existing providers
    2. Add custom LiteLLM-compatible providers
    3. Remove providers (comment out keys, remove CSV rows)
    """

    print("Provider Management Example\n")

    # First, scan the environment to see what's configured
    print("Scanning current configuration...")
    scan_results = scan_environment()

    # Example 1: Add or fix keys for missing/invalid providers
    print("\n--- Example 1: Add or Fix Keys ---")
    print("This would prompt for any missing or invalid keys found in the scan.")
    # add_or_fix_keys(scan_results)  # Uncomment to run interactively

    # Example 2: Add a custom provider
    print("\n--- Example 2: Add Custom Provider ---")
    print("This guides you through adding a custom LiteLLM provider (e.g., Together AI, Deepinfra).")
    # add_custom_provider()  # Uncomment to run interactively

    # Example 3: Remove a provider
    print("\n--- Example 3: Remove Provider ---")
    print("This shows configured providers and lets you remove one.")
    print("Removal comments out the key (doesn't delete) and removes model rows from CSV.")
    # remove_provider(scan_results)  # Uncomment to run interactively

    print("\nKey Features:")
    print("  • Smart storage: Only saves newly entered keys to ~/.pdd/api-env.{{shell}}")
    print("  • Key commenting: Never deletes keys, only comments with timestamp")
    print("  • Atomic CSV writes: Uses temp file + rename to prevent corruption")
    print("  • Validation: Tests keys with llm_invoke before saving")


if __name__ == "__main__":
    main()
