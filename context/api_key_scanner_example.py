from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.setup.api_key_scanner import scan_environment, KeyInfo


def main() -> None:
    """
    Demonstrates how to use the api_key_scanner module to:
    1. Dynamically discover all API keys from llm_model.csv
    2. Check multiple sources (shell env, .env file, ~/.pdd/api-env.*)
    3. Get transparency about where each key is loaded from
    """

    print("Scanning environment for API keys...\n")

    # Scan the environment for all API keys defined in llm_model.csv
    scan_results = scan_environment()

    # Display results
    for key_name, key_info in scan_results.items():
        status = "✓ Set" if key_info.is_set else "✗ Not set"
        source = f"({key_info.source})" if key_info.is_set else ""
        masked_value = key_info.value if key_info.is_set else "—"

        print(f"  {key_name:25s} {status:12s} {source:30s}")
        if key_info.is_set:
            print(f"    Value: {masked_value}")

    print(f"\nTotal keys found: {len([k for k in scan_results.values() if k.is_set])}")
    print(f"Total keys missing: {len([k for k in scan_results.values() if not k.is_set])}")


if __name__ == "__main__":
    main()
