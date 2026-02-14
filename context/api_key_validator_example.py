from __future__ import annotations

import os
import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.setup.api_key_validator import validate_key, ValidationResult


def main() -> None:
    """
    Demonstrates how to use the api_key_validator module to:
    1. Validate API keys using llm_invoke instead of HTTP requests
    2. Get detailed error messages for debugging
    3. Understand which model was tested and which provider
    """

    print("API Key Validation Example\n")

    # Example 1: Validate Anthropic API key
    anthropic_key = os.getenv("ANTHROPIC_API_KEY")
    if anthropic_key:
        print("Testing ANTHROPIC_API_KEY...")
        result = validate_key("ANTHROPIC_API_KEY", anthropic_key)
        display_result(result)
    else:
        print("ANTHROPIC_API_KEY not set - skipping validation")

    print()

    # Example 2: Validate OpenAI API key
    openai_key = os.getenv("OPENAI_API_KEY")
    if openai_key:
        print("Testing OPENAI_API_KEY...")
        result = validate_key("OPENAI_API_KEY", openai_key)
        display_result(result)
    else:
        print("OPENAI_API_KEY not set - skipping validation")

    print()

    # Example 3: Test with invalid key
    print("Testing with invalid key...")
    result = validate_key("ANTHROPIC_API_KEY", "sk-ant-invalid-key-123")
    display_result(result)


def display_result(result: ValidationResult) -> None:
    """Helper to display validation results"""
    if result.is_valid:
        print(f"  ✓ Valid - Provider: {result.provider}, Model tested: {result.model_tested}")
    else:
        print(f"  ✗ Invalid - Provider: {result.provider}")
        if result.error_message:
            print(f"    Error: {result.error_message}")


if __name__ == "__main__":
    main()
