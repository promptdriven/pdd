from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.setup.pddrc_initializer import offer_pddrc_init


def main() -> None:
    """
    Demonstrates how to use the pddrc_initializer module to:
    1. Check if .pddrc exists in current project
    2. Detect project language (Python/TypeScript/etc.)
    3. Offer to create .pddrc with sensible defaults
    """

    print(".pddrc Initialization Example\n")

    print("This checks for .pddrc in the current directory and offers to create one:")
    print()
    print("No .pddrc found in current project.")
    print()
    print("Would you like to create one with default settings?")
    print("  Default language: python")
    print("  Output path: pdd/")
    print("  Test output path: tests/")
    print()
    print("Create .pddrc? [Y/n]")

    # Run the actual initialization
    # was_created = offer_pddrc_init()  # Uncomment to run interactively
    # if was_created:
    #     print("✓ Created .pddrc with default settings")

    print("\n\nKey Features:")
    print("  • Auto-detection: Detects language from project files (setup.py, package.json, etc.)")
    print("  • Sensible defaults: Sets conventional paths for each language")
    print("  • Non-destructive: Never overwrites existing .pddrc")
    print("  • YAML format: Creates properly formatted configuration file")

    print("\n\nExample .pddrc content:")
    print("""
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
""")


if __name__ == "__main__":
    main()
