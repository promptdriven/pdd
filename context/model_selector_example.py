from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.setup.model_selector import interactive_selection


def main() -> None:
    """
    Demonstrates how to use the model_selector module to:
    1. Group models by cost/capability tier
    2. Display pricing information for transparency
    3. Let users select which tiers to enable
    4. Explain how --strength controls model selection
    """

    print("Model Tier Selection Example\n")

    # Assume we have validated providers from earlier steps
    validated_providers = ["Anthropic", "OpenAI", "Google"]

    print("This would present an interactive selection for each provider:")
    print()
    print("Models available for Anthropic:")
    print()
    print("  #  Model                          Input    Output   ELO")
    print("  1. anthropic/claude-opus-4-5      $5.00    $25.00   1474")
    print("  2. anthropic/claude-sonnet-4-5    $3.00    $15.00   1370")
    print("  3. anthropic/claude-haiku-4-5     $1.00    $5.00    1270")
    print()
    print("Tip: pdd uses --strength (0.0–1.0) to pick models by cost/quality at runtime.")
    print("Adding all models gives you the full range.")
    print()
    print("Include which models? [1,2,3] (default: all):")

    # Run the actual interactive selection
    # interactive_selection(validated_providers)  # Uncomment to run interactively

    print("\nKey Features:")
    print("  • Tier classification: Groups models by cost (Fast/Cheap, Balanced, Most Capable)")
    print("  • Cost transparency: Shows input/output token costs per million")
    print("  • Smart defaults: Press Enter to include all models")
    print("  • Strength explanation: Users learn how model selection works at runtime")


if __name__ == "__main__":
    main()
