# To run this example:
# From project root: python examples/cost_tracker_utility_example.py
# Note: sys.path manipulation in this script ensures imports work from project root

import logging
import sys
from pathlib import Path

# Add project root to Python path for imports
project_root = Path(__file__).parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

# Also ensure the src directory is on sys.path so edit_file_tool can be imported
src_path = project_root / "src"
if str(src_path) not in sys.path:
    sys.path.insert(0, str(src_path))

from edit_file_tool.cost_tracker_utility import (
    calculate_cost,
    get_model_pricing,
    normalize_model_name,
)

def demonstrate_operations() -> None:
    """Demonstrate calling the cost tracker utilities step by step."""

    print("Step 1: Resolve pricing data for a known Claude model.")
    model_alias = "Anthropic/claude-3-7-sonnet-20250219"
    print(f"  original model identifier: {model_alias}")
    normalized = normalize_model_name(model_alias)
    print(f"  normalized identifier for lookups: {normalized}")
    pricing = get_model_pricing(model_alias)
    print("  per-million rates:")
    print(f"    input: {pricing.input_per_million} USD per 1M tokens")
    print(f"    output: {pricing.output_per_million} USD per 1M tokens")

    print("\nStep 2: Calculate cost for a simple request without cache interactions.")
    cost = calculate_cost(
        model=model_alias,
        input_tokens=1200,
        output_tokens=400,
    )
    print(f"  total cost for 1200 input + 400 output tokens: {cost:.8f} USD")

    print("\nStep 3: Include cache writes and reads to see their effect on total cost.")
    cost_with_cache = calculate_cost(
        model=model_alias,
        input_tokens=1200,
        output_tokens=400,
        cache_write_tokens=200,
        cache_read_tokens=300,
    )
    print("  cache interactions use modified per-token rates:")
    print("    write tokens cost 25 percent more than standard input tokens")
    print("    read tokens cost only 10 percent of the standard input rate")
    print(f"  total cost with cache operations: {cost_with_cache:.8f} USD")

    print("\nStep 4: Demonstrate fallback pricing for a newer model string.")
    experimental_model = "claude-3-7-sonnet-preview-20250301"
    try:
        fallback_cost = calculate_cost(
            model=experimental_model,
            input_tokens=500,
            output_tokens=250,
        )
        print(
            f"  fallback cost for {experimental_model} resolved to family pricing: {fallback_cost:.8f} USD"
        )
    except ValueError as exc:
        print(f"  failed to resolve pricing for {experimental_model}: {exc}")

    print("\nStep 5: Show handling of invalid inputs with try/except blocks.")
    invalid_cases = [
        ("", 100, 100),
        ("claude-3-7-sonnet", -10, 50),
        ("claude-3-7-sonnet", 100, True),
        ("unknown-model", 10, 10),
    ]
    for case_model, input_tokens, output_tokens in invalid_cases:
        try:
            _ = calculate_cost(
                model=case_model,
                input_tokens=input_tokens,
                output_tokens=output_tokens,
            )
            print("  unexpected success in invalid case")
        except ValueError as exc:
            print(f"  expected error for model={case_model!r}: {exc}")

    print("\nDemonstration complete.")


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    demonstrate_operations()
