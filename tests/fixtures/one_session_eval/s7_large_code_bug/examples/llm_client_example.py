"""Example usage of the llm_client module.

Demonstrates basic invocation, model selection, structured output, and caching.
This example does NOT trigger retries, so it works correctly even with the
buggy code.
"""

import sys
import os
import json

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

import llm_client


def main():
    print("=== LLM Client Example ===\n")

    models = llm_client.load_models()
    print(f"Loaded {len(models)} models\n")

    print("--- Model Selection ---")
    cheap = llm_client.select_model(models, strength=0.0)
    mid = llm_client.select_model(models, strength=0.5)
    best = llm_client.select_model(models, strength=1.0)
    print(f"  Strength 0.0: {cheap.name} (ELO {cheap.elo}, ${cheap.effective_cost:.2f}/M avg)")
    print(f"  Strength 0.5: {mid.name} (ELO {mid.elo}, ${mid.effective_cost:.2f}/M avg)")
    print(f"  Strength 1.0: {best.name} (ELO {best.elo}, ${best.effective_cost:.2f}/M avg)")
    print()

    print("--- Basic Invocation ---")
    client = llm_client.LLMClient()
    result = client.invoke("What is the capital of France?", strength=0.3)
    print(f"  Model: {result.model_name}")
    print(f"  Response: {result.result[:80]}...")
    print(f"  Cost: ${result.cost:.8f}")
    print(f"  Tokens: {result.input_tokens} in / {result.output_tokens} out")
    print()

    print("--- Structured Output ---")
    schema = {
        "type": "object",
        "properties": {
            "result": {"type": "string"},
            "confidence": {"type": "number"},
        },
        "required": ["result"],
    }
    result = client.invoke(
        "Classify this text: 'The weather is nice today'",
        strength=0.5,
        output_schema=schema,
    )
    print(f"  Model: {result.model_name}")
    print(f"  Response: {result.result}")
    print(f"  Cost: ${result.cost:.8f}")
    print()

    print("--- Caching ---")
    r1 = client.invoke("Cached prompt test", strength=0.3)
    r2 = client.invoke("Cached prompt test", strength=0.3)
    print(f"  First call cached: {r1.cached}, cost: ${r1.cost:.8f}")
    print(f"  Second call cached: {r2.cached}, cost: ${r2.cost:.8f}")
    print(f"  Cache stats: {client.cache.stats()}")
    print()

    print("--- Prompt Formatting ---")
    template = "Summarize the following about {{topic}}: {{text}}"
    formatted = llm_client.format_prompt(template, {
        "topic": "Python",
        "text": "Python is a high-level programming language.",
    })
    print(f"  Template: {template}")
    print(f"  Formatted: {formatted}")
    print()

    print("--- Token Counting ---")
    sample = "This is a sample text for token counting demonstration."
    tokens = llm_client.count_tokens(sample)
    print(f"  Text: '{sample}'")
    print(f"  Estimated tokens: {tokens}")
    print()

    print("--- Model Comparison ---")
    comparator = llm_client.ModelComparator(models)
    print("  Top 5 by cost efficiency:")
    for name, efficiency in comparator.compare_by_efficiency()[:5]:
        print(f"    {name}: {efficiency:.1f} ELO/$")
    print()

    print("--- Cost Report ---")
    report = llm_client.CostReport(client.usage)
    print(report.format_text())
    print()

    print("=== Example Complete ===")


if __name__ == "__main__":
    main()
