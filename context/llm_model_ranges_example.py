import os
import sys
from typing import List, Dict, Any

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from pdd.llm_invoke import llm_invoke, _load_model_data, _select_model_candidates, LLM_MODEL_CSV_PATH, DEFAULT_BASE_MODEL


def calculate_model_ranges(step: float = 0.001) -> List[Dict[str, Any]]:
    """Calculate the strength ranges for each model by sampling strength values."""
    model_df = _load_model_data(LLM_MODEL_CSV_PATH)

    ranges = []
    current_model = None
    range_start = 0.0

    strength = 0.0
    while strength <= 1.0:
        candidates = _select_model_candidates(strength, DEFAULT_BASE_MODEL, model_df)
        selected_model = candidates[0]['model'] if candidates else None

        if current_model != selected_model:
            if current_model is not None:
                ranges.append({
                    'model': current_model,
                    'start': range_start,
                    'end': round(strength - step, 3),
                    'midpoint': round((range_start + strength - step) / 2, 3)
                })
            current_model = selected_model
            range_start = strength

        strength = round(strength + step, 3)

    if current_model is not None:
        ranges.append({
            'model': current_model,
            'start': range_start,
            'end': 1.0,
            'midpoint': round((range_start + 1.0) / 2, 3)
        })

    return ranges


def main():
    """Print model strength ranges and invoke each model once at its midpoint."""
    print("Calculating model strength ranges...\n")
    model_ranges = calculate_model_ranges()

    print(f"{'Model':<60} {'Range':>15}  {'Midpoint':>8}")
    print("-" * 88)
    for r in model_ranges:
        print(f"{r['model']:<60} {r['start']:.3f} - {r['end']:.3f}  {r['midpoint']:>8.3f}")

    prompt = "Say hello in one sentence as {persona}."
    print("\n\n=== Invoking Each Model (local, use_cloud=False) ===\n")

    passed = 0
    failed = 0
    skipped = 0

    for r in model_ranges:
        midpoint = r['midpoint']
        expected = r['model']
        print(f"--- {expected} (strength={midpoint:.3f}) ---")
        try:
            result = llm_invoke(
                prompt=prompt,
                input_json={"persona": "a pirate"},
                strength=midpoint,
                temperature=0.7,
                use_cloud=False,
            )
            actual = result['model_name']
            text = result['result']
            cost = result['cost']

            if actual == expected:
                print(f"  PASS | Result: {text}")
                print(f"         Cost: ${cost:.6f}")
                passed += 1
            else:
                print(f"  MISMATCH | Expected: {expected}")
                print(f"           | Actual:   {actual}")
                print(f"           | Result: {text}")
                print(f"           | Cost: ${cost:.6f}")
                failed += 1
        except Exception as e:
            err = str(e)
            # Local-only models (localhost) are expected to fail if not running
            if "localhost" in expected or "lm_studio" in expected or "mlx-community" in expected:
                print(f"  SKIP (local model not running) | {err[:100]}")
                skipped += 1
            else:
                print(f"  FAIL | {err[:200]}")
                failed += 1
        print()

    print("=" * 88)
    print(f"Results: {passed} passed, {failed} failed, {skipped} skipped (local models)")


if __name__ == "__main__":
    main()
