from pydantic import BaseModel, Field
from pdd.llm_invoke import llm_invoke, _load_model_data, _select_model_candidates, LLM_MODEL_CSV_PATH, DEFAULT_BASE_MODEL
from typing import List, Dict, Any

# Define a Pydantic model for structured output
class Joke(BaseModel):
    setup: str = Field(description="The setup of the joke")
    punchline: str = Field(description="The punchline of the joke")


def calculate_model_ranges(step: float = 0.001) -> List[Dict[str, Any]]:
    """
    Calculate the strength ranges for each model by sampling strength values.

    Args:
        step: The step size for sampling strength values (default 0.001)

    Returns:
        List of dicts with 'model', 'start', 'end', and 'midpoint' keys
    """
    model_df = _load_model_data(LLM_MODEL_CSV_PATH)

    ranges = []
    current_model = None
    range_start = 0.0

    # Sample strength values to find model boundaries
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

    # Add the final range
    if current_model is not None:
        ranges.append({
            'model': current_model,
            'start': range_start,
            'end': 1.0,
            'midpoint': round((range_start + 1.0) / 2, 3)
        })

    return ranges


def main():
    """
    Main function to demonstrate the usage of `llm_invoke`.

    Automatically calculates model ranges and runs each model once
    at its midpoint strength value.
    """
    # Calculate model ranges automatically
    print("Calculating model strength ranges...")
    model_ranges = calculate_model_ranges()

    # Print the calculated ranges
    print("\n=== Model Strength Ranges ===")
    for range_info in model_ranges:
        print(f"{range_info['model']}: {range_info['start']:.3f} to {range_info['end']:.3f} (midpoint: {range_info['midpoint']:.3f})")

    prompt = "Tell me a joke about {topic}"
    input_json = {"topic": "programmers"}
    temperature = 1
    verbose = False

    # Run each model once at its midpoint strength
    print("\n=== Running Each Model Once ===")
    for range_info in model_ranges:
        model_name = range_info['model']
        midpoint = range_info['midpoint']

        print(f"\n--- Model: {model_name} (strength: {midpoint}) ---")

        # Example 1: Unstructured Output
        print("\n  Unstructured Output:")
        response = llm_invoke(
            prompt=prompt,
            input_json=input_json,
            strength=midpoint,
            temperature=temperature,
            verbose=verbose
        )

        print(f"  Result: {response['result']}")
        print(f"  Cost: ${response['cost']:.6f}")
        print(f"  Model Used: {response['model_name']}")

        # Example 2: Structured Output with Pydantic Model
        prompt_structured = (
            "Generate a joke about {topic}. \n"
            "Return it in this exact JSON format:\n"
            "{{ \n"
            '    "setup": "your setup here",\n'
            '    "punchline": "your punchline here"\n'
            "}}\n"
            "Return ONLY the JSON with no additional text or explanation."
        )
        input_json_structured = {"topic": "data scientists"}
        output_pydantic = Joke

        print("\n  Structured Output:")
        try:
            response_structured = llm_invoke(
                prompt=prompt_structured,
                input_json=input_json_structured,
                strength=midpoint,
                temperature=temperature,
                verbose=verbose,
                output_pydantic=output_pydantic
            )
            print(f"  Result: {response_structured['result']}")
            print(f"  Cost: ${response_structured['cost']:.6f}")
            print(f"  Model Used: {response_structured['model_name']}")

            # Access structured data
            joke: Joke = response_structured['result']
            print(f"\n  Joke Setup: {joke.setup}")
            print(f"  Joke Punchline: {joke.punchline}")
        except Exception as e:
            print(f"  Error encountered during structured output: {e}")

if __name__ == "__main__":
    main()