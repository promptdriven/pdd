import os
import sys
import json
from pathlib import Path
from pydantic import BaseModel

# Import the llm_invoke function from the pdd package
from pdd.llm_invoke import llm_invoke, set_verbose_logging


class CapitalInfo(BaseModel):
    """Schema for structured output example."""
    country: str
    capital: str
    population_estimate: int
    fun_fact: str


def main():
    # The example requires an API key to run properly.
    # Using OPENAI_API_KEY as a common default for testing.
    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        print("OPENAI_API_KEY not set. Set it to run this example.")
        sys.exit(0)

    # Setup output directory
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)

    print("--- Example 1: Basic Text Generation ---")
    # Generate a simple text response using a prompt and input variables.
    # strength=0.5 uses the default base model.
    text_result = llm_invoke(
        prompt="What are the top {count} most popular programming languages in {year}? List them briefly.",
        input_json={"count": 3, "year": 2024},
        strength=0.5,
        temperature=0.3,
        verbose=False
    )
    print(f"Model Used: {text_result.get('model_name')}")
    print(f"Cost: ${text_result.get('cost'):.6f}")
    print(f"Result:\n{text_result.get('result')}\n")

    print("--- Example 2: Structured Output (Pydantic) ---")
    # Generate a strictly typed JSON response parsed into a Pydantic model.
    structured_result = llm_invoke(
        prompt="Give me information about the capital of {country}.",
        input_json={"country": "Japan"},
        strength=0.5,
        temperature=0.1,
        output_pydantic=CapitalInfo,
        verbose=False
    )
    
    model_used = structured_result.get('model_name')
    cost = structured_result.get('cost')
    pydantic_obj = structured_result.get('result')
    
    print(f"Model Used: {model_used}")
    print(f"Cost: ${cost:.6f}")
    
    if isinstance(pydantic_obj, CapitalInfo):
        print("Successfully parsed into CapitalInfo object:")
        print(json.dumps(pydantic_obj.model_dump(), indent=2))
        
        # Save structured output to file
        output_file = output_dir / "japan_capital_info.json"
        with open(output_file, "w") as f:
            json.dump(pydantic_obj.model_dump(), f, indent=2)
        print(f"\nSaved structured result to {output_file}")
    else:
        print("Failed to parse into CapitalInfo object.")
        print(f"Raw result: {pydantic_obj}")


if __name__ == "__main__":
    main()