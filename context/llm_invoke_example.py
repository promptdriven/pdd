from pydantic import BaseModel, Field
from pdd.llm_invoke import llm_invoke
from collections import defaultdict

# Define a Pydantic model for structured output
class Joke(BaseModel):
    setup: str = Field(description="The setup of the joke")
    punchline: str = Field(description="The punchline of the joke")

def main():
    """
    Main function to demonstrate the usage of `llm_invoke`.
    """
    # Dictionary to track strength ranges for each model
    model_ranges = defaultdict(list)
    current_model = None
    range_start = 0.0
    
    prompt = "Tell me a joke about {topic}"
    input_json = {"topic": "programmers"}
    temperature = 1
    verbose = True
    
    strength = 0.0
    while strength <= 1:
        print(f"\nStrength: {strength}")
        
        # Example 1: Unstructured Output
        print("\n--- Unstructured Output ---")
        response = llm_invoke(
            prompt=prompt,
            input_json=input_json,
            strength=strength,
            temperature=temperature,
            verbose=verbose
        )
        
        # Track model changes for strength ranges
        if current_model != response['model_name']:
            if current_model is not None:
                model_ranges[current_model].append((range_start, strength - 0.02))
            current_model = response['model_name']
            range_start = strength
        
        print(f"Result: {response['result']}")
        print(f"Cost: ${response['cost']:.6f}")
        print(f"Model Used: {response['model_name']}")
        
        # Example 2: Structured Output with Pydantic Model
        prompt_structured = "Provide a joke in JSON format with 'setup' and 'punchline' fields."
        input_json_structured = {"topic": "data scientists"}
        output_pydantic = Joke
        
        print("\n--- Structured Output ---")
        
        response_structured = llm_invoke(
            prompt=prompt_structured,
            input_json=input_json_structured,
            strength=strength,
            temperature=1,
            verbose=True,
            output_pydantic=output_pydantic
        )
        
        print(f"Result: {response_structured['result']}")
        print(f"Cost: ${response_structured['cost']:.6f}")
        print(f"Model Used: {response_structured['model_name']}")
        
        # Accessing structured data
        joke: Joke = response_structured['result']
        print(f"\nJoke Setup: {joke.setup}")
        print(f"Joke Punchline: {joke.punchline}")
        
        strength += 0.02
        # round to 2 decimal places
        strength = round(strength, 2)
    
    # Add the final range for the last model
    model_ranges[current_model].append((range_start, 1.0))
    
    # Print out the strength ranges for each model
    print("\n=== Model Strength Ranges ===")
    for model, ranges in model_ranges.items():
        print(f"\n{model}:")
        for start, end in ranges:
            print(f"  Strength {start:.2f} to {end:.2f}")

if __name__ == "__main__":
    main()