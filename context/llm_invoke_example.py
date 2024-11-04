# example.py

from pydantic import BaseModel, Field
from pdd.llm_invoke import llm_invoke  # Ensure llm_invoke.py is accessible in the PYTHONPATH

# Define a Pydantic model for structured output
class Joke(BaseModel):
    setup: str = Field(description="The setup of the joke")
    punchline: str = Field(description="The punchline of the joke")

def main():
    """
    Main function to demonstrate the usage of `llm_invoke`.
    """

    # Example 1: Unstructured Output
    prompt = "Tell me a joke about {topic}"
    input_json = {"topic": "programmers"}
    temperature = 0.7
    verbose = True

    strength = 0
    while strength <= 1:
        print(f"\nStrength: {strength}")
    
        print("\n--- Unstructured Output ---")
        response = llm_invoke(
            prompt=prompt,
            input_json=input_json,
            strength=strength,
            temperature=temperature,
            verbose=verbose
        )

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
            strength=strength,  # Select a model with higher ELO
            temperature=0.5,
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

        strength += 0.05
if __name__ == "__main__":
    main()