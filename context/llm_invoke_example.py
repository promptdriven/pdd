import os
import sys
from pydantic import BaseModel
from pdd.llm_invoke import llm_invoke, set_verbose_logging

# Check for an API key to ensure the example can run non-interactively.
# Note: llm_invoke abstracts over many providers, but we check for OpenAI here as a common default.
api_key = os.environ.get("OPENAI_API_KEY")
if not api_key:
    print("OPENAI_API_KEY not set. Set it to run this example.")
    sys.exit(0)

# Enable verbose logging to see model selection and token usage details
set_verbose_logging(True)

print("--- Example 1: Basic Text Generation ---")
# llm_invoke replaces the variables in `prompt` with values from `input_json`.
# strength=0.5 selects the base model defined in the configuration.
# time=0.0 disables extra reasoning/thinking overhead.
response1 = llm_invoke(
    prompt="Explain {topic} in one short sentence.",
    input_json={"topic": "machine learning"},
    strength=0.5,
    temperature=0.3,
    time=0.0
)

print(f"Result: {response1['result']}")
print(f"Model Used: {response1['model_name']}")
print(f"Cost: ${response1['cost']:.6f}\n")

print("--- Example 2: Structured Output using Pydantic ---")
# Define the expected structure of the output
class ElementInfo(BaseModel):
    name: str
    symbol: str
    atomic_number: int

# Pass the Pydantic class to output_pydantic to guarantee structured JSON output.
response2 = llm_invoke(
    prompt="Provide the details for the element {element}.",
    input_json={"element": "Helium"},
    strength=0.5,
    temperature=0.0,
    output_pydantic=ElementInfo
)

# The result will be automatically parsed into the Pydantic model instance
element = response2['result']
print(f"Parsed Pydantic Object - Name: {element.name}, Symbol: {element.symbol}, Atomic Number: {element.atomic_number}")
print(f"Model Used: {response2['model_name']}\n")

print("--- Example 3: Using Direct Messages Format ---")
# If you already have a conversational message history, you can bypass `prompt` and `input_json`
# and directly provide the `messages` array.
messages = [
    {"role": "system", "content": "You are a sarcastic calculator."},
    {"role": "user", "content": "What is 5 + 7?"}
]

# strength=0.1 attempts to select a cheaper, faster model (downwards interpolation from base)
response3 = llm_invoke(
    messages=messages,
    strength=0.1,
    temperature=0.5
)

print(f"Result: {response3['result']}")
print(f"Model Used: {response3['model_name']}")
print(f"Attempted Models Chain: {response3['attempted_models']}")