from __future__ import annotations

import os
import sys
import json
from typing import Optional, List, Dict, Any
from pydantic import BaseModel

# Import the core function from the pdd package
from pdd.llm_invoke import llm_invoke, set_verbose_logging

# --- Setup for Non-Interactive Example ---
# Ensure we are in non-interactive mode for headless environments
os.environ["PDD_FORCE"] = "1"

def run_llm_invoke_examples() -> None:
    """
    Demonstrates the various capabilities of the llm_invoke module,
    including simple text generation, structured output, and batching.
    """
    
    # 1. Configuration & API Key Checks
    # The module dynamically selects models from pdd/data/llm_model.csv based on 'strength'.
    # Most models require an API key (e.g., OPENAI_API_KEY, ANTHROPIC_API_KEY, or GOOGLE_API_KEY).
    # We check for a generic key to ensure the example has a chance to run.
    api_key = os.environ.get("OPENAI_API_KEY") or os.environ.get("ANTHROPIC_API_KEY") or os.environ.get("GOOGLE_API_KEY")
    if not api_key:
        print("No LLM API keys (OPENAI_API_KEY, ANTHROPIC_API_KEY, or GOOGLE_API_KEY) found.")
        print("Set one to run this example. Skipping execution.")
        sys.exit(0)

    # Enable detailed logging to see model selection and token usage
    set_verbose_logging(verbose=True)

    # --- Example 1: Simple Prompt with Input Data ---
    print("\n--- Example 1: Basic Invocation ---")
    # strength 0.5: Uses the base model (default or first available).
    # temperature 0.1: Low randomness for deterministic output.
    try:
        response = llm_invoke(
            prompt="Summarize the following topic in one sentence: {topic}",
            input_json={"topic": "Quantum Computing"},
            strength=0.5,
            temperature=0.1
        )
        
        print(f"Model Used: {response['model_name']}")
        print(f"Result: {response['result']}")
        print(f"Cost: ${response['cost']:.6f}") # Cost is in USD
    except Exception as e:
        print(f"Invocation failed: {e}")

    # --- Example 2: Structured Output using Pydantic ---
    print("\n--- Example 2: Structured Output (Pydantic) ---")
    
    class CodeAnalysis(BaseModel):
        language: str
        complexity_score: int
        is_functional: bool
        summary: str

    # strength 0.8: Targets a higher-ELO (more capable) model.
    # output_pydantic: Forces the LLM to return valid JSON matching the schema.
    code_to_analyze = "def add(a, b): return a + b"
    
    try:
        response_struct = llm_invoke(
            prompt="Analyze this code snippet: {code}",
            input_json={"code": code_to_analyze},
            strength=0.8,
            output_pydantic=CodeAnalysis
        )
        
        # 'result' is automatically parsed into a Pydantic object
        analysis: CodeAnalysis = response_struct['result']
        print(f"Language: {analysis.language}")
        print(f"Summary: {analysis.summary}")
        print(f"Cost: ${response_struct['cost']:.6f}")
    except Exception as e:
        print(f"Structured invocation failed: {e}")

    # --- Example 3: Batch Processing ---
    print("\n--- Example 3: Batch Mode ---")
    # input_json as a list triggers batch mode.
    # strength 0.2: Targets a cheaper model to save costs.
    batch_inputs = [
        {"word": "Python"},
        {"word": "Rust"},
        {"word": "C++"}
    ]
    
    try:
        response_batch = llm_invoke(
            prompt="What is the primary use case for the {word} programming language?",
            input_json=batch_inputs,
            strength=0.2,
            use_batch_mode=True
        )
        
        # In batch mode, 'result' is a list of strings (or objects)
        for i, res in enumerate(response_batch['result']):
            print(f"Result {i+1} ({batch_inputs[i]['word']}): {res[:50]}...")
            
        print(f"Total Batch Cost: ${response_batch['cost']:.6f}")
    except Exception as e:
        print(f"Batch invocation failed: {e}")

    # --- Example 4: Reasoning/Thinking Time ---
    print("\n--- Example 4: Reasoning Time (Thinking) ---")
    # time 0.7: Requests high thinking effort (0.0 to 1.0 scale).
    # This maps to 'thinking' (Anthropic) or 'reasoning_effort' (OpenAI/O1).
    try:
        response_thinking = llm_invoke(
            prompt="Solve this logic puzzle: If all A are B, and some B are C, are all A necessarily C? Explain.",
            input_json={},
            strength=1.0, # Target the most capable model
            time=0.7      # Request significant reasoning time
        )
        
        print(f"Result: {response_thinking['result']}")
        # thinking_output contains the internal reasoning chain if the provider exposes it
        if response_thinking['thinking_output']:
            print(f"Thinking Process: {response_thinking['thinking_output'][:100]}...")
    except Exception as e:
        print(f"Reasoning invocation failed: {e}")

if __name__ == "__main__":
    # Ensure the output directory exists as per requirements
    os.makedirs("./output", exist_ok=True)
    run_llm_invoke_examples()