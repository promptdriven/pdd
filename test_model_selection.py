#!/usr/bin/env python3
"""Test script to check which model PDD would select"""

import os
import sys
sys.path.insert(0, 'pdd')

from pdd.llm_invoke import llm_invoke

# Load environment variables
from dotenv import load_dotenv
load_dotenv()

def test_model_selection():
    print("Testing model selection with current environment...")
    print(f"OPENAI_API_KEY: {'Set' if os.getenv('OPENAI_API_KEY') else 'Not set'}")
    print(f"ANTHROPIC_API_KEY: {'Set' if os.getenv('ANTHROPIC_API_KEY') else 'Not set'}")
    print(f"VERTEX_CREDENTIALS: {'Set' if os.getenv('VERTEX_CREDENTIALS') else 'Not set'}")
    print(f"GOOGLE_API_KEY: {'Set' if os.getenv('GOOGLE_API_KEY') else 'Not set'}")
    print()
    
    # Test different strength values with minimal prompt
    for strength in [0.5, 0.75, 0.9, 0.95]:
        print(f"Strength {strength}:")
        try:
            # Use a minimal prompt to test model selection
            result = llm_invoke(
                prompt="Hello",
                strength=strength,
                temperature=0.0,
                max_tokens=10,
                verbose=True  # This should show which model is selected
            )
            print(f"  Response received (model info should be in logs above)")
        except Exception as e:
            print(f"  Error: {e}")
        print()

if __name__ == "__main__":
    test_model_selection()