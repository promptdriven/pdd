from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.setup.local_llm_configurator import configure_local_llm


def main() -> None:
    """
    Demonstrates how to use the local_llm_configurator module to:
    1. Configure Ollama with auto-detection of installed models
    2. Configure LM Studio with custom port
    3. Add custom local LLM endpoints
    """

    print("Local LLM Configuration Example\n")

    print("This would present an interactive menu:")
    print()
    print("What tool are you using?")
    print("  1. LM Studio (default: localhost:1234)")
    print("  2. Ollama (default: localhost:11434)")
    print("  3. Other (custom base URL)")
    print("  Choice: 2")
    print()
    print("Querying Ollama at http://localhost:11434...")
    print("Found installed models:")
    print("  1. llama3:70b")
    print("  2. codellama:34b")
    print("  3. mistral:7b")
    print()
    print("Which models do you want to add? [1,2,3]: 1,2")
    print("✓ Added ollama_chat/llama3:70b and ollama_chat/codellama:34b to llm_model.csv")

    # Run the actual configuration
    # configure_local_llm()  # Uncomment to run interactively

    print("\n\nKey Features:")
    print("  • Ollama auto-detection: Queries API for installed models")
    print("  • LM Studio defaults: Pre-filled localhost:1234 base URL")
    print("  • Custom endpoints: Support for any LiteLLM-compatible provider")
    print("  • Multiple models: Add several models in one session")
    print("  • Zero cost: Local models set to $0.0001 or $0 costs")


if __name__ == "__main__":
    main()
