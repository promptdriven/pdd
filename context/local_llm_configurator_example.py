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
    2. Configure LM Studio with default base URL
    3. Add custom local LLM endpoints
    """

    # Run the interactive configuration
    # was_added = configure_local_llm()  # Uncomment to run interactively

    # Example flow for Ollama:
    #   What tool are you using?
    #     1. LM Studio (default: localhost:1234)
    #     2. Ollama (default: localhost:11434)
    #     3. Other (custom base URL)
    #   Choice: 2
    #
    #   Querying Ollama at http://localhost:11434...
    #   Found installed models:
    #     1. llama3:70b
    #     2. codellama:34b
    #     3. mistral:7b
    #
    #   Which models do you want to add? [1,2,3]: 1,2
    #   ✓ Added ollama_chat/llama3:70b and ollama_chat/codellama:34b to llm_model.csv
    pass


if __name__ == "__main__":
    main()
