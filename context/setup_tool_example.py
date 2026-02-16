from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.setup.setup_tool import run_setup


def main() -> None:
    """
    Demonstrates how to use the setup_tool module to:
    1. Launch the interactive pdd setup wizard
    2. Scan for configured API keys
    3. Navigate the 6-option menu

    The setup wizard is fully interactive. Running it will:
    - Scan ~/.pdd/llm_model.csv for configured models and their API key status
    - Display a menu with options to add/remove providers, test models, etc.
    - Loop until the user selects Done or presses Ctrl-C
    """

    # Run the interactive setup wizard
    # run_setup()  # Uncomment to run interactively

    # Example flow:
    #   ╭──────────────────────────────╮
    #   │        pdd setup             │
    #   ╰──────────────────────────────╯
    #
    #   API-key scan
    #   ──────────────────────────────────────────────────
    #     ANTHROPIC_API_KEY               ✓ Found  (shell environment)
    #     OPENAI_API_KEY                  — Not found
    #
    #     💡 To edit API keys: update ~/.pdd/api-env.zsh or .env file
    #
    #   Models configured: 1 (from 1 API keys + 0 local)
    #
    #   What would you like to do?
    #     1. Add a provider
    #     2. Remove models
    #     3. Test a model
    #     4. Detect CLI tools
    #     5. Initialize .pddrc
    #     6. Done
    #
    #   Choice [1-6]: 1
    #
    #   Add a provider:
    #     a. Search providers
    #     b. Add a local LLM
    #     c. Add a custom provider
    pass


if __name__ == "__main__":
    main()
