from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.setup_tool import run_setup


def main() -> None:
    """
    Demonstrates how to use the setup_tool module to:
    1. Launch the two-phase pdd setup flow
    2. Phase 1: Bootstrap an agentic CLI (Claude/Gemini/Codex)
    3. Phase 2: Auto-configure API keys, models, local LLMs, and .pddrc

    The setup flow is mostly automatic. Phase 1 asks 0-2 questions
    (which CLI to use), then Phase 2 runs 4 deterministic steps
    with "Press Enter" pauses between them.
    """

    # Run the setup flow
    # run_setup()  # Uncomment to run interactively

    # Example flow:
    #   +------------------------------+
    #   |        pdd setup             |
    #   +------------------------------+
    #
    #   Phase 1 -- CLI Bootstrap
    #   Detected: claude (Anthropic)
    #   API key: configured
    #
    #   Ready to auto-configure PDD. Press Enter to continue...
    #
    #   [Step 1/4] Scanning for API keys...
    #     ANTHROPIC_API_KEY   shell environment
    #     GEMINI_API_KEY      shell environment
    #
    #     2 API key(s) found.
    #
    #   Press Enter to continue to the next step...
    #
    #   [Step 2/4] Configuring models...
    #     3 new model(s) added to ~/.pdd/llm_model.csv
    #     4 cloud model(s) configured
    #       Anthropic: 3 models
    #       Google: 1 model
    #
    #   Press Enter to continue to the next step...
    #
    #   [Step 3/4] Checking local LLMs and .pddrc...
    #     Ollama running -- found llama3.2:3b, openhermes:latest
    #     LM Studio not running (skip)
    #     .pddrc already exists at /path/to/project/.pddrc
    #
    #   Press Enter to continue to the next step...
    #
    #   [Step 4/4] Testing and summarizing...
    #     Testing anthropic/claude-sonnet-4-5-20250929...
    #     claude-sonnet-4-5-20250929 responded OK (1.2s)
    #
    #     ===============================================
    #       PDD Setup Complete
    #     ===============================================
    #
    #       API Keys:  2 found
    #       Models:    4 configured (Anthropic: 3, Google: 1)
    #       Local:     Ollama -- llama3.2:3b, openhermes:latest
    #       .pddrc:    exists
    #       Test:      OK
    #
    #     ===============================================
    #       Run 'pdd generate' or 'pdd sync' to start.
    #     ===============================================
    #
    #   Setup complete. Happy prompting!
    pass


if __name__ == "__main__":
    main()
