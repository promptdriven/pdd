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
    2. Phase 1: Bootstrap agentic CLIs (Claude/Gemini/Codex/OpenCode)
    3. Phase 2: Auto-configure API keys, models, and .pddrc

    The setup flow is mostly automatic. Phase 1 asks 0-2 questions
    (which CLIs to use), then Phase 2 runs 3 deterministic steps
    with "Press Enter" pauses between them.
    """

    # Run the setup flow
    # run_setup()  # Uncomment to run interactively

    # Example flow:
    #   (PDD ASCII logo in cyan)
    #   Let's get set up quickly with a solid basic configuration!
    #
    #   Phase 1 -- CLI Bootstrap
    #   Detected: claude (Anthropic)
    #   API key: configured
    #
    #   ────────────────────────────────────────
    #   Scanning for API keys...
    #   ────────────────────────────────────────
    #     ✓ ANTHROPIC_API_KEY   shell environment
    #     ✓ GEMINI_API_KEY      shell environment
    #
    #     Found 2 API key(s).
    #     You can edit your global API keys in ~/.pdd/api-env.zsh
    #
    #   Press Enter to continue to the next step...
    #
    #   ────────────────────────────────────────
    #   Configuring models...
    #   ────────────────────────────────────────
    #     ✓ Added 3 new model(s) to ~/.pdd/llm_model.csv
    #
    #     Total: 4 model(s) configured
    #       Anthropic: 3
    #       Google: 1
    #     ✓ .pddrc detected in this project
    #
    #   Press Enter to continue to the next step...
    #
    #   ────────────────────────────────────────
    #   Testing and summarizing...
    #   ────────────────────────────────────────
    #     Selected model: anthropic/claude-sonnet-4-5-20250929
    #     Testing......
    #     ✓ anthropic/claude-sonnet-4-5-20250929 responded OK (1.2s, $0.0001)
    #
    #     PDD Setup Complete!
    #
    #       ✓ CLI: claude
    #       ✓ API Keys: 2 found
    #       ✓ Models: 4 (Anthropic: 3, Google: 1)
    #           ~/.pdd/llm_model.csv
    #       ✓ .pddrc: exists
    #       ✓ Test: anthropic/claude-sonnet-4-5-20250929 OK
    #
    #   Press Enter to finish, or 'm' for more options:
    #
    #   (user presses Enter)
    #
    #   ────────────────────────────────────────────────────────────────────────────────
    #   QUICK START
    #     pdd generate success_python.prompt
    #
    #   LEARN MORE
    #     • pdd --help
    #     • https://promptdriven.ai
    #     • Discord: https://discord.gg/Yp4RTh8bG7
    #
    #   Important: To load your API keys into this terminal session, run:
    #     source ~/.pdd/api-env.zsh
    #
    #   Full summary saved to PDD-SETUP-SUMMARY.txt
    #
    #   --- OR if user enters 'm': ---
    #
    #   Options:
    #     1. Add a provider
    #     2. Test a model
    #
    #   Choose (Enter to exit):
    pass


if __name__ == "__main__":
    main()
