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
    2. Phase 1: Bootstrap agentic CLIs (Claude/Gemini/Codex)
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
    #     2 API key(s) found.
    #     You can edit your global API keys in ~/.pdd/api-env.zsh
    #
    #   Press Enter to continue to the next step...
    #
    #   ────────────────────────────────────────
    #   Configuring models...
    #   ────────────────────────────────────────
    #     ✓ 3 new model(s) added to ~/.pdd/llm_model.csv
    #     ✓ 4 model(s) configured
    #       Anthropic: 3 models
    #       Google: 1 model
    #     ✓ .pddrc detected at /path/to/project/.pddrc
    #
    #   Press Enter to continue to the next step...
    #
    #   ────────────────────────────────────────
    #   Testing and summarizing...
    #   ────────────────────────────────────────
    #     Testing anthropic/claude-sonnet-4-5-20250929......
    #     ✓ claude-sonnet-4-5-20250929 responded OK (1.2s)
    #
    #     PDD Setup Complete!
    #
    #       CLI:       ✓ claude configured
    #       API Keys:  ✓ 2 found
    #       Models:    4 configured (Anthropic: 3, Google: 1) in ~/.pdd/llm_model.csv
    #       .pddrc:    ✓ exists
    #       Test:      ✓ claude-sonnet-4-5-20250929 responded OK (1.2s)
    #
    #   Press Enter to finish, or 'm' for more options:
    #
    #   (user presses Enter)
    #
    #   ────────────────────────────────────────────────────────────────────────────────
    #   QUICK START:
    #   1. Generate code from the sample prompt:
    #      pdd generate success_python.prompt
    #   ────────────────────────────────────────────────────────────────────────────────
    #   LEARN MORE:
    #   • PDD documentation: pdd --help
    #   • PDD website: https://promptdriven.ai/
    #   • Discord community: https://discord.gg/Yp4RTh8bG7
    #
    #   Full summary saved to PDD-SETUP-SUMMARY.txt
    #
    #   --- OR if user enters 'm': ---
    #
    #   Options:
    #     1. Add a provider
    #     2. Test a model
    #
    #   Select an option (Enter to finish):
    pass


if __name__ == "__main__":
    main()
