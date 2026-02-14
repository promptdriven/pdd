from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.setup.cli_detector import detect_cli_tools


def main() -> None:
    """
    Demonstrates how to use the cli_detector module to:
    1. Detect installed agentic CLI harnesses (claude, codex, gemini)
    2. Cross-reference with available API keys
    3. Offer installation for missing CLIs
    """

    # Run the interactive detector
    # detect_cli_tools()  # Uncomment to run interactively

    # Example flow:
    #   Checking CLI tools...
    #   (Required for: pdd fix, pdd change, pdd bug)
    #
    #   Claude CLI   ✓ Found at /usr/local/bin/claude
    #   Codex CLI    ✗ Not found
    #   Gemini CLI   ✗ Not found
    #
    #   You have OPENAI_API_KEY but Codex CLI is not installed.
    #   Install with: npm install -g @openai/codex
    #   Install now? [y/N]
    pass


if __name__ == "__main__":
    main()
