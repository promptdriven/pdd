from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.cli_detector import detect_and_bootstrap_cli, detect_cli_tools


def main() -> None:
    """
    Demonstrates how to use the cli_detector module to:
    1. Bootstrap an agentic CLI for pdd setup (detect_and_bootstrap_cli)
    2. Detect installed CLI harnesses (claude, codex, gemini)
    3. Cross-reference with available API keys
    4. Offer installation for missing CLIs
    """

    # Primary entry point used by pdd setup Phase 1:
    # result = detect_and_bootstrap_cli()
    # result.cli_name   -> "claude" | "codex" | "gemini" | ""
    # result.provider   -> "Anthropic" | "OpenAI" | "Google" | ""
    # result.api_key_configured -> True | False

    # Legacy function for detection only:
    # detect_cli_tools()  # Uncomment to run interactively

    # Example flow (detect_and_bootstrap_cli):
    #   Checking CLI tools...
    #   (Required for: pdd fix, pdd change, pdd bug)
    #
    #   Claude CLI   Found at /usr/local/bin/claude
    #   Codex CLI    Not found
    #   Gemini CLI   Not found
    #
    #   Using Claude CLI (Anthropic).
    #   API key: configured
    #
    # Returns CliBootstrapResult(cli_name="claude", provider="Anthropic",
    #                            api_key_configured=True)
    pass


if __name__ == "__main__":
    main()
