from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.cli_detector import detect_and_bootstrap_cli, detect_cli_tools, CliBootstrapResult


def main() -> None:
    """
    Demonstrates how to use the cli_detector module to:
    1. Bootstrap agentic CLIs for pdd setup (detect_and_bootstrap_cli)
    2. Detect installed CLI harnesses (claude, codex, gemini)
    3. Cross-reference with available API keys
    4. Offer installation for missing CLIs
    """

    # Primary entry point used by pdd setup Phase 1:
    # results = detect_and_bootstrap_cli()  # Returns List[CliBootstrapResult]
    # for r in results:
    #     r.cli_name           -> "claude" | "codex" | "gemini" | ""
    #     r.provider           -> "anthropic" | "openai" | "google" | ""
    #     r.cli_path           -> "/usr/local/bin/claude" | ""
    #     r.api_key_configured -> True | False
    #     r.skipped            -> True | False

    # Legacy function for detection only:
    # detect_cli_tools()  # Uncomment to run interactively

    # Example flow (detect_and_bootstrap_cli with multi-select):
    #   Checking CLI tools...
    #
    #   1. Claude CLI   ✓ Found at /usr/local/bin/claude   ✓ ANTHROPIC_API_KEY is set
    #   2. Codex CLI    ✗ Not found                         ✗ OPENAI_API_KEY not set
    #   3. Gemini CLI   ✗ Not found                         ✓ GEMINI_API_KEY is set
    #
    #   Select CLIs to use for pdd agentic tools (enter numbers separated by commas, e.g., 1,3):
    #
    # Returns [CliBootstrapResult(cli_name="claude", ...), CliBootstrapResult(cli_name="gemini", ...)]
    pass


if __name__ == "__main__":
    main()
