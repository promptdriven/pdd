from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.model_tester import test_model_interactive


def main() -> None:
    """
    Demonstrates how to use the model_tester module to:
    1. List configured models from ~/.pdd/llm_model.csv
    2. Test a selected model via litellm.completion()
    3. Display diagnostics (API key status, timing, cost)
    """

    # Run the interactive tester
    # test_model_interactive()  # Uncomment to run interactively

    # Example flow:
    #   Configured models:
    #     1. anthropic/claude-haiku-4-5-20251001  ANTHROPIC_API_KEY
    #     2. gpt-5-nano                           OPENAI_API_KEY
    #     3. lm_studio/openai-gpt-oss-120b-mlx-6  (local)
    #
    #   Test which model? 1
    #   Testing anthropic/claude-haiku-4-5-20251001...
    #   API key    ANTHROPIC_API_KEY ✓ Found (shell environment)
    #   LLM call   ✓ OK (0.3s, $0.0001)
    #
    #   Test which model? 3
    #   Testing lm_studio/openai-gpt-oss-120b-mlx-6...
    #   API key    (local — no key required)
    #   Base URL   http://localhost:1234/v1
    #   LLM call   ✗ Connection refused (localhost:1234)
    pass


if __name__ == "__main__":
    main()
