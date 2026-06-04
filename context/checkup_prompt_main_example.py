"""Example: run unified prompt-space check on a repo fixture (no LLM)."""

import sys
from pathlib import Path

project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

from pdd.checkup_prompt_main import run_checkup_prompt  # noqa: E402


def main() -> None:
    """Human-runnable touch point using the payment_api lint fixture."""
    fixture = (
        project_root
        / "tests"
        / "fixtures"
        / "prompt_lint"
        / "payment_api_python.prompt"
    )
    success, message, cost, model = run_checkup_prompt(
        str(fixture),
        explain=False,
        interactive=False,
        apply=False,
        quiet=False,
        verbose=True,
        project_root=project_root,
    )
    print("-" * 60)
    print(f"Success: {success}")
    print(f"Message: {message}")
    print(f"Cost: ${cost:.4f}")
    print(f"Model: {model or 'N/A'}")


if __name__ == "__main__":
    main()
