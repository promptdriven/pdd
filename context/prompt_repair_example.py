"""Offline example for the bounded prompt-repair entry point."""

from __future__ import annotations

import tempfile
from pathlib import Path

from pdd.prompt_repair import PromptRepairConfig, run_prompt_repair_loop


def main() -> None:
    """Show the disabled mode without invoking any model provider."""
    with tempfile.TemporaryDirectory() as tmp:
        prompt_path = Path(tmp) / "example_python.prompt"
        prompt_path.write_text("% Return the input unchanged.\n", encoding="utf-8")

        result = run_prompt_repair_loop(
            prompt_path,
            PromptRepairConfig(mode="off"),
            cwd=Path(tmp),
        )

    assert result.success
    assert result.repair_skipped
    assert result.message == "repair disabled"
    print(result.message)


if __name__ == "__main__":
    main()
