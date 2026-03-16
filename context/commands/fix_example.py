from __future__ import annotations

import sys
from pathlib import Path
from unittest.mock import patch

from click.testing import CliRunner


PROJECT_ROOT = Path(__file__).resolve().parents[2]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from pdd.commands.fix import fix


def _invoke_fix(args: list[str], *, obj: dict[str, object]) -> None:
    """Run the click command and fail fast if the invocation is not successful."""
    result = CliRunner().invoke(fix, args, obj=obj)
    print(result.output.rstrip())
    if result.exception is not None:
        raise result.exception
    if result.exit_code != 0:
        raise SystemExit(result.exit_code)


def run_agentic_example() -> None:
    """Demonstrate agentic issue routing with a mocked backend."""
    with patch(
        "pdd.agentic_e2e_fix.run_agentic_e2e_fix",
        return_value=(
            True,
            "Applied fix for issue #822",
            0.42,
            "mock-agentic-model",
            ["pdd/commands/fix.py"],
        ),
    ):
        _invoke_fix(
            ["https://github.com/example/repo/issues/822", "--ci-retries", "4"],
            obj={"quiet": False, "verbose": True},
        )


def run_user_story_example() -> None:
    """Demonstrate story-file routing with a mocked prompt-fix workflow."""
    runner = CliRunner()
    with runner.isolated_filesystem():
        story_file = Path("story__fix-command.md")
        story_file.write_text("# Story\n\nAs a user, I want the fix command routed correctly.\n")
        with patch(
            "pdd.user_story_tests.run_user_story_fix",
            return_value=(
                True,
                "Updated prompts for the story",
                0.18,
                "mock-story-model",
                ["prompts/commands/fix_python.prompt"],
            ),
        ):
            result = runner.invoke(
                fix,
                [str(story_file)],
                obj={
                    "quiet": False,
                    "verbose": True,
                    "prompts_dir": "prompts",
                    "strength": 0.3,
                    "temperature": 0.0,
                    "time": 0.25,
                },
            )
        print(result.output.rstrip())
        if result.exception is not None:
            raise result.exception
        if result.exit_code != 0:
            raise SystemExit(result.exit_code)


def run_manual_example() -> None:
    """Demonstrate manual routing with a mocked fix_main implementation."""
    with patch(
        "pdd.fix_main.fix_main",
        return_value=(True, "fixed test", "fixed code", 2, 0.27, "mock-manual-model"),
    ):
        _invoke_fix(
            ["--manual", "prompts/commands/fix_python.prompt", "pdd/commands/fix.py", "tests/commands/test_fix.py", "error.log"],
            obj={"quiet": False, "verbose": True},
        )


if __name__ == "__main__":
    print("Agentic mode")
    run_agentic_example()
    print("\nUser story mode")
    run_user_story_example()
    print("\nManual mode")
    run_manual_example()
