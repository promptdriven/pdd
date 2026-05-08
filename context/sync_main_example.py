"""
Example demonstrating the `sync_main` function.

This script simulates a `pdd sync greeting` command by:
1. Setting up a mock project with prompt files for Python and JavaScript.
2. Creating a mock `click.Context` object to pass global options.
3. Mocking `construct_paths` and `sync_orchestration` so it runs standalone.
4. Calling `sync_main` and printing its aggregated results.
"""
import json
import os
import shutil
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

# Make the local pdd package importable regardless of cwd. This must happen
# before `from pdd.sync_main import sync_main` so we don't accidentally import
# an older installed version of the package.
_REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_REPO_ROOT))

# Force reimport of pdd from the local source if a different one was loaded.
for _mod_name in [m for m in list(sys.modules) if m == "pdd" or m.startswith("pdd.")]:
    del sys.modules[_mod_name]

import click  # noqa: E402
from rich.console import Console  # noqa: E402

from pdd.sync_main import sync_main  # noqa: E402


def setup_mock_project(base_dir: Path) -> None:
    """Create a mock project directory with prompt files for two languages."""
    prompts_dir = base_dir / "prompts"
    src_dir = base_dir / "src"
    tests_dir = base_dir / "tests"
    examples_dir = base_dir / "examples"

    if base_dir.exists():
        shutil.rmtree(base_dir)
    for d in [prompts_dir, src_dir, tests_dir, examples_dir]:
        d.mkdir(parents=True, exist_ok=True)

    (prompts_dir / "greeting_python.prompt").write_text(
        "Create a Python function `greet()` that returns 'Hello, Python!'"
    )
    (prompts_dir / "greeting_javascript.prompt").write_text(
        "Create a JavaScript function `greet()` that returns 'Hello, JavaScript!'"
    )
    (prompts_dir / "unrelated_file.txt").write_text("This file should be ignored.")

    print(f"Mock project created in: {base_dir.resolve()}")


def main() -> None:
    """Run the example."""
    console = Console()

    # Use a temp directory derived from this file's location to avoid hardcoded
    # absolute paths and to keep the example side-effect-clean.
    output_directory = Path(os.path.dirname(__file__)) / "_sync_main_example_output"

    console.rule("[bold green]1. Setting up Mock Project[/bold green]")
    setup_mock_project(output_directory)

    # Build a Click context whose obj mirrors what the CLI populates.
    ctx = click.Context(click.Command("sync"))
    ctx.obj = {
        "strength": 0.5,
        "temperature": 0.0,
        "time": 0.25,
        "verbose": False,
        "force": False,
        "quiet": False,
        "output_cost": None,
        "review_examples": False,
        "local": True,  # disable cloud auto-submit in the demo
        "context": None,
    }
    mock_source = MagicMock()
    mock_source.name = "DEFAULT"
    ctx.get_parameter_source = MagicMock(return_value=mock_source)

    # construct_paths returns (resolved_config, input_strings, output_paths, language)
    def mock_construct_paths(*args, **kwargs):
        # Derive language from command_options if provided so sync_main's
        # per-language path resolution receives a non-None resolved_language.
        opts = kwargs.get("command_options") or {}
        language = opts.get("language")
        resolved_config = {
            "prompts_dir": str(output_directory / "prompts"),
            "code_dir": str(output_directory / "src"),
            "tests_dir": str(output_directory / "tests"),
            "examples_dir": str(output_directory / "examples"),
            "target_coverage": 90.0,
            "max_attempts": 3,
            "budget": 5.0,
        }
        return (resolved_config, {}, {}, language)

    # sync_orchestration returns the per-language result dict.
    def mock_sync_orchestration(*args, **kwargs):
        language = kwargs.get("language")
        if kwargs.get("dry_run"):
            return {"success": True, "total_cost": 0.0, "summary": "dry-run"}
        if language == "python":
            return {
                "success": True,
                "total_cost": 0.025,
                "summary": "Code generated, 2/2 tests passed.",
                "model_name": "test-model-v1",
            }
        if language == "javascript":
            return {
                "success": False,
                "total_cost": 0.015,
                "error": "Test execution failed: ReferenceError.",
                "summary": "Code generated, 0/1 tests passed.",
                "model_name": "test-model-v1",
            }
        return {"success": False, "error": "Unknown language", "total_cost": 0.0}

    console.rule("[bold green]2. Calling `sync_main`[/bold green]")
    print("`sync_main` will now run, using mocks for its dependencies.")

    with patch("pdd.sync_main.construct_paths", side_effect=mock_construct_paths), \
         patch("pdd.sync_main.sync_orchestration", side_effect=mock_sync_orchestration), \
         patch("pdd.sync_main._find_prompt_in_contexts", return_value=None):
        results, total_cost, model = sync_main(
            ctx=ctx,
            basename="greeting",
            max_attempts=3,
            budget=1.0,
            skip_verify=False,
            skip_tests=False,
            target_coverage=90.0,
            dry_run=False,
        )

    console.rule("[bold blue]3. Results from `sync_main`[/bold blue]")
    print(f"Overall Success: {results.get('overall_success')}")
    print(f"Total Cost: ${total_cost:.4f} USD")
    print(f"Primary Model: {model!r}")
    print()
    print("Detailed Results (JSON):")
    print(json.dumps(results, indent=2, default=str))


if __name__ == "__main__":
    main()
