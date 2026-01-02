import json
import shutil
from pathlib import Path
from unittest.mock import MagicMock, patch

import click
from rich.console import Console

# The sync_main function is designed to be called by the Click framework.
# We import it to demonstrate its use in a controlled, programmatic way.
from pdd.sync_main import sync_main


def setup_mock_project(base_dir: Path) -> None:
    """
    Creates a mock project structure with prompt files for multiple languages.
    This setup is required for the `sync_main` language detection to work.

    Args:
        base_dir (Path): The root directory for the mock project (e.g., './output').
    """
    prompts_dir = base_dir / "prompts"
    src_dir = base_dir / "src"
    tests_dir = base_dir / "tests"
    examples_dir = base_dir / "examples"

    # Clean up previous runs
    if base_dir.exists():
        shutil.rmtree(base_dir)

    # Create project directories
    for dir_path in [prompts_dir, src_dir, tests_dir, examples_dir]:
        dir_path.mkdir(parents=True, exist_ok=True)

    # Create prompt files for the 'greeting' basename in two different languages
    (prompts_dir / "greeting_python.prompt").write_text(
        "Create a Python function `greet()` that returns 'Hello, Python!'"
    )
    (prompts_dir / "greeting_javascript.prompt").write_text(
        "Create a JavaScript function `greet()` that returns 'Hello, JavaScript!'"
    )
    (prompts_dir / "unrelated_file.txt").write_text("This file should be ignored.")

    print(f"Mock project created in: {base_dir.resolve()}")
    print("  - prompts/greeting_python.prompt")
    print("  - prompts/greeting_javascript.prompt")


def main() -> None:
    """
    A concise example demonstrating the `sync_main` function.

    This script simulates a `pdd sync greeting` command by:
    1.  Setting up a mock project with prompt files for Python and JavaScript.
    2.  Creating a mock `click.Context` object to pass global options.
    3.  Mocking the `construct_paths` and `sync_orchestration` functions to
        simulate their behavior without external dependencies (like LLM calls).
    4.  Calling `sync_main` and printing its aggregated results.
    """
    console = Console()
    output_directory = Path("./output")

    console.rule("[bold green]1. Setting up Mock Project[/bold green]")
    setup_mock_project(output_directory)

    # --- Create a mock Click context ---
    # In a real CLI, Click creates and populates this object automatically.
    # We create it manually to simulate the environment for sync_main.
    ctx = click.Context(click.Command("sync"))
    ctx.obj = {
        "strength": 0.5,
        "temperature": 0.1,
        "time": 0.25,
        "verbose": False,
        "force": False,
        "quiet": False,
        "output_cost": None,
        "review_examples": False,
        "local": False,
        "context": None,
    }
    # Mock the method that checks if a parameter was passed on the command line
    mock_source = MagicMock()
    mock_source.name = "DEFAULT"  # Simulate parameters coming from defaults
    ctx.get_parameter_source = MagicMock(return_value=mock_source)

    # --- Mock internal dependencies ---
    # We replace the real functions with mocks to control their output for this example.

    # This mock simulates the behavior of `construct_paths`.
    def mock_construct_paths(*args, **kwargs):
        command_options = kwargs.get("command_options", {})
        lang = command_options.get("language")
        # First call: General setup to find the prompts directory
        if not lang:
            return (
                {},
                {"prompts_dir": str(output_directory / "prompts")},
                None,
            )
        # Second call (in loop): Return paths for a specific language
        else:
            ext = "py" if lang == "python" else "js"
            return (
                {},
                {
                    "generate_output_path": f"{output_directory}/src/greeting.{ext}",
                    "test_output_path": f"{output_directory}/tests/test_greeting.{ext}",
                    "example_output_path": f"{output_directory}/examples/ex_greeting.{ext}",
                },
                lang,
            )

    # This mock simulates the behavior of `sync_orchestration`.
    def mock_sync_orchestration(*args, **kwargs):
        language = kwargs.get("language")
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
        return {"success": False, "error": "Unknown language"}

    console.rule("[bold green]2. Calling `sync_main`[/bold green]")
    print("`sync_main` will now run, using mocks for internal logic.")
    print("It will detect both 'python' and 'javascript' and process them sequentially.")

    # Use patch to temporarily replace real functions with our mocks
    with patch("pdd.sync_main.construct_paths", side_effect=mock_construct_paths), patch(
        "pdd.sync_main.sync_orchestration", side_effect=mock_sync_orchestration
    ):
        # Call the function with typical parameters
        results, total_cost, model = sync_main(
            ctx=ctx,
            basename="greeting",
            max_attempts=3,
            budget=1.0,  # Budget in USD
            skip_verify=False,
            skip_tests=False,
            target_coverage=90.0,
            dry_run=False,
        )

    console.rule("[bold blue]3. Results from `sync_main`[/bold blue]")
    print(f"Overall Success: {results.get('overall_success')}")
    print(f"Total Cost: ${total_cost:.4f} USD")
    print(f"Primary Model: {model}")
    print("\nDetailed Results (JSON):")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
