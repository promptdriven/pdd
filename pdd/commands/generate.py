"""
Generate, test, and example commands.
"""
import click
from typing import Dict, Optional, Tuple, List

from ..code_generator_main import code_generator_main
from ..context_generator_main import context_generator_main
from ..cmd_test_main import cmd_test_main
from ..track_cost import track_cost
from ..core.errors import handle_error, console

class GenerateCommand(click.Command):
    """Ensure help shows PROMPT_FILE as required even when validated at runtime."""

    def collect_usage_pieces(self, ctx: click.Context) -> List[str]:
        pieces = super().collect_usage_pieces(ctx)
        return ["PROMPT_FILE" if piece == "[PROMPT_FILE]" else piece for piece in pieces]


@click.command("generate", cls=GenerateCommand)
@click.argument("prompt_file", required=False, type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the generated code (file or directory).",
)
@click.option(
    "--original-prompt",
    "original_prompt_file_path",
    type=click.Path(exists=True, dir_okay=False),
    default=None,
    help="Path to the original prompt file for incremental generation.",
)
@click.option(
    "--incremental",
    "incremental_flag",
    is_flag=True,
    default=False,
    help="Force incremental patching even if changes are significant (requires existing output).",
)
@click.option(
    "-e",
    "--env",
    "env_kv",
    multiple=True,
    help="Set template variable (KEY=VALUE) or read KEY from env",
)
@click.option(
    "--template",
    "template_name",
    type=str,
    default=None,
    help="Use a packaged/project template by name (e.g., architecture/architecture_json)",
)
@click.option(
    "--unit-test",
    "unit_test_file",
    type=click.Path(exists=True, dir_okay=False),
    default=None,
    help="Path to a unit test file to include in the prompt.",
)
@click.option(
    "--exclude-tests",
    "exclude_tests",
    is_flag=True,
    default=False,
    help="Do not automatically include test files found in the default tests directory.",
)
@click.pass_context
@track_cost
def generate(
    ctx: click.Context,
    prompt_file: Optional[str],
    output: Optional[str],
    original_prompt_file_path: Optional[str],
    incremental_flag: bool,
    env_kv: Tuple[str, ...],
    template_name: Optional[str],
    unit_test_file: Optional[str],
    exclude_tests: bool,
) -> Optional[Tuple[str, float, str]]:
    """
    Generate code from a prompt file.

       \b
    Related commands:
      test      Generate unit tests for a prompt.
      example   Generate example code for a prompt.

    \b
    Note:
      Global options (for example ``--force``, ``--temperature``, ``--time``)
      can be placed either before or after the subcommand. For example:

        pdd generate my.prompt --force --temperature 0.5
    """
    try:
        # Resolve template to a prompt path when requested
        if template_name and prompt_file:
            raise click.UsageError("Provide either --template or a PROMPT_FILE path, not both.")
        if template_name:
            try:
                from .. import template_registry as _tpl
                meta = _tpl.load_template(template_name)
                prompt_file = meta.get("path")
                if not prompt_file:
                    raise click.UsageError(f"Template '{template_name}' did not return a valid path")
            except Exception as e:
                raise click.UsageError(f"Failed to load template '{template_name}': {e}")
        if not template_name and not prompt_file:
            raise click.UsageError("Missing PROMPT_FILE. To use a template, pass --template NAME instead.")
        # Parse -e/--env arguments into a dict
        env_vars: Dict[str, str] = {}
        import os as _os
        for item in env_kv or ():
            if "=" in item:
                key, value = item.split("=", 1)
                key = key.strip()
                if key:
                    env_vars[key] = value
            else:
                key = item.strip()
                if key:
                    val = _os.environ.get(key)
                    if val is not None:
                        env_vars[key] = val
                    else:
                        if ctx.obj.get("verbose") and not ctx.obj.get("quiet"):
                            console.print(f"[warning]-e {key} not found in environment; skipping[/warning]")
        generated_code, incremental, total_cost, model_name = code_generator_main(
            ctx=ctx,
            prompt_file=prompt_file,  # resolved template path or user path
            output=output,
            original_prompt_file_path=original_prompt_file_path,
            force_incremental_flag=incremental_flag,
            env_vars=env_vars or None,
            unit_test_file=unit_test_file,
            exclude_tests=exclude_tests,
        )
        return generated_code, total_cost, model_name
    except click.Abort:
        # Let user cancellation (e.g., pressing 'no' on overwrite prompt) propagate
        # to PDDCLI.invoke() for graceful handling (fix for issue #186)
        raise
    except Exception as exception:
        handle_error(exception, "generate", ctx.obj.get("quiet", False))
        return None


@click.command("example")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the generated example code (file or directory).",
)
@click.pass_context
@track_cost
def example(
    ctx: click.Context, 
    prompt_file: str, 
    code_file: str, 
    output: Optional[str]
) -> Optional[Tuple[str, float, str]]:
    """Generate example code for a given prompt and implementation."""
    try:
        example_code, total_cost, model_name = context_generator_main(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            output=output,
        )
        return example_code, total_cost, model_name
    except click.Abort:
        raise
    except Exception as exception:
        handle_error(exception, "example", ctx.obj.get("quiet", False))
        return None


@click.command("test")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the generated test file (file or directory).",
)
@click.option(
    "--language", 
    type=str, 
    default=None, 
    help="Specify the programming language."
)
@click.option(
    "--coverage-report",
    type=click.Path(exists=True, dir_okay=False),
    default=None,
    help="Path to the coverage report file for existing tests.",
)
@click.option(
    "--existing-tests",
    type=click.Path(exists=True, dir_okay=False),
    multiple=True,
    help="Path to existing unit test file(s). Can be specified multiple times.",
)
@click.option(
    "--target-coverage",
    type=click.FloatRange(0.0, 100.0),
    default=None,  # Use None, default handled in cmd_test_main or env var
    help="Desired code coverage percentage (default: 10.0 or PDD_TEST_COVERAGE_TARGET).",
)
@click.option(
    "--merge",
    is_flag=True,
    default=False,
    help="Merge new tests with existing test file instead of creating a separate file.",
)
@click.pass_context
@track_cost
def test(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    output: Optional[str],
    language: Optional[str],
    coverage_report: Optional[str],
    existing_tests: Tuple[str, ...],
    target_coverage: Optional[float],
    merge: bool,
) -> Optional[Tuple[str, float, str]]:
    """Generate unit tests for a given prompt and implementation."""
    try:
        # Convert empty tuple to None for cmd_test_main compatibility
        existing_tests_list = list(existing_tests) if existing_tests else None
        test_code, total_cost, model_name = cmd_test_main(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            output=output,
            language=language,
            coverage_report=coverage_report,
            existing_tests=existing_tests_list,
            target_coverage=target_coverage,
            merge=merge,
        )
        return test_code, total_cost, model_name
    except click.Abort:
        raise
    except Exception as exception:
        handle_error(exception, "test", ctx.obj.get("quiet", False))
        return None
