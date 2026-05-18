"""CLI commands for the Generate Suite: ``generate``, ``test``, ``example``.

Implements the public CLI surface that dispatches to the LLM-driven generation
backends (``code_generator_main``, ``context_generator_main``, ``cmd_test_main``,
``run_agentic_architecture``, ``run_incremental_architecture``,
``run_agentic_test``, ``cache_story_prompt_links``, ``generate_user_story``).

Mode dispatch:
    * ``generate`` — standard prompt-file generation; agentic-issue mode when
      the positional argument is a GitHub issue URL; incremental-PRD mode when
      ``--incremental --experimental-prd`` is paired with an issue URL or a
      PRD-like file.
    * ``test`` — agentic mode for a GitHub issue URL, story-prompt linking for
      ``story__*.md`` inputs, story generation for ``*.prompt`` inputs, and
      manual mode (explicit via ``--manual`` or implicit when two non-URL,
      non-story positional arguments are given).
    * ``example`` — context example generation from a prompt + code pair.
"""

from __future__ import annotations

import os
import re
from pathlib import Path
from typing import Any, List, Optional, Tuple

import click
from rich.console import Console

from .. import DEFAULT_STRENGTH, DEFAULT_TEMPERATURE, DEFAULT_TIME
from ..context_generator_main import context_generator_main
from ..core.errors import handle_error
from ..operation_log import log_operation
from ..track_cost import track_cost
from ..user_story_tests import cache_story_prompt_links, generate_user_story

console = Console()

# ---------------------------------------------------------------------------
# Lazy code-generator binding
# ---------------------------------------------------------------------------
# ``code_generator_main`` is imported lazily so that test fixtures can patch
# ``pdd.code_generator_main.code_generator_main`` and have the patched version
# picked up on the next invocation. The module-level cache lets tests reset
# state by clearing both names (see ``reset_generate_module_state`` in
# ``tests/commands/test_generate.py``).
code_generator_main: Optional[Any] = None
_DEFAULT_CODE_GENERATOR_MAIN: Optional[Any] = None

_GITHUB_ISSUE_RE = re.compile(r"github\.com/.+/issues/\d+", re.IGNORECASE)
_PRD_SUFFIXES = {".md", ".markdown", ".txt", ".rst", ".adoc"}
_STORY_FILENAME_RE = re.compile(r"^story__.+\.md$", re.IGNORECASE)


def _resolve_code_generator_main() -> Any:
    """Return the (possibly mocked) ``code_generator_main`` implementation.

    Imports are re-resolved on every call so that ``patch`` targeting
    ``pdd.code_generator_main.code_generator_main`` is observed; the resolved
    callable is cached on the module so tests can clear it between cases.
    """
    global code_generator_main, _DEFAULT_CODE_GENERATOR_MAIN
    if code_generator_main is None:
        from ..code_generator_main import code_generator_main as _impl  # local import
        code_generator_main = _impl
        _DEFAULT_CODE_GENERATOR_MAIN = _impl
    return code_generator_main


def _is_github_issue_url(value: str) -> bool:
    """Return True iff *value* looks like a GitHub issue URL."""
    if not value:
        return False
    return bool(_GITHUB_ISSUE_RE.search(value))


def _is_prd_like(value: str) -> bool:
    """Return True iff *value* names a PRD-like markdown/text file."""
    if not value:
        return False
    return Path(value).suffix.lower() in _PRD_SUFFIXES


def _is_story_file(value: str) -> bool:
    """Return True for ``story__*.md`` filenames (case-insensitive)."""
    if not value:
        return False
    return bool(_STORY_FILENAME_RE.match(Path(value).name))


def _is_prompt_file(value: str) -> bool:
    """Return True iff *value* ends with ``.prompt``."""
    if not value:
        return False
    return Path(value).suffix.lower() == ".prompt"


def _ctx_value(ctx: click.Context, key: str, default: Any) -> Any:
    """Look up *key* in ``ctx.obj`` (dict-like) with a default."""
    obj = getattr(ctx, "obj", None)
    if isinstance(obj, dict):
        return obj.get(key, default)
    if obj is not None and hasattr(obj, key):
        return getattr(obj, key, default)
    return default


# ---------------------------------------------------------------------------
# generate
# ---------------------------------------------------------------------------

class GenerateCommand(click.Command):
    """Custom Command subclass — kept for future help-text customisation.

    The spec calls this out so help formatting for the conditionally-required
    ``prompt_file`` argument can be specialised later. For now it behaves like
    a stock ``click.Command``.
    """


@click.command(cls=GenerateCommand, name="generate")
@click.argument("prompt_file", type=click.UNPROCESSED, required=False)
@click.option("--template", "template", default=None,
              help="Use a packaged template by name instead of a prompt file.")
@click.option("-e", "--env", "env", multiple=True,
              help="Set template variables as KEY=VALUE, or KEY to read $KEY from the environment.")
@click.option("--output", "output", default=None,
              help="Where to save generated code.")
@click.option("--original-prompt", "original_prompt", default=None,
              help="Original prompt file path for incremental generation.")
@click.option("--incremental", is_flag=True, default=False,
              help="Force incremental patching against the existing output file.")
@click.option("--experimental-prd", is_flag=True, default=False,
              help="Opt in to experimental PRD propagation mode.")
@click.option("--dry-run", is_flag=True, default=False,
              help="Dry run (only valid in Incremental PRD mode).")
@click.option("--unit-test", "unit_test", default=None,
              help="Generate unit tests alongside code.")
@click.option("--exclude-tests", is_flag=True, default=False,
              help="Exclude tests during generation.")
@click.option("--skip-prompts", is_flag=True, default=False,
              help="Skip prompt generation in agentic mode.")
@click.option("--output-dir", "output_dir", default=None,
              help="Output directory for agentic / PRD modes.")
@click.option("--force-single", is_flag=True, default=False,
              help="Force single-file output (agentic mode).")
@click.option("--no-github-state", is_flag=True, default=False,
              help="Disable GitHub issue comment-based state persistence.")
@click.option("--project-root", "project_root", type=click.Path(), default=None,
              help="Explicit project root override for agentic and incremental PRD modes.")
@click.pass_context
@log_operation(operation="generate", clears_run_report=True, updates_fingerprint=True)
@track_cost
def generate(
    ctx: click.Context,
    prompt_file: Optional[str],
    template: Optional[str],
    env: Tuple[str, ...],
    output: Optional[str],
    original_prompt: Optional[str],
    incremental: bool,
    experimental_prd: bool,
    dry_run: bool,
    unit_test: Optional[str],
    exclude_tests: bool,
    skip_prompts: bool,
    output_dir: Optional[str],
    force_single: bool,
    no_github_state: bool,
    project_root: Optional[str],
) -> Tuple[Any, float, str]:
    """Generate code from a prompt, or trigger agentic / PRD architecture flows."""

    quiet = bool(_ctx_value(ctx, "quiet", False))
    verbose = bool(_ctx_value(ctx, "verbose", False))

    try:
        # ----- argument validation (XOR between prompt_file and template) ----
        if prompt_file and template:
            raise click.UsageError("Cannot specify both PROMPT_FILE and --template.")
        if not prompt_file and not template:
            raise click.UsageError("Missing argument 'PROMPT_FILE' or option '--template'.")

        target = prompt_file if prompt_file else template
        is_issue = _is_github_issue_url(target) if prompt_file else False
        is_prd = _is_prd_like(target) if prompt_file else False

        # ----- dry-run guard ------------------------------------------------
        if dry_run and not (incremental and experimental_prd):
            raise click.UsageError(
                "--dry-run is only valid with --incremental --experimental-prd."
            )

        # ----- experimental-prd requires --incremental ---------------------
        # `--experimental-prd` is meaningful only when paired with
        # `--incremental`; without it the flag would silently no-op and
        # users would fall through to agentic or standard code generation.
        if experimental_prd and not incremental:
            raise click.UsageError(
                "--experimental-prd requires --incremental."
            )

        # Code-generation options that, when present, signal the caller
        # wants legacy prompt-to-code generation even if the target file
        # looks PRD-like (e.g. a `.md` prompt with `--output out.py`).
        code_gen_options_present = bool(
            output
            or original_prompt
            or unit_test
            or exclude_tests
            or env
            or template
        )

        # ----- explicit PRD opt-in -----------------------------------------
        # An --incremental run pointing at a GitHub issue URL or a PRD-like
        # file must say so explicitly via --experimental-prd; we refuse to
        # dispatch based on suffix alone. PRD-like prompts combined with
        # explicit code-generation options stay in legacy code generation.
        if (
            incremental
            and not experimental_prd
            and (is_issue or (is_prd and not code_gen_options_present))
        ):
            raise click.UsageError(
                "To use incremental PRD mode, run: "
                f"pdd generate --incremental --experimental-prd {target}"
            )

        # ----- experimental-prd requires a PRD-like target -----------------
        # `--experimental-prd` is only valid when the target is a GitHub issue
        # URL or a PRD-like file. Reject combinations like `--template` or a
        # plain prompt file so the flag cannot silently fall through to
        # standard code generation.
        if incremental and experimental_prd and not (is_issue or is_prd):
            raise click.UsageError(
                "--experimental-prd requires a GitHub issue URL or a PRD-like "
                "file (e.g. .md/.markdown/.prd) as the target."
            )

        # ----- incremental PRD mode ----------------------------------------
        if incremental and experimental_prd and (is_issue or is_prd):
            forbidden = {
                "--output": output,
                "--original-prompt": original_prompt,
                "--env": tuple(env) if env else None,
                "--template": template,
                "--unit-test": unit_test,
                "--exclude-tests": exclude_tests if exclude_tests else None,
            }
            offending = [name for name, value in forbidden.items() if value]
            if offending:
                raise click.UsageError(
                    "Incremental PRD mode does not accept code-generation options: "
                    + ", ".join(sorted(offending))
                )

            from ..agentic_architecture import run_incremental_architecture

            strength = float(_ctx_value(ctx, "strength", DEFAULT_STRENGTH))
            temperature = float(_ctx_value(ctx, "temperature", DEFAULT_TEMPERATURE))
            time_val = float(_ctx_value(ctx, "time", DEFAULT_TIME))

            success, message, cost, model, changed_files = run_incremental_architecture(
                prd_source=target,
                dry_run=dry_run,
                target_dir=output_dir,
                use_github_state=not no_github_state,
                strength=strength,
                temperature=temperature,
                time=time_val,
                project_root=project_root,
                verbose=verbose,
                quiet=quiet,
            )

            if not quiet:
                label = "Would change files:" if dry_run else "Output files:"
                console.print(f"[bold]{label}[/bold] {changed_files}")
                style = "green" if success else "red"
                console.print(f"[{style}]{message}[/{style}]")

            if not success:
                raise click.exceptions.Exit(1)

            return ({"success": success, "message": message, "changed_files": changed_files},
                    cost, model)

        # ----- agentic-issue mode (non-incremental) ------------------------
        if is_issue and not incremental:
            from ..agentic_architecture import run_agentic_architecture

            success, message, cost, model, output_files = run_agentic_architecture(
                issue_url=target,
                skip_prompts=skip_prompts,
                target_dir=output_dir,
                use_github_state=not no_github_state,
                force_single=force_single,
                project_root=project_root,
                verbose=verbose,
                quiet=quiet,
            )
            if not quiet:
                style = "green" if success else "red"
                console.print(f"[{style}]Agentic architecture: {message}[/{style}]")
                console.print(f"Output files: {output_files}")

            if not success:
                raise click.exceptions.Exit(1)

            return ({"success": success, "message": message, "output_files": output_files},
                    cost, model)

        # ----- standard prompt-file / template mode ------------------------
        if project_root is not None:
            raise click.UsageError(
                "--project-root is only supported in agentic-issue mode (GitHub issue URL) "
                "or --incremental --experimental-prd mode."
            )

        resolved_prompt = prompt_file
        if template:
            from ..template_registry import load_template
            try:
                resolved = load_template(template)
            except FileNotFoundError as exc:
                raise click.UsageError(
                    f"Failed to load template '{template}': {exc}"
                ) from exc
            except Exception as exc:  # noqa: BLE001 — surface as UsageError
                raise click.UsageError(
                    f"Failed to load template '{template}': {exc}"
                ) from exc
            if isinstance(resolved, dict):
                resolved_prompt = resolved.get("path") or resolved.get("prompt_path") or resolved.get("file")
            else:
                resolved_prompt = resolved
            if not resolved_prompt:
                raise click.UsageError(f"Failed to load template '{template}': empty path.")

        # Validate that the standard-mode prompt file exists before invoking
        # the generator backend. Without this, a missing prompt would propagate
        # as an error tuple that the CLI wrapper treats as success (exit 0),
        # masking failures from scripts and users. We restrict this to direct
        # prompt-file invocations; template resolution is the registry's
        # responsibility.
        if prompt_file and not template:
            prompt_path = Path(prompt_file)
            if not prompt_path.exists():
                raise click.UsageError(
                    f"Input file not found: {prompt_file}"
                )
            if prompt_path.is_dir():
                raise click.UsageError(
                    f"Input path is a directory, not a file: {prompt_file}"
                )

        # Parse -e/--env into KEY=VALUE pairs and propagate into os.environ for
        # template / prompt-include resolution. Bare KEY entries are looked up
        # in the live environment.
        env_vars: dict[str, str] = {}
        for entry in env:
            if "=" in entry:
                key, value = entry.split("=", 1)
                env_vars[key.strip()] = value
                os.environ[key.strip()] = value
            else:
                key = entry.strip()
                if key in os.environ:
                    env_vars[key] = os.environ[key]
                # else: leave it absent; downstream may raise its own error.

        impl = _resolve_code_generator_main()
        result = impl(
            ctx=ctx,
            prompt_file=resolved_prompt,
            output=output,
            original_prompt_file_path=original_prompt,
            force_incremental_flag=bool(incremental),
            env_vars=env_vars,
            unit_test_file=unit_test,
            exclude_tests=bool(exclude_tests),
        )

        # ``code_generator_main`` returns ``(code, was_incremental, cost, model)``.
        if not isinstance(result, tuple) or len(result) < 4:
            raise click.UsageError(
                f"code_generator_main returned unexpected shape: {result!r}"
            )
        generated_code, _was_incremental, total_cost, model_name = result[:4]

        return generated_code, total_cost, model_name

    except (click.ClickException, click.exceptions.Exit, click.Abort):
        raise
    except Exception as exception:  # noqa: BLE001 — centralised handling
        handle_error(exception, "generate", quiet)
        raise click.exceptions.Exit(1) from exception


# ---------------------------------------------------------------------------
# example
# ---------------------------------------------------------------------------

@click.command(name="example")
@click.argument("prompt_file", type=click.UNPROCESSED)
@click.argument("code_file", type=click.UNPROCESSED)
@click.option("--output", default=None, help="Where to save the generated example.")
@click.option("--format", "format_", type=click.Choice(["code", "md"]), default="code",
              show_default=True,
              help="Output format: 'code' (uses language extension) or 'md' (markdown).")
@click.pass_context
@log_operation(operation="example", clears_run_report=True, updates_fingerprint=True)
@track_cost
def example(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    output: Optional[str],
    format_: Optional[str],
) -> Tuple[Any, float, str]:
    """Generate a runnable context example from a prompt + code pair."""

    quiet = bool(_ctx_value(ctx, "quiet", False))
    try:
        generated, cost, model = context_generator_main(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            output=output,
            format=format_,
        )
        return generated, cost, model
    except (click.ClickException, click.exceptions.Exit, click.Abort):
        raise
    except Exception as exception:  # noqa: BLE001
        handle_error(exception, "example", quiet)
        raise click.exceptions.Exit(1) from exception


# ---------------------------------------------------------------------------
# test
# ---------------------------------------------------------------------------

@click.command(name="test")
@click.argument("args", nargs=-1, type=click.UNPROCESSED)
@click.option("--manual", is_flag=True, default=False,
              help="Force manual mode (PROMPT CODE arguments).")
@click.option("--timeout-adder", type=float, default=0.0,
              help="Additional timeout seconds for agentic mode.")
@click.option("--no-github-state", is_flag=True, default=False,
              help="Disable GitHub issue comment-based state persistence (agentic mode).")
@click.option("--output", default=None, help="Output path for the generated test file.")
@click.option("--language", default=None, help="Programming language override.")
@click.option("--coverage-report", "coverage_report", default=None,
              help="Path to a coverage report for test-augmentation mode.")
@click.option("--existing-tests", "existing_tests", multiple=True,
              help="Existing test files (repeatable) to augment.")
@click.option("--target-coverage", "target_coverage", type=float, default=None,
              help="Desired coverage percentage (0.0-100.0).")
@click.option("--merge", is_flag=True, default=False,
              help="Merge new tests into the existing test file.")
@click.pass_context
@log_operation(operation="test", updates_run_report=True)
@track_cost
def test(
    ctx: click.Context,
    args: Tuple[str, ...],
    manual: bool,
    timeout_adder: float,
    no_github_state: bool,
    output: Optional[str],
    language: Optional[str],
    coverage_report: Optional[str],
    existing_tests: Tuple[str, ...],
    target_coverage: Optional[float],
    merge: bool,
) -> Tuple[Any, float, str]:
    """Generate or enhance unit tests in agentic, story or manual modes."""

    quiet = bool(_ctx_value(ctx, "quiet", False))
    verbose = bool(_ctx_value(ctx, "verbose", False))

    try:
        if not args:
            raise click.UsageError("Missing arguments. See 'pdd test --help'.")

        first_arg = args[0]

        # ----- agentic mode (issue URL, no --manual) -----------------------
        if not manual and _is_github_issue_url(first_arg):
            if len(args) != 1:
                raise click.UsageError(
                    "Agentic mode requires exactly one argument (issue URL)."
                )

            from ..agentic_test import run_agentic_test

            success, message, cost, model, changed_files = run_agentic_test(
                issue_url=first_arg,
                timeout_adder=timeout_adder,
                use_github_state=not no_github_state,
                verbose=verbose,
                quiet=quiet,
            )

            if not quiet:
                style = "green" if success else "red"
                console.print(f"[{style}]Agentic test: {message}[/{style}]")
                console.print(f"Changed files: {changed_files}")

            if not success:
                raise click.exceptions.Exit(1)

            return ({"success": success, "message": message, "changed_files": changed_files},
                    cost, model)

        # ----- story-link mode (single ``story__*.md`` argument) -----------
        if not manual and len(args) == 1 and _is_story_file(first_arg):
            strength = float(_ctx_value(ctx, "strength", 0.2))
            temperature = float(_ctx_value(ctx, "temperature", DEFAULT_TEMPERATURE))
            time_val = float(_ctx_value(ctx, "time", DEFAULT_TIME))

            success, message, cost, model, refs = cache_story_prompt_links(
                story_file=first_arg,
                prompts_dir=_ctx_value(
                    ctx, "prompts_dir", os.environ.get("PDD_PROMPTS_DIR")
                ),
                strength=strength,
                temperature=temperature,
                time=time_val,
                verbose=verbose,
            )
            if not quiet:
                style = "green" if success else "red"
                console.print(f"[{style}]Story prompt links: {message}[/{style}]")
            return ({"success": success, "message": message, "linked_prompt_refs": refs},
                    cost, model)

        # ----- story-generation mode (all args are .prompt files) ----------
        if not manual and args and all(_is_prompt_file(a) for a in args):
            strength = float(_ctx_value(ctx, "strength", 0.2))
            temperature = float(_ctx_value(ctx, "temperature", DEFAULT_TEMPERATURE))
            time_val = float(_ctx_value(ctx, "time", DEFAULT_TIME))

            story_result = generate_user_story(
                prompt_files=list(args),
                output=output,
                stories_dir=_ctx_value(
                    ctx, "stories_dir", os.environ.get("PDD_USER_STORIES_DIR")
                ),
                prompts_dir=_ctx_value(
                    ctx, "prompts_dir", os.environ.get("PDD_PROMPTS_DIR")
                ),
                strength=strength,
                temperature=temperature,
                time=time_val,
                verbose=verbose,
            )
            success, message, cost, model, story_path, refs = story_result
            if not quiet:
                style = "green" if success else "red"
                console.print(f"[{style}]Story generation: {message}[/{style}]")
            return (
                {
                    "success": success,
                    "message": message,
                    "story_path": story_path,
                    "linked_prompt_refs": refs,
                },
                cost,
                model,
            )

        # ----- manual mode (--manual or two non-URL/non-prompt args) -------
        if len(args) != 2:
            raise click.UsageError(
                "Manual mode requires exactly two arguments: PROMPT_FILE CODE_FILE."
            )

        from ..cmd_test_main import cmd_test_main

        prompt_file_arg, code_file_arg = args
        strength = float(_ctx_value(ctx, "strength", DEFAULT_STRENGTH))
        temperature = float(_ctx_value(ctx, "temperature", DEFAULT_TEMPERATURE))

        result = cmd_test_main(
            ctx=ctx,
            prompt_file=prompt_file_arg,
            code_file=code_file_arg,
            output=output,
            language=language,
            coverage_report=coverage_report,
            existing_tests=list(existing_tests) if existing_tests else None,
            target_coverage=target_coverage,
            merge=merge,
            strength=strength,
            temperature=temperature,
            manual=manual,
        )

        # ``cmd_test_main`` returns a 3- or 4-tuple depending on language path.
        if isinstance(result, tuple):
            if len(result) >= 3:
                unit_test_code = result[0]
                total_cost = result[-2] if len(result) >= 2 else 0.0
                model_name = result[-1] if len(result) >= 1 else ""
                # When the tuple is (content, cost, model, agentic_success):
                if len(result) >= 4:
                    total_cost = result[1]
                    model_name = result[2]
                return unit_test_code, total_cost, model_name
        raise click.UsageError(
            f"cmd_test_main returned unexpected shape: {result!r}"
        )

    except (click.ClickException, click.exceptions.Exit, click.Abort):
        raise
    except Exception as exception:  # noqa: BLE001
        handle_error(exception, "test", quiet)
        raise click.exceptions.Exit(1) from exception


__all__: List[str] = [
    "generate",
    "test",
    "example",
    "GenerateCommand",
    "code_generator_main",
    "context_generator_main",
    "cache_story_prompt_links",
    "generate_user_story",
]
