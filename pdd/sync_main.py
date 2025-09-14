import re
import time
from pathlib import Path
from typing import Any, Dict, List, Tuple

import click
from rich.console import Console
from rich.panel import Panel
from rich.table import Table
from rich import print as rprint

# Relative imports from the pdd package
from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .construct_paths import (
    _is_known_language, 
    construct_paths,
    _find_pddrc_file,
    _load_pddrc_config,
    _detect_context,
    _get_context_config
)
from .sync_orchestration import sync_orchestration

# A simple regex for basename validation to prevent path traversal or other injection
VALID_BASENAME_CHARS = re.compile(r"^[a-zA-Z0-9_-]+$")


def _validate_basename(basename: str) -> None:
    """Raises UsageError if the basename is invalid."""
    if not basename:
        raise click.UsageError("BASENAME cannot be empty.")
    if not VALID_BASENAME_CHARS.match(basename):
        raise click.UsageError(
            f"Basename '{basename}' contains invalid characters. "
            "Only alphanumeric, underscore, and hyphen are allowed."
        )


def _detect_languages(basename: str, prompts_dir: Path) -> List[str]:
    """
    Detects all available languages for a given basename by finding
    matching prompt files in the prompts directory.
    Excludes runtime languages (LLM) as they cannot form valid development units.
    """
    development_languages = []
    if not prompts_dir.is_dir():
        return []

    pattern = f"{basename}_*.prompt"
    for prompt_file in prompts_dir.glob(pattern):
        # stem is 'basename_language'
        stem = prompt_file.stem
        # Ensure the file starts with the exact basename followed by an underscore
        if stem.startswith(f"{basename}_"):
            potential_language = stem[len(basename) + 1 :]
            try:
                if _is_known_language(potential_language):
                    # Exclude runtime languages (LLM) as they cannot form valid development units
                    if potential_language.lower() != 'llm':
                        development_languages.append(potential_language)
            except ValueError:
                # PDD_PATH not set (likely during testing) - assume language is valid
                # if it matches common language patterns
                common_languages = {"python", "javascript", "java", "cpp", "c", "go", "rust", "typescript"}
                if potential_language.lower() in common_languages:
                    development_languages.append(potential_language)
                # Explicitly exclude 'llm' even in test scenarios
    
    # Return only development languages, with Python prioritized first, then sorted alphabetically
    if 'python' in development_languages:
        # Put Python first, then the rest sorted alphabetically
        other_languages = sorted([lang for lang in development_languages if lang != 'python'])
        return ['python'] + other_languages
    else:
        # No Python, just return sorted alphabetically
        return sorted(development_languages)


def sync_main(
    ctx: click.Context,
    basename: str,
    max_attempts: int,
    budget: float,
    skip_verify: bool,
    skip_tests: bool,
    target_coverage: float,
    log: bool,
) -> Tuple[Dict[str, Any], float, str]:
    """
    CLI wrapper for the sync command. Handles parameter validation, path construction,
    language detection, and orchestrates the sync workflow for each detected language.

    Args:
        ctx: The Click context object.
        basename: The base name for the prompt file.
        max_attempts: Maximum number of fix attempts.
        budget: Maximum total cost for the sync process.
        skip_verify: Skip the functional verification step.
        skip_tests: Skip unit test generation and fixing.
        target_coverage: Desired code coverage percentage.
        log: If True, display sync logs instead of running the sync.

    Returns:
        A tuple containing the results dictionary, total cost, and primary model name.
    """
    console = Console()
    start_time = time.time()

    # 1. Retrieve global parameters from context
    strength = ctx.obj.get("strength", DEFAULT_STRENGTH)
    temperature = ctx.obj.get("temperature", 0.0)
    time_param = ctx.obj.get("time", DEFAULT_TIME)
    verbose = ctx.obj.get("verbose", False)
    force = ctx.obj.get("force", False)
    quiet = ctx.obj.get("quiet", False)
    output_cost = ctx.obj.get("output_cost", None)
    review_examples = ctx.obj.get("review_examples", False)
    local = ctx.obj.get("local", False)
    context_override = ctx.obj.get("context", None)

    # 2. Validate inputs
    _validate_basename(basename)
    if budget <= 0:
        raise click.BadParameter("Budget must be a positive number.", param_hint="--budget")
    if max_attempts <= 0:
        raise click.BadParameter("Max attempts must be a positive integer.", param_hint="--max-attempts")

    if not quiet and budget < 1.0:
        console.log(f"[yellow]Warning:[/] Budget of ${budget:.2f} is low. Complex operations may exceed this limit.")

    # 3. Use construct_paths in 'discovery' mode to find the prompts directory.
    try:
        initial_config, _, _, _ = construct_paths(
            input_file_paths={},
            force=False,
            quiet=True,
            command="sync",
            command_options={"basename": basename},
            context_override=context_override,
        )
        prompts_dir = Path(initial_config.get("prompts_dir", "prompts"))
    except Exception as e:
        rprint(f"[bold red]Error initializing PDD paths:[/bold red] {e}")
        raise click.Abort()

    # 4. Detect all languages for the given basename
    languages = _detect_languages(basename, prompts_dir)
    if not languages:
        raise click.UsageError(
            f"No prompt files found for basename '{basename}' in directory '{prompts_dir}'.\n"
            f"Expected files with format: '{basename}_<language>.prompt'"
        )

    # 5. Handle --log mode separately
    if log:
        if not quiet:
            rprint(Panel(f"Displaying sync logs for [bold cyan]{basename}[/bold cyan]", title="PDD Sync Log", expand=False))

        for lang in languages:
            if not quiet:
                rprint(f"\n--- Log for language: [bold green]{lang}[/bold green] ---")

            # Use construct_paths to get proper directory configuration for log mode
            prompt_file_path = prompts_dir / f"{basename}_{lang}.prompt"
            
            try:
                resolved_config, _, _, _ = construct_paths(
                    input_file_paths={"prompt_file": str(prompt_file_path)},
                    force=True,  # Always use force=True in log mode to avoid prompts
                    quiet=True,
                    command="sync",
                    command_options={"basename": basename, "language": lang},
                    context_override=context_override,
                )
                
                code_dir = resolved_config.get("code_dir", "src")
                tests_dir = resolved_config.get("tests_dir", "tests")
                examples_dir = resolved_config.get("examples_dir", "examples")
            except Exception:
                # Fallback to default paths if construct_paths fails
                code_dir = str(prompts_dir.parent / "src")
                tests_dir = str(prompts_dir.parent / "tests")
                examples_dir = str(prompts_dir.parent / "examples")

            sync_orchestration(
                basename=basename,
                language=lang,
                prompts_dir=str(prompts_dir),
                code_dir=str(code_dir),
                examples_dir=str(examples_dir),
                tests_dir=str(tests_dir),
                log=True,
                verbose=verbose,
                quiet=quiet,
                context_override=context_override,
            )
        return {}, 0.0, ""

    # 6. Main Sync Workflow
    if not quiet:
        summary_panel = Panel(
            f"Basename: [bold cyan]{basename}[/bold cyan]\n"
            f"Languages: [bold green]{', '.join(languages)}[/bold green]\n"
            f"Budget: [bold yellow]${budget:.2f}[/bold yellow]\n"
            f"Max Attempts: [bold blue]{max_attempts}[/bold blue]",
            title="PDD Sync Starting",
            expand=False,
        )
        rprint(summary_panel)

    aggregated_results: Dict[str, Any] = {"results_by_language": {}}
    total_cost = 0.0
    primary_model = ""
    overall_success = True
    remaining_budget = budget

    for lang in languages:
        if not quiet:
            rprint(f"\n[bold]🚀 Syncing for language: [green]{lang}[/green]...[/bold]")

        if remaining_budget <= 0:
            if not quiet:
                rprint(f"[yellow]Budget exhausted. Skipping sync for '{lang}'.[/yellow]")
            overall_success = False
            aggregated_results["results_by_language"][lang] = {"success": False, "error": "Budget exhausted"}
            continue

        try:
            # Get the fully resolved configuration for this specific language using construct_paths.
            prompt_file_path = prompts_dir / f"{basename}_{lang}.prompt"
            
            command_options = {
                "basename": basename,
                "language": lang,
                "max_attempts": max_attempts,
                "budget": budget,
                "target_coverage": target_coverage,
                "strength": strength,
                "temperature": temperature,
                "time": time_param,
            }

            resolved_config, _, _, resolved_language = construct_paths(
                input_file_paths={"prompt_file": str(prompt_file_path)},
                force=force,
                quiet=True,
                command="sync",
                command_options=command_options,
                context_override=context_override,
            )

            # Extract all parameters directly from the resolved configuration
            final_strength = resolved_config.get("strength", strength)
            final_temp = resolved_config.get("temperature", temperature)
            final_max_attempts = resolved_config.get("max_attempts", max_attempts)
            final_target_coverage = resolved_config.get("target_coverage", target_coverage)
            
            code_dir = resolved_config.get("code_dir", "src")
            tests_dir = resolved_config.get("tests_dir", "tests")
            examples_dir = resolved_config.get("examples_dir", "examples")

            sync_result = sync_orchestration(
                basename=basename,
                language=resolved_language,
                prompts_dir=str(prompts_dir),
                code_dir=str(code_dir),
                examples_dir=str(examples_dir),
                tests_dir=str(tests_dir),
                budget=remaining_budget,
                max_attempts=final_max_attempts,
                skip_verify=skip_verify,
                skip_tests=skip_tests,
                target_coverage=final_target_coverage,
                strength=final_strength,
                temperature=final_temp,
                time_param=time_param,
                force=force,
                quiet=quiet,
                verbose=verbose,
                output_cost=output_cost,
                review_examples=review_examples,
                local=local,
                context_config=resolved_config,
                context_override=context_override,
            )

            lang_cost = sync_result.get("total_cost", 0.0)
            total_cost += lang_cost
            remaining_budget -= lang_cost

            if sync_result.get("model_name"):
                primary_model = sync_result["model_name"]

            if not sync_result.get("success", False):
                overall_success = False

            aggregated_results["results_by_language"][lang] = sync_result

        except Exception as e:
            if not quiet:
                rprint(f"[bold red]An unexpected error occurred during sync for '{lang}':[/bold red] {e}")
                if verbose:
                    console.print_exception(show_locals=True)
            overall_success = False
            aggregated_results["results_by_language"][lang] = {"success": False, "error": str(e)}

    # 7. Final Summary Report
    if not quiet:
        elapsed_time = time.time() - start_time
        final_table = Table(title="PDD Sync Complete", show_header=True, header_style="bold magenta")
        final_table.add_column("Language", style="cyan", no_wrap=True)
        final_table.add_column("Status", justify="center")
        final_table.add_column("Cost (USD)", justify="right", style="yellow")
        final_table.add_column("Details")

        for lang, result in aggregated_results["results_by_language"].items():
            status = "[green]Success[/green]" if result.get("success") else "[red]Failed[/red]"
            cost_str = f"${result.get('total_cost', 0.0):.4f}"
            details = result.get("summary") or result.get("error", "No details.")
            final_table.add_row(lang, status, cost_str, str(details))

        rprint(final_table)

        summary_text = (
            f"Total time: [bold]{elapsed_time:.2f}s[/bold] | "
            f"Total cost: [bold yellow]${total_cost:.4f}[/bold yellow] | "
            f"Overall status: {'[green]Success[/green]' if overall_success else '[red]Failed[/red]'}"
        )
        rprint(Panel(summary_text, expand=False))

    aggregated_results["overall_success"] = overall_success
    aggregated_results["total_cost"] = total_cost
    aggregated_results["primary_model"] = primary_model

    return aggregated_results, total_cost, primary_model
