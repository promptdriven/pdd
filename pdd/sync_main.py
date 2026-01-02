import re
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

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

# Regex for basename validation supporting subdirectory paths (e.g., 'core/cloud')
# Allows: alphanumeric, underscore, hyphen, and forward slash for subdirectory paths
# Structure inherently prevents:
#   - Path traversal (..) - dot not in character class
#   - Leading slash (/abs) - must start with [a-zA-Z0-9_-]+
#   - Trailing slash (path/) - must end with [a-zA-Z0-9_-]+
#   - Double slash (a//b) - requires characters between slashes
VALID_BASENAME_CHARS = re.compile(r"^[a-zA-Z0-9_-]+(/[a-zA-Z0-9_-]+)*$")


def _validate_basename(basename: str) -> None:
    """Raises UsageError if the basename is invalid."""
    if not basename:
        raise click.UsageError("BASENAME cannot be empty.")
    if not VALID_BASENAME_CHARS.match(basename):
        raise click.UsageError(
            f"Basename '{basename}' contains invalid characters. "
            "Only alphanumeric, underscore, hyphen, and forward slash (for subdirectories) are allowed."
        )


def _detect_languages(basename: str, prompts_dir: Path) -> List[str]:
    """
    Detects all available languages for a given basename by finding
    matching prompt files in the prompts directory.
    Excludes runtime languages (LLM) as they cannot form valid development units.

    Supports subdirectory basenames like 'core/cloud':
    - For basename 'core/cloud', searches in prompts/core/ for cloud_*.prompt files
    - The stem comparison only uses the filename part ('cloud'), not the path ('core/cloud')
    """
    development_languages = []
    if not prompts_dir.is_dir():
        return []

    # For subdirectory basenames, extract just the name part for stem comparison
    if '/' in basename:
        name_part = basename.rsplit('/', 1)[1]  # 'cloud' from 'core/cloud'
    else:
        name_part = basename

    pattern = f"{basename}_*.prompt"
    for prompt_file in prompts_dir.glob(pattern):
        # stem is the filename without extension (e.g., 'cloud_python')
        stem = prompt_file.stem
        # Ensure the file starts with the exact name part followed by an underscore
        if stem.startswith(f"{name_part}_"):
            potential_language = stem[len(name_part) + 1 :]
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
    max_attempts: Optional[int],
    budget: Optional[float],
    skip_verify: bool,
    skip_tests: bool,
    target_coverage: float,
    dry_run: bool,
) -> Tuple[Dict[str, Any], float, str]:
    """
    CLI wrapper for the sync command. Handles parameter validation, path construction,
    language detection, and orchestrates the sync workflow for each detected language.

    Args:
        ctx: The Click context object.
        basename: The base name for the prompt file.
        max_attempts: Maximum number of fix attempts. If None, uses .pddrc value or default (3).
        budget: Maximum total cost for the sync process. If None, uses .pddrc value or default (20.0).
        skip_verify: Skip the functional verification step.
        skip_tests: Skip unit test generation and fixing.
        target_coverage: Desired code coverage percentage.
        dry_run: If True, analyze sync state without executing operations.

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

    # Default values for max_attempts, budget, target_coverage when not specified via CLI or .pddrc
    DEFAULT_MAX_ATTEMPTS = 3
    DEFAULT_BUDGET = 20.0
    DEFAULT_TARGET_COVERAGE = 90.0

    # 2. Validate inputs (basename only - budget/max_attempts validated after config resolution)
    _validate_basename(basename)

    # Validate CLI-specified values if provided (not None)
    # Note: max_attempts=0 is valid (skips LLM loop, goes straight to agentic mode)
    if budget is not None and budget <= 0:
        raise click.BadParameter("Budget must be a positive number.", param_hint="--budget")
    if max_attempts is not None and max_attempts < 0:
        raise click.BadParameter("Max attempts must be a non-negative integer.", param_hint="--max-attempts")

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

    # 5. Handle --dry-run mode separately
    if dry_run:
        if not quiet:
            rprint(Panel(f"Displaying sync analysis for [bold cyan]{basename}[/bold cyan]", title="PDD Sync Dry Run", expand=False))

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
                dry_run=True,
                verbose=verbose,
                quiet=quiet,
                context_override=context_override,
            )
        return {}, 0.0, ""

    # 6. Main Sync Workflow
    # Determine display values for summary panel (use CLI values or defaults for display)
    display_budget = budget if budget is not None else DEFAULT_BUDGET
    display_max_attempts = max_attempts if max_attempts is not None else DEFAULT_MAX_ATTEMPTS

    if not quiet and display_budget < 1.0:
        console.log(f"[yellow]Warning:[/] Budget of ${display_budget:.2f} is low. Complex operations may exceed this limit.")

    if not quiet:
        summary_panel = Panel(
            f"Basename: [bold cyan]{basename}[/bold cyan]\n"
            f"Languages: [bold green]{', '.join(languages)}[/bold green]\n"
            f"Budget: [bold yellow]${display_budget:.2f}[/bold yellow]\n"
            f"Max Attempts: [bold blue]{display_max_attempts}[/bold blue]",
            title="PDD Sync Starting",
            expand=False,
        )
        rprint(summary_panel)

    aggregated_results: Dict[str, Any] = {"results_by_language": {}}
    total_cost = 0.0
    primary_model = ""
    overall_success = True
    # remaining_budget will be set from resolved config on first language iteration
    remaining_budget: Optional[float] = None

    for lang in languages:
        if not quiet:
            rprint(f"\n[bold]🚀 Syncing for language: [green]{lang}[/green]...[/bold]")

        # Check budget exhaustion (after first iteration when remaining_budget is set)
        if remaining_budget is not None and remaining_budget <= 0:
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
                "target_coverage": target_coverage,
                "time": time_param,
            }
            # Only pass values if explicitly set by user (not CLI defaults)
            # This allows .pddrc values to take precedence when user doesn't pass CLI flags
            if max_attempts is not None:
                command_options["max_attempts"] = max_attempts
            if budget is not None:
                command_options["budget"] = budget
            if strength != DEFAULT_STRENGTH:
                command_options["strength"] = strength
            if temperature != 0.0:  # 0.0 is the CLI default for temperature
                command_options["temperature"] = temperature

            # Use force=True for path discovery - actual file writes happen in sync_orchestration
            # which will handle confirmations via the TUI's confirm_callback
            resolved_config, _, _, resolved_language = construct_paths(
                input_file_paths={"prompt_file": str(prompt_file_path)},
                force=True,  # Always force during path discovery
                quiet=True,
                command="sync",
                command_options=command_options,
                context_override=context_override,
            )

            # Extract all parameters directly from the resolved configuration
            # Priority: CLI value > .pddrc value > hardcoded default
            final_strength = resolved_config.get("strength", strength)
            final_temp = resolved_config.get("temperature", temperature)

            # For target_coverage, max_attempts and budget: CLI > .pddrc > hardcoded default
            # If CLI value is provided (not None), use it. Otherwise, use .pddrc or default.
            # Issue #194: target_coverage was not being handled consistently with the others
            if target_coverage is not None:
                final_target_coverage = target_coverage
            else:
                final_target_coverage = resolved_config.get("target_coverage") or DEFAULT_TARGET_COVERAGE

            if max_attempts is not None:
                final_max_attempts = max_attempts
            else:
                final_max_attempts = resolved_config.get("max_attempts") or DEFAULT_MAX_ATTEMPTS

            if budget is not None:
                final_budget = budget
            else:
                final_budget = resolved_config.get("budget") or DEFAULT_BUDGET

            # Validate the resolved values
            # Note: max_attempts=0 is valid (skips LLM loop, goes straight to agentic mode)
            if final_budget <= 0:
                raise click.BadParameter("Budget must be a positive number.", param_hint="--budget")
            if final_max_attempts < 0:
                raise click.BadParameter("Max attempts must be a non-negative integer.", param_hint="--max-attempts")

            # Initialize remaining_budget from first resolved config if not set yet
            if remaining_budget is None:
                remaining_budget = final_budget

            # Update ctx.obj with resolved values so sub-commands inherit them
            ctx.obj["strength"] = final_strength
            ctx.obj["temperature"] = final_temp

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
