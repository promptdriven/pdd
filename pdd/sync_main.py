import fnmatch
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
    _get_relative_basename,
    _load_pddrc_config,
    _detect_context,
    _get_context_config,
    get_extension
)
from .sync_orchestration import sync_orchestration
from .template_expander import expand_template

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


def _python_first_sorted(lang_to_path: Dict[str, Path]) -> Dict[str, Path]:
    """Return lang-to-path dict with Python first (if present), then sorted alphabetically."""
    if 'python' in lang_to_path:
        result: Dict[str, Path] = {'python': lang_to_path['python']}
        for k in sorted(lang_to_path.keys()):
            if k != 'python':
                result[k] = lang_to_path[k]
        return result
    return dict(sorted(lang_to_path.items()))


def _get_extension_safe(language: str) -> str:
    """Get file extension with fallback for when PDD_PATH is not set."""
    try:
        return get_extension(language)
    except (ValueError, FileNotFoundError):
        # Fallback to built-in mapping
        builtin_ext_map = {
            'python': 'py', 'javascript': 'js', 'typescript': 'ts', 'java': 'java',
            'typescriptreact': 'tsx', 'javascriptreact': 'jsx',
            'cpp': 'cpp', 'c': 'c', 'go': 'go', 'ruby': 'rb', 'rust': 'rs',
        }
        return builtin_ext_map.get(language.lower(), '')


def _relative_basename_for_context(basename: str, context_config: Dict[str, Any]) -> str:
    """Return basename relative to a context's most specific path or prompt prefix."""
    matches = []

    for path_pattern in context_config.get('paths', []):
        pattern_base = path_pattern.rstrip('/**').rstrip('/*')
        if fnmatch.fnmatch(basename, path_pattern) or \
           basename.startswith(pattern_base + '/') or \
           basename == pattern_base:
            relative = _get_relative_basename(basename, path_pattern)
            matches.append((len(pattern_base), relative))

    defaults = context_config.get('defaults', {})
    prompts_dir = defaults.get('prompts_dir', '')
    if prompts_dir:
        normalized = prompts_dir.rstrip('/')
        prefix = normalized
        if normalized == 'prompts':
            prefix = ''
        elif normalized.startswith('prompts/'):
            prefix = normalized[len('prompts/'):]

        if prefix and (basename == prefix or basename.startswith(prefix + '/')):
            relative = basename[len(prefix) + 1 :] if basename != prefix else basename.split('/')[-1]
            matches.append((len(prefix), relative))

    if not matches:
        return basename

    matches.sort(key=lambda item: item[0], reverse=True)
    return matches[0][1]


def _normalize_prompts_root(prompts_dir: Path) -> Path:
    """
    Resolve prompts_dir to an absolute path relative to the project root.

    This function takes a potentially relative prompts_dir path (e.g., "prompts/backend")
    and resolves it to an absolute path using the .pddrc location as the project root.

    Note: This function previously stripped subdirectories after "prompts" which was
    incorrect for context-specific prompts_dir values. Fixed in Issue #253.
    """
    prompts_root = Path(prompts_dir)
    pddrc_path = _find_pddrc_file()
    if pddrc_path and not prompts_root.is_absolute():
        prompts_root = pddrc_path.parent / prompts_root

    return prompts_root


def _find_prompt_in_contexts(basename: str) -> Optional[Tuple[str, Path, str]]:
    """
    Search for a prompt file across all contexts using outputs.prompt.path templates.

    This enables finding prompts when the basename alone doesn't match context path patterns.
    For example, 'credit_helpers' can find 'prompts/backend/utils/credit_helpers_python.prompt'
    if the backend-utils context has outputs.prompt.path configured.

    Args:
        basename: The base name for the prompt file (e.g., 'credit_helpers')

    Returns:
        Tuple of (context_name, prompt_path, language) if found, None otherwise
    """
    pddrc_path = _find_pddrc_file()
    if not pddrc_path:
        return None

    try:
        config = _load_pddrc_config(pddrc_path)
    except Exception:
        return None

    # Resolve paths relative to .pddrc location, not CWD
    pddrc_parent = pddrc_path.parent

    contexts = config.get('contexts', {})

    # Common languages to try
    languages_to_try = ['python', 'typescript', 'javascript', 'typescriptreact', 'go', 'rust', 'java']

    for context_name, context_config in contexts.items():
        if context_name == 'default':
            continue

        defaults = context_config.get('defaults', {})
        outputs = defaults.get('outputs', {})
        prompt_config = outputs.get('prompt', {})
        prompt_template = prompt_config.get('path')

        if not prompt_template:
            continue

        context_basename = _relative_basename_for_context(basename, context_config)
        parts = context_basename.split('/') if context_basename else ['']
        name_part = parts[-1]
        category = '/'.join(parts[:-1]) if len(parts) > 1 else ''
        dir_prefix = f"{category}/" if category else ''

        # Try each language
        for lang in languages_to_try:
            ext = _get_extension_safe(lang)
            template_context = {
                'name': name_part,
                'category': category,
                'dir_prefix': dir_prefix,
                'ext': ext,
                'language': lang,
            }

            expanded_path = expand_template(prompt_template, template_context)
            # Resolve relative to .pddrc location, not CWD
            prompt_path = pddrc_parent / expanded_path

            if prompt_path.exists():
                return (context_name, prompt_path, lang)

    return None


def _extract_prompts_base_dir(prompt_template: str) -> Optional[str]:
    """
    Extract the base prompts directory from a template path.

    For example:
    - "prompts/frontend/{category}/{name}_{language}.prompt" -> "prompts/frontend"
    - "prompts/backend/utils/{name}_{language}.prompt" -> "prompts/backend/utils"
    - "{name}_{language}.prompt" -> None (no fixed prefix)
    """
    # Find the first placeholder
    first_placeholder = prompt_template.find('{')
    if first_placeholder == -1:
        # No placeholders, return parent directory
        return str(Path(prompt_template).parent)
    if first_placeholder == 0:
        # Template starts with placeholder, no fixed prefix
        return None

    # Get the part before the first placeholder
    prefix = prompt_template[:first_placeholder]
    # Remove trailing slash if present
    prefix = prefix.rstrip('/')
    # If prefix ends with a partial path segment, get the parent
    if prefix and not prefix.endswith('/'):
        # e.g., "prompts/frontend/" -> "prompts/frontend"
        return prefix
    return prefix if prefix else None


def _detect_languages_with_context(basename: str, prompts_dir: Path, context_name: Optional[str] = None) -> Dict[str, Path]:
    """
    Detects all available languages for a given basename, optionally using context config.

    If context_name is provided and has outputs.prompt.path configured, uses template-based
    discovery. Otherwise falls back to directory scanning.

    When context_name is provided but template expansion fails (e.g., missing category),
    falls back to recursive glob search in the context's prompts directory.

    Returns:
        Dict mapping normalized language names to their prompt file paths.
        E.g., {'typescriptreact': Path('prompts/frontend/app/sales/page_TypescriptReact.prompt')}
    """
    if context_name:
        pddrc_path = _find_pddrc_file()
        if pddrc_path:
            try:
                config = _load_pddrc_config(pddrc_path)
                # Resolve paths relative to .pddrc location, not CWD
                pddrc_parent = pddrc_path.parent
                contexts = config.get('contexts', {})
                context_config = contexts.get(context_name, {})
                defaults = context_config.get('defaults', {})
                outputs = defaults.get('outputs', {})
                prompt_config = outputs.get('prompt', {})
                prompt_template = prompt_config.get('path')

                if prompt_template:
                    context_basename = _relative_basename_for_context(basename, context_config)
                    parts = context_basename.split('/') if context_basename else ['']
                    name_part = parts[-1]
                    category = '/'.join(parts[:-1]) if len(parts) > 1 else ''
                    dir_prefix = f"{category}/" if category else ''

                    # Try all known languages
                    languages_to_try = ['python', 'typescript', 'javascript', 'typescriptreact', 'go', 'rust', 'java']
                    found_lang_to_path: Dict[str, Path] = {}

                    for lang in languages_to_try:
                        ext = _get_extension_safe(lang)
                        template_context = {
                            'name': name_part,
                            'category': category,
                            'dir_prefix': dir_prefix,
                            'ext': ext,
                            'language': lang,
                        }
                        expanded_path = expand_template(prompt_template, template_context)
                        # Resolve relative to .pddrc location, not CWD
                        full_path = pddrc_parent / expanded_path
                        if full_path.exists():
                            found_lang_to_path[lang] = full_path

                    if found_lang_to_path:
                        return _python_first_sorted(found_lang_to_path)

                    # Template expansion didn't find files - fallback to recursive glob
                    # This handles cases where basename alone doesn't provide category info
                    # e.g., pdd sync --basename page --context frontend
                    prompts_base_dir = _extract_prompts_base_dir(prompt_template)
                    if prompts_base_dir:
                        prompts_base_path = pddrc_parent / prompts_base_dir
                        if prompts_base_path.is_dir():
                            # Recursively search for {basename}_*.prompt files
                            pattern = f"**/{name_part}_*.prompt"
                            for prompt_file in prompts_base_path.glob(pattern):
                                stem = prompt_file.stem
                                if stem.startswith(f"{name_part}_"):
                                    potential_language = stem[len(name_part) + 1:]
                                    # Normalize language name (e.g., TypescriptReact -> typescriptreact)
                                    normalized_lang = potential_language.lower()
                                    if normalized_lang not in found_lang_to_path:
                                        try:
                                            if _is_known_language(potential_language):
                                                if potential_language.lower() != 'llm':
                                                    found_lang_to_path[normalized_lang] = prompt_file
                                        except ValueError:
                                            # PDD_PATH not set - use common languages
                                            common_languages = {"python", "javascript", "java", "cpp", "c", "go", "rust", "typescript", "typescriptreact", "javascriptreact"}
                                            if normalized_lang in common_languages:
                                                found_lang_to_path[normalized_lang] = prompt_file

                            if found_lang_to_path:
                                return _python_first_sorted(found_lang_to_path)
            except Exception:
                pass

    # Fallback to original directory scanning
    return _detect_languages(basename, prompts_dir)


def _detect_languages(basename: str, prompts_dir: Path) -> Dict[str, Path]:
    """
    Detects all available languages for a given basename by finding
    matching prompt files in the prompts directory.
    Excludes runtime languages (LLM) as they cannot form valid development units.

    Supports subdirectory basenames like 'core/cloud':
    - For basename 'core/cloud', searches in prompts/core/ for cloud_*.prompt files
    - The stem comparison only uses the filename part ('cloud'), not the path ('core/cloud')

    Returns:
        Dict mapping language names to their prompt file paths.
        E.g., {'python': Path('prompts/my_module_python.prompt')}
    """
    lang_to_path: Dict[str, Path] = {}
    if not prompts_dir.is_dir():
        return {}

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
            # Normalize language to lowercase for case-insensitive matching
            # (e.g., "Python" from "task_model_Python.prompt" -> "python")
            normalized_language = potential_language.lower()
            try:
                if _is_known_language(potential_language):
                    # Exclude runtime languages (LLM) as they cannot form valid development units
                    if normalized_language != 'llm':
                        lang_to_path[normalized_language] = prompt_file
            except ValueError:
                # PDD_PATH not set (likely during testing) - assume language is valid
                # if it matches common language patterns
                common_languages = {"python", "javascript", "java", "cpp", "c", "go", "rust", "typescript"}
                if normalized_language in common_languages:
                    lang_to_path[normalized_language] = prompt_file
                # Explicitly exclude 'llm' even in test scenarios

    return _python_first_sorted(lang_to_path)


def sync_main(
    ctx: click.Context,
    basename: str,
    max_attempts: Optional[int],
    budget: Optional[float],
    skip_verify: bool,
    skip_tests: bool,
    target_coverage: float,
    dry_run: bool,
    agentic_mode: bool = False,
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

    # 3. Try template-based prompt discovery first (uses outputs.prompt.path from .pddrc)
    template_result = _find_prompt_in_contexts(basename)
    discovered_context = None

    if template_result:
        discovered_context, discovered_prompt_path, first_lang = template_result
        prompts_dir_raw = discovered_prompt_path.parent
        pddrc_path = _find_pddrc_file()
        if pddrc_path and not prompts_dir_raw.is_absolute():
            prompts_dir = pddrc_path.parent / prompts_dir_raw
        else:
            prompts_dir = prompts_dir_raw
        # Use context override if not already set
        if not context_override:
            context_override = discovered_context
        if not quiet:
            rprint(f"[dim]Found prompt via template in context: {discovered_context}[/dim]")

    # 4. Fallback: Use construct_paths in 'discovery' mode to find the prompts directory.
    if not template_result:
        try:
            initial_config, _, _, _ = construct_paths(
                input_file_paths={},
                force=False,
                quiet=True,
                command="sync",
                command_options={"basename": basename},
                context_override=context_override,
            )
            prompts_dir_raw = initial_config.get("prompts_dir", "prompts")
            pddrc_path = _find_pddrc_file()
            if pddrc_path and not Path(prompts_dir_raw).is_absolute():
                prompts_dir = pddrc_path.parent / prompts_dir_raw
            else:
                prompts_dir = Path(prompts_dir_raw)
        except Exception as e:
            rprint(f"[bold red]Error initializing PDD paths:[/bold red] {e}")
            raise click.Abort()

    # 5. Detect all languages for the given basename
    # Use context_override (CLI --context value) instead of discovered_context
    # because discovered_context is None when template discovery fails
    # Returns Dict[str, Path] mapping language -> prompt file path
    lang_to_path = _detect_languages_with_context(basename, prompts_dir, context_name=context_override)
    if not lang_to_path:
        raise click.UsageError(
            f"No prompt files found for basename '{basename}' in directory '{prompts_dir}'.\n"
            f"Expected files with format: '{basename}_<language>.prompt'"
        )

    # 5. Handle --dry-run mode separately
    if dry_run:
        if not quiet:
            rprint(Panel(f"Displaying sync analysis for [bold cyan]{basename}[/bold cyan]", title="PDD Sync Dry Run", expand=False))

        for lang, prompt_file_path in lang_to_path.items():
            if not quiet:
                rprint(f"\n--- Log for language: [bold green]{lang}[/bold green] ---")

            # prompt_file_path is now the correct discovered path from lang_to_path
            
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
                prompts_dir=str(prompt_file_path.parent),  # Use discovered path's parent
                code_dir=str(code_dir),
                examples_dir=str(examples_dir),
                tests_dir=str(tests_dir),
                dry_run=True,
                verbose=verbose,
                quiet=quiet,
                context_override=context_override,
                agentic_mode=agentic_mode,
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
            f"Languages: [bold green]{', '.join(lang_to_path.keys())}[/bold green]\n"
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

    for lang, prompt_file_path in lang_to_path.items():
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
            # prompt_file_path is now the correct discovered path from lang_to_path
            
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
                prompts_dir=str(prompt_file_path.parent),  # Use discovered path's parent
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
                agentic_mode=agentic_mode,
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
