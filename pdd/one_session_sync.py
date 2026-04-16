"""
One-session sync: run example, crash-fix, verify, test, and fix steps
in a single agentic session instead of separate sessions per step.
"""

import logging
import threading
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

from rich.console import Console
from rich import print as rprint

from .agentic_common import run_agentic_task
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess

logger = logging.getLogger(__name__)
console = Console()


# Step display names for progress reporting
_STEP_DISPLAY = {
    "example_generate": "Example file created",
    "crash_fix": "Example runs without errors",
    "verify": "Behavior verified against spec",
    "test_generate": "Test file created",
    "test_pass": "All tests passing",
    "done": "All steps complete",
}

# Map one-session step markers to PDD_PHASE names that AsyncSyncRunner parses
_STEP_TO_PHASE = {
    "example_generate": "example",
    "crash_fix": "crash",
    "verify": "verify",
    "test_generate": "test",
    "done": "synced",
}


def _read_new_progress(progress_file: Path, skip_count: int) -> List[str]:
    """Read new STEP_COMPLETE lines from the progress file, skipping already-reported ones."""
    if not progress_file.exists():
        return []
    try:
        content = progress_file.read_text(encoding="utf-8")
    except OSError:
        return []
    lines = [
        line.split("STEP_COMPLETE:", 1)[1].strip()
        for line in content.splitlines()
        if line.startswith("STEP_COMPLETE:")
    ]
    return lines[skip_count:]


def _format_step_display(step_name: str) -> str:
    """Convert a step marker name to a user-friendly display string."""
    if step_name in _STEP_DISPLAY:
        return _STEP_DISPLAY[step_name]
    if step_name.startswith("crash_fix_attempt:"):
        attempt = step_name.split(":")[1]
        return f"Crash fix attempt {attempt}"
    if step_name.startswith("test_fix_attempt:"):
        attempt = step_name.split(":")[1]
        return f"Test fix attempt {attempt}"
    return step_name


def _compute_import_base(code_path: Path, project_root: Path) -> str:
    """Compute the Python import base from the code file path relative to project root.

    For example, if code_path is /proj/pdd/crm_models.py and project_root is /proj,
    returns 'pdd.crm_models'.
    """
    try:
        relative = code_path.resolve().relative_to(project_root.resolve())
    except ValueError:
        # code_path is not relative to project_root — use stem only
        return code_path.stem

    # Convert path parts to dotted module path, stripping .py extension
    parts = list(relative.parts)
    if parts and parts[-1].endswith(".py"):
        parts[-1] = parts[-1][:-3]
    return ".".join(parts)


def build_one_session_prompt(
    basename: str,
    language: str,
    pdd_files: Dict[str, Path],
    project_root: Path,
    *,
    target_coverage: float = 90.0,
) -> str:
    """
    Build the mega-prompt for one-session sync.

    Reads the module prompt, preprocesses includes, reads generated code,
    and assembles the full instruction from the LLM template.

    Args:
        basename: Module basename (e.g., 'crm_models').
        language: Target language (e.g., 'python').
        pdd_files: Dict from get_pdd_file_paths with keys 'prompt', 'code', 'example', 'test'.
        project_root: Project root directory.
        target_coverage: Target test coverage percentage.

    Returns:
        Fully assembled prompt string.
    """
    # Read and preprocess the module prompt (resolve <include> tags)
    prompt_path = pdd_files["prompt"]
    prompt_content = prompt_path.read_text(encoding="utf-8")
    resolved_prompt_content = preprocess(
        prompt_content, recursive=True, double_curly_brackets=False
    )

    # Read current generated code (must exist)
    code_path = pdd_files["code"]
    code_content = code_path.read_text(encoding="utf-8")

    # Load the mega-prompt template
    template = load_prompt_template("one_session_agent_LLM")
    if template is None:
        raise FileNotFoundError(
            "Could not find prompt template 'one_session_agent_LLM'. "
            "Ensure prompts/one_session_agent_LLM.prompt exists."
        )

    # Progress file path for step-level reporting
    # Sanitize basename to avoid nested paths for subdirectory modules (e.g., core/cloud)
    safe_basename = basename.replace("/", "_")
    progress_file = project_root / f".pdd_one_session_progress_{safe_basename}"

    # Compute import base for example generation guidance
    import_base = _compute_import_base(code_path, project_root)

    # Step numbering is fixed: example=1, crash=2, verify=3, test=4
    verify_step_num = 3
    test_step_num = 4

    # Escape braces in dynamic content to prevent .format() from interpreting
    # code like {uid} or {name} as template placeholders
    def _escape_braces(s: str) -> str:
        return s.replace("{", "{{").replace("}", "}}")

    safe_prompt_content = _escape_braces(resolved_prompt_content)
    safe_code_content = _escape_braces(code_content)

    # Substitute all placeholders
    prompt = template.format(
        basename=basename,
        language=language,
        prompt_path=pdd_files["prompt"],
        code_path=pdd_files["code"],
        example_path=pdd_files["example"],
        test_path=pdd_files["test"],
        project_root=project_root,
        resolved_prompt_content=safe_prompt_content,
        code_content=safe_code_content,
        target_coverage=target_coverage,
        progress_file=progress_file,
        import_base=import_base,
        verify_step_num=verify_step_num,
        test_step_num=test_step_num,
    )

    return prompt


def run_one_session_sync(
    basename: str,
    language: str,
    pdd_files: Dict[str, Path],
    project_root: Path,
    *,
    target_coverage: float = 90.0,
    budget: Optional[float] = None,
    verbose: bool = False,
    quiet: bool = False,
    timeout: Optional[float] = None,
) -> Dict[str, Any]:
    """
    Run example/crash/verify/test/fix in a single agentic session.

    Args:
        basename: Module basename.
        language: Target language.
        pdd_files: Dict from get_pdd_file_paths.
        project_root: Project root directory.
        target_coverage: Target test coverage percentage.
        budget: Max cost budget (informational, not enforced here).
        verbose: Enable verbose output.
        quiet: Suppress output.
        timeout: Session timeout in seconds (default: 1200).

    Returns:
        Dict with keys: success, total_cost, model_name, operations_completed, errors.
    """
    # Validate code file exists (generated by prior pdd generate step)
    code_path = pdd_files["code"]
    if not code_path.exists():
        raise FileNotFoundError(
            f"Code file not found: {code_path}\n"
            f"Run `pdd generate {basename}` first."
        )

    # Build the mega-prompt
    prompt = build_one_session_prompt(
        basename=basename,
        language=language,
        pdd_files=pdd_files,
        project_root=project_root,
        target_coverage=target_coverage,
    )

    logger.info("Starting one-session sync for %s (%s)", basename, language)

    # Progress file for step-level reporting from the agent
    # Sanitize basename to avoid nested paths for subdirectory modules (e.g., core/cloud)
    safe_basename = basename.replace("/", "_")
    progress_file = project_root / f".pdd_one_session_progress_{safe_basename}"
    # Clean up any stale progress file from a previous run
    if progress_file.exists():
        progress_file.unlink()

    # Show planned steps before starting
    if not quiet:
        rprint(
            f"[bold cyan]One-session sync:[/bold cyan] {basename} ({language})\n"
            f"[dim]Steps: example -> crash-fix -> verify -> test & fix[/dim]"
        )

    # Run the agentic task with a progress heartbeat
    session_timeout = timeout if timeout is not None else 1200.0
    start_time = time.time()

    # Heartbeat thread polls progress file and prints step-level updates
    stop_heartbeat = threading.Event()
    last_reported_line_count = 0

    def _heartbeat() -> None:
        """Poll progress file every 10s and print new step completions."""
        nonlocal last_reported_line_count
        while not stop_heartbeat.wait(10.0):
            elapsed = time.time() - start_time
            mins, secs = divmod(int(elapsed), 60)
            if quiet:
                continue

            # Check for new progress markers
            new_steps = _read_new_progress(progress_file, last_reported_line_count)
            if new_steps:
                for step_name in new_steps:
                    display = _format_step_display(step_name)
                    console.print(
                        f"  [green]{display}[/green] [dim]({mins}m{secs:02d}s)[/dim]"
                    )
                    phase = _STEP_TO_PHASE.get(step_name)
                    if phase:
                        print(f"PDD_PHASE: {phase}", flush=True)
                last_reported_line_count += len(new_steps)
            else:
                # No new steps — just show elapsed time every 30s
                if int(elapsed) > 0 and int(elapsed) % 30 == 0:
                    console.print(
                        f"[dim]  {basename}: running ({mins}m{secs:02d}s)...[/dim]"
                    )

    heartbeat_thread = threading.Thread(target=_heartbeat, daemon=True)
    heartbeat_thread.start()

    try:
        success, output_text, cost, provider = run_agentic_task(
            instruction=prompt,
            cwd=project_root,
            verbose=verbose,
            quiet=quiet,
            label=f"one_session_sync:{basename}",
            timeout=session_timeout,
            max_retries=3,  # One-session runs are long; retry on transient empty-result
        )
    finally:
        stop_heartbeat.set()
        heartbeat_thread.join(timeout=2.0)

        # Print any remaining progress that arrived after last heartbeat
        if not quiet:
            remaining = _read_new_progress(progress_file, last_reported_line_count)
            elapsed = time.time() - start_time
            mins, secs = divmod(int(elapsed), 60)
            for step_name in remaining:
                display = _format_step_display(step_name)
                console.print(
                    f"  [green]{display}[/green] [dim]({mins}m{secs:02d}s)[/dim]"
                )
                phase = _STEP_TO_PHASE.get(step_name)
                if phase:
                    print(f"PDD_PHASE: {phase}", flush=True)

        # Clean up progress file
        if progress_file.exists():
            try:
                progress_file.unlink()
            except OSError:
                pass

    elapsed = time.time() - start_time
    mins, secs = divmod(int(elapsed), 60)

    # Emit final phase marker for runner to parse
    if success:
        print("PDD_PHASE: synced", flush=True)
    else:
        print("PDD_PHASE: conflict", flush=True)

    # Show completion summary
    if not quiet:
        status = "[green]Success[/green]" if success else "[red]Failed[/red]"
        rprint(
            f"[bold]One-session sync {status}[/bold] "
            f"({mins}m{secs:02d}s, ${cost:.4f})"
        )

    # Determine which operations were completed
    operations: List[str] = []
    if success:
        operations = ["example", "crash_fix", "verify", "test"]

    errors: List[str] = []
    if not success:
        errors.append(output_text[:500] if output_text else "One-session sync failed")

    return {
        "success": success,
        "total_cost": cost,
        "model_name": provider,
        "operations_completed": operations,
        "errors": errors,
        # sync_main's summary table reads result.get("error") (singular).
        # Without this key, one-session errors display as "No details."
        "error": "; ".join(errors) if errors else "",
    }
