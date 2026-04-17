from __future__ import annotations

import subprocess
from pathlib import Path
from typing import List, Optional, Tuple

from rich.console import Console

from .agentic_common_worktree import get_git_root
from .agentic_split_orchestrator import run_agentic_split_orchestrator
from .get_language import get_language

console = Console()


def run_agentic_split(
    target_file: str,
    *,
    verbose: bool = False,
    quiet: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True,
    diagnose_only: bool = False,
    propose_only: bool = False,
    delete_dead: bool = False,
    force_split: bool = False,
    no_verify: bool = False,
    skip_regen_gate: bool = False,
    experimental_language: bool = False,
    intent: Optional[str] = None,
    no_phase_extraction: bool = False,
    strangler: bool = False,
) -> Tuple[bool, str, float, str, List[str]]:
    """CLI entry point for the agentic split workflow.

    Validates the target file, detects language, resolves git root,
    then invokes the orchestrator.

    Returns:
        Tuple of (success, message, total_cost, model_used, changed_files).
    """
    # Resolve and validate target file
    target_path = Path(target_file).resolve()
    if not target_path.exists() or not target_path.is_file():
        error_msg = f"Target file does not exist or is not a file: {target_file}"
        if not quiet:
            console.print(f"[bold red]Error:[/bold red] {error_msg}")
        return False, error_msg, 0.0, "", []

    # Detect language
    language = get_language(target_path.suffix)
    if not language:
        error_msg = f"Unsupported file extension '{target_path.suffix}' for: {target_file}"
        if not quiet:
            console.print(f"[bold red]Error:[/bold red] {error_msg}")
        return False, error_msg, 0.0, "", []

    # Resolve git root
    git_root = get_git_root(target_path.parent)
    if not git_root:
        error_msg = f"Not inside a git repository: {target_file}"
        if not quiet:
            console.print(f"[bold red]Error:[/bold red] {error_msg}")
        return False, error_msg, 0.0, "", []

    # Check for corresponding prompt file (warning, not blocking)
    # Try multiple naming / location conventions across projects
    stem = target_path.stem
    prompt_basenames = [
        f"{stem}_{language}.prompt",
        f"{stem}_{language.capitalize()}.prompt",  # e.g. "Python"
    ]
    prompt_dirs_by_path = [
        git_root / "prompts",
        git_root / "pdd" / "prompts",
    ]
    # Also search extensions/*/prompts/ (pdd_cloud convention)
    extensions_root = git_root / "extensions"
    if extensions_root.is_dir():
        for ext_dir in extensions_root.iterdir():
            if ext_dir.is_dir():
                prompts_dir = ext_dir / "prompts"
                if prompts_dir.is_dir():
                    prompt_dirs_by_path.append(prompts_dir)
                    # Recursive: extensions/X/prompts/**/
                    for sub in prompts_dir.rglob("*"):
                        if sub.is_dir():
                            prompt_dirs_by_path.append(sub)

    prompt_found = False
    for dir_ in prompt_dirs_by_path:
        for basename in prompt_basenames:
            if (dir_ / basename).exists():
                prompt_found = True
                break
        if prompt_found:
            break

    if not prompt_found and not quiet:
        console.print(
            f"[yellow]Warning: No prompt file found for {target_path.name}.[/yellow]"
        )

    # Check for test file (info only)
    test_candidates = [
        git_root / "tests" / f"test_{target_path.stem}{target_path.suffix}",
        target_path.parent / f"test_{target_path.stem}{target_path.suffix}",
    ]
    # Extensions convention: extensions/X/tests/test_<stem>.py
    if extensions_root.is_dir():
        for ext_dir in extensions_root.iterdir():
            if ext_dir.is_dir():
                tests_dir = ext_dir / "tests"
                if tests_dir.is_dir():
                    test_candidates.append(
                        tests_dir / f"test_{target_path.stem}{target_path.suffix}"
                    )
    test_found = any(p.exists() for p in test_candidates)
    if not test_found and not quiet:
        console.print(f"[yellow]Warning: No test file found for {target_path.name}[/yellow]")

    # Strangler mode (U7): produce N sequential runs, one per child,
    # each with its own worktree / PR boundary. Implemented as
    # --propose-only followed by N focused --force-split runs.
    if strangler:
        return _run_strangler_split(
            target_path=target_path,
            git_root=git_root,
            verbose=verbose,
            quiet=quiet,
            timeout_adder=timeout_adder,
            use_github_state=use_github_state,
            force_split=force_split,
            no_verify=no_verify,
            skip_regen_gate=skip_regen_gate,
            experimental_language=experimental_language,
            intent=intent,
            no_phase_extraction=no_phase_extraction,
        )

    # Invoke orchestrator
    try:
        return run_agentic_split_orchestrator(
            target_file=str(target_path),
            cwd=git_root,
            verbose=verbose,
            quiet=quiet,
            timeout_adder=timeout_adder,
            use_github_state=use_github_state,
            diagnose_only=diagnose_only,
            propose_only=propose_only,
            delete_dead=delete_dead,
            force_split=force_split,
            no_verify=no_verify,
            skip_regen_gate=skip_regen_gate,
            experimental_language=experimental_language,
            intent=intent,
            no_phase_extraction=no_phase_extraction,
        )
    except Exception as e:
        error_msg = f"Orchestrator failed: {e}"
        if not quiet:
            console.print(f"[bold red]Error:[/bold red] {error_msg}")
        return False, error_msg, 0.0, "", []


def _run_strangler_split(
    *,
    target_path: Path,
    git_root: Path,
    verbose: bool,
    quiet: bool,
    timeout_adder: float,
    use_github_state: bool,
    force_split: bool,
    no_verify: bool,
    skip_regen_gate: bool,
    experimental_language: bool,
    intent: Optional[str],
    no_phase_extraction: bool,
) -> Tuple[bool, str, float, str, List[str]]:
    """Sequential strangler-fig split: one child per PR.

    Runs `--propose-only` once to get the plan, then invokes the
    orchestrator N times, each time extracting exactly one child
    from the still-growing parent. Each run produces its own worktree
    / branch, keeping a re-export shim on the parent for reversibility.

    Python does the sequencing; the orchestrator still does the
    per-pass work agentically. No new judgment in Python.
    """
    if not quiet:
        console.print(
            "[cyan]Strangler mode: proposing plan, then extracting "
            "children one at a time...[/cyan]"
        )

    # Pass 1 — propose only. The orchestrator persists the plan; we'll
    # read it from state to enumerate children for subsequent passes.
    propose_success, propose_msg, propose_cost, model, _ = run_agentic_split_orchestrator(
        target_file=str(target_path),
        cwd=git_root,
        verbose=verbose,
        quiet=quiet,
        timeout_adder=timeout_adder,
        use_github_state=use_github_state,
        diagnose_only=False,
        propose_only=True,
        delete_dead=False,
        force_split=force_split,
        no_verify=no_verify,
        skip_regen_gate=skip_regen_gate,
        experimental_language=experimental_language,
        intent=intent,
        no_phase_extraction=no_phase_extraction,
    )
    if not propose_success and "Propose only complete" not in propose_msg:
        return False, propose_msg, propose_cost, model, []

    # Read the proposed plan from state to enumerate children.
    from .agentic_common import load_workflow_state
    from .agentic_split_orchestrator import _stable_split_id
    state_dir = git_root / ".pdd" / "split-state"
    # Compute split_id the same way the orchestrator does: use the
    # repo-relative path so it matches what was saved by the propose-only run.
    _target_resolved = target_path.resolve()
    try:
        _id_path = str(_target_resolved.relative_to(git_root))
    except ValueError:
        _id_path = str(target_path)
    split_id = _stable_split_id(_id_path)
    state, _ = load_workflow_state(
        git_root, split_id, "split", state_dir, "", "", use_github_state
    )
    if state is None:
        return (
            False,
            "Strangler: could not load propose-only state",
            propose_cost, model, [],
        )
    step4_raw = state.get("step_outputs", {}).get("4", "")
    if not step4_raw:
        return False, "Strangler: no plan from propose", propose_cost, model, []

    from .agentic_split_orchestrator import (
        OptionsConsidered, SplitOption, _parse_step_output, _dict_to_dataclass,
    )
    parsed = _parse_step_output(step4_raw, OptionsConsidered)
    if not isinstance(parsed, OptionsConsidered) or not parsed.options:
        return False, "Strangler: could not parse plan", propose_cost, model, []
    rebuilt = []
    for o in parsed.options:
        if isinstance(o, SplitOption):
            rebuilt.append(o)
        elif isinstance(o, dict):
            rebuilt.append(_dict_to_dataclass(SplitOption, o))
    if not rebuilt:
        return False, "Strangler: plan had no options", propose_cost, model, []
    best_plan = max(rebuilt, key=lambda o: o.numeric_score)
    total_children = len(best_plan.plan.children)
    if not quiet:
        console.print(
            f"[cyan]Strangler: {total_children} children planned, "
            "will extract one per pass.[/cyan]"
        )

    # Pass 2...N — extract each child, one at a time. For each child,
    # clear prior state and re-run the full pipeline with force_split
    # and a fresh worktree. The agentic code does the per-pass extraction;
    # this wrapper just sequences.
    total_cost = propose_cost
    all_changed: List[str] = []
    from .agentic_common import clear_workflow_state
    clear_workflow_state(git_root, split_id, "split", state_dir, "", "", use_github_state)

    for idx in range(total_children):
        if not quiet:
            console.print(
                f"\n[bold cyan]=== Strangler pass {idx+1}/{total_children} "
                f"===[/bold cyan]"
            )
        # Each pass is a full run. The agent will see the updated state
        # of the target (already partially reduced) and propose
        # extracting the next child.
        ok, msg, cost, model, changed = run_agentic_split_orchestrator(
            target_file=str(target_path),
            cwd=git_root,
            verbose=verbose,
            quiet=quiet,
            timeout_adder=timeout_adder,
            use_github_state=use_github_state,
            diagnose_only=False,
            propose_only=False,
            delete_dead=False,
            force_split=True,  # we know it needs splitting
            no_verify=no_verify,
            skip_regen_gate=skip_regen_gate,
            experimental_language=experimental_language,
            intent=intent,
            no_phase_extraction=no_phase_extraction,
        )
        total_cost += cost
        all_changed.extend(changed)
        if not ok:
            return (
                False,
                f"Strangler pass {idx+1} failed: {msg}",
                total_cost, model, all_changed,
            )
        # Clear state between passes so the next run starts fresh.
        clear_workflow_state(
            git_root, split_id, "split", state_dir, "", "", use_github_state
        )

    return (
        True,
        f"Strangler complete: {total_children} children extracted",
        total_cost, model, all_changed,
    )
