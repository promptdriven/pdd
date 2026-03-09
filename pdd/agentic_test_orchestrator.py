from __future__ import annotations

"""
Orchestrator for the 18-step agentic test generation workflow.
Runs each step as a separate agentic task, accumulates context between steps,
tracks overall progress and cost, and supports resuming from saved state.
"""

import json
import os
import re
import shutil
import subprocess
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Union

from .agentic_common import (
    run_agentic_task,
    load_workflow_state,
    save_workflow_state,
    clear_workflow_state,
    validate_cached_state,
    DEFAULT_MAX_RETRIES,
)
from .load_prompt_template import load_prompt_template


TEST_STEP_TIMEOUTS: Dict[Union[int, float], float] = {
    1: 240.0,    # Duplicate Check
    2: 400.0,    # Docs Check
    3: 400.0,    # Analyze & Clarify
    4: 340.0,    # Detect Frontend
    5: 600.0,    # Create Test Plan
    5.5: 400.0,  # Enhance Plan (schema + accessibility)
    6: 300.0,    # Assess Automated Test Coverage (web only)
    7: 400.0,    # Create Manual Testing Checklist (web only)
    8: 1800.0,   # Manual Testing Execution (web only, serial mode)
    9: 600.0,    # Create Regression Tests (web only)
    10: 400.0,   # Validate Regression Tests (web only)
    11: 60.0,    # Loop Until Checklist Complete (web only)
    12: 1000.0,  # Generate Tests (Most Complex)
    13: 600.0,   # Run Tests
    14: 800.0,   # Fix & Iterate
    15: 600.0,   # Validate Tests Against Plan
    16: 600.0,   # Run Newly Generated Tests
    17: 240.0,   # Submit PR
}


def _get_console():
    from rich.console import Console

    return Console()


console = _get_console()


def _get_git_root(cwd: Path) -> Optional[Path]:
    """Get repo root via git rev-parse."""
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=cwd,
            capture_output=True,
            text=True,
            check=True,
        )
        return Path(result.stdout.strip())
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None


def _worktree_exists(cwd: Path, worktree_path: Path) -> bool:
    """Check if path is in git worktree list --porcelain output."""
    git_root = _get_git_root(cwd)
    if not git_root:
        return False
    try:
        wt_list = subprocess.run(
            ["git", "worktree", "list", "--porcelain"],
            cwd=git_root,
            capture_output=True,
            text=True,
        ).stdout
        return str(worktree_path) in wt_list
    except Exception:
        return False


def _branch_exists(cwd: Path, branch: str) -> bool:
    """Check via git show-ref --verify refs/heads/{branch}."""
    git_root = _get_git_root(cwd)
    if not git_root:
        return False
    try:
        subprocess.run(
            ["git", "show-ref", "--verify", f"refs/heads/{branch}"],
            cwd=git_root,
            check=True,
            capture_output=True,
        )
        return True
    except subprocess.CalledProcessError:
        return False


def _remove_worktree(cwd: Path, worktree_path: Path) -> Tuple[bool, str]:
    """Remove via git worktree remove --force."""
    git_root = _get_git_root(cwd)
    if not git_root:
        return False, "Not a git repository"
    try:
        subprocess.run(
            ["git", "worktree", "remove", "--force", str(worktree_path)],
            cwd=git_root,
            capture_output=True,
            check=True,
        )
        return True, ""
    except subprocess.CalledProcessError as e:
        return False, str(e)


def _delete_branch(cwd: Path, branch: str) -> Tuple[bool, str]:
    """Delete via git branch -D."""
    git_root = _get_git_root(cwd)
    if not git_root:
        return False, "Not a git repository"
    try:
        subprocess.run(
            ["git", "branch", "-D", branch],
            cwd=git_root,
            capture_output=True,
            check=True,
        )
        return True, ""
    except subprocess.CalledProcessError as e:
        return False, str(e)


def _setup_worktree(
    cwd: Path,
    issue_number: int,
    quiet: bool,
    console: Any,
) -> Tuple[Optional[Path], Optional[str]]:
    """
    Create an isolated git worktree for the issue.
    Returns (worktree_path, error_message).
    """
    git_root = _get_git_root(cwd)
    if not git_root:
        return None, "Not a git repository"

    branch_name = f"test/issue-{issue_number}"
    worktree_rel_path = Path(".pdd") / "worktrees" / f"test-issue-{issue_number}"
    worktree_path = git_root / worktree_rel_path

    if worktree_path.exists():
        if _worktree_exists(cwd, worktree_path):
            success, _err = _remove_worktree(cwd, worktree_path)
            if not success:
                try:
                    shutil.rmtree(worktree_path)
                except Exception:
                    pass
        else:
            shutil.rmtree(worktree_path)

    if _branch_exists(cwd, branch_name):
        del_ok, del_err = _delete_branch(cwd, branch_name)
        if not del_ok:
            return None, f"Failed to delete existing branch {branch_name}: {del_err}"

    try:
        worktree_path.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["git", "worktree", "add", "-b", branch_name, str(worktree_path), "HEAD"],
            cwd=git_root,
            capture_output=True,
            check=True,
        )
        if not quiet:
            console.print(f"[blue]Working in worktree: {worktree_path}[/blue]")
        return worktree_path, None
    except subprocess.CalledProcessError as e:
        return None, f"Git worktree creation failed: {e}"


def _parse_changed_files(output: str) -> List[str]:
    """Extract file paths from FILES_CREATED or FILES_MODIFIED lines."""
    sentinel_values = {"none", "n/a", "na", "null", ""}
    files: List[str] = []
    created_match = re.search(r"FILES_CREATED:\s*(.*)", output)
    if created_match:
        files.extend([f.strip().strip("*") for f in created_match.group(1).split(",")
                       if f.strip() and f.strip().strip("*").lower() not in sentinel_values])

    modified_match = re.search(r"FILES_MODIFIED:\s*(.*)", output)
    if modified_match:
        files.extend([f.strip().strip("*") for f in modified_match.group(1).split(",")
                       if f.strip() and f.strip().strip("*").lower() not in sentinel_values])

    return list(dict.fromkeys(files))


def _extract_tag(output: str, tag: str) -> Optional[str]:
    match = re.search(rf"{re.escape(tag)}:\s*(.*)", output)
    if match:
        return match.group(1).strip()
    return None


def _extract_int_tag(output: str, tag: str) -> Optional[int]:
    value = _extract_tag(output, tag)
    if value is None:
        return None
    try:
        return int(re.findall(r"\d+", value)[0])
    except Exception:
        return None


def _get_state_dir(cwd: Path) -> Path:
    root = _get_git_root(cwd) or cwd
    return root / ".pdd" / "test-state"


def _format_prompt(template: str, context: Dict[str, Any]) -> str:
    formatted = template
    for key, value in context.items():
        formatted = formatted.replace(f"{{{key}}}", str(value))
    return formatted


def _check_hard_stop(step_num: Union[int, float], output: str) -> Optional[str]:
    """Check output for hard stop conditions.

    Clarification step (3) requires the explicit STOP_CONDITION: tag.
    A universal STOP_CONDITION: tag is recognized on any step.
    """
    if not output:
        return None
    stop_match = re.search(r'STOP_CONDITION:\s*(.+)', output, re.IGNORECASE)
    output_lower = output.lower()

    if step_num == 1 and "duplicate of #" in output_lower:
        return "Issue is a duplicate"
    if step_num == 3:
        if stop_match and "needs more info" in stop_match.group(1).lower():
            return "Needs more info from author"
        return None
    if step_num == 5 and "plan_blocked" in output_lower:
        return "Test plan not achievable"
    if step_num == 12:
        files = _parse_changed_files(output)
        if not files:
            return "No test file generated"
    # Universal fallback: any STOP_CONDITION tag on an unhandled step
    if stop_match:
        return stop_match.group(1).strip()
    return None


# Steps where a hard stop is a "clarification" request (step should re-run on resume)
_CLARIFICATION_STEPS = {3}


def _poll_parallel_results(results_path: Path, timeout: float) -> Optional[str]:
    start = time.time()
    while time.time() - start < timeout:
        if results_path.exists():
            try:
                return results_path.read_text()
            except Exception:
                return None
        time.sleep(5)
    return None


def run_agentic_test_orchestrator(
    issue_url: str,
    issue_content: str,
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    issue_author: str,
    issue_title: str,
    *,
    cwd: Path,
    verbose: bool = False,
    quiet: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True,
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Orchestrates the 18-step agentic test generation workflow.

    Returns:
        (success, final_message, total_cost, model_used, changed_files)
    """
    console = _get_console()

    if not quiet:
        console.print(f"Generating tests for issue #{issue_number}: \"{issue_title}\"")

    state_dir = _get_state_dir(cwd)
    state, loaded_gh_id = load_workflow_state(
        cwd, issue_number, "test", state_dir, repo_owner, repo_name, use_github_state
    )

    if state is not None:
        last_completed_step = state.get("last_completed_step", 0)
        step_outputs = state.get("step_outputs", {})
        total_cost = state.get("total_cost", 0.0)
        model_used = state.get("model_used", "unknown")
        github_comment_id = loaded_gh_id
        worktree_path_str = state.get("worktree_path")
        worktree_path = Path(worktree_path_str) if worktree_path_str else None
        last_completed_step = validate_cached_state(last_completed_step, step_outputs, quiet=quiet)
    else:
        state = {"step_outputs": {}, "last_completed_step": 0}
        last_completed_step = 0
        step_outputs = state["step_outputs"]
        total_cost = 0.0
        model_used = "unknown"
        github_comment_id = None
        worktree_path = None

    context: Dict[str, Any] = {
        "issue_url": issue_url,
        "issue_content": issue_content,
        "repo_owner": repo_owner,
        "repo_name": repo_name,
        "issue_number": issue_number,
        "issue_author": issue_author,
        "issue_title": issue_title,
    }

    for s_num, s_out in step_outputs.items():
        context[f"step{s_num}_output"] = s_out
        if s_num == "5.5":
            context["step5b_output"] = s_out
            context["enhanced_test_plan"] = s_out

    changed_files: List[str] = []
    if "step12_output" in context:
        changed_files.extend(_parse_changed_files(context["step12_output"]))
    if "step14_output" in context:
        for f in _parse_changed_files(context["step14_output"]):
            if f not in changed_files:
                changed_files.append(f)
    if "step9_output" in context:
        for f in _parse_changed_files(context["step9_output"]):
            if f not in changed_files:
                changed_files.append(f)
    if "step15_output" in context:
        for f in _parse_changed_files(context["step15_output"]):
            if f not in changed_files:
                changed_files.append(f)

    if changed_files:
        context["files_to_stage"] = ", ".join(changed_files)
        context["test_files"] = "\n".join(f"- {f}" for f in changed_files)

    step_order: List[Union[int, float]] = [
        1,
        2,
        3,
        4,
        5,
        5.5,
        6,
        7,
        8,
        9,
        10,
        11,
        12,
        13,
        14,
        15,
        16,
        17,
    ]

    try:
        start_index = step_order.index(last_completed_step) + 1
    except ValueError:
        start_index = 0

    if last_completed_step and not quiet:
        console.print(f"Resuming test generation for issue #{issue_number}")
        console.print(f"   Steps 1-{last_completed_step} already complete (cached)")
        console.print(f"   Starting from Step {step_order[start_index]}")

    playwright_available = shutil.which("playwright-cli") is not None

    current_work_dir = cwd

    def run_step(
        step_num: Union[int, float],
        template_name: str,
        description: str,
        use_playwright: bool = False,
        step_cwd: Optional[Path] = None,
    ) -> Tuple[bool, str, float, str]:
        if not quiet:
            console.print(f"[bold][Step {step_num}/18][/bold] {description}...")

        prompt_template = load_prompt_template(template_name)
        if not prompt_template:
            return False, f"Missing prompt template: {template_name}", 0.0, "unknown"

        formatted_prompt = _format_prompt(prompt_template, context)
        timeout = TEST_STEP_TIMEOUTS.get(step_num, 340.0) + timeout_adder
        step_success, step_output, step_cost, step_model = run_agentic_task(
            instruction=formatted_prompt,
            cwd=step_cwd or current_work_dir,
            verbose=verbose,
            quiet=quiet,
            timeout=timeout,
            label=f"step{step_num}",
            max_retries=DEFAULT_MAX_RETRIES,
            use_playwright=use_playwright,
        )
        return step_success, step_output, step_cost, step_model

    def save_state(step_num: Union[int, float], step_output: str, success: bool,
                   *, completed_step_override: Optional[Union[int, float]] = None) -> None:
        nonlocal github_comment_id
        context[f"step{step_num}_output"] = step_output
        if success:
            state["step_outputs"][str(step_num)] = step_output
            state["last_completed_step"] = completed_step_override if completed_step_override is not None else step_num
        else:
            state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"
        state["total_cost"] = total_cost
        state["model_used"] = model_used
        save_result = save_workflow_state(
            cwd,
            issue_number,
            "test",
            state,
            state_dir,
            repo_owner,
            repo_name,
            use_github_state,
            github_comment_id,
        )
        if save_result:
            github_comment_id = save_result
            state["github_comment_id"] = github_comment_id

    def finish_hard_stop(step_num: Union[int, float], reason: str) -> Tuple[bool, str, float, str, List[str]]:
        if not quiet:
            console.print(f"[yellow]Investigation stopped at Step {step_num}: {reason}[/yellow]")
        # Clarification steps save previous step as completed so they re-run on resume
        if step_num in _CLARIFICATION_STEPS:
            prev_idx = step_order.index(step_num) - 1
            override = step_order[prev_idx] if prev_idx >= 0 else 0
        else:
            override = None
        save_state(step_num, context.get(f"step{step_num}_output", ""), True,
                   completed_step_override=override)
        return False, f"Stopped at step {step_num}: {reason}", total_cost, model_used, changed_files

    # Steps 1-5.5
    steps_static = [
        (1, "agentic_test_step1_duplicate_LLM", "Search for duplicate test requests"),
        (2, "agentic_test_step2_docs_LLM", "Review codebase to understand what to test"),
        (3, "agentic_test_step3_clarify_LLM", "Determine if enough info"),
        (4, "agentic_test_step4_detect_frontend_LLM", "Identify test type"),
        (5, "agentic_test_step5_test_plan_LLM", "Create test plan"),
        (5.5, "agentic_test_step5b_enhance_plan_LLM", "Enhance plan"),
    ]

    for step_num, template, description in steps_static:
        if step_order.index(step_num) < start_index:
            continue

        step_success, step_output, step_cost, step_model = run_step(step_num, template, description)
        total_cost += step_cost
        model_used = step_model

        stop_reason = _check_hard_stop(step_num, step_output)
        context[f"step{step_num}_output"] = step_output
        if step_num == 4:
            test_type = _extract_tag(step_output, "TEST_TYPE")
            if test_type:
                context["frontend_type"] = test_type
            target_url = _extract_tag(step_output, "TARGET_URL")
            if target_url:
                context["target_url"] = target_url

        if step_num == 5:
            context["enhanced_test_plan"] = step_output

        if step_num == 5.5:
            context["enhanced_test_plan"] = step_output
            context["step5b_output"] = step_output

        save_state(step_num, step_output, step_success)

        if stop_reason:
            return finish_hard_stop(step_num, stop_reason)

        if not step_success and not quiet:
            console.print(f"[yellow]Warning: Step {step_num} reported failure but continuing...[/yellow]")

        if not quiet:
            brief = step_output.strip().split("\n")[-1] if step_output.strip() else "Done"
            console.print(f"   -> {brief[:80]}")
            if step_success:
                console.print(f"  → Step {step_num} complete.")

    # Manual testing steps 6-11
    test_type = context.get("frontend_type", "").lower()
    run_manual = test_type == "web" and playwright_available
    if test_type == "web" and not playwright_available and not quiet:
        console.print(
            "[yellow]playwright-cli not found in PATH. Skipping manual testing steps (6-11).[/yellow]"
        )

    coverage_gaps = None
    issues_found = None
    checklist_status = "PARTIAL"

    if run_manual:
        # Step 6
        step_num = 6
        if step_order.index(step_num) >= start_index:
            step_success, step_output, step_cost, step_model = run_step(
                step_num,
                "agentic_test_step6_coverage_LLM",
                "Assess automated test coverage",
            )
            total_cost += step_cost
            model_used = step_model
            context[f"step{step_num}_output"] = step_output
            save_state(step_num, step_output, step_success)
            coverage_gaps = _extract_int_tag(step_output, "COVERAGE_GAPS")
            if coverage_gaps == 0:
                run_manual = False
            if not step_success and not quiet:
                console.print(f"[yellow]Warning: Step {step_num} reported failure but continuing...[/yellow]")
            if not quiet:
                brief = step_output.strip().split("\n")[-1] if step_output.strip() else "Done"
                console.print(f"   -> {brief[:80]}")
                if step_success:
                    console.print(f"  → Step {step_num} complete.")

        # Step 7
        step_num = 7
        if run_manual and (coverage_gaps is None or coverage_gaps > 0):
            if step_order.index(step_num) >= start_index:
                step_success, step_output, step_cost, step_model = run_step(
                    step_num,
                    "agentic_test_step7_checklist_LLM",
                    "Create manual testing checklist",
                )
                total_cost += step_cost
                model_used = step_model
                context[f"step{step_num}_output"] = step_output
                save_state(step_num, step_output, step_success)
                if not step_success and not quiet:
                    console.print(f"[yellow]Warning: Step {step_num} reported failure but continuing...[/yellow]")
                if not quiet:
                    brief = step_output.strip().split("\n")[-1] if step_output.strip() else "Done"
                    console.print(f"   -> {brief[:80]}")
                    if step_success:
                        console.print(f"  → Step {step_num} complete.")

        # Steps 8-11 loop
        if run_manual and (coverage_gaps is None or coverage_gaps > 0):
            iteration = 0
            while iteration < 3:
                iteration += 1
                # Step 8
                step_num = 8
                if step_order.index(step_num) >= start_index:
                    context["iteration_number"] = iteration
                    context["checklist_chunk"] = context.get("step7_output", "")
                    cloud_run = os.getenv("PDD_CLOUD_RUN", "false").lower() == "true"
                    if cloud_run:
                        git_root = _get_git_root(cwd) or cwd
                        request_path = git_root / ".pdd" / "parallel-manual-test-request.json"
                        results_path = git_root / ".pdd" / "parallel-manual-test-results.json"
                        request_path.parent.mkdir(parents=True, exist_ok=True)
                        request_payload = {
                            "issue_number": issue_number,
                            "checklist": context.get("step7_output", ""),
                            "target_url": context.get("target_url", ""),
                        }
                        request_path.write_text(json.dumps(request_payload, indent=2))
                        step_output = _poll_parallel_results(results_path, TEST_STEP_TIMEOUTS[8] + timeout_adder) or ""
                        step_success = bool(step_output)
                        step_cost = 0.0
                        step_model = model_used
                    else:
                        step_success, step_output, step_cost, step_model = run_step(
                            step_num,
                            "agentic_test_step8_manual_test_LLM",
                            "Manual browser testing",
                            use_playwright=True,
                        )
                    total_cost += step_cost
                    model_used = step_model
                    context[f"step{step_num}_output"] = step_output
                    save_state(step_num, step_output, step_success)

                issues_found = _extract_int_tag(context.get("step8_output", ""), "ISSUES_FOUND")

                # Step 9
                step_num = 9
                if issues_found and issues_found > 0:
                    if step_order.index(step_num) >= start_index:
                        step_success, step_output, step_cost, step_model = run_step(
                            step_num,
                            "agentic_test_step9_regression_LLM",
                            "Create regression tests",
                        )
                        total_cost += step_cost
                        model_used = step_model
                        context[f"step{step_num}_output"] = step_output
                        new_files = _parse_changed_files(step_output)
                        for f in new_files:
                            if f not in changed_files:
                                changed_files.append(f)
                        context["files_to_stage"] = ", ".join(changed_files)
                        save_state(step_num, step_output, step_success)

                # Step 10
                step_num = 10
                if "step9_output" in context and _parse_changed_files(context["step9_output"]):
                    if step_order.index(step_num) >= start_index:
                        step_success, step_output, step_cost, step_model = run_step(
                            step_num,
                            "agentic_test_step10_validate_LLM",
                            "Validate regression tests",
                        )
                        total_cost += step_cost
                        model_used = step_model
                        context[f"step{step_num}_output"] = step_output
                        save_state(step_num, step_output, step_success)

                # Step 11
                step_num = 11
                if step_order.index(step_num) >= start_index:
                    context["iteration_number"] = iteration
                    step_success, step_output, step_cost, step_model = run_step(
                        step_num,
                        "agentic_test_step11_loop_LLM",
                        "Check checklist completion",
                    )
                    total_cost += step_cost
                    model_used = step_model
                    context[f"step{step_num}_output"] = step_output
                    save_state(step_num, step_output, step_success)
                    checklist_status = _extract_tag(step_output, "CHECKLIST_STATUS") or "PARTIAL"

                if checklist_status.upper() == "COMPLETE":
                    break

    # Worktree setup before Step 12
    if worktree_path and worktree_path.exists():
        current_work_dir = worktree_path
        context["worktree_path"] = str(worktree_path)
    else:
        try:
            current_branch = subprocess.run(
                ["git", "rev-parse", "--abbrev-ref", "HEAD"],
                cwd=cwd,
                capture_output=True,
                text=True,
                check=True,
            ).stdout.strip()
            if current_branch not in ["main", "master"] and not quiet:
                console.print(
                    f"[yellow]Note: Creating branch from HEAD ({current_branch}), not origin/main. PR will include commits from this branch. Run from main for independent changes.[/yellow]"
                )
        except (subprocess.CalledProcessError, FileNotFoundError):
            pass

        wt_path, err = _setup_worktree(cwd, issue_number, quiet, console)
        if not wt_path:
            return False, f"Failed to create worktree: {err}", total_cost, model_used, []
        worktree_path = wt_path
        current_work_dir = worktree_path
        state["worktree_path"] = str(worktree_path)
        context["worktree_path"] = str(worktree_path)

    # Steps 12-17
    steps_tail = [
        (12, "agentic_test_step6_generate_tests_LLM", "Generate tests"),
        (13, "agentic_test_step7_run_tests_LLM", "Execute generated tests"),
        (14, "agentic_test_step8_fix_iterate_LLM", "Fix failing tests"),
        (15, "agentic_test_step15_plan_validation_LLM", "Validate tests against plan"),
        (16, "agentic_test_step16_run_tests_LLM", "Run newly generated tests"),
        (17, "agentic_test_step9_submit_pr_LLM", "Create draft PR"),
    ]

    for step_num, template, description in steps_tail:
        if step_order.index(step_num) < start_index:
            continue

        if step_num == 16 and "step15_output" in context:
            if not _parse_changed_files(context["step15_output"]):
                if not quiet:
                    console.print(f"[bold][Step {step_num}/18][/bold] {description}... (skipped)")
                continue

        step_success, step_output, step_cost, step_model = run_step(
            step_num,
            template,
            description,
            step_cwd=current_work_dir,
        )
        total_cost += step_cost
        model_used = step_model
        context[f"step{step_num}_output"] = step_output

        if step_num in (12, 14, 15):
            new_files = _parse_changed_files(step_output)
            for f in new_files:
                if f not in changed_files:
                    changed_files.append(f)
            if changed_files:
                context["files_to_stage"] = ", ".join(changed_files)
                context["test_files"] = "\n".join(f"- {f}" for f in changed_files)

        if step_num == 13:
            context["test_results"] = step_output

        save_state(step_num, step_output, step_success)

        stop_reason = _check_hard_stop(step_num, step_output)
        if stop_reason:
            return finish_hard_stop(step_num, stop_reason)

        if not step_success and not quiet:
            console.print(f"[yellow]Warning: Step {step_num} reported failure but continuing...[/yellow]")

        if not quiet:
            brief = step_output.strip().split("\n")[-1] if step_output.strip() else "Done"
            console.print(f"   -> {brief[:80]}")
            if step_success:
                console.print(f"  → Step {step_num} complete.")

    pr_url = "Unknown"
    if "step17_output" in context:
        url_match = re.search(r"https://github.com/\S+/pull/\d+", context["step17_output"])
        if url_match:
            pr_url = url_match.group(0)

    if not quiet:
        console.print("\n[green]Test generation complete[/green]")
        console.print(f"   Total cost: ${total_cost:.4f}")
        console.print(f"   Files created: {', '.join(changed_files)}")
        if worktree_path:
            console.print(f"   Worktree: {worktree_path}")
        console.print(f"   PR created: {pr_url}")

    clear_workflow_state(cwd, issue_number, "test", state_dir, repo_owner, repo_name, use_github_state)

    final_msg = f"PR Created: {pr_url}" if pr_url != "Unknown" else "Workflow completed"
    return True, final_msg, total_cost, model_used, changed_files
