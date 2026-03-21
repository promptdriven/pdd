from __future__ import annotations

import re
import shlex
import shutil
import subprocess
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Union

from rich.console import Console
from rich.markup import escape

from .agentic_common import (
    run_agentic_task,
    load_workflow_state,
    save_workflow_state,
    clear_workflow_state,
    set_agentic_progress,
    clear_agentic_progress,
    DEFAULT_MAX_RETRIES,
)
from .get_test_command import get_test_command_for_file
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .pytest_output import run_pytest_and_capture_output

# Initialize console for rich output
console = Console()

# Per-Step Timeouts (Workflow specific)
BUG_STEP_TIMEOUTS: Dict[Union[int, float], float] = {
    1: 240.0,    # Duplicate Check
    2: 400.0,    # Docs Check
    3: 400.0,    # Triage
    4: 600.0,    # Reproduce (Complex)
    5: 600.0,    # Root Cause (Complex)
    5.5: 600.0,  # Prompt Classification (may auto-fix prompts)
    6: 340.0,    # Test Plan
    7: 1000.0,   # Generate Unit Test (Most Complex)
    8: 600.0,    # Verify Unit Test
    9: 2000.0,   # E2E Test (Complex - needs to discover env & run tests)
    10: 240.0,   # Create PR
}


def _get_git_root(cwd: Path) -> Optional[Path]:
    """Get repo root via git rev-parse."""
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=cwd,
            capture_output=True,
            text=True,
            check=True
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
            text=True
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
            capture_output=True
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
            check=True
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
            check=True
        )
        return True, ""
    except subprocess.CalledProcessError as e:
        return False, str(e)


def _setup_worktree(cwd: Path, issue_number: int, quiet: bool, resume_existing: bool = False) -> Tuple[Optional[Path], Optional[str]]:
    """
    Create an isolated git worktree for the issue.
    Returns (worktree_path, error_message).
    """
    git_root = _get_git_root(cwd)
    if not git_root:
        return None, "Not a git repository"

    branch_name = f"fix/issue-{issue_number}"
    worktree_rel_path = Path(".pdd") / "worktrees" / f"fix-issue-{issue_number}"
    worktree_path = git_root / worktree_rel_path

    # Clean up existing directory if it exists
    if worktree_path.exists():
        if _worktree_exists(cwd, worktree_path):
            success, err = _remove_worktree(cwd, worktree_path)
            if not success:
                # Fallback to rmtree if git command fails but dir exists
                try:
                    shutil.rmtree(worktree_path)
                except Exception:
                    pass
        else:
            # Just a directory
            shutil.rmtree(worktree_path)

    # Clean up branch if it exists
    reset_after_attach = False
    branch_exists = _branch_exists(cwd, branch_name)
    if branch_exists and not resume_existing:
        success, _err = _delete_branch(cwd, branch_name)
        if success:
            branch_exists = False
        else:
            # Branch couldn't be deleted — will reuse with --force,
            # then reset to HEAD so old commits don't pollute the PR.
            reset_after_attach = True

    # Create worktree
    try:
        worktree_path.parent.mkdir(parents=True, exist_ok=True)
        if branch_exists:
            # Branch exists (resume or undeletable) — use --force
            cmd = ["git", "worktree", "add", "--force", str(worktree_path), branch_name]
        else:
            cmd = ["git", "worktree", "add", "-b", branch_name, str(worktree_path), "HEAD"]
        subprocess.run(
            cmd,
            cwd=git_root,
            capture_output=True,
            check=True
        )
        # Reset branch to main HEAD if we reused an undeletable branch
        if reset_after_attach:
            main_head = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=git_root,
                capture_output=True, text=True, check=True,
            ).stdout.strip()
            subprocess.run(
                ["git", "reset", "--hard", main_head],
                cwd=worktree_path,
                capture_output=True,
                check=True,
            )
        if not quiet:
            console.print(f"[blue]Working in worktree: {worktree_path}[/blue]")
        return worktree_path, None
    except subprocess.CalledProcessError as e:
        return None, f"Git worktree creation failed: {e}"


def _get_modified_and_untracked(cwd: Path) -> List[str]:
    """Returns modified tracked files plus untracked files."""
    files = []
    # Modified tracked
    result = subprocess.run(["git", "diff", "--name-only", "HEAD"], cwd=cwd, capture_output=True, text=True)
    files.extend([f for f in result.stdout.strip().split('\n') if f])
    # Untracked
    result = subprocess.run(["git", "ls-files", "--others", "--exclude-standard"], cwd=cwd, capture_output=True, text=True)
    files.extend([f for f in result.stdout.strip().split('\n') if f])
    return files


def _verify_e2e_tests(e2e_files: List[str], cwd: Path) -> Tuple[bool, str]:
    """Run E2E test files independently to verify they execute correctly.

    Dispatches the correct runner based on file extension:
    - .py → pytest via run_pytest_and_capture_output
    - Non-Python → resolved via get_test_command_for_file (e.g. npx jest, npx playwright)

    Returns (all_passed, output). For E2E tests in the bug workflow, "passed"
    means the tests executed without setup errors. Tests are expected to FAIL
    (detecting the bug) — a clean failure is still a successful verification.
    """
    all_outputs: List[str] = []
    any_setup_error = False

    for test_file in e2e_files:
        abs_path = str(cwd / test_file)

        if test_file.endswith(".py"):
            result = run_pytest_and_capture_output(abs_path)
            if not result or not result.get("test_results"):
                any_setup_error = True
                all_outputs.append(f"{test_file}: no results (setup error)")
                continue

            tr = result["test_results"][0]
            failures = tr.get("failures", 0) + tr.get("errors", 0)
            passed = tr.get("passed", 0)
            stdout = tr.get("standard_output", "")

            if failures > 0:
                # Failures are expected — E2E tests should fail on buggy code
                all_outputs.append(f"{test_file}: {failures} failure(s) (bug detected)\n{stdout}")
            else:
                all_outputs.append(f"{test_file}: {passed} passed")
        else:
            test_cmd = get_test_command_for_file(abs_path)
            if not test_cmd:
                any_setup_error = True
                all_outputs.append(f"{test_file}: FAILED (no test runner available)")
                continue

            try:
                proc = subprocess.run(
                    shlex.split(test_cmd),
                    shell=False,
                    cwd=str(cwd),
                    capture_output=True,
                    text=True,
                    timeout=120,
                )
                if proc.returncode != 0:
                    # Non-zero exit is expected — E2E tests should fail on buggy code
                    output = proc.stdout + proc.stderr
                    all_outputs.append(
                        f"{test_file}: test failed (exit code {proc.returncode}, bug detected)\n{output}"
                    )
                else:
                    all_outputs.append(f"{test_file}: passed")
            except subprocess.TimeoutExpired:
                any_setup_error = True
                all_outputs.append(f"{test_file}: FAILED (timeout)")
            except Exception as e:
                any_setup_error = True
                all_outputs.append(f"{test_file}: FAILED ({e})")

    return not any_setup_error, "\n".join(all_outputs)


def _parse_changed_files(output: str, marker: str) -> List[str]:
    """Extract file paths from specific marker lines."""
    files = []
    match = re.search(rf"{marker}:\s*(.*)", output)
    if match:
        files.extend([f.strip() for f in match.group(1).split(",") if f.strip()])
    return files


def _check_hard_stop(step_num: Union[int, float], output: str, files_extracted: bool) -> Optional[str]:
    """Check output for hard stop conditions."""
    if step_num == 1 and "Duplicate of #" in output:
        return "Issue is a duplicate"
    if step_num == 2:
        if "Feature Request (Not a Bug)" in output:
            return "Feature Request (Not a Bug)"
        if "User Error (Not a Bug)" in output:
            return "User Error (Not a Bug)"
    if step_num == 3 and "Needs More Info" in output:
        return "Needs more info from author"
    if step_num == 7 and "PROMPT_REVIEW:" in output:
        return "Prompt defect needs human review"
    if step_num == 9 and not files_extracted:
        return "No test file generated"
    if step_num == 10 and "FAIL: Test does not work as expected" in output:
        return "Test doesn't fail correctly"
    if step_num == 11 and "E2E_FAIL: Test does not catch bug correctly" in output:
        return "E2E test doesn't catch bug"
    return None


def _get_state_dir(cwd: Path) -> Path:
    """Get the state directory relative to git root."""
    root = _get_git_root(cwd) or cwd
    return root / ".pdd" / "bug-state"


def detect_structural_test_patterns(file_path: str) -> List[str]:
    """Scan a test file for structural/non-behavioral test patterns.

    Returns a list of human-readable violation descriptions. Empty list means
    the file is clean.

    Detected patterns:
    - inspect.getsource / inspect.signature used to read source or signatures
    - assert "keyword" in source (source string matching)
    - hasattr(module, ...) used as the primary assertion
    - Path.read_text() / open().read() followed by string-in-content assertions
    """
    path = Path(file_path)
    if not path.exists():
        return []

    try:
        content = path.read_text()
    except (OSError, UnicodeDecodeError):
        return []

    if not content.strip():
        return []

    violations: List[str] = []

    lines = content.splitlines()

    # Track whether inspect.getsource or inspect.signature is used
    has_getsource = False
    has_signature = False

    for i, line in enumerate(lines, 1):
        stripped = line.strip()

        # Detect inspect.getsource usage
        if "inspect.getsource" in stripped:
            # Exclude comments
            if not stripped.startswith("#"):
                has_getsource = True
                violations.append(
                    f"Line {i}: inspect.getsource — reads source code as string "
                    f"for structural assertion instead of testing behavior"
                )

        # Detect inspect.signature usage
        if "inspect.signature" in stripped:
            if not stripped.startswith("#"):
                has_signature = True
                violations.append(
                    f"Line {i}: inspect.signature — inspects function signature "
                    f"instead of calling the function and asserting on behavior"
                )

        # Detect hasattr as the primary assertion
        if re.match(r"\s*assert\s+hasattr\s*\(", line):
            violations.append(
                f"Line {i}: assert hasattr() — checks attribute existence "
                f"instead of calling and asserting on behavior"
            )

    # Detect source-string-matching patterns:
    # Look for read_text()/read()/getsource() result being used in `assert ... in ...`
    # Pattern: variable = <source read>, then assert "x" in variable
    #
    # Only flag when the file being read is Python source (.py). Reading config
    # files (Dockerfile, YAML, JSON, etc.) and asserting on their content is a
    # legitimate test pattern — it tests build/config correctness, not code structure.
    _NON_SOURCE_EXTENSIONS = {
        ".yaml", ".yml", ".json", ".toml", ".cfg", ".ini", ".env", ".txt",
        ".md", ".rst", ".html", ".css", ".js", ".ts", ".sh", ".bash",
    }
    _NON_SOURCE_FILENAMES = {"dockerfile", "makefile", "gemfile", "rakefile"}

    source_read_pattern = re.compile(
        r'(\w+)\s*=\s*('
        r'inspect\.getsource\s*\('
        r'|(.+)\.read_text\s*\('
        r'|(.+)\.read\s*\('
        r')',
    )

    # Track `with open("filename") as var:` so we can resolve var.read()
    open_as_pattern = re.compile(
        r'with\s+open\s*\(\s*["\']([^"\']+)["\']\s*.*\)\s+as\s+(\w+)',
    )
    file_handle_filenames: dict = {}  # var_name -> filename
    for line in lines:
        om = open_as_pattern.search(line)
        if om and not line.strip().startswith("#"):
            file_handle_filenames[om.group(2)] = om.group(1)

    def _is_non_source_file(filename: str) -> bool:
        """Check if a filename refers to a non-source (config/build) file."""
        basename = Path(filename).name.lower()
        ext = Path(filename).suffix.lower()
        if ext in _NON_SOURCE_EXTENSIONS:
            return True
        if basename in _NON_SOURCE_FILENAMES:
            return True
        if ext and ext != ".py":
            return True
        return False

    source_var_names: set = set()
    for line in lines:
        m = source_read_pattern.search(line)
        if m and not line.strip().startswith("#"):
            # For getsource, always track (group 3 and 4 will be None)
            if "inspect.getsource" in line:
                source_var_names.add(m.group(1))
                continue

            # For read_text/read, check what file is being read
            full_expr = m.group(3) or m.group(4) or ""

            # Check if this is a file handle from `with open("file") as f:`
            handle_name = full_expr.strip()
            if handle_name in file_handle_filenames:
                if _is_non_source_file(file_handle_filenames[handle_name]):
                    continue
                source_var_names.add(m.group(1))
                continue

            # Extract any quoted filename from the expression
            filename_match = re.search(r"""['"]([^'"]+)['"]""", full_expr)
            if filename_match:
                if _is_non_source_file(filename_match.group(1)):
                    continue
            else:
                # No quoted filename — could be a variable path.
                # If the expression contains a non-.py hint, skip it.
                expr_lower = full_expr.lower()
                if any(name in expr_lower for name in _NON_SOURCE_FILENAMES):
                    continue
                if any(ext in expr_lower for ext in _NON_SOURCE_EXTENSIONS):
                    continue

            source_var_names.add(m.group(1))

    if source_var_names:
        for i, line in enumerate(lines, 1):
            stripped = line.strip()
            if stripped.startswith("#"):
                continue
            for var in source_var_names:
                # assert "keyword" in var  or  assert "keyword" not in var
                if re.search(
                    rf'assert\s+.*\bin\s+{re.escape(var)}\b', stripped
                ):
                    # Only flag if not already flagged by getsource/signature
                    if not has_getsource and not has_signature:
                        violations.append(
                            f"Line {i}: source string matching — asserts keyword "
                            f"presence in file/source content instead of testing behavior"
                        )

    return violations


def run_agentic_bug_orchestrator(
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
    use_github_state: bool = True
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Orchestrates the 11-step agentic bug investigation workflow.
    
    Returns:
        (success, final_message, total_cost, model_used, changed_files)
    """

    # Ensure any stale agentic progress from prior runs is cleared.
    clear_agentic_progress()

    if not quiet:
        console.print(f"[bold]🔍 Investigating issue #{issue_number}: \"{escape(issue_title)}\"[/bold]")

    state_dir = _get_state_dir(cwd)

    # Load state
    state, loaded_gh_id = load_workflow_state(
        cwd, issue_number, "bug", state_dir, repo_owner, repo_name, use_github_state
    )

    # Initialize variables from state or defaults
    if state is not None:
        last_completed_step = state.get("last_completed_step", 0)
        step_outputs = state.get("step_outputs", {})
        total_cost = state.get("total_cost", 0.0)
        model_used = state.get("model_used", "unknown")
        github_comment_id = loaded_gh_id
        worktree_path_str = state.get("worktree_path")
        worktree_path = Path(worktree_path_str) if worktree_path_str else None
    else:
        state = {"step_outputs": {}}
        last_completed_step = 0
        step_outputs = state["step_outputs"]
        total_cost = 0.0
        model_used = "unknown"
        github_comment_id = None
        worktree_path = None

    context = {
        "issue_url": issue_url,
        "issue_content": issue_content,
        "repo_owner": repo_owner,
        "repo_name": repo_name,
        "issue_number": str(issue_number),
        "issue_author": issue_author,
        "issue_title": issue_title,
    }
    
    # Populate context with previous step outputs
    for s_key, s_out in step_outputs.items():
        context[f"step{s_key}_output"] = s_out

    # Re-extract files from step 5.5/7/9 outputs if available
    changed_files: List[str] = []
    
    # Step 5.5
    if "step5.5_output" in context:
        s55_out = context["step5.5_output"]
        prompt_fixed = _parse_changed_files(s55_out, "PROMPT_FIXED")
        changed_files.extend(prompt_fixed)

    # Step 7
    if "step7_output" in context:
        s7_out = context["step7_output"]
        created = _parse_changed_files(s7_out, "FILES_CREATED")
        modified = _parse_changed_files(s7_out, "FILES_MODIFIED")
        changed_files.extend(created + modified)
    
    # Step 9
    if "step9_output" in context:
        s9_out = context["step9_output"]
        e2e_created = _parse_changed_files(s9_out, "E2E_FILES_CREATED")
        changed_files.extend(e2e_created)

    changed_files = list(set(changed_files))  # Deduplicate
    if changed_files:
        context["files_to_stage"] = ", ".join(changed_files)

    # State validation: find actual last successful step
    ordered_steps: List[Union[int, float]] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    actual_last: Union[int, float] = 0
    for s in ordered_steps:
        key = str(s)
        if key in step_outputs and not step_outputs[key].startswith("FAILED:"):
            actual_last = s
        else:
            break
    if actual_last < last_completed_step:
        if not quiet:
            console.print(f"[yellow]State validation: correcting last_completed_step from {last_completed_step} to {actual_last}[/yellow]")
        last_completed_step = actual_last

    # Determine start step
    start_step: Union[int, float] = ordered_steps[0]
    if last_completed_step > 0:
        try:
            idx = ordered_steps.index(last_completed_step)
            if idx + 1 < len(ordered_steps):
                start_step = ordered_steps[idx + 1]
            else:
                start_step = 999  # All done
        except ValueError:
            start_step = 1

    if last_completed_step > 0 and start_step <= 10 and not quiet:
        console.print(f"Resuming bug investigation for issue #{issue_number}")
        console.print(f"   Steps 1-{last_completed_step} already complete (cached)")
        console.print(f"   Starting from Step {start_step}")

    steps_config = [
        (1, "duplicate", "Search for duplicate issues"),
        (2, "docs", "Check documentation for user error"),
        (3, "triage", "Assess if enough info to proceed"),
        (4, "api_research", "Researching external API dependencies and constraints"),
        (5, "reproduce", "Attempt to reproduce the bug"),
        (6, "root_cause", "Analyze root cause"),
        (7, "prompt_classification", "Classifying defect: code bug vs prompt defect"),
        (8, "test_plan", "Design test strategy"),
        (9, "generate", "Generate failing unit test"),
        (10, "verify", "Verify test catches the bug"),
        (11, "e2e_test", "Generate and run E2E tests"),
        (12, "pr", "Create draft PR and link to issue"),
    ]

    total_steps = len(steps_config)  # 12

    current_work_dir = cwd
    consecutive_failures = 0
    skip_e2e = False

    # Worktree restoration for resume
    if start_step >= 5.5 and start_step <= 10:
        if worktree_path and worktree_path.exists():
            if not quiet:
                console.print(f"[blue]Reusing existing worktree: {worktree_path}[/blue]")
            current_work_dir = worktree_path
            context["worktree_path"] = str(worktree_path)
        else:
            wt_path, err = _setup_worktree(cwd, issue_number, quiet, resume_existing=True)
            if not wt_path:
                return False, f"Failed to restore worktree: {err}", total_cost, model_used, []
            worktree_path = wt_path
            current_work_dir = worktree_path
            state["worktree_path"] = str(worktree_path)
            context["worktree_path"] = str(worktree_path)

    for step_index, (step_num, name, description) in enumerate(steps_config, 1):
        if step_num < start_step:
            continue

        # Worktree setup before Step 7 (prompt classification)
        if step_num == 7:
            if worktree_path and worktree_path.exists():
                current_work_dir = worktree_path
                if not quiet:
                    console.print(f"[blue]Using existing worktree: {worktree_path}[/blue]")
            else:
                try:
                    current_branch = subprocess.run(
                        ["git", "rev-parse", "--abbrev-ref", "HEAD"],
                        cwd=cwd,
                        capture_output=True,
                        text=True,
                        check=True
                    ).stdout.strip()
                    if current_branch not in ["main", "master"] and not quiet:
                        console.print(f"[yellow]Note: Creating branch from HEAD ({current_branch}), not origin/main. PR will include commits from this branch. Run from main for independent changes.[/yellow]")
                except (subprocess.CalledProcessError, FileNotFoundError):
                    pass

                wt_path, err = _setup_worktree(cwd, issue_number, quiet, resume_existing=False)
                if not wt_path:
                    return False, f"Failed to create worktree: {err}", total_cost, model_used, []
                worktree_path = wt_path
                current_work_dir = worktree_path
                state["worktree_path"] = str(worktree_path)
                context["worktree_path"] = str(worktree_path)

        # Skip E2E if flagged
        if step_num == 11 and skip_e2e:
            if not quiet:
                console.print("Skipping Step 9 (E2E): unit tests provide sufficient coverage")
            continue

        # Record progress so KeyboardInterrupt can report how far we got.
        completed_list = (
            list(range(1, int(last_completed_step) + 1))
            if last_completed_step
            else []
        )
        set_agentic_progress(
            workflow="bug",
            current_step=step_num,
            total_steps=12,
            step_name=description,
            completed_steps=completed_list,
        )

        # Display step progress
        if not quiet:
            console.print(f"[bold][Step {step_index}/{total_steps}][/bold] {description}...")

        # Snapshot filesystem BEFORE step 9 (generate) runs (for fallback detection)
        pre_step7_files: List[str] = []
        if step_num == 9:
            pre_step7_files = _get_modified_and_untracked(current_work_dir)

        # Load and preprocess template
        step_str = str(step_num).replace(".", "_")
        template_name = f"agentic_bug_step{step_str}_{name}_LLM"
        
        prompt_template = load_prompt_template(template_name)
        if not prompt_template:
            return False, f"Missing prompt template: {template_name}", total_cost, model_used, []

        prompt_template = preprocess(prompt_template, recursive=True, double_curly_brackets=True, exclude_keys=list(context.keys()))

        prompt_template = prompt_template.replace("{{", "{").replace("}}", "}")
        formatted_prompt = prompt_template
        for key, value in context.items():
            formatted_prompt = formatted_prompt.replace(f"{{{key}}}", str(value))

        timeout = BUG_STEP_TIMEOUTS.get(step_num, 340.0) + timeout_adder
        
        # Run task
        step_label = f"step{step_str}"
        
        step_success, step_output, step_cost, step_model = run_agentic_task(
            instruction=formatted_prompt,
            cwd=current_work_dir,
            verbose=verbose,
            quiet=quiet,
            timeout=timeout,
            label=step_label,
            max_retries=DEFAULT_MAX_RETRIES,
        )

        total_cost += step_cost
        model_used = step_model
        state["total_cost"] = total_cost
        state["model_used"] = model_used

        # Consecutive provider failure check (only when the step actually failed)
        if not step_success and "All agent providers failed" in step_output:
            consecutive_failures += 1
            if consecutive_failures >= 3:
                state["last_completed_step"] = last_completed_step
                state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"
                save_workflow_state(cwd, issue_number, "bug", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
                return False, "Aborting: 3 consecutive steps failed — agent providers unavailable", total_cost, model_used, changed_files
        else:
            consecutive_failures = 0

        # Store output in context
        context[f"step{str(step_num)}_output"] = step_output

        files_extracted = False

        # Step-specific handling
        if step_num == 7:
            defect_type_match = re.search(r"DEFECT_TYPE:\s*(code|prompt)", step_output)
            if defect_type_match:
                defect_type = defect_type_match.group(1)
                if defect_type == "prompt":
                    prompt_fixed = _parse_changed_files(step_output, "PROMPT_FIXED")
                    if prompt_fixed:
                        changed_files.extend(prompt_fixed)
                        context["files_to_stage"] = ", ".join(changed_files)
                        files_extracted = True

        if step_num == 9:
            created = _parse_changed_files(step_output, "FILES_CREATED")
            modified = _parse_changed_files(step_output, "FILES_MODIFIED")
            extracted = created + modified
            if not extracted:
                # Filesystem fallback: diff against pre-snapshot
                post_files = _get_modified_and_untracked(current_work_dir)
                new_files = [f for f in post_files if f not in pre_step7_files]
                extracted = new_files
            if extracted:
                files_extracted = True
                changed_files.extend(extracted)
                changed_files = list(set(changed_files))
                context["files_to_stage"] = ", ".join(changed_files)

            # Structural test guard: scan generated files for banned patterns
            all_violations: List[str] = []
            for fpath in extracted:
                abs_path = (current_work_dir / fpath) if not Path(fpath).is_absolute() else Path(fpath)
                violations = detect_structural_test_patterns(str(abs_path))
                if violations:
                    all_violations.extend(violations)

            if all_violations:
                if not quiet:
                    console.print(
                        f"[yellow]  → Structural test patterns detected in generated tests, "
                        f"retrying step 9:[/yellow]"
                    )
                    for v in all_violations:
                        console.print(f"[yellow]    • {v}[/yellow]")

                # Re-run step 9 with feedback about the violations
                violation_summary = "\n".join(f"  - {v}" for v in all_violations)
                retry_addendum = (
                    "\n\n% IMPORTANT: Your previous attempt generated STRUCTURAL tests that "
                    "were rejected. The following violations were detected:\n"
                    f"{violation_summary}\n\n"
                    "You MUST rewrite these tests as BEHAVIORAL tests that call functions "
                    "and assert on observable outputs or side effects. Do NOT use "
                    "inspect.getsource, inspect.signature, hasattr assertions, or "
                    "source string matching."
                )

                retry_success, retry_output, retry_cost, retry_model = run_agentic_task(
                    instruction=formatted_prompt + retry_addendum,
                    cwd=current_work_dir,
                    verbose=verbose,
                    quiet=quiet,
                    timeout=timeout,
                    label="step9",
                    max_retries=DEFAULT_MAX_RETRIES,
                )
                total_cost += retry_cost
                model_used = retry_model
                state["total_cost"] = total_cost
                state["model_used"] = model_used
                step_success = retry_success

                if not retry_success:
                    if not quiet:
                        console.print(
                            "[red]  → Retry of step 9 failed; keeping original output.[/red]"
                        )
                else:
                    # Re-extract files from retry
                    retry_created = _parse_changed_files(retry_output, "FILES_CREATED")
                    retry_modified = _parse_changed_files(retry_output, "FILES_MODIFIED")
                    retry_extracted = retry_created + retry_modified
                    if retry_extracted:
                        changed_files.extend(retry_extracted)
                        changed_files = list(set(changed_files))
                        context["files_to_stage"] = ", ".join(changed_files)

                    # Re-scan retry output for structural patterns
                    retry_violations: List[str] = []
                    for fpath in retry_extracted:
                        abs_path = (current_work_dir / fpath) if not Path(fpath).is_absolute() else Path(fpath)
                        v = detect_structural_test_patterns(str(abs_path))
                        if v:
                            retry_violations.extend(v)

                    if retry_violations and not quiet:
                        console.print(
                            "[yellow]  → Retry still contains structural patterns "
                            "(proceeding with warning):[/yellow]"
                        )
                        for v in retry_violations:
                            console.print(f"[yellow]    • {v}[/yellow]")

                    # Update step output to the retry output
                    step_output = retry_output
                    context["step9_output"] = retry_output

        if step_num == 10:
            # Check for E2E classification marker in step output.
            # Safe default: if marker is missing, E2E runs (backward compatible).
            if "E2E_NEEDED: no" in step_output:
                skip_e2e = True
                if not quiet:
                    console.print("   (E2E skipped: E2E_NEEDED: no)")

        if step_num == 11:
            e2e_skipped = "E2E_SKIP:" in step_output
            if e2e_skipped:
                # E2E skipped, continue normally
                pass
            else:
                e2e_created = _parse_changed_files(step_output, "E2E_FILES_CREATED")

                # Independent E2E verification (unless E2E_SKIP was emitted)
                if e2e_created and not e2e_skipped:
                    verify_ok, verify_output = _verify_e2e_tests(e2e_created, current_work_dir)
                    if not quiet:
                        if verify_ok:
                            console.print(f"  → E2E verification passed: {verify_output}")
                        else:
                            console.print(f"[yellow]  → E2E verification issue: {verify_output}[/yellow]")

                changed_files.extend(e2e_created)
                changed_files = list(set(changed_files))
                context["files_to_stage"] = ", ".join(changed_files)

        # Check for hard stops
        stop_reason = _check_hard_stop(step_num, step_output, files_extracted)
        if stop_reason:
            if not quiet:
                console.print(f"[yellow]⏹️  Investigation stopped at Step {step_num}: {stop_reason}[/yellow]")
            state["last_completed_step"] = step_num
            state["step_outputs"][str(step_num)] = step_output
            save_workflow_state(cwd, issue_number, "bug", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
            return False, f"Stopped at step {step_num}: {stop_reason}", total_cost, model_used, changed_files

        if not step_success:
            if not quiet:
                console.print(f"[yellow]Warning: Step {step_num} reported failure but continuing...[/yellow]")

        # Update state
        if step_success:
            state["step_outputs"][str(step_num)] = step_output
            state["last_completed_step"] = step_num
            last_completed_step = step_num
        else:
            state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"

        save_result = save_workflow_state(cwd, issue_number, "bug", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
        if save_result:
            github_comment_id = save_result

        # Print step completion marker (required for credential waterfall detection)
        if not quiet:
            console.print(f"  → Step {step_num} complete.")

    # Final Summary
    pr_url = "Unknown"
    if "step12_output" in context:
        s10_out = context["step12_output"]
        url_match = re.search(r"https://github.com/\S+/pull/\d+", s10_out)
        if url_match:
            pr_url = url_match.group(0)

    if not quiet:
        console.print("\n[green]✅ Investigation complete[/green]")
        console.print(f"   Total cost: ${total_cost:.4f}")
        console.print(f"   Files changed: {', '.join(changed_files) if changed_files else 'none'}")
        if worktree_path:
            console.print(f"   Worktree: {worktree_path}")
        console.print(f"   PR created: {pr_url}")

    # Clear progress on successful completion so future runs start clean.
    clear_agentic_progress()

    final_msg = f"Investigation complete — PR: {pr_url}"
    return True, final_msg, total_cost, model_used, changed_files

if __name__ == "__main__":
    # Example usage logic could go here if needed for testing
    pass
