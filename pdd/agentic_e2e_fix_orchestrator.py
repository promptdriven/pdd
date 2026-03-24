from __future__ import annotations

import hashlib
import os
import shlex
import shutil
import subprocess
import sys
import time
import json
from datetime import datetime
from pathlib import Path
from typing import List, Tuple, Dict, Any, Optional, Set

from rich.console import Console

import re as _re

from .agentic_common import (
    run_agentic_task,
    load_workflow_state,
    save_workflow_state,
    clear_workflow_state,
    validate_cached_state,
    post_final_comment,
    DEFAULT_MAX_RETRIES,
    detect_control_token,
    classify_step_output,
)
from .get_test_command import get_test_command_for_file
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .pytest_output import run_pytest_and_capture_output
from .ci_validation import run_ci_validation_loop

# Constants
STEP_NAMES = {
    1: "unit_tests",
    2: "e2e_tests",
    3: "root_cause",
    4: "fix_e2e_tests",
    5: "identify_devunits",
    6: "create_unit_tests",
    7: "verify_tests",
    8: "run_pdd_fix",
    9: "verify_all",
}

STEP_DESCRIPTIONS = {
    1: "Running unit tests from issue",
    2: "Running e2e tests",
    3: "Analyzing root cause",
    4: "Fixing e2e tests",
    5: "Identifying dev units",
    6: "Creating unit tests",
    7: "Verifying tests detect bugs",
    8: "Running pdd fix",
    9: "Final verification",
}

# Per-step timeouts for the 10-step agentic e2e fix workflow
E2E_FIX_STEP_TIMEOUTS: Dict[int, float] = {
    1: 340.0,   # Run unit tests from issue, pdd fix failures
    2: 240.0,   # Run e2e tests, check completion (early exit)
    3: 340.0,   # Root cause analysis (code vs test vs both)
    4: 340.0,   # Fix e2e tests if needed
    5: 340.0,   # Identify dev units involved in failures
    6: 600.0,   # Create/append unit tests for dev units (Complex)
    7: 600.0,   # Verify unit tests detect bugs (Complex)
    8: 1000.0,  # Run pdd fix on failing dev units (Most Complex - multiple LLM calls)
    9: 240.0,   # Final verification, loop control
    10: 600.0,  # Post-push CI validation and remediation
}

console = Console()

# Re-export for backward compatibility with tests that import from this module
_detect_control_token = detect_control_token

# Additional fail patterns not in the shared SEMANTIC_PATTERNS (step-specific)
_FAIL_PATTERNS = [
    _re.compile(r"\b[1-9]\d*\s+(?:tests?\s+)?(?:still\s+)?fail", _re.IGNORECASE),
    _re.compile(r"\bneed(?:s)?\s+(?:another|more)\s+cycle", _re.IGNORECASE),
    _re.compile(r"\bstill\s+failing\b", _re.IGNORECASE),
]


def _classify_step_output(output: str, step_num: int) -> Optional[str]:
    """Classify step output into a control token using shared 3-tier detection.

    Uses detect_control_token (exact → case-insensitive → semantic regex with
    tail-only scoping) from agentic_common, plus step-specific logic for
    VERIFICATION_FAILED priority and fail-before-pass ordering.

    Returns the token string or None if the output is ambiguous.
    """
    # Priority: VERIFICATION_FAILED overrides everything
    if "VERIFICATION_FAILED" in output:
        return "VERIFICATION_FAILED"

    if step_num == 3:
        # Check for positive tokens first — if CODE_BUG/TEST_BUG/BOTH is found,
        # return it so tier 4 NOT_A_BUG fallback is skipped (same fail-before-pass
        # pattern used for Steps 1/2/9). Case-sensitive substring match (consistent
        # with VERIFICATION_FAILED, LOCAL_TESTS_PASS, and detect_control_token tier 1)
        # is safe here because these tokens don't appear uppercase in natural language
        # (e.g., "Both tests passed" won't match "BOTH").
        for positive_token in ("CODE_BUG", "TEST_BUG", "BOTH"):
            if positive_token in output:
                return positive_token

        match = detect_control_token(output, "NOT_A_BUG")
        if match:
            if match.tier == "semantic":
                console.print(f"[yellow]NOT_A_BUG detected via semantic fallback (pattern: {match.pattern})[/yellow]")
            return "NOT_A_BUG"

    if step_num in (1, 2, 9):
        # Exact match for LOCAL_TESTS_PASS (not in shared SEMANTIC_PATTERNS)
        if "LOCAL_TESTS_PASS" in output:
            return "LOCAL_TESTS_PASS"

        # Check for failure indicators first — they take priority over pass
        for pat in _FAIL_PATTERNS:
            if pat.search(output):
                if step_num == 9:
                    return "CONTINUE_CYCLE"
                return None

        match = detect_control_token(output, "ALL_TESTS_PASS")
        if match:
            if match.tier == "semantic":
                console.print(f"[yellow]ALL_TESTS_PASS detected via semantic fallback (pattern: {match.pattern})[/yellow]")
            if step_num == 9:
                return "LOCAL_TESTS_PASS"
            return "ALL_TESTS_PASS"

    if step_num == 9:
        if detect_control_token(output, "MAX_CYCLES_REACHED"):
            return "MAX_CYCLES_REACHED"
        if detect_control_token(output, "CONTINUE_CYCLE"):
            return "CONTINUE_CYCLE"

    return None


def _check_e2e_environment(cwd: Path) -> Tuple[bool, str]:
    """Check if the executor environment has E2E test infrastructure.

    Returns (available, reason) where available is True if E2E tests
    can run, False otherwise with a reason string.
    """
    # Check for npx (needed for playwright)
    if not shutil.which("npx"):
        return (False, "npx not found — playwright/browser infrastructure unavailable")

    # Check for playwright config files (root + one level of subdirectories)
    playwright_configs = [
        "playwright.config.ts",
        "playwright.config.js",
        "playwright.config.mjs",
    ]
    try:
        search_dirs = [cwd] + [d for d in cwd.iterdir() if d.is_dir() and not d.name.startswith(".")]
    except (FileNotFoundError, NotADirectoryError):
        search_dirs = [cwd]
    has_config = any(
        (d / cfg).exists()
        for d in search_dirs
        for cfg in playwright_configs
    )
    if not has_config:
        return (False, "no playwright config found in project")

    return (True, "")


def _get_state_dir(cwd: Path) -> Path:
    """Returns the state directory .pdd/e2e-fix-state/ relative to git root."""
    # Simple heuristic: look for .git, otherwise use cwd
    d = cwd.resolve()
    root = d
    while d != d.parent:
        if (d / ".git").exists():
            root = d
            break
        d = d.parent
    
    state_dir = root / ".pdd" / "e2e-fix-state"
    state_dir.mkdir(parents=True, exist_ok=True)
    return state_dir

def _parse_changed_files(output: str) -> List[str]:
    """Parses FILES_CREATED and FILES_MODIFIED from agent output."""
    files = []
    for line in output.splitlines():
        if line.startswith("FILES_CREATED:") or line.startswith("FILES_MODIFIED:"):
            # Extract content after colon
            content = line.split(":", 1)[1].strip()
            if content:
                # Split by comma and strip
                paths = [p.strip() for p in content.split(",") if p.strip()]
                files.extend(paths)
    return files

def _parse_dev_units(output: str) -> str:
    """Parses DEV_UNITS_IDENTIFIED from output."""
    for line in output.splitlines():
        if line.startswith("DEV_UNITS_IDENTIFIED:"):
            return line.split(":", 1)[1].strip()
    return ""

# Patterns for intermediate/debug files that should not be committed
# These are created by `pdd fix` as intermediate outputs (see generate_output_paths.py)
_FIXED_SUFFIXES = ("_fixed", ".fixed", "-fixed")
_BACKUP_EXTENSIONS = (".bak", ".backup", ".orig", ".tmp")


def _is_intermediate_file(filepath: str) -> bool:
    """Check if a file is an intermediate/debug file that should not be committed.

    Intermediate files are created during the `pdd fix` workflow as default outputs
    and should be filtered out before committing changes.

    Patterns detected:
    - *_fixed.* (e.g., module_fixed.py, test_auth_fixed.py)
    - *.fixed.* (e.g., module.fixed.py)
    - *-fixed.* (e.g., module-fixed.py)
    - *.bak, *.backup, *.orig, *.tmp extensions
    - error_output*.txt (e.g., error_output.txt, error_output_models.txt)
    - .pdd/** (any file under .pdd/ directory — backups, core_dumps, etc.)
    - *_errors.txt, *_fix_errors.txt (e.g., waitlist_fix_errors.txt)
    - step*_output.md (e.g., step9_output.md)
    - test_issue_*_reproduction.py (e.g., test_issue_824_reproduction.py)

    Args:
        filepath: Relative path to the file

    Returns:
        True if the file should be excluded from commits
    """
    path = Path(filepath)
    stem = path.stem  # filename without extension
    suffix = path.suffix  # extension including dot

    # Check for backup extensions (e.g., foo.py.bak, foo.py.backup)
    if suffix in _BACKUP_EXTENSIONS:
        return True

    # Check for double extensions with backup (e.g., foo.py.orig)
    if path.suffixes and len(path.suffixes) >= 2:
        if path.suffixes[-1] in _BACKUP_EXTENSIONS:
            return True

    # Check for fixed patterns in the stem
    # e.g., module_fixed.py -> stem is "module_fixed"
    for fixed_suffix in _FIXED_SUFFIXES:
        if stem.endswith(fixed_suffix):
            return True

    # Check for error_output debug files (e.g., error_output.txt, error_output_models.txt)
    if suffix == ".txt" and stem.startswith("error_output"):
        return True

    # Check for .pdd/ directory files (backups, core_dumps, and any future artifacts)
    # Exclude .pdd/e2e-fix-state/ which contains workflow state needed for resume
    normalized = filepath.replace("\\", "/")
    if normalized.startswith(".pdd/") or "/.pdd/" in normalized:
        if "/e2e-fix-state/" in normalized or normalized.startswith(".pdd/e2e-fix-state/"):
            return False
        return True

    # Check for *_errors.txt and *_fix_errors.txt files
    if suffix == ".txt" and (stem.endswith("_errors") or stem.endswith("_fix_errors")):
        return True

    # Check for step*_output.md debug output files
    if suffix == ".md" and stem.startswith("step") and stem.endswith("_output"):
        return True

    # Check for test_issue_*_reproduction.py leftover reproduction tests
    # Pattern: test_issue_<number>_reproduction (not test_issue_reproduction_helper etc.)
    if suffix == ".py" and stem.startswith("test_issue_") and stem.endswith("_reproduction"):
        return True

    return False


# TypeScript/JavaScript test file extensions
_TS_TEST_EXTENSIONS = (".test.ts", ".test.tsx", ".spec.ts", ".spec.tsx")


def _is_test_file(filename: str) -> bool:
    """Check if a filename matches test file conventions for any supported language.

    Recognizes:
    - Python: test_*.py
    - Jest: *.test.ts, *.test.tsx (including files in __test__/ directories)
    - Playwright: *.spec.ts, *.spec.tsx
    """
    basename = Path(filename).name
    # Python convention
    if basename.startswith("test_") and basename.endswith(".py"):
        return True
    # TypeScript/JavaScript conventions (Jest + Playwright)
    for ext in _TS_TEST_EXTENSIONS:
        if basename.endswith(ext):
            return True
    return False


def _extract_test_files(
    issue_content: str,
    changed_files: List[str],
    cwd: Path,
    initial_file_hashes: Optional[Dict[str, Optional[str]]] = None,
) -> List[str]:
    """Extract test file paths from issue content, changed files, and disk changes.

    Looks for:
    - E2E_FILES_CREATED: markers from pdd bug output
    - FILES_CREATED: markers
    - File paths matching test conventions (Python test_*.py, Jest *.test.ts/tsx,
      Playwright *.spec.ts/tsx) in changed_files
    - Test files actually created/modified on disk (hash comparison)

    Returns only paths that exist on disk, deduplicated.
    """
    test_files: List[str] = []
    seen: set = set()

    def _add(path: str) -> None:
        path = path.strip()
        if path and path not in seen and (cwd / path).exists():
            seen.add(path)
            test_files.append(path)

    # Parse markers from issue content
    for line in issue_content.splitlines():
        for prefix in ("E2E_FILES_CREATED:", "FILES_CREATED:"):
            if line.strip().startswith(prefix):
                content = line.split(":", 1)[1].strip()
                for p in content.split(","):
                    p = p.strip()
                    if _is_test_file(p):
                        _add(p)

    # Include test files from changed_files list
    for f in changed_files:
        if _is_test_file(f):
            _add(f)

    # Scan issue content for inline test file references
    # Match Python test files (test_*.py) and TypeScript test files (*.test.ts/tsx, *.spec.ts/tsx)
    for match in _re.finditer(
        r'((?:[\w/._-]+/)*(?:test_[\w.-]+\.py|[\w.-]+\.(?:test|spec)\.(?:tsx|ts)))',
        issue_content,
    ):
        _add(match.group(1))

    # Detect test files actually created/modified on disk during workflow
    if initial_file_hashes is not None:
        actual_changes = _detect_changed_files(cwd, initial_file_hashes)
        for f in actual_changes:
            if _is_test_file(f):
                _add(f)

    # Fallback: scan for test files committed on the feature branch that escaped
    # the other discovery paths. This catches files committed during pdd bug that
    # aren't in markers, changed_files, or hash detection (e.g., when
    # initial_file_hashes is None or the files were committed before the hash
    # snapshot was taken).
    count_before_git = len(test_files)
    committed_files = _get_modified_and_untracked(cwd)
    for f in committed_files:
        basename = Path(f).name
        if basename.startswith("test_") and basename.endswith(".py"):
            _add(f)

    # Ultimate fallback: directory scan for test_*.py files on disk.
    # Only runs when git-based discovery didn't add any new files, to avoid
    # pulling the entire test suite into verification (slow + timeouts).
    # Scoped to tests/ dir (recursive) and root-level test_*.py (non-recursive).
    git_found_nothing_new = len(test_files) == count_before_git
    if git_found_nothing_new:
        scan_dirs = [cwd / "tests", cwd]
        for scan_dir in scan_dirs:
            if not scan_dir.is_dir():
                continue
            glob_fn = scan_dir.rglob if scan_dir != cwd else scan_dir.glob
            for test_py in sorted(glob_fn("test_*.py")):
                rel = str(test_py.relative_to(cwd))
                if any(part.startswith(".") or part == "__pycache__" for part in Path(rel).parts):
                    continue
                _add(rel)

    return test_files


def _verify_tests_independently(test_files: List[str], cwd: Path) -> Tuple[bool, str]:
    """Run appropriate test runner on test files via subprocess. Returns (all_passed, output).

    Dispatches the correct runner based on file extension:
    - .py → pytest via run_pytest_and_capture_output
    - Non-Python → resolved via get_test_command_for_file (e.g. npx jest, npx playwright)
    """
    all_outputs: List[str] = []
    all_passed = True

    for test_file in test_files:
        abs_path = str(cwd / test_file)

        if test_file.endswith(".py"):
            # Python: use existing pytest runner
            result = run_pytest_and_capture_output(abs_path)
            if not result or not result.get("test_results"):
                all_passed = False
                all_outputs.append(f"{test_file}: no results (pytest error)")
                continue

            tr = result["test_results"][0]
            failures = tr.get("failures", 0) + tr.get("errors", 0)
            passed = tr.get("passed", 0)
            stdout = tr.get("standard_output", "")

            if failures > 0:
                all_passed = False
                all_outputs.append(f"{test_file}: {failures} failure(s)\n{stdout}")
            else:
                all_outputs.append(f"{test_file}: {passed} passed")
        else:
            # Non-Python: resolve test command via get_test_command_for_file
            test_cmd = get_test_command_for_file(abs_path)
            if not test_cmd:
                all_passed = False
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
                    all_passed = False
                    output = proc.stdout + proc.stderr
                    all_outputs.append(f"{test_file}: FAILED (exit code {proc.returncode})\n{output}")
                else:
                    all_outputs.append(f"{test_file}: passed")
            except subprocess.TimeoutExpired:
                all_passed = False
                all_outputs.append(f"{test_file}: FAILED (timeout)")
            except Exception as e:
                all_passed = False
                all_outputs.append(f"{test_file}: FAILED ({e})")

    return all_passed, "\n".join(all_outputs)


def _update_dev_unit_states(output: str, current_states: Dict[str, Any], identified_units_str: str) -> Dict[str, Any]:
    """Updates dev unit states based on Step 8 output."""
    identified_units = [u.strip() for u in identified_units_str.split(",") if u.strip()]
    
    # Initialize if not present
    for unit in identified_units:
        if unit not in current_states:
            current_states[unit] = {"fixed": False, "fix_attempts": 0}
        current_states[unit]["fix_attempts"] += 1

    # Parse results from output
    # Heuristic: look for "unit_name: FIXED" or "unit_name: Failed"
    # This depends on the LLM following instructions in Step 8 prompt.
    for line in output.splitlines():
        for unit in identified_units:
            if unit in line:
                if "FIXED" in line:
                    current_states[unit]["fixed"] = True
                elif "Failed" in line or "FAIL" in line:
                    current_states[unit]["fixed"] = False
    
    return current_states

def _check_staleness(state: Dict[str, Any], cwd: Path) -> None:
    """Checks if files have changed since state was saved."""
    last_saved_str = state.get("last_saved_at")
    if not last_saved_str:
        return

    try:
        last_saved = datetime.fromisoformat(last_saved_str)
    except ValueError:
        return

    changed_files = state.get("changed_files", [])
    stale = False
    
    for file_path in changed_files:
        p = cwd / file_path
        if not p.exists():
            console.print(f"[yellow]Warning: File '{file_path}' from previous state is missing.[/yellow]")
            continue
        
        # Check mtime
        mtime = datetime.fromtimestamp(p.stat().st_mtime)
        if mtime > last_saved:
            stale = True
            break
    
    if stale:
        console.print("[yellow]Warning: Codebase may have changed since last run. Consider --no-resume for fresh start.[/yellow]")


def _get_modified_and_untracked(cwd: Path) -> Set[str]:
    """Returns set of modified tracked files, untracked files, and files committed on the branch.

    Includes files added in commits since the branch diverged from the base branch
    (e.g., test files committed during pdd bug), not just uncommitted changes.
    """
    files: Set[str] = set()

    # Get modified tracked files (uncommitted changes)
    result = subprocess.run(
        ["git", "diff", "--name-only", "HEAD"],
        cwd=cwd,
        capture_output=True,
        text=True
    )
    if result.returncode == 0:
        files.update(f for f in result.stdout.strip().split("\n") if f)

    # Get untracked files
    result = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard"],
        cwd=cwd,
        capture_output=True,
        text=True
    )
    if result.returncode == 0:
        files.update(f for f in result.stdout.strip().split("\n") if f)

    # Get files committed on the feature branch (since diverging from base branch).
    # This catches test files committed during pdd bug that are neither uncommitted
    # nor untracked — they're committed and clean, but new relative to the base.
    # Try merge-base first (feature branch vs main/master), then fall back to
    # listing all tracked files (single-branch scenario).
    for base in ("main", "master"):
        # Use merge-base to find the divergence point
        mb_result = subprocess.run(
            ["git", "merge-base", base, "HEAD"],
            cwd=cwd,
            capture_output=True,
            text=True
        )
        if mb_result.returncode == 0 and mb_result.stdout.strip():
            merge_base = mb_result.stdout.strip()
            result = subprocess.run(
                ["git", "diff", "--name-only", merge_base, "HEAD"],
                cwd=cwd,
                capture_output=True,
                text=True
            )
            if result.returncode == 0 and result.stdout.strip():
                files.update(f for f in result.stdout.strip().split("\n") if f)
            break

    # Note: no blanket `git ls-files` fallback here — returning ALL tracked
    # files would cause _commit_and_push to falsely detect unchanged files as
    # "changed". Single-branch repos are handled by the rglob fallback in
    # _extract_test_files() instead.

    return files


def _get_file_hashes(cwd: Path) -> Dict[str, Optional[str]]:
    """
    Returns {filepath: md5_hash} for all modified and untracked files.

    If a file is deleted or unreadable, stores None for that file.
    """
    hashes: Dict[str, Optional[str]] = {}
    for filepath in _get_modified_and_untracked(cwd):
        path = cwd / filepath
        if path.exists() and path.is_file():
            try:
                hashes[filepath] = hashlib.md5(path.read_bytes()).hexdigest()
            except (IOError, OSError):
                hashes[filepath] = None
        else:
            hashes[filepath] = None  # Deleted or not a file
    return hashes


def _detect_changed_files(cwd: Path, initial_file_hashes: Dict[str, Optional[str]]) -> List[str]:
    """Detects files actually changed during the workflow using hash comparison.

    Compares current file hashes against the snapshot taken before the workflow
    started to find files that were created or modified on disk, regardless of
    whether the LLM output included FILES_MODIFIED/FILES_CREATED markers.
    """
    current_hashes = _get_file_hashes(cwd)
    changed: List[str] = []
    for filepath, current_hash in current_hashes.items():
        if filepath not in initial_file_hashes:
            changed.append(filepath)
        elif initial_file_hashes[filepath] != current_hash:
            changed.append(filepath)
    return changed


def _has_unpushed_commits(cwd: Path) -> bool:
    """Check if there are commits ahead of the remote tracking branch."""
    result = subprocess.run(
        ["git", "rev-list", "--count", "@{u}..HEAD"],
        cwd=cwd,
        capture_output=True,
        text=True
    )
    if result.returncode == 0:
        count = int(result.stdout.strip() or "0")
        return count > 0
    return False


def _push_with_retry(
    cwd: Path,
    repo_owner: str,
    repo_name: str,
) -> Tuple[bool, str]:
    """
    Pushes to remote, retrying with PDD_GH_TOKEN_FILE on auth failure.

    On push auth failure (Authentication failed, HTTP 401, could not read Username,
    or HTTP Basic: Access denied):
    - If PDD_GH_TOKEN_FILE env var is set and the file exists with non-empty content:
      - Read the token from the file (strip whitespace)
      - Save the current remote origin URL
      - Set remote origin URL to https://x-access-token:{token}@github.com/{repo_owner}/{repo_name}.git
      - Retry the push once
      - Restore the original remote URL in a finally block (prevents token leakage in git config)
    - If no token file available, file is empty, or retry also fails: return (False, error)

    Returns:
        (success, message)
    """
    push_result = subprocess.run(
        ["git", "push", "-u", "origin", "HEAD"],
        cwd=cwd,
        capture_output=True,
        text=True
    )

    if push_result.returncode == 0:
        return True, ""

    stderr = push_result.stderr
    auth_errors = ["Authentication failed", "HTTP 401", "could not read Username", "HTTP Basic: Access denied"]
    is_auth_failure = any(err in stderr for err in auth_errors)

    if not is_auth_failure:
        return False, stderr

    # Auth failure — try PDD_GH_TOKEN_FILE
    token_file_path = os.environ.get("PDD_GH_TOKEN_FILE")
    if not token_file_path:
        return False, stderr

    token_path = Path(token_file_path)
    if not token_path.exists():
        return False, stderr

    token = token_path.read_text().strip()
    if not token:
        return False, stderr

    # Save original remote URL — abort retry if we can't capture it
    url_result = subprocess.run(
        ["git", "remote", "get-url", "origin"],
        cwd=cwd,
        capture_output=True,
        text=True
    )
    if url_result.returncode != 0:
        return False, stderr
    original_url = url_result.stdout.strip()

    try:
        # Set remote URL with token (URL-encode to guard against reserved characters)
        from urllib.parse import quote
        token_url = f"https://x-access-token:{quote(token, safe='')}@github.com/{repo_owner}/{repo_name}.git"
        subprocess.run(
            ["git", "remote", "set-url", "origin", token_url],
            cwd=cwd,
            capture_output=True,
            text=True
        )

        # Retry push
        retry_result = subprocess.run(
            ["git", "push", "-u", "origin", "HEAD"],
            cwd=cwd,
            capture_output=True,
            text=True
        )

        if retry_result.returncode == 0:
            return True, ""
        else:
            return False, retry_result.stderr
    finally:
        # Restore original remote URL (prevents token leakage in git config)
        if original_url:
            restore = subprocess.run(
                ["git", "remote", "set-url", "origin", original_url],
                cwd=cwd,
                capture_output=True,
                text=True
            )
            if restore.returncode != 0:
                console.print(
                    "[yellow]WARNING: Failed to restore original remote URL:"
                    f" {restore.stderr}[/yellow]"
                )


def _commit_and_push(
    cwd: Path,
    issue_number: int,
    issue_title: str,
    repo_owner: str,
    repo_name: str,
    initial_file_hashes: Dict[str, Optional[str]],
    quiet: bool = False
) -> Tuple[bool, str]:
    """
    Commits only files that changed during the workflow and pushes.

    Uses hash comparison to detect actual content changes, avoiding
    staging pre-existing modified/untracked files.

    The PR was already created by `pdd bug`, so pushing
    automatically updates it.

    On push auth failure, retries using PDD_GH_TOKEN_FILE if available.

    Args:
        cwd: Working directory
        issue_number: GitHub issue number
        issue_title: Issue title for commit message
        repo_owner: GitHub repository owner
        repo_name: GitHub repository name
        initial_file_hashes: File hashes from before workflow started
        quiet: Suppress output

    Returns:
        (success, message)
    """
    # Get current file hashes
    current_hashes = _get_file_hashes(cwd)

    # Find files that changed during workflow
    changed_files_raw: List[str] = []
    for filepath, current_hash in current_hashes.items():
        if filepath not in initial_file_hashes:
            # New file created during workflow
            changed_files_raw.append(filepath)
        elif initial_file_hashes[filepath] != current_hash:
            # Content changed during workflow
            changed_files_raw.append(filepath)

    # Filter out intermediate/debug files (Issue #383)
    # These are created by `pdd fix` as default outputs and should not be committed
    files_to_commit = [f for f in changed_files_raw if not _is_intermediate_file(f)]

    if not files_to_commit:
        # Fallback: hash snapshot may be tainted (captured after a prior
        # interrupted run's modifications already existed on disk). Check
        # git diff directly to catch orphaned unstaged changes (#545).
        fallback_files = _get_modified_and_untracked(cwd)
        # Apply the same intermediate file filter to fallback files
        fallback_files = [f for f in fallback_files if not _is_intermediate_file(f)]
        if fallback_files:
            files_to_commit = list(fallback_files)
        elif _has_unpushed_commits(cwd):
            # Check if there are unpushed commits to push
            push_ok, push_err = _push_with_retry(cwd, repo_owner, repo_name)
            if push_ok:
                return True, "Pushed existing commits"
            else:
                return False, f"Push failed: {push_err}"
        else:
            return True, "No changes to commit"

    # Stage only workflow-changed files
    for filepath in files_to_commit:
        stage_result = subprocess.run(
            ["git", "add", filepath],
            cwd=cwd,
            capture_output=True,
            text=True
        )
        if stage_result.returncode != 0:
            return False, f"Failed to stage {filepath}: {stage_result.stderr}"

    # Commit with message referencing issue
    commit_msg = f"fix: {issue_title}\n\nFixes #{issue_number}"
    commit_result = subprocess.run(
        ["git", "commit", "-m", commit_msg],
        cwd=cwd,
        capture_output=True,
        text=True
    )
    if commit_result.returncode != 0:
        # Commit may fail with "nothing to commit" when fallback files were
        # already committed on the branch (merge-base diff includes them).
        # In that case, push any unpushed commits instead of failing.
        if _has_unpushed_commits(cwd):
            push_ok, push_err = _push_with_retry(cwd, repo_owner, repo_name)
            if push_ok:
                return True, "Pushed existing commits"
            else:
                return False, f"Push failed: {push_err}"
        return False, f"Failed to commit: {commit_result.stderr}"

    # Push to remote with retry on auth failure
    push_ok, push_err = _push_with_retry(cwd, repo_owner, repo_name)

    if push_ok:
        return True, f"Committed and pushed {len(files_to_commit)} file(s)"
    else:
        return False, f"Push failed: {push_err}"


def run_agentic_e2e_fix_orchestrator(
    issue_url: str,
    issue_content: str,
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    issue_author: str,
    issue_title: str,
    *,
    cwd: Path,
    timeout_adder: float = 0.0,
    max_cycles: int = 5,
    resume: bool = True,
    verbose: bool = False,
    quiet: bool = False,
    use_github_state: bool = True,
    protect_tests: bool = False,
    ci_retries: int = 3,
    skip_ci: bool = False,
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Orchestrator for the 10-step agentic e2e fix workflow.
    
    Returns:
        Tuple[bool, str, float, str, List[str]]: 
        (success, final_message, total_cost, model_used, changed_files)
    """
    state_dir = _get_state_dir(cwd)
    workflow_name = "e2e_fix"
    
    # Initialize state variables
    current_cycle = 0
    last_completed_step = 0
    step_outputs: Dict[str, str] = {}
    total_cost = 0.0
    model_used = "unknown"
    changed_files: List[str] = []
    dev_unit_states: Dict[str, Any] = {}
    skipped_steps: Dict[int, str] = {}
    github_comment_id: Optional[int] = None
    
    # Resume Logic
    if resume:
        loaded_state, gh_id = load_workflow_state(
            cwd, issue_number, workflow_name, state_dir, repo_owner, repo_name, use_github_state
        )
        if loaded_state:
            console.print(f"[blue]Resuming from cycle {loaded_state.get('current_cycle', 1)} step {loaded_state.get('last_completed_step', 0)}...[/blue]")
            current_cycle = loaded_state.get("current_cycle", 0)
            last_completed_step = loaded_state.get("last_completed_step", 0)
            step_outputs = loaded_state.get("step_outputs", {})
            total_cost = loaded_state.get("total_cost", 0.0)
            model_used = loaded_state.get("model_used", "unknown")
            changed_files = loaded_state.get("changed_files", [])
            dev_unit_states = loaded_state.get("dev_unit_states", {})
            # Load skipped_steps from state (keys are strings in JSON, convert to int)
            skipped_steps_raw = loaded_state.get("skipped_steps", {})
            skipped_steps = {int(k): v for k, v in skipped_steps_raw.items()}
            github_comment_id = gh_id

            # Issue #467: Validate cached state — correct last_completed_step
            # if any cached step outputs have "FAILED:" prefix.
            last_completed_step = validate_cached_state(
                last_completed_step, step_outputs, quiet=quiet
            )

            _check_staleness(loaded_state, cwd)

            # If we finished a cycle but didn't exit, prepare for next cycle
            if last_completed_step >= 9:
                current_cycle += 1
                last_completed_step = 0
                step_outputs = {} # Clear outputs for new cycle
        else:
            # No state found, start fresh
            clear_workflow_state(cwd, issue_number, workflow_name, state_dir, repo_owner, repo_name, use_github_state)
    else:
        clear_workflow_state(cwd, issue_number, workflow_name, state_dir, repo_owner, repo_name, use_github_state)

    console.print(f"Fixing e2e tests for issue #{issue_number}: \"{issue_title}\"")

    # Reuse pdd-bug analysis if available (Issue #830: skip redundant diagnosis)
    # Load the bug workflow state to check if Steps 2-3 were already analyzed.
    # Search common state locations for the bug workflow state file.
    bug_step_outputs: Dict[str, str] = {}
    _bug_state_candidates = [
        state_dir / f"bug_state_{issue_number}.json",
        cwd / ".pdd" / "state" / f"bug_state_{issue_number}.json",
        cwd / ".pdd" / "bug-state" / f"bug_state_{issue_number}.json",
    ]
    for bug_state_file in _bug_state_candidates:
        if bug_state_file.exists():
            try:
                with open(bug_state_file, "r") as f:
                    bug_state = json.load(f)
                bug_outputs = bug_state.get("step_outputs", {})
                # Reuse step 2 and 3 outputs if they completed successfully
                for s in ("2", "3"):
                    if s in bug_outputs and not bug_outputs[s].startswith("FAILED:"):
                        bug_step_outputs[s] = bug_outputs[s]
                if bug_step_outputs:
                    console.print(f"[blue]Reusing pdd-bug analysis for steps {', '.join(sorted(bug_step_outputs.keys()))}[/blue]")
                    # Pre-populate step_outputs so subsequent steps can reference them
                    for s, output in bug_step_outputs.items():
                        if s not in step_outputs:
                            step_outputs[s] = output
                break
            except (OSError, json.JSONDecodeError, KeyError) as e:
                console.print(f"[dim]Warning: Could not load bug state from {bug_state_file}: {e}[/dim]")
                continue  # Try next candidate

    # Snapshot file state before workflow (for hash-based commit detection)
    initial_file_hashes = _get_file_hashes(cwd)

    success = False
    final_message = ""
    consecutive_provider_failures = 0

    try:
        # Outer Loop
        if current_cycle == 0:
            current_cycle = 1
        
        while current_cycle <= max_cycles:
            console.print(f"\n[bold cyan][Cycle {current_cycle}/{max_cycles}] Starting fix cycle...[/bold cyan]")
            
            # Inner Loop (Steps 1-9)
            for step_num in range(1, 10):
                if step_num <= last_completed_step:
                    continue # Skip already completed steps in this cycle

                # Skip steps that failed for environmental/timeout reasons in previous cycles
                if step_num in skipped_steps:
                    skip_reason = skipped_steps[step_num]
                    console.print(f"[bold][Step {step_num}/9] Skipped (remembered): {skip_reason}[/bold]")
                    step_outputs[str(step_num)] = f"E2E_SKIP: {skip_reason}"
                    last_completed_step = step_num

                    # Early exit: Step 1 ALL_TESTS_PASS + Step 2 skipped (via skipped_steps)
                    if step_num == 2:
                        step1_token = _classify_step_output(step_outputs.get("1", ""), step_num=1)
                        if step1_token in ("ALL_TESTS_PASS", "LOCAL_TESTS_PASS"):
                            test_files = _extract_test_files(issue_content, changed_files, cwd, initial_file_hashes)
                            if test_files:
                                verified, _ = _verify_tests_independently(test_files, cwd)
                                if verified:
                                    console.print("[green]ALL_TESTS_PASS (Step 1) verified — Step 2 skipped. Exiting early.[/green]")
                                    success = True
                                    final_message = "All tests passed (Step 1 verified, Step 2 skipped)."
                                    break
                            else:
                                console.print("[green]ALL_TESTS_PASS (Step 1) — Step 2 skipped, no test files for verification. Exiting early.[/green]")
                                success = True
                                final_message = "All tests passed (Step 1, Step 2 skipped)."
                                break

                    continue

                # Skip redundant diagnosis steps when pdd-bug already analyzed (Issue #830)
                if str(step_num) in bug_step_outputs and current_cycle == 1:
                    console.print(f"[bold][Step {step_num}/9] Reusing pdd-bug analysis[/bold]")
                    last_completed_step = step_num
                    continue

                step_name = STEP_NAMES[step_num]
                description = STEP_DESCRIPTIONS[step_num]

                # Pre-flight check for Step 2 (E2E tests)
                if step_num == 2:
                    e2e_available, e2e_reason = _check_e2e_environment(cwd)
                    if not e2e_available:
                        console.print(f"[bold][Step 2/9] E2E test skipped: {e2e_reason}[/bold]")
                        step_outputs[str(step_num)] = f"E2E_SKIP: {e2e_reason}"
                        skipped_steps[step_num] = e2e_reason
                        last_completed_step = step_num

                        # Early exit: Step 1 ALL_TESTS_PASS + Step 2 skipped (first time)
                        step1_token = _classify_step_output(step_outputs.get("1", ""), step_num=1)
                        if step1_token in ("ALL_TESTS_PASS", "LOCAL_TESTS_PASS"):
                            test_files = _extract_test_files(issue_content, changed_files, cwd, initial_file_hashes)
                            if test_files:
                                verified, _ = _verify_tests_independently(test_files, cwd)
                                if verified:
                                    console.print("[green]ALL_TESTS_PASS (Step 1) verified — Step 2 skipped. Exiting early.[/green]")
                                    success = True
                                    final_message = "All tests passed (Step 1 verified, Step 2 skipped)."
                                    break
                            else:
                                console.print("[green]ALL_TESTS_PASS (Step 1) — Step 2 skipped, no test files for verification. Exiting early.[/green]")
                                success = True
                                final_message = "All tests passed (Step 1, Step 2 skipped)."
                                break

                        continue

                console.print(f"[bold][Step {step_num}/9] {description}...[/bold]")

                # 1. Load Prompt
                template_name = f"agentic_e2e_fix_step{step_num}_{step_name}_LLM"
                prompt_template = load_prompt_template(template_name)
                if not prompt_template:
                    raise ValueError(f"Could not load prompt template: {template_name}")

                # 2. Prepare Context
                context = {
                    "issue_url": issue_url,
                    "repo_owner": repo_owner,
                    "repo_name": repo_name,
                    "issue_number": issue_number,
                    "cycle_number": current_cycle,
                    "max_cycles": max_cycles,
                    "issue_content": issue_content,
                    "protect_tests": "true" if protect_tests else "false",
                    "protect_tests_flag": "--protect-tests" if protect_tests else "",
                    "ci_retries": ci_retries,
                    "skip_ci": "true" if skip_ci else "false",
                }
                
                # Add previous step outputs
                for prev_step in range(1, step_num):
                    key = f"step{prev_step}_output"
                    context[key] = step_outputs.get(str(prev_step), "")

                # Derived variables for specific steps
                if step_num >= 6:
                    s5_out = step_outputs.get("5", "")
                    context["dev_units_identified"] = _parse_dev_units(s5_out)
                
                if step_num == 8:
                    s5_out = step_outputs.get("5", "")
                    context["failing_dev_units"] = _parse_dev_units(s5_out)

                if step_num == 9:
                    context["next_cycle"] = current_cycle + 1

                # Preprocess to escape curly braces in included content
                exclude_keys = list(context.keys())
                prompt_template = preprocess(prompt_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys)
                # Safe substitution (Issue #549): un-double template braces first, then substitute.
                prompt_template = prompt_template.replace("{{", "{").replace("}}", "}")
                formatted_prompt = prompt_template
                for key, value in context.items():
                    formatted_prompt = formatted_prompt.replace(f'{{{key}}}', str(value))

                # Append E2E_SKIP context for steps following skipped steps
                for prev_step in range(1, step_num):
                    prev_output = step_outputs.get(str(prev_step), "")
                    if prev_output.startswith("E2E_SKIP:"):
                        formatted_prompt += f"\n\nNote: Step {prev_step} was skipped — {prev_output}"

                # 3. Run Task
                base_timeout = E2E_FIX_STEP_TIMEOUTS.get(step_num, 340.0)
                timeout = base_timeout + timeout_adder

                step_success, step_output, step_cost, step_model = run_agentic_task(
                    instruction=formatted_prompt,
                    cwd=cwd,
                    verbose=verbose,
                    quiet=quiet,
                    timeout=timeout,
                    label=f"cycle{current_cycle}_step{step_num}",
                    max_retries=DEFAULT_MAX_RETRIES,
                )

                # Step 1 timeout retry: retry once with increased timeout
                # before falling through to diagnostic steps (Issue #830)
                if (
                    step_num == 1
                    and not step_success
                    and "Timeout" in step_output
                ):
                    console.print("[yellow]Step 1 timed out. Retrying with extended timeout...[/yellow]")
                    retry_timeout = timeout * 1.5
                    step_success, step_output, retry_cost, step_model = run_agentic_task(
                        instruction=formatted_prompt,
                        cwd=cwd,
                        verbose=verbose,
                        quiet=quiet,
                        timeout=retry_timeout,
                        label=f"cycle{current_cycle}_step{step_num}_retry1",
                        max_retries=DEFAULT_MAX_RETRIES,
                    )
                    step_cost += retry_cost

                # 4. Store Output & Accumulate
                # Only mark step completed if it succeeded; failed steps get "FAILED:" prefix
                # and last_completed_step stays at previous step (ensures resume re-runs failed step)
                if step_success:
                    step_outputs[str(step_num)] = step_output
                    last_completed_step = step_num
                else:
                    step_outputs[str(step_num)] = f"FAILED: {step_output}"
                    # Don't update last_completed_step - keep it at previous value

                    # Convert Step 2 timeout failures to skipped_steps so they
                    # are not retried on subsequent cycles (Issue #791).
                    # Only trigger on timeout-specific errors — transient provider
                    # outages (rate limits, etc.) should still be retried.
                    if (
                        step_num == 2
                        and "All agent providers failed" in step_output
                        and ("Timeout" in step_output or "timed out" in step_output)
                    ):
                        skipped_steps[step_num] = step_output

                total_cost += step_cost
                model_used = step_model if step_model else model_used

                # Parse changed files
                new_files = _parse_changed_files(step_output)
                for f in new_files:
                    if f not in changed_files:
                        changed_files.append(f)

                # Parse dev unit states (Step 8)
                if step_num == 8:
                    s5_out = step_outputs.get("5", "")
                    dev_units_str = _parse_dev_units(s5_out)
                    dev_unit_states = _update_dev_unit_states(step_output, dev_unit_states, dev_units_str)

                # Print brief result
                if step_success:
                    consecutive_provider_failures = 0
                    console.print(f"  -> Step {step_num} complete. Cost: ${step_cost:.4f}")
                else:
                    console.print(f"  -> Step {step_num} [red]failed[/red]. Cost: ${step_cost:.4f}")

                    # Track consecutive provider failures for early abort
                    if "All agent providers failed" in step_output:
                        consecutive_provider_failures += 1
                        if consecutive_provider_failures >= 3:
                            console.print(f"[bold red]Aborting: {consecutive_provider_failures} consecutive steps failed — agent providers unavailable[/bold red]")
                            return False, f"Aborting: {consecutive_provider_failures} consecutive steps failed — agent providers unavailable", total_cost, model_used, changed_files
                    else:
                        consecutive_provider_failures = 0

                # 5. Save State
                state_data = {
                    "workflow": workflow_name,
                    "issue_url": issue_url,
                    "issue_number": issue_number,
                    "current_cycle": current_cycle,
                    "last_completed_step": last_completed_step,
                    "step_outputs": step_outputs.copy(),  # Copy to avoid shared reference
                    "dev_unit_states": dev_unit_states.copy(),  # Copy to avoid shared reference
                    "total_cost": total_cost,
                    "model_used": model_used,
                    "changed_files": changed_files.copy(),  # Copy to avoid shared reference
                    "skipped_steps": {str(k): v for k, v in skipped_steps.items()},
                    "last_saved_at": datetime.now().isoformat(),
                    "github_comment_id": github_comment_id
                }
                
                new_gh_id = save_workflow_state(
                    cwd, issue_number, workflow_name, state_data, state_dir, repo_owner, repo_name, use_github_state, github_comment_id
                )
                if new_gh_id:
                    github_comment_id = new_gh_id

                # Check Early Exit (Step 2): ALL_TESTS_PASS
                _step2_token = _classify_step_output(step_output, step_num=2) if step_num == 2 else None
                if step_num == 2 and _step2_token in ("ALL_TESTS_PASS", "LOCAL_TESTS_PASS"):
                    # Independent verification: don't trust LLM output alone
                    test_files = _extract_test_files(issue_content, changed_files, cwd, initial_file_hashes)
                    if test_files:
                        verified, verify_output = _verify_tests_independently(test_files, cwd)
                        if verified:
                            console.print("[green]ALL_TESTS_PASS verified by independent pytest run.[/green]")
                            success = True
                            final_message = "All tests passed (independently verified)."
                            break
                        else:
                            console.print("[bold red]LLM claimed ALL_TESTS_PASS but independent verification FAILED.[/bold red]")
                            step_output = f"VERIFICATION_FAILED: LLM claimed ALL_TESTS_PASS but pytest failed.\n{verify_output}"
                            step_outputs[str(step_num)] = f"FAILED: {step_output}"
                            last_completed_step = step_num - 1
                    else:
                        console.print("[yellow]No test files found for independent verification. Trusting LLM output.[/yellow]")
                        success = True
                        final_message = "All tests passed during e2e check (no independent verification)."
                        break

                # Check Early Exit (Step 3): NOT_A_BUG
                _step3_token = _classify_step_output(step_output, step_num=3) if step_num == 3 else None
                if not _step3_token and step_num == 3:
                    # Tier 4: LLM classification fallback — only ask about NOT_A_BUG
                    # to avoid false positives (e.g., CODE_BUG being misclassified)
                    tier4 = classify_step_output(step_output, ["NOT_A_BUG"])
                    if tier4:
                        console.print("[yellow]NOT_A_BUG detected via LLM classification (tier 4)[/yellow]")
                        _step3_token = "NOT_A_BUG"
                if step_num == 3 and _step3_token == "NOT_A_BUG":
                    # Block NOT_A_BUG if fixes were already applied in prior cycles
                    has_fixed_units = any(s.get("fixed") for s in dev_unit_states.values())
                    if has_fixed_units:
                        console.print("[yellow]NOT_A_BUG ignored — fixes were already applied in prior cycles.[/yellow]")
                    else:
                        console.print("[yellow]NOT_A_BUG detected in Step 3. Issue is not a bug, stopping workflow.[/yellow]")
                        success = False
                        final_message = "Issue determined to be not a bug."
                        break

                # Check Loop Control (Step 9)
                if step_num == 9:
                    _step9_token = _classify_step_output(step_output, step_num=9)
                    if not _step9_token:
                        # Tier 4: LLM classification fallback
                        tier4 = classify_step_output(
                            step_output, ["ALL_TESTS_PASS", "CONTINUE_CYCLE", "MAX_CYCLES_REACHED"]
                        )
                        if tier4:
                            console.print("[yellow]Loop control token detected via LLM classification (tier 4)[/yellow]")
                            _step9_token = "CONTINUE_CYCLE"  # Safe default: keep cycling
                    if _step9_token in ("ALL_TESTS_PASS", "LOCAL_TESTS_PASS"):
                        # Independent verification: don't trust LLM output alone
                        test_files = _extract_test_files(issue_content, changed_files, cwd, initial_file_hashes)
                        if test_files:
                            verified, verify_output = _verify_tests_independently(test_files, cwd)
                            if verified:
                                console.print("[green]LOCAL_TESTS_PASS verified by independent pytest run (Step 9).[/green]")
                                success = True
                                final_message = "All tests passed after fixes (independently verified)."
                                break
                            else:
                                console.print("[bold red]LLM claimed tests pass at Step 9 but independent verification FAILED.[/bold red]")
                                step_output = f"VERIFICATION_FAILED: LLM claimed tests pass but pytest failed.\n{verify_output}"
                                step_outputs[str(step_num)] = f"FAILED: {step_output}"
                                last_completed_step = step_num - 1
                                # Don't break — fall through to cycle increment
                        else:
                            console.print("[green]LOCAL_TESTS_PASS detected in Step 9.[/green]")
                            success = True
                            final_message = "All tests passed after fixes."
                            break
                    elif _step9_token == "MAX_CYCLES_REACHED":
                        console.print("[yellow]MAX_CYCLES_REACHED detected in Step 9.[/yellow]")
                        final_message = "Max cycles reached."
                        break
                    elif _step9_token == "CONTINUE_CYCLE":
                        break  # Break inner loop — outer loop will start next cycle
                    else:
                        console.print("[yellow]Warning: No loop control token found in Step 9. Stopping workflow — missing token treated as terminal condition.[/yellow]")
                        final_message = "Workflow stopped: no loop control token in Step 9 output."
                        break

            # Check if we should exit the outer loop
            if success:
                break

            # Check if NOT_A_BUG was detected (exit outer loop too)
            has_fixed_units = any(s.get("fixed") for s in dev_unit_states.values())
            if step_num == 3 and _classify_step_output(step_outputs.get("3", ""), step_num=3) == "NOT_A_BUG" and not has_fixed_units:
                break

            # Check if workflow was stopped due to missing loop control token or max cycles
            if final_message:
                break
            
            # Prepare for next cycle
            current_cycle += 1
            last_completed_step = 0
            step_outputs = {} # Clear outputs for next cycle
            
            state_data["current_cycle"] = current_cycle
            state_data["last_completed_step"] = 0
            state_data["step_outputs"] = {}
            state_data["last_saved_at"] = datetime.now().isoformat()
            
            if current_cycle <= max_cycles:
                 save_workflow_state(
                    cwd, issue_number, workflow_name, state_data, state_dir, repo_owner, repo_name, use_github_state, github_comment_id
                )

        if success:
            # Detect actual file changes via hash comparison (not LLM output parsing)
            # This fixes issue #355: summary showing empty "Files changed" despite
            # real modifications, especially on early exit at Step 2.
            actual_changed_files = _detect_changed_files(cwd, initial_file_hashes)
            if actual_changed_files:
                changed_files = actual_changed_files

            console.print("\n[bold green]E2E fix complete[/bold green]")
            console.print(f"   Total cost: ${total_cost:.4f}")
            console.print(f"   Cycles used: {current_cycle if current_cycle <= max_cycles else max_cycles}/{max_cycles}")
            console.print(f"   Files changed: {', '.join(changed_files)}")
            fixed_units = [u for u, s in dev_unit_states.items() if s.get("fixed")]
            console.print(f"   Dev units fixed: {', '.join(fixed_units)}")

            # Commit and push changes to update the existing PR
            commit_success, commit_message = _commit_and_push(
                cwd=cwd,
                issue_number=issue_number,
                issue_title=issue_title,
                repo_owner=repo_owner,
                repo_name=repo_name,
                initial_file_hashes=initial_file_hashes,
                quiet=quiet
            )
            if commit_success:
                console.print(f"   [green]{commit_message}[/green]")
            else:
                console.print(f"   [yellow]Warning: {commit_message}[/yellow]")
                return False, final_message, total_cost, model_used, changed_files

            if skip_ci:
                if not quiet:
                    console.print("[yellow]Skipping CI validation (--skip-ci)[/yellow]")
                clear_workflow_state(cwd, issue_number, workflow_name, state_dir, repo_owner, repo_name, use_github_state)
                return True, final_message, total_cost, model_used, changed_files

            step10_template = load_prompt_template("agentic_e2e_fix_step10_ci_validation_LLM")
            if not step10_template:
                return False, "Could not load prompt template: agentic_e2e_fix_step10_ci_validation_LLM", total_cost, model_used, changed_files

            ci_success, ci_message, ci_cost = run_ci_validation_loop(
                cwd=cwd,
                repo_owner=repo_owner,
                repo_name=repo_name,
                issue_number=issue_number,
                max_retries=ci_retries,
                step_template=step10_template,
                run_agentic_task_fn=run_agentic_task,
                timeout=E2E_FIX_STEP_TIMEOUTS[10] + timeout_adder,
                quiet=quiet,
            )
            total_cost += ci_cost
            changed_files = _detect_changed_files(cwd, initial_file_hashes) or changed_files
            if ci_success:
                if ci_message not in {
                    "No open PR found for current branch; skipping CI validation",
                    "No CI checks detected",
                }:
                    final_message = ci_message
                clear_workflow_state(cwd, issue_number, workflow_name, state_dir, repo_owner, repo_name, use_github_state)
                return True, final_message, total_cost, model_used, changed_files

            return False, ci_message, total_cost, model_used, changed_files
        else:
            if not final_message:
                final_message = f"Max cycles ({max_cycles}) reached without all tests passing"
            if "not a bug" in final_message.lower():
                console.print(f"\n[bold yellow]E2E fix stopped: not a bug[/bold yellow]")
            else:
                console.print(f"\n[bold red]E2E fix incomplete[/bold red]")
            console.print(f"   Total cost: ${total_cost:.4f}")
            remaining = [u for u, s in dev_unit_states.items() if not s.get("fixed")]
            if remaining:
                console.print(f"   Remaining failures: {', '.join(remaining)}")

            # Post final status comment to GitHub so users see why the workflow stopped
            post_final_comment(
                repo_owner=repo_owner,
                repo_name=repo_name,
                issue_number=issue_number,
                reason=final_message,
                total_cost=total_cost,
                steps_completed=last_completed_step or step_num,
                total_steps=10,
                cwd=cwd,
            )

            return False, final_message, total_cost, model_used, changed_files

    except KeyboardInterrupt:
        console.print("\n[bold red]Interrupted by user. Saving state...[/bold red]")
        state_data = {
            "workflow": workflow_name,
            "issue_url": issue_url,
            "issue_number": issue_number,
            "current_cycle": current_cycle,
            "last_completed_step": last_completed_step,
            "step_outputs": step_outputs,
            "dev_unit_states": dev_unit_states,
            "skipped_steps": {str(k): v for k, v in skipped_steps.items()},
            "total_cost": total_cost,
            "model_used": model_used,
            "changed_files": changed_files,
            "last_saved_at": datetime.now().isoformat(),
            "github_comment_id": github_comment_id
        }
        save_workflow_state(
            cwd, issue_number, workflow_name, state_data, state_dir, repo_owner, repo_name, use_github_state, github_comment_id
        )
        raise

    except Exception as e:
        console.print(f"\n[bold red]Fatal error: {e}[/bold red]")
        try:
            state_data = {
                "workflow": workflow_name,
                "issue_url": issue_url,
                "issue_number": issue_number,
                "current_cycle": current_cycle,
                "last_completed_step": last_completed_step,
                "step_outputs": step_outputs,
                "dev_unit_states": dev_unit_states,
                "skipped_steps": {str(k): v for k, v in skipped_steps.items()},
                "total_cost": total_cost,
                "model_used": model_used,
                "changed_files": changed_files,
                "last_saved_at": datetime.now().isoformat(),
                "github_comment_id": github_comment_id
            }
            save_workflow_state(
                cwd, issue_number, workflow_name, state_data, state_dir, repo_owner, repo_name, use_github_state, github_comment_id
            )
        except Exception:
            pass
        return False, f"Stopped at cycle {current_cycle} step {last_completed_step}: {str(e)}", total_cost, model_used, changed_files
