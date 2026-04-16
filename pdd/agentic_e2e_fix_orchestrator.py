from __future__ import annotations

import hashlib
import logging
import os
import shlex
import shutil
import subprocess
import sys
import time
import json
from datetime import datetime
from pathlib import Path
from typing import List, Tuple, Dict, Any, Optional, Set, NamedTuple

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
    GITHUB_STATE_MARKER_START,
    GITHUB_STATE_MARKER_END,
    _revert_out_of_scope_changes,
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
    10: "ci_validation",
    11: "code_cleanup",
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
    10: "CI validation and remediation",
    11: "Code cleanup",
}

# Per-step timeouts for the 11-step agentic e2e fix workflow
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
    11: 600.0,  # Code cleanup pass
}

# Maximum wall-clock seconds for _verify_tests_independently.
# Checked before starting each file, so actual runtime may overshoot by the
# duration of the last file executed.  Module-level so tests can monkeypatch.
# See Issues #953, #1010, #1031 for history of fallback-scan stalls.
VERIFY_TIMEOUT_SECONDS = 600

# Maximum number of test files the fallback directory scan in _extract_test_files
# may return.  Prevents runaway verification when targeted discovery fails and
# the scan finds hundreds of files.  See Issue #1010.
MAX_FALLBACK_TEST_FILES = 20

# Set by _extract_test_files when the fallback scan exceeds MAX_FALLBACK_TEST_FILES.
# Callers check this after verification to avoid treating a partial run as
# authoritative success (see PR #1162 review).
_fallback_scan_was_capped = False

console = Console()
logger = logging.getLogger(__name__)

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


# Patterns that indicate "code not written / can't load" rather than "code wrong".
# Used by _classify_verification_failure as deterministic detection.
# All patterns anchored to pytest ^E traceback format to avoid false positives
# from log lines, print statements, or assertion messages.
# Since _verify_tests_independently runs pytest, all exceptions surface as ^E lines.
_IMPORT_ERROR_PATTERNS = [
    # Python — pytest ^E traceback format only
    _re.compile(r"^E\s+ImportError:", _re.MULTILINE),
    _re.compile(r"^E\s+ModuleNotFoundError:", _re.MULTILINE),
    _re.compile(r"^E\s+NameError:", _re.MULTILINE),
    _re.compile(r"^E\s+AttributeError:", _re.MULTILINE),
    _re.compile(r"^E\s+SyntaxError:", _re.MULTILINE),
    # JS/TS — pytest ^E format or test runner line-start errors
    _re.compile(r"^E\s+Cannot find module", _re.MULTILINE),
    _re.compile(r"^E\s+Module not found", _re.MULTILINE),
    _re.compile(r"^E\s+ReferenceError:", _re.MULTILINE),
    # Test runner unavailable (from _verify_tests_independently itself)
    _re.compile(r"FAILED \(no test runner available\)"),
]


def _classify_verification_failure(output: str) -> str:
    """Classify verification failure via deterministic pattern matching.

    Checks for common error signatures (ImportError, ModuleNotFoundError,
    NameError, etc.) that indicate code was not written or can't compile.
    Unrecognized patterns default to test_failure (conservative — no LLM call).

    Returns:
        'import_error' if code was not written, can't compile, or fails to load.
        'test_failure' if code exists and loads but produces wrong results.
    """
    for pattern in _IMPORT_ERROR_PATTERNS:
        if pattern.search(output):
            return "import_error"

    return "test_failure"


def _handle_verification_failure(
    verify_output: str,
    import_error_retries: int,
    console: "Console",
) -> Tuple[str, int, bool]:
    """Classify verification failure and determine retry action.

    Centralizes the classify-then-retry logic used at all 4 verification
    call sites. Returns whether the caller should retry from Step 1.

    Args:
        verify_output: Raw output from _verify_tests_independently.
        import_error_retries: Global retry count (max 1 across all cycles).
        console: Rich Console for logging.

    Returns:
        (failure_type, updated_import_error_retries, should_retry)
        should_retry is True if caller should set last_completed_step=0 and break.
    """
    failure_type = _classify_verification_failure(verify_output)
    if failure_type == "import_error" and import_error_retries < 1:
        console.print("[yellow][VERIFICATION] Failure classified as import_error — retrying from Step 1[/yellow]")
        return failure_type, import_error_retries + 1, True
    console.print(f"[yellow][VERIFICATION] Failure classified as {failure_type} — proceeding with fallback workflow[/yellow]")
    return failure_type, import_error_retries, False


def _resolve_step9_loop_token(step_output: str, console: Console) -> Optional[str]:
    """Resolve Step 9 loop-control token (tiers 1–3 + tier-4 fallback).

    Maps ALL_TESTS_PASS at step 9 to LOCAL_TESTS_PASS for downstream handling.
    Tier-4 CLASSIFICATION_ERROR is treated as CONTINUE_CYCLE (transient classifier).
    """
    tok = _classify_step_output(step_output, step_num=9)
    if tok:
        return tok
    tier4 = classify_step_output(
        step_output, ["ALL_TESTS_PASS", "CONTINUE_CYCLE", "MAX_CYCLES_REACHED"]
    )
    if tier4 and tier4.token in ("ALL_TESTS_PASS", "CONTINUE_CYCLE", "MAX_CYCLES_REACHED"):
        console.print(
            "[yellow]Loop control token detected via LLM classification (tier 4)[/yellow]"
        )
        return "LOCAL_TESTS_PASS" if tier4.token == "ALL_TESTS_PASS" else tier4.token
    if tier4 and tier4.token == "CLASSIFICATION_ERROR":
        console.print(
            "[yellow]Step 9 classification unavailable (tier 4 error); "
            "starting next cycle.[/yellow]"
        )
        return "CONTINUE_CYCLE"
    return None


class _Step9TokenApplyResult(NamedTuple):
    """Outcome of applying a resolved Step 9 loop token (shared initial + retry paths)."""

    break_inner: bool
    import_error_retries: int
    success: Optional[bool] = None
    final_message: Optional[str] = None
    last_completed_step: Optional[int] = None
    step_outputs_9: Optional[str] = None
    verification_failure_context_update: Optional[str] = None  # None = no change; str = set


def _apply_step9_resolved_token(
    resolved_token: str,
    step_output: str,
    *,
    issue_content: str,
    changed_files: List[str],
    cwd: Path,
    initial_file_hashes: Dict[str, Optional[str]],
    cycle_start_hashes: Dict[str, Optional[str]],
    import_error_retries: int,
    console: Console,
    step_num: int,
    current_cycle: int,
    is_retry_path: bool = False,
) -> _Step9TokenApplyResult:
    """Handle ALL_TESTS_PASS verification, MAX_CYCLES_REACHED, CONTINUE_CYCLE (+ hash guard).

    Single implementation for the primary Step 9 path and the one-shot Step 9 retry
    so verification and convergence logic cannot diverge.
    """
    tag = "Step 9 retry" if is_retry_path else "Step 9"

    if resolved_token in ("ALL_TESTS_PASS", "LOCAL_TESTS_PASS"):
        test_files = _extract_test_files(issue_content, changed_files, cwd, initial_file_hashes)
        if test_files:
            verified, verify_output = _verify_tests_independently(test_files, cwd)
            if _fallback_scan_was_capped and verified:
                verified = False
                verify_output += (
                    f"\nFALLBACK_CAPPED: Only {len(test_files)} of potentially "
                    "hundreds of test files were verified; cannot confirm full suite pass."
                )
            if verified:
                console.print(
                    f"[green]LOCAL_TESTS_PASS verified by independent pytest run ({tag}).[/green]"
                )
                return _Step9TokenApplyResult(
                    break_inner=True,
                    import_error_retries=import_error_retries,
                    success=True,
                    final_message="All tests passed after fixes (independently verified).",
                )
            console.print(
                f"[bold red]LLM claimed tests pass at {tag} but independent "
                "verification FAILED.[/bold red]"
            )
            _, new_retries, should_retry = _handle_verification_failure(
                verify_output, import_error_retries, console
            )
            failed_body = (
                f"VERIFICATION_FAILED: LLM claimed tests pass but pytest failed.\n{verify_output}"
            )
            full_failed = f"FAILED: {failed_body}"
            if should_retry:
                return _Step9TokenApplyResult(
                    break_inner=True,
                    import_error_retries=new_retries,
                    step_outputs_9=full_failed,
                    verification_failure_context_update=verify_output,
                    last_completed_step=0,
                )
            return _Step9TokenApplyResult(
                break_inner=False,
                import_error_retries=new_retries,
                step_outputs_9=full_failed,
                last_completed_step=step_num - 1,
            )
        console.print(f"[green]LOCAL_TESTS_PASS detected in {tag}.[/green]")
        return _Step9TokenApplyResult(
            break_inner=True,
            import_error_retries=import_error_retries,
            success=True,
            final_message="All tests passed after fixes.",
        )

    if resolved_token == "MAX_CYCLES_REACHED":
        console.print(f"[yellow]MAX_CYCLES_REACHED detected in {tag}.[/yellow]")
        return _Step9TokenApplyResult(
            break_inner=True,
            import_error_retries=import_error_retries,
            final_message="Max cycles reached.",
        )

    if resolved_token == "CONTINUE_CYCLE":
        cycle_changed = _detect_changed_files(cwd, cycle_start_hashes)
        if not cycle_changed:
            console.print(
                f"[yellow]Warning: No file changes detected in cycle {current_cycle}. "
                "Stopping to avoid infinite loop.[/yellow]"
            )
            return _Step9TokenApplyResult(
                break_inner=True,
                import_error_retries=import_error_retries,
                final_message=f"No progress made in cycle {current_cycle} (no file changes).",
            )
        return _Step9TokenApplyResult(
            break_inner=True,
            import_error_retries=import_error_retries,
        )

    console.print(
        "[yellow]Warning: No recognized loop control token found in Step 9. "
        "Stopping workflow — missing or unknown token treated as terminal "
        "condition.[/yellow]"
    )
    return _Step9TokenApplyResult(
        break_inner=True,
        import_error_retries=import_error_retries,
        final_message="Workflow stopped: no recognized loop control token in Step 9 output.",
    )


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

def _parse_dev_units(output: str) -> Optional[str]:
    """Parses DEV_UNITS_IDENTIFIED from output.
    
    Returns:
        None if the marker is absent from the output.
        "" if the marker is present but empty.
        The content after the marker if present and non-empty.
    """
    for line in output.splitlines():
        if line.startswith("DEV_UNITS_IDENTIFIED:"):
            return line.split(":", 1)[1].strip()
    return None

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


def _extract_marker_files(text: str) -> List[str]:
    """Extract test file paths from E2E_FILES_CREATED/FILES_CREATED markers in text.

    Scans each line for marker prefixes. Returns raw paths (not deduplicated,
    not existence-checked) — the caller handles that via _add().
    """
    paths: List[str] = []
    for line in text.splitlines():
        for prefix in ("E2E_FILES_CREATED:", "FILES_CREATED:"):
            if line.strip().startswith(prefix):
                content = line.split(":", 1)[1].strip()
                for p in content.split(","):
                    p = p.strip()
                    if _is_test_file(p):
                        paths.append(p)
    return paths


def _extract_test_files(
    issue_content: str,
    changed_files: List[str],
    cwd: Path,
    initial_file_hashes: Optional[Dict[str, Optional[str]]] = None,
) -> List[str]:
    """Extract test file paths from issue content, changed files, and disk changes.

    Looks for:
    - E2E_FILES_CREATED: markers from pdd bug output
    - FILES_CREATED: markers (including inside PDD_WORKFLOW_STATE JSON)
    - File paths matching test conventions (Python test_*.py, Jest *.test.ts/tsx,
      Playwright *.spec.ts/tsx) in changed_files
    - Test files actually created/modified on disk (hash comparison)

    Returns only paths that exist on disk, deduplicated.

    Sets module-level ``_fallback_scan_was_capped`` to True when the ultimate
    fallback directory scan exceeds MAX_FALLBACK_TEST_FILES (callers must check
    this to avoid treating a capped partial run as authoritative success).
    """
    global _fallback_scan_was_capped
    _fallback_scan_was_capped = False

    test_files: List[str] = []
    seen: set = set()

    def _add(path: str) -> None:
        path = path.strip()
        if path and path not in seen and (cwd / path).exists():
            seen.add(path)
            test_files.append(path)

    # Parse markers from issue content (plain text lines)
    for p in _extract_marker_files(issue_content):
        _add(p)

    # Parse markers from PDD_WORKFLOW_STATE JSON comments (pdd-issue fresh-clone
    # context). In fresh-clone runs, step outputs are JSON-serialized inside
    # <!-- PDD_WORKFLOW_STATE:... --> HTML comments, turning embedded newlines
    # into \n escape sequences that splitlines() above cannot see. We find all
    # workflow state blocks, deserialize the JSON to restore real newlines, then
    # run the same marker parser on each step output value.
    # This is safe from issue #633 false positives because it only parses
    # structured workflow state data, not free-form narrative.
    marker_start = GITHUB_STATE_MARKER_START
    marker_end = GITHUB_STATE_MARKER_END
    search_start = 0
    while True:
        idx = issue_content.find(marker_start, search_start)
        if idx == -1:
            break
        # JSON begins after the first newline following the marker tag
        json_start = issue_content.find("\n", idx)
        if json_start == -1:
            break
        json_start += 1  # skip the newline itself
        end_idx = issue_content.find(marker_end, json_start)
        if end_idx == -1:
            break
        json_str = issue_content[json_start:end_idx].strip()
        search_start = end_idx + len(marker_end)
        try:
            state = json.loads(json_str)
        except (json.JSONDecodeError, ValueError):
            continue
        step_outputs = state.get("step_outputs", {})
        if not isinstance(step_outputs, dict):
            continue
        for value in step_outputs.values():
            if isinstance(value, str):
                for p in _extract_marker_files(value):
                    _add(p)

    # Include test files from changed_files list
    for f in changed_files:
        if _is_test_file(f):
            _add(f)

    # NOTE: Raw regex scan of issue content was removed (issue #633) because it
    # matched file paths mentioned as examples in narrative text. The JSON-aware
    # PDD_WORKFLOW_STATE parser above is safe: it only parses structured data.

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
    committed_files = _get_modified_and_untracked(cwd)
    for f in committed_files:
        basename = Path(f).name
        if basename.startswith("test_") and basename.endswith(".py"):
            _add(f)

    # Ultimate fallback: directory scan for test_*.py files on disk.
    # Only runs when NO discovery path found ANY files, to avoid
    # pulling the entire test suite into verification (slow + timeouts).
    # Scoped to tests/ dir (recursive) and root-level test_*.py (non-recursive).
    # Capped at MAX_FALLBACK_TEST_FILES to prevent runaway verification on
    # large repos (see Issues #953, #1010, #1031, #1155).
    if not test_files:
        candidates: List[str] = []
        scan_dirs = [cwd / "tests", cwd]
        for scan_dir in scan_dirs:
            if not scan_dir.is_dir():
                continue
            glob_fn = scan_dir.rglob if scan_dir != cwd else scan_dir.glob
            for test_py in glob_fn("test_*.py"):
                try:
                    rel = str(test_py.relative_to(cwd))
                except ValueError:
                    continue
                if any(part.startswith(".") or part == "__pycache__" for part in Path(rel).parts):
                    continue
                candidates.append(rel)

        # Sort by mtime descending so the cap keeps recently-modified files
        # (more likely relevant) rather than arbitrary alphabetical order.
        def _mtime(p: str) -> float:
            try:
                return (cwd / p).stat().st_mtime
            except OSError:
                return 0.0

        candidates.sort(key=_mtime, reverse=True)

        if len(candidates) > MAX_FALLBACK_TEST_FILES:
            _fallback_scan_was_capped = True
            console.print(
                f"[yellow]Fallback scan found {len(candidates)} test files, "
                f"capped at {MAX_FALLBACK_TEST_FILES} most recently modified; "
                f"targeted discovery failed.[/yellow]"
            )
            logger.warning(
                "Fallback scan capped at %d/%d test files",
                MAX_FALLBACK_TEST_FILES, len(candidates),
            )
            candidates = candidates[:MAX_FALLBACK_TEST_FILES]

        for rel in candidates:
            _add(rel)

    return test_files


def _verify_tests_independently(test_files: List[str], cwd: Path) -> Tuple[bool, str]:
    """Run appropriate test runner on test files via subprocess. Returns (all_passed, output).

    Dispatches the correct runner based on file extension:
    - .py → pytest via run_pytest_and_capture_output
    - Non-Python → resolved via get_test_command_for_file (e.g. npx jest, npx playwright)

    Caps total runtime at VERIFY_TIMEOUT_SECONDS to prevent runaway verification
    when the ultimate fallback in _extract_test_files discovers hundreds of files
    (e.g., shallow clone where git merge-base fails — see Issues #1010, #1155).
    """
    all_outputs: List[str] = []
    all_passed = True
    start_time = time.monotonic()

    for test_file in test_files:
        elapsed = time.monotonic() - start_time
        if elapsed >= VERIFY_TIMEOUT_SECONDS:
            all_passed = False
            all_outputs.append(
                f"TIMEOUT: Independent verification exceeded {VERIFY_TIMEOUT_SECONDS}s "
                f"after {len(all_outputs)} file(s); skipping remaining "
                f"{len(test_files) - len(all_outputs)} file(s)."
            )
            console.print(f"[yellow]Verification timeout after {elapsed:.0f}s — {len(all_outputs)} files checked[/yellow]")
            break

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

            effective_cwd = str(test_cmd.cwd) if test_cmd.cwd is not None else str(cwd)

            try:
                proc = subprocess.run(
                    shlex.split(test_cmd.command),
                    shell=False,
                    cwd=effective_cwd,
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
    try:
        result = subprocess.run(
            ["git", "diff", "--name-only", "HEAD"],
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=30,
        )
        if result.returncode == 0:
            files.update(f for f in result.stdout.strip().splitlines() if f)
    except subprocess.TimeoutExpired:
        console.print("[yellow]Warning: git diff timed out, continuing with partial results[/yellow]")

    # Get untracked files
    try:
        result = subprocess.run(
            ["git", "ls-files", "--others", "--exclude-standard"],
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=30,
        )
        if result.returncode == 0:
            files.update(f for f in result.stdout.strip().splitlines() if f)
    except subprocess.TimeoutExpired:
        console.print("[yellow]Warning: git ls-files timed out, continuing with partial results[/yellow]")

    # Get files committed on the feature branch (since diverging from base branch).
    # This catches test files committed during pdd bug that are neither uncommitted
    # nor untracked — they're committed and clean, but new relative to the base.
    # Try merge-base first (feature branch vs main/master), then fall back to
    # origin/ refs for shallow clones where local main/master don't exist (Issue #1010).
    for base in ("main", "master", "origin/main", "origin/master"):
        try:
            mb_result = subprocess.run(
                ["git", "merge-base", base, "HEAD"],
                cwd=cwd,
                capture_output=True,
                text=True,
                timeout=30,
            )
        except subprocess.TimeoutExpired:
            continue
        if mb_result.returncode == 0 and mb_result.stdout.strip():
            merge_base = mb_result.stdout.strip()
            try:
                result = subprocess.run(
                    ["git", "diff", "--name-only", merge_base, "HEAD"],
                    cwd=cwd,
                    capture_output=True,
                    text=True,
                    timeout=30,
                )
            except subprocess.TimeoutExpired:
                break
            if result.returncode == 0 and result.stdout.strip():
                files.update(f for f in result.stdout.strip().splitlines() if f)
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
    Pushes to remote, retrying on non-fast-forward or auth failure.

    On non-fast-forward error (branch diverged after rebase):
    - Retry with --force-with-lease, which safely overwrites the remote only
      if it hasn't changed since the last fetch.

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

    # Non-fast-forward: branch diverged (e.g. after rebase onto main).
    # Retry with --force-with-lease which is safe — it only overwrites
    # the remote if it matches what we last fetched.
    # Only match specific non-ff markers — avoid generic "[rejected]" which
    # could be protected branches, pre-receive hooks, etc.
    non_ff_markers = ["non-fast-forward", "tip of your current branch is behind"]
    is_non_fast_forward = any(marker in stderr for marker in non_ff_markers)

    if is_non_fast_forward:
        console.print(
            "[yellow]WARNING: Push rejected (non-fast-forward). "
            "Retrying with --force-with-lease...[/yellow]"
        )
        retry_result = subprocess.run(
            ["git", "push", "--force-with-lease", "-u", "origin", "HEAD"],
            cwd=cwd,
            capture_output=True,
            text=True
        )
        if retry_result.returncode == 0:
            return True, ""
        return False, retry_result.stderr

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


def _run_step11_code_cleanup(
    *,
    cwd: Path,
    issue_number: int,
    issue_content: str,
    issue_url: str = "",
    repo_owner: str = "",
    repo_name: str = "",
    initial_file_hashes: Dict[str, Optional[str]],
    initial_sha: str = "",
    total_cost: float,
    changed_files: List[str],
    timeout_adder: float,
    verbose: bool,
    quiet: bool,
) -> Tuple[float, List[str]]:
    """Run Step 11: Code cleanup before CI validation.

    Collects the full diff and changed file contents, invokes the cleanup LLM,
    re-runs tests to verify, and commits as a separate commit if tests pass.
    Reverts all cleanup changes if tests fail.

    Args:
        cwd: Working directory.
        issue_number: GitHub issue number.
        issue_content: Original issue content.
        initial_file_hashes: File hashes from before workflow started.
        total_cost: Running total cost.
        changed_files: List of changed files.
        timeout_adder: Additional timeout for steps.
        verbose: Verbose output flag.
        quiet: Quiet output flag.

    Returns:
        (updated_total_cost, updated_changed_files)
    """
    # Detect files changed during the workflow
    cleanup_files = _detect_changed_files(cwd, initial_file_hashes)
    if not cleanup_files:
        if not quiet:
            console.print("[bold][Step 11/11] Skipped: No files changed during workflow.[/bold]")
        return total_cost, changed_files

    if not quiet:
        console.print("[bold][Step 11/11] Running code cleanup...[/bold]")

    # Load the step 11 prompt template
    step11_template = load_prompt_template("agentic_e2e_fix_step11_code_cleanup_LLM")
    if not step11_template:
        if not quiet:
            console.print("[yellow]Step 11 skipped: Could not load cleanup prompt template.[/yellow]")
        return total_cost, changed_files

    # Compute the full diff since workflow started (covers all commits, not just last)
    diff_ref = initial_sha if initial_sha else "HEAD~1"
    diff_result = subprocess.run(
        ["git", "diff", diff_ref],
        cwd=cwd,
        capture_output=True,
        text=True,
    )
    full_diff = diff_result.stdout if diff_result.returncode == 0 else ""

    # Read changed file contents
    file_contents: Dict[str, str] = {}
    for filepath in cleanup_files:
        fpath = cwd / filepath
        if fpath.exists() and fpath.is_file():
            try:
                file_contents[filepath] = fpath.read_text(errors="replace")
            except (IOError, OSError):
                pass

    # Format the cleanup prompt
    changed_file_text = "\n\n".join(
        f"### {fp}\n```\n{content}\n```"
        for fp, content in file_contents.items()
    )
    context = {
        "issue_url": issue_url,
        "repo_owner": repo_owner,
        "repo_name": repo_name,
        "issue_number": issue_number,
        "issue_description": issue_content,
        "full_diff": full_diff,
        "changed_files_content": changed_file_text,
    }
    formatted_prompt = step11_template
    for key, value in context.items():
        formatted_prompt = formatted_prompt.replace(f"{{{key}}}", str(value))

    # Run the cleanup LLM task
    cleanup_timeout = E2E_FIX_STEP_TIMEOUTS.get(11, 600.0) + timeout_adder
    cleanup_success, cleanup_output, cleanup_cost, _ = run_agentic_task(
        instruction=formatted_prompt,
        cwd=cwd,
        verbose=verbose,
        quiet=quiet,
        timeout=cleanup_timeout,
        label="step11_code_cleanup",
        max_retries=DEFAULT_MAX_RETRIES,
    )
    total_cost += cleanup_cost

    if not cleanup_success:
        if not quiet:
            console.print("[yellow]Step 11: Cleanup LLM task failed. Skipping cleanup.[/yellow]")
        return total_cost, changed_files

    # Safety: revert out-of-scope changes BEFORE commit+push
    try:
        allowed = {(cwd / f).resolve() for f in cleanup_files}
        _revert_out_of_scope_changes(cwd, allowed)
    except (subprocess.SubprocessError, OSError) as e:
        if not quiet:
            console.print(f"[yellow]Step 11: revert out-of-scope failed: {e}[/yellow]")

    # Re-run tests to verify cleanup didn't break anything
    test_files = _extract_test_files(issue_content, changed_files, cwd, initial_file_hashes)
    if test_files:
        verified, verify_output = _verify_tests_independently(test_files, cwd)
        if _fallback_scan_was_capped and verified:
            verified = False
        if verified:
            # Commit cleanup as a separate commit
            cleanup_changed = _detect_changed_files(cwd, initial_file_hashes)
            if cleanup_changed:
                commit_msg = f"chore: clean up code from fix for #{issue_number}"
                # Stage cleanup changes
                for filepath in cleanup_changed:
                    if not _is_intermediate_file(filepath):
                        subprocess.run(
                            ["git", "add", filepath],
                            cwd=cwd,
                            capture_output=True,
                            text=True,
                        )
                commit_result = subprocess.run(
                    ["git", "commit", "-m", commit_msg],
                    cwd=cwd,
                    capture_output=True,
                    text=True,
                )
                if commit_result.returncode == 0:
                    # Push the cleanup commit
                    push_ok, push_err = _push_with_retry(cwd, repo_owner, repo_name)
                    if push_ok and not quiet:
                        console.print("  -> Step 11 cleanup committed and pushed.")
                    elif not push_ok and not quiet:
                        console.print(f"  [yellow]Step 11 cleanup committed but push failed: {push_err}[/yellow]")
                changed_files = cleanup_changed or changed_files
        else:
            # Tests failed after cleanup — revert ALL cleanup changes
            if not quiet:
                console.print("[yellow]Step 11: Tests failed after cleanup. Reverting cleanup changes.[/yellow]")
            subprocess.run(
                ["git", "checkout", "."],
                cwd=cwd,
                capture_output=True,
                text=True,
            )
    else:
        if not quiet:
            console.print("[yellow]Step 11: No test files found for verification. Skipping cleanup commit.[/yellow]")

    return total_cost, changed_files


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
    skip_cleanup: bool = False,
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Orchestrator for the 11-step agentic e2e fix workflow.
    
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

    # Capture initial commit SHA for full diff in Step 11
    _initial_sha_result = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=cwd, capture_output=True, text=True,
    )
    initial_sha = _initial_sha_result.stdout.strip() if _initial_sha_result.returncode == 0 else ""

    success = False
    final_message = ""
    consecutive_provider_failures = 0
    import_error_retries = 0  # Global budget: max 1 retry across all cycles
    verification_failure_context = ""  # Injected into Step 1 prompt on retry

    try:
        # Outer Loop
        if current_cycle == 0:
            current_cycle = 1

        while current_cycle <= max_cycles:
            console.print(f"\n[bold cyan][Cycle {current_cycle}/{max_cycles}] Starting fix cycle...[/bold cyan]")

            # Snapshot file hashes at cycle start for convergence detection (5b)
            cycle_start_hashes = _get_file_hashes(cwd)
            
            # Inner Loop (Steps 1-9)
            for step_num in range(1, 10):
                if step_num <= last_completed_step:
                    continue # Skip already completed steps in this cycle

                # Empty dev-units short-circuit (5a): Skip Steps 6-8 if Step 5 found nothing
                if step_num in (6, 7, 8):
                    step5_out = step_outputs.get("5", "")
                    dev_units = _parse_dev_units(step5_out)
                    # Short-circuit if marker present AND (empty or "0" or "0/N")
                    if dev_units is not None:
                        is_empty = not dev_units or dev_units == "0" or dev_units.startswith("0/")
                        if is_empty:
                            console.print(f"[bold][Step {step_num}/9] Skipped: No dev units identified for fixing.[/bold]")
                            step_outputs[str(step_num)] = f"E2E_SKIP: No dev units identified (short-circuit)"
                            last_completed_step = step_num
                            continue

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
                                verified, verify_output = _verify_tests_independently(test_files, cwd)
                                if _fallback_scan_was_capped and verified:
                                    verified = False
                                    verify_output += (
                                        f"\nFALLBACK_CAPPED: Only {len(test_files)} of potentially "
                                        "hundreds of test files were verified; cannot confirm full suite pass."
                                    )
                                if verified:
                                    console.print("[green]ALL_TESTS_PASS (Step 1) verified — Step 2 skipped. Exiting early.[/green]")
                                    success = True
                                    final_message = "All tests passed (Step 1 verified, Step 2 skipped)."
                                    break
                                else:
                                    _, import_error_retries, should_retry = _handle_verification_failure(verify_output, import_error_retries, console)
                                    step_outputs[str(step_num)] = f"FAILED: VERIFICATION_FAILED: {verify_output}"
                                    if should_retry:
                                        verification_failure_context = verify_output
                                        last_completed_step = 0
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
                                verified, verify_output = _verify_tests_independently(test_files, cwd)
                                if _fallback_scan_was_capped and verified:
                                    verified = False
                                    verify_output += (
                                        f"\nFALLBACK_CAPPED: Only {len(test_files)} of potentially "
                                        "hundreds of test files were verified; cannot confirm full suite pass."
                                    )
                                if verified:
                                    console.print("[green]ALL_TESTS_PASS (Step 1) verified — Step 2 skipped. Exiting early.[/green]")
                                    success = True
                                    final_message = "All tests passed (Step 1 verified, Step 2 skipped)."
                                    break
                                else:
                                    _, import_error_retries, should_retry = _handle_verification_failure(verify_output, import_error_retries, console)
                                    step_outputs[str(step_num)] = f"FAILED: VERIFICATION_FAILED: {verify_output}"
                                    if should_retry:
                                        verification_failure_context = verify_output
                                        last_completed_step = 0
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
                    dev_units = _parse_dev_units(s5_out)
                    context["dev_units_identified"] = dev_units if dev_units is not None else ""
                
                if step_num == 8:
                    s5_out = step_outputs.get("5", "")
                    dev_units = _parse_dev_units(s5_out)
                    context["failing_dev_units"] = dev_units if dev_units is not None else ""

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

                # Inject verification failure context on Step 1 retry
                if step_num == 1 and verification_failure_context:
                    formatted_prompt += (
                        "\n\nPREVIOUS ATTEMPT FAILED: Independent verification found the "
                        "following errors after you claimed ALL_TESTS_PASS. You MUST write "
                        "all required code to disk before claiming tests pass:\n"
                        f"{verification_failure_context}"
                    )
                    verification_failure_context = ""  # Clear after use

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
                    if dev_units_str is not None:
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
                        if _fallback_scan_was_capped and verified:
                            verified = False
                            verify_output += (
                                f"\nFALLBACK_CAPPED: Only {len(test_files)} of potentially "
                                "hundreds of test files were verified; cannot confirm full suite pass."
                            )
                        if verified:
                            console.print("[green]ALL_TESTS_PASS verified by independent pytest run.[/green]")
                            success = True
                            final_message = "All tests passed (independently verified)."
                            break
                        else:
                            console.print("[bold red]LLM claimed ALL_TESTS_PASS but independent verification FAILED.[/bold red]")
                            _, import_error_retries, should_retry = _handle_verification_failure(verify_output, import_error_retries, console)
                            step_output = f"VERIFICATION_FAILED: LLM claimed ALL_TESTS_PASS but pytest failed.\n{verify_output}"
                            step_outputs[str(step_num)] = f"FAILED: {step_output}"
                            if should_retry:
                                verification_failure_context = verify_output
                                last_completed_step = 0
                                break
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
                    if tier4 and tier4.token == "NOT_A_BUG":
                        console.print("[yellow]NOT_A_BUG detected via LLM classification (tier 4)[/yellow]")
                        _step3_token = "NOT_A_BUG"
                    elif tier4 and tier4.token == "CLASSIFICATION_ERROR":
                        console.print(
                            "[yellow]Step 3 token classification unavailable (tier 4 error); "
                            "continuing without NOT_A_BUG fallback.[/yellow]"
                        )
                if step_num == 3 and _step3_token == "NOT_A_BUG":
                    # Block NOT_A_BUG if fixes were already applied in prior cycles
                    has_fixed_units = any(s.get("fixed") for s in dev_unit_states.values())
                    has_direct_edits = bool(_detect_changed_files(cwd, initial_file_hashes))
                    if has_fixed_units or has_direct_edits:
                        console.print("[yellow]NOT_A_BUG ignored — fixes were already applied in prior cycles.[/yellow]")
                    else:
                        console.print("[yellow]NOT_A_BUG detected in Step 3. Issue is not a bug, stopping workflow.[/yellow]")
                        success = False
                        final_message = "Issue determined to be not a bug."
                        break

                # Check Loop Control (Step 9)
                if step_num == 9:
                    _step9_token = _resolve_step9_loop_token(step_output, console)

                    def _merge_step9_apply(r: _Step9TokenApplyResult) -> None:
                        nonlocal import_error_retries, success, final_message
                        nonlocal last_completed_step, verification_failure_context
                        import_error_retries = r.import_error_retries
                        if r.step_outputs_9 is not None:
                            step_outputs[str(step_num)] = r.step_outputs_9
                        if r.success is not None:
                            success = r.success
                        if r.final_message is not None:
                            final_message = r.final_message
                        if r.last_completed_step is not None:
                            last_completed_step = r.last_completed_step
                        if r.verification_failure_context_update is not None:
                            verification_failure_context = r.verification_failure_context_update

                    if _step9_token is not None:
                        r9 = _apply_step9_resolved_token(
                            _step9_token,
                            step_output,
                            issue_content=issue_content,
                            changed_files=changed_files,
                            cwd=cwd,
                            initial_file_hashes=initial_file_hashes,
                            cycle_start_hashes=cycle_start_hashes,
                            import_error_retries=import_error_retries,
                            console=console,
                            step_num=step_num,
                            current_cycle=current_cycle,
                            is_retry_path=False,
                        )
                        _merge_step9_apply(r9)
                        if r9.break_inner:
                            break
                    elif not step_success:
                        # Provider/timeout failure with no control token: treat as transient, start next cycle.
                        console.print(
                            "[yellow]Step 9 failed with no parseable loop-control token; "
                            "starting next cycle.[/yellow]"
                        )
                        break
                    else:
                        # Step 9 succeeded but emitted no token: retry once to get an explicit loop-control signal.
                        console.print(
                            "[yellow]No loop control token in Step 9 output; retrying Step 9 once.[/yellow]"
                        )
                        retry_success, retry_output, retry_cost, retry_model = run_agentic_task(
                            instruction=formatted_prompt,
                            cwd=cwd,
                            verbose=verbose,
                            quiet=quiet,
                            timeout=base_timeout + timeout_adder,
                            label=f"cycle{current_cycle}_step9_retry",
                            max_retries=DEFAULT_MAX_RETRIES,
                        )
                        total_cost += retry_cost
                        if retry_model:
                            model_used = retry_model

                        # Persist retry accounting immediately so resumed state
                        # stays consistent (total_cost + which retry was used).
                        try:
                            step_outputs[f"{step_num}_retry"] = retry_output
                            state_data["total_cost"] = total_cost
                            state_data["model_used"] = model_used
                            state_data["step_outputs"] = step_outputs.copy()
                            state_data["last_saved_at"] = datetime.now().isoformat()

                            new_gh_id = save_workflow_state(
                                cwd,
                                issue_number,
                                workflow_name,
                                state_data,
                                state_dir,
                                repo_owner,
                                repo_name,
                                use_github_state,
                                github_comment_id,
                            )
                            if new_gh_id:
                                github_comment_id = new_gh_id
                                state_data["github_comment_id"] = github_comment_id
                        except Exception as e:
                            logger.debug(
                                "Best-effort Step 9 retry state save failed: %s",
                                e,
                                exc_info=True,
                            )

                        retry_token = _resolve_step9_loop_token(retry_output, console)
                        if retry_token is None and not retry_success:
                            console.print(
                                "[yellow]Step 9 retry failed with no parseable loop-control token; "
                                "starting next cycle.[/yellow]"
                            )
                            break
                        if retry_token is None:
                            console.print(
                                "[bold yellow]Step 9 did not emit a loop control token after retry; "
                                "stopping.[/bold yellow]"
                            )
                            final_message = (
                                "Workflow stopped: Step 9 did not emit a loop control token after retry."
                            )
                            break
                        r_retry = _apply_step9_resolved_token(
                            retry_token,
                            retry_output,
                            issue_content=issue_content,
                            changed_files=changed_files,
                            cwd=cwd,
                            initial_file_hashes=initial_file_hashes,
                            cycle_start_hashes=cycle_start_hashes,
                            import_error_retries=import_error_retries,
                            console=console,
                            step_num=step_num,
                            current_cycle=current_cycle,
                            is_retry_path=True,
                        )
                        _merge_step9_apply(r_retry)
                        if r_retry.break_inner:
                            break

            # Check if we should exit the outer loop
            if success:
                break

            # Check if NOT_A_BUG was detected (exit outer loop too)
            has_fixed_units = any(s.get("fixed") for s in dev_unit_states.values())
            has_direct_edits = bool(_detect_changed_files(cwd, initial_file_hashes))
            if step_num == 3 and _classify_step_output(step_outputs.get("3", ""), step_num=3) == "NOT_A_BUG" and not has_fixed_units and not has_direct_edits:
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

            # Step 11: Code Cleanup (runs BEFORE CI so cleanup is CI-validated)
            if not skip_cleanup:
                total_cost, changed_files = _run_step11_code_cleanup(
                    cwd=cwd,
                    issue_number=issue_number,
                    issue_content=issue_content,
                    issue_url=issue_url,
                    repo_owner=repo_owner,
                    repo_name=repo_name,
                    initial_file_hashes=initial_file_hashes,
                    initial_sha=initial_sha,
                    total_cost=total_cost,
                    changed_files=changed_files,
                    timeout_adder=timeout_adder,
                    verbose=verbose,
                    quiet=quiet,
                )

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
                total_steps=11,
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