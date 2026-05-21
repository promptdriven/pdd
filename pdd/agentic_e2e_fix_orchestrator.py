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
    extract_step_report,
    normalize_step_comments_state,
    post_step_comment_once,
)
from .get_test_command import get_test_command_for_file
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .pytest_output import run_pytest_and_capture_output
from .ci_validation import _find_open_pr_number, run_ci_validation_loop

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
    8: 3600.0,  # Run pdd fix on failing dev units (Most Complex - multiple LLM calls; large dev units (>2000 lines) need >>1000s for full file regeneration)
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


def _resolve_cached_step9_output(step_outputs: Dict[str, str]) -> str:
    """Return the authoritative Step 9 output for resume token resolution.

    Step 9 may run twice in one cycle: the initial pass, plus a retry when the
    initial pass emits no recognizable loop-control token. The retry output is
    stored under ``step_outputs["9_retry"]`` (see the retry persistence site
    in the inner loop); the initial output is ``step_outputs["9"]``. The retry
    output is the authoritative one when it ran — if the retry succeeded with
    ``ALL_TESTS_PASS`` but the workflow was interrupted before the next pause,
    reading only ``"9"`` (which can be tokenless) would let resume fall
    through to ``CONTINUE_CYCLE`` and silently advance into a fresh cycle even
    though Step 9 actually succeeded. Prefer the retry output when present
    and non-empty (#1001).
    """
    retry_out = step_outputs.get("9_retry", "")
    if retry_out:
        return retry_out
    return step_outputs.get("9", "")


def _post_step9_resume_action(
    step9_output: str,
    current_cycle: int,
    max_cycles: int,
    console: Console,
) -> str:
    """Decide what resume should do when last_completed_step >= 9 (Issue #1001).

    The prior buggy code unconditionally advanced the cycle whenever
    `last_completed_step >= 9` on resume, ignoring what Step 9 actually
    emitted. This helper inspects the cached Step 9 output and branches:

    - "SUCCESS_FALL_THROUGH" — Step 9 declared success (ALL_TESTS_PASS,
      LOCAL_TESTS_PASS, or NOT_A_BUG). Caller must keep `current_cycle`,
      `last_completed_step`, and `step_outputs` intact and fall through
      to Step 11 cleanup + Step 10 CI validation.
    - "ADVANCE_CYCLE" — Step 9 wants another cycle and budget remains.
    - "MAX_CYCLES_REACHED" — Either Step 9 explicitly emitted
      MAX_CYCLES_REACHED (resolved via the tier-1–3 classifier in
      `_classify_step_output` or the tier-4 LLM fallback in
      `_resolve_step9_loop_token`), or Step 9 wants another cycle but
      the cycle budget is exhausted. In both cases the caller must
      surface this as a non-success exit, reusing the same path Step 9
      uses when emitting MAX_CYCLES_REACHED directly (see
      `_apply_step9_resolved_token` MAX_CYCLES_REACHED handler).
    """
    # Defensive NOT_A_BUG check: Step 9 normally doesn't emit NOT_A_BUG
    # (that's Step 3), but if the cached output surfaces it, treat as
    # success — Step 3 would already have determined no bug exists.
    if "NOT_A_BUG" in step9_output:
        return "SUCCESS_FALL_THROUGH"
    tok = _resolve_step9_loop_token(step9_output, console)
    if tok in ("ALL_TESTS_PASS", "LOCAL_TESTS_PASS"):
        return "SUCCESS_FALL_THROUGH"
    # Explicit terminal token from Step 9 (tier-1–3 detect_control_token
    # or tier-4 LLM classifier) must NOT be overridden by the budget
    # check below — Step 9 already declared the loop terminal.
    if tok == "MAX_CYCLES_REACHED":
        return "MAX_CYCLES_REACHED"
    if current_cycle < max_cycles:
        return "ADVANCE_CYCLE"
    return "MAX_CYCLES_REACHED"


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
    - .gh-wrapper/** (executor `gh` wrapper artifacts — Issue #1001)
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

    # Issue #1001: filter executor wrapper artifacts.
    # Anchor on the directory boundary so legitimate paths like
    # "gh-wrapper-docs.md" or "tools/gh_wrapper.py" are not over-filtered.
    normalized_gh = str(filepath).replace("\\", "/")
    if normalized_gh.startswith(".gh-wrapper/") or "/.gh-wrapper/" in normalized_gh:
        return True

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


# Build/cache/log artifacts that should not count as "fixes applied" when deciding
# whether NOT_A_BUG classifications are legitimate. Matched as path components or
# suffixes against the forward-slash-normalized relative path.
_NOISE_PATH_COMPONENTS = frozenset({
    "__pycache__",
    ".pytest_cache",
    ".mypy_cache",
    ".ruff_cache",
    ".tox",
    "node_modules",
    ".coverage",
    "htmlcov",
    ".DS_Store",
    ".eggs",
    ".next",
    ".turbo",
    ".parcel-cache",
})
_NOISE_SUFFIXES = (".pyc", ".pyo", ".log", ".swp", ".swo")
_NOISE_BASENAMES = frozenset({"coverage.xml"})


def _is_noise_path(path: str) -> bool:
    """Return True if path is a build/cache/log artifact that should not count
    as a fix for NOT_A_BUG suppression purposes."""
    normalized = path.replace("\\", "/")
    if any(normalized.endswith(suffix) for suffix in _NOISE_SUFFIXES):
        return True
    parts = normalized.split("/")
    if any(part in _NOISE_PATH_COMPONENTS for part in parts):
        return True
    if parts and parts[-1] in _NOISE_BASENAMES:
        return True
    # parallel coverage files (.coverage.<host>.<pid>.<rand>) and *.egg-info dirs
    return any(
        part.startswith(".coverage.") or part.endswith(".egg-info")
        for part in parts
    )


def _detect_meaningful_changes(cwd: Path, initial_file_hashes: Dict[str, Optional[str]]) -> List[str]:
    """Like _detect_changed_files but filters out build/cache/log noise.

    Used by the Step 3 NOT_A_BUG guards: a fix must be a *meaningful* edit
    (not a stray `__pycache__/*.pyc` or `.pytest_cache` write) to suppress
    a legitimate NOT_A_BUG classification.
    """
    return [p for p in _detect_changed_files(cwd, initial_file_hashes) if not _is_noise_path(p)]


# Sentinel returned by ``_reevaluate_step3_not_a_bug_on_resume`` to signal that
# the resume-time cycle-waste-breaker condition holds (cached NOT_A_BUG,
# direct edits, no fixed units, current_cycle > 1). The caller treats this as a
# terminal-success short-circuit equivalent to the inline Step 3 cycle-waste
# breaker (Issue #1034) — it MUST NOT be written into ``step_outputs``.
NOT_A_BUG_TERMINAL_SUCCESS_ON_RESUME = "NOT_A_BUG_TERMINAL_SUCCESS_ON_RESUME"
NOT_A_BUG_TERMINAL_SUCCESS_MESSAGE = (
    "Direct-edit fix applied in a prior cycle; Step 3 classifies remaining "
    "state as not a bug."
)


def _reevaluate_step3_not_a_bug_on_resume(
    cached_output: str,
    *,
    dev_unit_states: Dict[str, Any],
    initial_file_hashes: Optional[Dict[str, Optional[str]]],
    cwd: Path,
    quiet: bool = False,
    source: str = "step_outputs",
    current_cycle: Optional[int] = None,
    cycle_start_hashes: Optional[Dict[str, Optional[str]]] = None,
) -> str:
    """Re-evaluate a cached Step 3 ``NOT_A_BUG`` token on workflow resume.

    Implements the resume-time guard described in
    ``pdd/prompts/agentic_e2e_fix_orchestrator_python.prompt`` (Issue #1034):
    when the cached entry classifies as ``NOT_A_BUG``, re-run the same
    direct-edit + ``dev_unit_states`` + cycle-waste-breaker checks that the
    inline Step 3 path applies. If any guard would have suppressed the token,
    demote the cached output to
    ``FAILED: NOT_A_BUG_SUPPRESSED_ON_RESUME:<reason>`` so the existing
    ``FAILED:`` rewind in :func:`validate_cached_state` reruns Step 3.

    The raw cached token MUST NOT be trusted on resume. Both
    ``step_outputs["3"]`` and ``bug_step_outputs["3"]`` callers route through
    this helper for symmetry.

    Cycle-waste-breaker terminal-success path: when ``current_cycle > 1`` and
    direct edits exist with no FIXED dev units, mirror the inline Step 3
    cycle-waste-breaker (lines 2127-2134 of the inner loop) by returning the
    :data:`NOT_A_BUG_TERMINAL_SUCCESS_ON_RESUME` sentinel instead of demoting.
    The caller is expected to translate that sentinel into a terminal-success
    workflow exit so the orchestrator does NOT spend another Step 3 LLM call
    when the prior-cycle direct-edit fix is already terminal — but ONLY when
    we can prove no in-cycle progress was made since the cycle's start
    snapshot. Without that proof, conservatively demote and rerun Step 3.

    Args:
        cached_output: The cached Step 3 output text.
        dev_unit_states: Restored ``dev_unit_states`` from workflow state.
        initial_file_hashes: Restored workflow-start file hash snapshot. If
            ``None``, the direct-edit check is skipped (fail open).
        cwd: Repo working directory used for direct-edit detection.
        quiet: Suppress console messages when True.
        source: Diagnostic label (``"step_outputs"`` or ``"bug_step_outputs"``).
        current_cycle: Restored cycle counter from workflow state. When
            ``current_cycle > 1`` and the direct-edit guard would otherwise
            fire with no FIXED units AND ``cycle_start_hashes`` proves no
            in-cycle progress, return the terminal-success sentinel instead
            of the FAILED demotion token. When ``None``, the cycle-waste-
            breaker terminal-success path is disabled (backwards compatible
            with helper-only test callers).
        cycle_start_hashes: Restored snapshot of file hashes captured at the
            start of the current cycle. Required to prove the cycle has made
            no in-cycle progress before authorizing terminal-success on
            resume. If ``None`` (legacy state or stale post-cycle save), the
            terminal-success branch conservatively demotes to ``FAILED:
            NOT_A_BUG_SUPPRESSED_ON_RESUME:direct_edits`` instead.

    Returns:
        The original ``cached_output`` if the token should still be trusted,
        a ``"FAILED: NOT_A_BUG_SUPPRESSED_ON_RESUME:<reason>"`` token if a
        guard demotes it, or :data:`NOT_A_BUG_TERMINAL_SUCCESS_ON_RESUME` when
        the cycle-waste-breaker terminal-success path applies.
    """
    if not cached_output or str(cached_output).startswith("FAILED:"):
        return cached_output
    if _classify_step_output(cached_output, step_num=3) != "NOT_A_BUG":
        return cached_output

    # Guard 1: dev_unit_states with any FIXED unit suppresses NOT_A_BUG.
    # Per the prompt's cycle-waste-breaker rule on resume (no cycle_start_hashes
    # available), has_fixed_units True is treated as terminal-for-cycle and
    # suppresses the cached token.
    has_fixed_units = any(
        isinstance(s, dict) and s.get("fixed") for s in (dev_unit_states or {}).values()
    )
    if has_fixed_units:
        if not quiet:
            console.print(
                f"[yellow]Resume guard: cached Step 3 NOT_A_BUG in {source} suppressed "
                f"because dev_unit_states has FIXED units. Demoting to "
                f"FAILED: NOT_A_BUG_SUPPRESSED_ON_RESUME:dev_unit_states.[/yellow]"
            )
        return "FAILED: NOT_A_BUG_SUPPRESSED_ON_RESUME:dev_unit_states"

    # Guard 2: direct-edit detection using restored initial_file_hashes.
    # If the snapshot is missing, fail open (do not suppress) per the prompt.
    if initial_file_hashes is not None:
        try:
            direct_edits = _detect_meaningful_changes(cwd, initial_file_hashes)
        except Exception:
            direct_edits = []
        if direct_edits:
            # Cycle-waste-breaker terminal success on resume (Issue #1034):
            # mirror the inline Step 3 path at lines 2127-2134 — when
            # current_cycle > 1, direct edits exist, no FIXED dev units exist,
            # AND we can prove no in-cycle progress has been made (via the
            # restored ``cycle_start_hashes`` snapshot), the prior-cycle
            # direct-edit fix is treated as terminal and the workflow exits
            # successfully instead of rerunning Step 3.
            #
            # Without ``cycle_start_hashes`` we CANNOT trust the assumption
            # that the resumed cycle made no progress: Step 1 inside the
            # resumed cycle can run ``pdd fix`` and write meaningful edits
            # BEFORE Step 3 is reached (``dev_unit_states`` is only updated
            # at Step 8). So when ``cycle_start_hashes`` is missing or shows
            # any in-cycle progress, conservatively demote to FAILED so
            # Step 3 reruns instead of silently exiting as terminal-success.
            if current_cycle is not None and current_cycle > 1:
                cycle_progress: List[str] = []
                if cycle_start_hashes is not None:
                    try:
                        cycle_progress = _detect_meaningful_changes(
                            cwd, cycle_start_hashes
                        )
                    except Exception:
                        cycle_progress = []
                if cycle_start_hashes is None or cycle_progress:
                    if not quiet:
                        if cycle_start_hashes is None:
                            console.print(
                                f"[yellow]Resume guard: cached Step 3 NOT_A_BUG in "
                                f"{source} cannot terminal-success on resume — "
                                f"cycle_start_hashes is missing (legacy state). "
                                f"Conservatively demoting to FAILED: "
                                f"NOT_A_BUG_SUPPRESSED_ON_RESUME:direct_edits "
                                f"so Step 3 reruns.[/yellow]"
                            )
                        else:
                            console.print(
                                f"[yellow]Resume guard: cached Step 3 NOT_A_BUG in "
                                f"{source} cannot terminal-success on resume — "
                                f"current cycle has in-cycle progress "
                                f"({len(cycle_progress)} file(s) changed since "
                                f"cycle_start_hashes). Demoting to FAILED: "
                                f"NOT_A_BUG_SUPPRESSED_ON_RESUME:direct_edits "
                                f"so Step 3 reruns.[/yellow]"
                            )
                    return "FAILED: NOT_A_BUG_SUPPRESSED_ON_RESUME:direct_edits"
                if not quiet:
                    console.print(
                        f"[yellow]Resume guard: cached Step 3 NOT_A_BUG in {source} "
                        f"matches cycle-waste-breaker (current_cycle={current_cycle}, "
                        f"direct edits present, no FIXED dev units, no in-cycle "
                        f"progress vs cycle_start_hashes). Treating prior direct-edit "
                        f"fix as terminal success instead of rerunning Step 3.[/yellow]"
                    )
                return NOT_A_BUG_TERMINAL_SUCCESS_ON_RESUME
            if not quiet:
                console.print(
                    f"[yellow]Resume guard: cached Step 3 NOT_A_BUG in {source} suppressed "
                    f"because direct edits exist on disk relative to initial_file_hashes. "
                    f"Demoting to FAILED: NOT_A_BUG_SUPPRESSED_ON_RESUME:direct_edits.[/yellow]"
                )
            return "FAILED: NOT_A_BUG_SUPPRESSED_ON_RESUME:direct_edits"

    return cached_output


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


def _push_unpushed_commits_or_report_noop(
    cwd: Path,
    repo_owner: str,
    repo_name: str,
) -> Tuple[bool, str]:
    """Push ahead commits if present; otherwise treat the commit step as a no-op."""
    if _has_unpushed_commits(cwd):
        push_ok, push_err = _push_with_retry(cwd, repo_owner, repo_name)
        if push_ok:
            return True, "Pushed existing commits"
        return False, f"Push failed: {push_err}"
    return True, "No changes to commit"


def push_with_retry(
    cwd: Path,
    *,
    repo_owner: str,
    repo_name: str,
    remote: str = "origin",
    refspec: str = "HEAD",
    set_upstream: bool = True,
    force_with_lease_on_non_fast_forward: bool = True,
) -> Tuple[bool, str]:
    """Push to a git remote with shared non-fast-forward and token-refresh retries.

    Used by both the e2e fix orchestrator (default `origin HEAD` push of the
    fix branch) and `pdd checkup --review-loop` (push back to a PR head ref,
    which may live on a fork's `clone_url`).

    Behaviour:
    - First attempt: ``git push [-u] <remote> <refspec>``.
    - Non-fast-forward: by default, retry with ``--force-with-lease`` (safe —
      only overwrites the remote if it still matches what we last fetched).
      Callers that push to a shared PR head can disable this and handle the
      rejection by fetching/rebasing instead.
    - Auth failure (``Authentication failed``, ``HTTP 401``,
      ``could not read Username``, ``HTTP Basic: Access denied``): read a
      token from a non-empty ``PDD_GH_TOKEN_FILE`` or fall back to
      ``GH_TOKEN``, ``GITHUB_TOKEN``, then ``PDD_GITHUB_TOKEN``. Save the
      current remote URL, rewrite it to
      ``https://x-access-token:{quote(token)}@github.com/{owner}/{repo}.git``,
      retry the push once, and restore the original URL in ``finally`` so
      the token never leaks into git config.

    Returns ``(success, error_message)``.
    """
    base_cmd = ["git", "push"]
    if set_upstream:
        base_cmd.append("-u")
    base_cmd.extend([remote, refspec])

    push_result = subprocess.run(base_cmd, cwd=cwd, capture_output=True, text=True)
    if push_result.returncode == 0:
        return True, ""

    stderr = push_result.stderr

    # Non-fast-forward: branch diverged (e.g. after rebase onto main).
    # Only match specific non-ff markers — avoid generic "[rejected]" which
    # could be protected branches, pre-receive hooks, etc.
    non_ff_markers = ["non-fast-forward", "tip of your current branch is behind"]
    is_non_fast_forward = any(marker in stderr for marker in non_ff_markers)

    if is_non_fast_forward:
        if not force_with_lease_on_non_fast_forward:
            return False, stderr
        console.print(
            "[yellow]WARNING: Push rejected (non-fast-forward). "
            "Retrying with --force-with-lease...[/yellow]"
        )
        force_cmd = ["git", "push", "--force-with-lease"]
        if set_upstream:
            force_cmd.append("-u")
        force_cmd.extend([remote, refspec])
        retry_result = subprocess.run(force_cmd, cwd=cwd, capture_output=True, text=True)
        if retry_result.returncode == 0:
            return True, ""
        return False, retry_result.stderr

    auth_errors = [
        "Authentication failed",
        "HTTP 401",
        "could not read Username",
        "HTTP Basic: Access denied",
    ]
    is_auth_failure = any(err in stderr for err in auth_errors)

    if not is_auth_failure:
        return False, stderr

    # Auth failure — try PDD_GH_TOKEN_FILE first, then standard GitHub token env vars.
    # The cloud executor writes a refreshed token file, while direct verifier
    # paths and GitHub Actions commonly provide only GH_TOKEN/GITHUB_TOKEN.
    token_file_path = os.environ.get("PDD_GH_TOKEN_FILE")
    token = ""
    if token_file_path:
        token_path = Path(token_file_path)
        if token_path.exists():
            token = token_path.read_text().strip()
    if not token:
        token = (
            os.environ.get("GH_TOKEN")
            or os.environ.get("GITHUB_TOKEN")
            or os.environ.get("PDD_GITHUB_TOKEN")
            or ""
        ).strip()
    if not token:
        return False, stderr

    # Save original remote URL — abort retry if we can't capture it.
    url_result = subprocess.run(
        ["git", "remote", "get-url", remote],
        cwd=cwd,
        capture_output=True,
        text=True,
    )
    original_url = url_result.stdout.strip() if url_result.returncode == 0 else ""

    # Some callers pass a clone URL as `remote` (e.g. the review-loop pushing to
    # the PR head repo via its clone URL rather than a configured remote name).
    # In that case `git remote get-url` won't recognize it. Detect via heuristic
    # and rewrite the URL inline rather than via `git remote set-url`.
    remote_is_url = remote.startswith(("http://", "https://", "git@", "ssh://"))

    from urllib.parse import quote
    token_url = (
        f"https://x-access-token:{quote(token, safe='')}@github.com/"
        f"{repo_owner}/{repo_name}.git"
    )

    if remote_is_url:
        retry_cmd = ["git", "push"]
        if set_upstream:
            retry_cmd.append("-u")
        retry_cmd.extend([token_url, refspec])
        retry_result = subprocess.run(retry_cmd, cwd=cwd, capture_output=True, text=True)
        if retry_result.returncode == 0:
            return True, ""
        return False, retry_result.stderr

    if not original_url:
        return False, stderr

    try:
        subprocess.run(
            ["git", "remote", "set-url", remote, token_url],
            cwd=cwd,
            capture_output=True,
            text=True,
        )
        retry_cmd = ["git", "push"]
        if set_upstream:
            retry_cmd.append("-u")
        retry_cmd.extend([remote, refspec])
        retry_result = subprocess.run(retry_cmd, cwd=cwd, capture_output=True, text=True)
        if retry_result.returncode == 0:
            return True, ""
        return False, retry_result.stderr
    finally:
        if original_url:
            restore = subprocess.run(
                ["git", "remote", "set-url", remote, original_url],
                cwd=cwd,
                capture_output=True,
                text=True,
            )
            if restore.returncode != 0:
                console.print(
                    "[yellow]WARNING: Failed to restore original remote URL:"
                    f" {restore.stderr}[/yellow]"
                )


def _push_with_retry(
    cwd: Path,
    repo_owner: str,
    repo_name: str,
) -> Tuple[bool, str]:
    """Backwards-compatible wrapper for ``push_with_retry`` (origin HEAD)."""
    return push_with_retry(
        cwd,
        repo_owner=repo_owner,
        repo_name=repo_name,
        remote="origin",
        refspec="HEAD",
        set_upstream=True,
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

    On push auth failure, retries using PDD_GH_TOKEN_FILE or standard GitHub
    token environment variables if available.

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
        else:
            return _push_unpushed_commits_or_report_noop(cwd, repo_owner, repo_name)

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
        commit_output = f"{commit_result.stdout}\n{commit_result.stderr}".lower()
        if (
            "nothing to commit" in commit_output
            or "no changes added to commit" in commit_output
        ):
            return _push_unpushed_commits_or_report_noop(cwd, repo_owner, repo_name)
        return False, f"Failed to commit: {commit_result.stderr}"

    # Push to remote with retry on auth failure
    push_ok, push_err = _push_with_retry(cwd, repo_owner, repo_name)

    if push_ok:
        return True, f"Committed and pushed {len(files_to_commit)} file(s)"
    else:
        return False, f"Push failed: {push_err}"


def _fetch_pr_head_sha(repo_owner: str, repo_name: str, pr_number: int) -> str:
    """Best-effort fetch of the PR's remote head SHA. Empty string on failure."""
    try:
        from .checkup_review_loop import _fetch_pr_metadata  # pylint: disable=import-outside-toplevel
        metadata = _fetch_pr_metadata(repo_owner, repo_name, pr_number)
    except Exception:  # noqa: BLE001 — best-effort; empty means "can't compare"
        return ""
    return str(metadata.get("head_sha", "") or "")


def _read_checkup_worktree_head_sha(cwd: Path, pr_number: int) -> str:
    """Read HEAD SHA of the PR-mode checkup worktree.

    The checkup orchestrator creates ``.pdd/worktrees/checkup-pr-{N}/``
    under the repository's git root and runs Step 7 verification (plus
    any rebased push) against that worktree. After ``run_agentic_checkup``
    returns, the worktree's HEAD is the *exact* SHA the checkup's verdict
    and push apply to.

    Comparing this SHA to the live PR remote head SHA is what
    distinguishes "checkup pushed" from "external party pushed during
    checkup". On equality, the checkup's verdict covers the current PR
    head; on divergence, the PR advanced past what was verified and
    pdd-issue must NOT green-light it.

    Returns the worktree HEAD SHA or empty string on any failure.
    """
    try:
        toplevel = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return ""
    if toplevel.returncode != 0:
        return ""
    git_root = Path(toplevel.stdout.strip())

    worktree = git_root / ".pdd" / "worktrees" / f"checkup-pr-{pr_number}"
    if not worktree.exists():
        return ""

    try:
        rev = subprocess.run(
            ["git", "-C", str(worktree), "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return ""
    if rev.returncode != 0:
        return ""
    return rev.stdout.strip()


def _run_final_checkup_on_pr(
    *,
    issue_url: str,
    issue_number: int,
    repo_owner: str,
    repo_name: str,
    cwd: Path,
    verbose: bool,
    quiet: bool,
    timeout_adder: float,
    use_github_state: bool,
    reasoning_time: Optional[float],
    ci_step_template: str,
    ci_validation_timeout: float,
) -> Tuple[bool, str, float, str]:
    """Run full PR-mode checkup against the current branch's open PR.

    Closes the post-CI mutation hole: the final checkup gate runs with
    ``no_fix=False`` and may push generated fixes to the PR head. CI passed
    against the head SHA we observed before this call, so any push advances
    the PR to code that has not been CI-validated. We snapshot the PR head
    SHA before and after; if it advanced, we re-run ``run_ci_validation_loop``
    with ``max_retries=0`` (verify-only — no further fixing on top of fixes).
    """
    pr_number = _find_open_pr_number(repo_owner, repo_name, cwd)
    if pr_number is None:
        return (
            True,
            "No open PR found for current branch; skipping final checkup",
            0.0,
            "",
        )

    pre_checkup_head_sha = _fetch_pr_head_sha(repo_owner, repo_name, pr_number)

    pr_url = f"https://github.com/{repo_owner}/{repo_name}/pull/{pr_number}"
    from .agentic_checkup import run_agentic_checkup

    checkup_success, checkup_message, checkup_cost, checkup_model = run_agentic_checkup(
        issue_url=issue_url,
        verbose=verbose,
        quiet=quiet,
        no_fix=False,
        timeout_adder=timeout_adder,
        use_github_state=use_github_state,
        reasoning_time=reasoning_time,
        pr_url=pr_url,
        cwd=cwd,
    )

    if not checkup_success:
        return checkup_success, checkup_message, checkup_cost, checkup_model

    if not pre_checkup_head_sha:
        # Fail closed: without the pre-checkup SHA we cannot tell whether the
        # checkup pushed new commits on top of the CI-validated head. Returning
        # success here would re-introduce the post-CI mutation hole.
        return (
            False,
            (
                "Final checkup completed but the pre-checkup PR head SHA was "
                "unavailable; cannot verify whether checkup pushed new commits "
                "that bypass CI. Re-run after confirming gh access."
            ),
            checkup_cost,
            checkup_model,
        )

    post_checkup_head_sha = _fetch_pr_head_sha(repo_owner, repo_name, pr_number)
    if not post_checkup_head_sha:
        return (
            False,
            (
                "Final checkup completed but the post-checkup PR head SHA was "
                "unavailable; cannot verify whether checkup pushed new commits "
                "that bypass CI. Re-run after confirming gh access."
            ),
            checkup_cost,
            checkup_model,
        )

    if post_checkup_head_sha == pre_checkup_head_sha:
        return checkup_success, checkup_message, checkup_cost, checkup_model

    # Round-5 finding: the PR head can advance externally during the
    # final checkup (maintainer push, another bot, etc.). Treating EVERY
    # SHA delta as a checkup push would re-validate CI on code that
    # Step 7 never saw, green-lighting an unverified head. The checkup
    # worktree's HEAD is the authoritative "last verified/pushed" SHA;
    # if it differs from the remote PR head, an external push raced us.
    checkup_worktree_head_sha = _read_checkup_worktree_head_sha(cwd, pr_number)
    if not checkup_worktree_head_sha:
        return (
            False,
            (
                "Final checkup completed but the checkup worktree HEAD SHA "
                "was unavailable; cannot prove the PR remote head matches "
                "what was verified. Failing closed to avoid green-lighting "
                "an unverified head."
            ),
            checkup_cost,
            checkup_model,
        )
    if checkup_worktree_head_sha != post_checkup_head_sha:
        return (
            False,
            (
                f"PR head advanced to {post_checkup_head_sha[:8]} during "
                f"final checkup but the checkup worktree last verified "
                f"{checkup_worktree_head_sha[:8]}. External push during "
                f"checkup detected — re-run pdd-issue so the new head is "
                f"verified by Step 7 before CI re-validation."
            ),
            checkup_cost,
            checkup_model,
        )

    if not quiet:
        console.print(
            f"[yellow]Final checkup pushed to PR head "
            f"({pre_checkup_head_sha[:8]}->{post_checkup_head_sha[:8]}, "
            f"verified by checkup worktree); re-validating CI on new "
            f"head...[/yellow]"
        )

    # The checkup pushes from its OWN worktree (.pdd/worktrees/checkup-pr-N),
    # so ``cwd``'s local HEAD is stale relative to the PR remote. Without the
    # override below, ``run_ci_validation_loop`` would use ``_get_head_sha(cwd)``
    # as the expected head and burn the poll timeout waiting for the remote
    # to match a SHA it will never reach.
    revalidate_success, revalidate_message, revalidate_cost = run_ci_validation_loop(
        cwd=cwd,
        repo_owner=repo_owner,
        repo_name=repo_name,
        issue_number=issue_number,
        max_retries=0,
        step_template=ci_step_template,
        run_agentic_task_fn=run_agentic_task,
        timeout=ci_validation_timeout,
        quiet=quiet,
        expected_head_sha_override=post_checkup_head_sha,
    )

    total_cost = checkup_cost + revalidate_cost
    if not revalidate_success:
        return (
            False,
            (
                f"Final checkup pushed fixes ({pre_checkup_head_sha[:8]}->"
                f"{post_checkup_head_sha[:8]}) but post-push CI re-validation "
                f"failed: {revalidate_message}"
            ),
            total_cost,
            checkup_model,
        )
    return True, checkup_message, total_cost, checkup_model


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
    reasoning_time: Optional[float] = None,
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
        reasoning_time=reasoning_time,
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
    reasoning_time: Optional[float] = None,
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
    step_comments_set: Set[int] = set()
    resumed_from_state = False
    # On resume, restore the workflow-start file snapshot so guards that diff
    # against it (e.g. NOT_A_BUG direct-edit suppression) keep working.
    resumed_initial_file_hashes: Optional[Dict[str, Optional[str]]] = None
    resumed_initial_sha: Optional[str] = None
    # Issue #1001: deferred action computed during resume that must be applied
    # after `success`/`final_message` are initialized below. Default: no-op.
    _resume_deferred_action: Optional[str] = None
    _cached_step9_resume_action: Optional[str] = None
    # On resume, restore the current cycle's start snapshot so the resume-time
    # cycle-waste-breaker can prove no in-cycle progress before authorizing
    # terminal success. None when the saved state is legacy (no snapshot) or
    # was saved after Step 9 completed (the snapshot is stale across cycles).
    resumed_cycle_start_hashes: Optional[Dict[str, Optional[str]]] = None
    # Set by the resume-time Step 3 re-evaluation if the cycle-waste-breaker
    # terminal-success condition holds (Issue #1034). Skips the inner workflow.
    resume_terminal_success = False
    # Issue #1034 follow-up: True when the resumed cycle was mid-flight
    # (last_completed_step > 0, current_cycle > 1) but no cycle_start_hashes
    # was persisted (legacy state file or pre-snapshot interrupt). The outer
    # loop will capture a fresh post-edit snapshot at the cycle-entry point,
    # which would make `_detect_meaningful_changes(cwd, cycle_start_hashes)`
    # falsely report "no in-cycle progress" and let the inline cycle-waste-
    # breaker terminal-success on a baseline it cannot verify. This flag is
    # consulted in the inline cycle-waste-breaker and cleared at the next
    # legitimate cycle rollover.
    cycle_baseline_unverified = False

    # Resume Logic
    if resume:
        loaded_state, gh_id = load_workflow_state(
            cwd, issue_number, workflow_name, state_dir, repo_owner, repo_name, use_github_state
        )
        if loaded_state:
            resumed_from_state = True
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
            # Restore the workflow-start file snapshot so direct-edit detection
            # still sees prior-cycle changes after a resume.
            saved_hashes = loaded_state.get("initial_file_hashes")
            if isinstance(saved_hashes, dict):
                resumed_initial_file_hashes = saved_hashes
            saved_sha = loaded_state.get("initial_sha")
            if isinstance(saved_sha, str) and saved_sha:
                resumed_initial_sha = saved_sha

            step_comments_set = normalize_step_comments_state(
                loaded_state.get("step_comments")
            )

            # Issue #1034 (codex P2 follow-up): restore the current cycle's
            # start snapshot so the resume-time cycle-waste-breaker can prove
            # no in-cycle progress before authorizing terminal success.
            #
            # Restore the snapshot UNCONDITIONALLY here — the cached Step 3
            # NOT_A_BUG demotion below depends on the in-cycle-progress proof,
            # and a stale-snapshot guard cannot run until AFTER
            # ``validate_cached_state`` has had a chance to rewind
            # ``last_completed_step`` (FAILED-rewind from 9 → 2 keeps us in
            # the same cycle). The cycle-rollover branch below
            # (``if last_completed_step >= 9: ...``) is the only place that
            # legitimately invalidates the restored snapshot — when it fires
            # we null the local so the next cycle's body recaptures.
            saved_cycle_start_hashes = loaded_state.get("cycle_start_hashes")
            if isinstance(saved_cycle_start_hashes, dict):
                resumed_cycle_start_hashes = saved_cycle_start_hashes
            else:
                resumed_cycle_start_hashes = None
                # Legacy state file or pre-snapshot-save interrupt: we have
                # no proof of where the cycle started. If we're mid-cycle
                # (last_completed_step > 0) past cycle 1, the inline
                # cycle-waste-breaker MUST be blocked from terminal-success
                # because the fresh capture it gets at outer-loop entry will
                # be post-edits and falsely report "no in-cycle progress".
                if last_completed_step > 0 and current_cycle > 1:
                    cycle_baseline_unverified = True

            # Issue #1034: Re-evaluate cached Step 3 NOT_A_BUG before trusting
            # last_completed_step. If guards (direct edits or FIXED dev_unit_states)
            # would have suppressed NOT_A_BUG, demote the cached entry to
            # "FAILED: NOT_A_BUG_SUPPRESSED_ON_RESUME:<reason>" so the existing
            # validate_cached_state FAILED-rewind reruns Step 3.
            # If the cycle-waste-breaker condition holds on resume (cached
            # NOT_A_BUG + direct edits + no FIXED units + current_cycle > 1),
            # the helper returns NOT_A_BUG_TERMINAL_SUCCESS_ON_RESUME to signal
            # the inline cycle-waste-breaker terminal-success path (mirrors
            # lines 2127-2134 of the inner loop) instead of a demotion.
            has_cached_failed_output = any(
                isinstance(output, str) and output.startswith("FAILED:")
                for output in step_outputs.values()
            )
            if last_completed_step >= 9 and not has_cached_failed_output:
                step9_cached = _resolve_cached_step9_output(step_outputs)
                _cached_step9_resume_action = _post_step9_resume_action(
                    step9_cached, current_cycle, max_cycles, console
                )

            cached_step3 = step_outputs.get("3")
            # A cached Step 9 success is authoritative for a completed inner
            # loop. Step 3's cached raw output was already guarded during the
            # original run, and demoting it here would rewind last_completed_step
            # before the Step 9 success branch can re-verify and fall through.
            skip_step3_resume_reeval = (
                _cached_step9_resume_action == "SUCCESS_FALL_THROUGH"
            )
            if cached_step3 and not skip_step3_resume_reeval:
                demoted = _reevaluate_step3_not_a_bug_on_resume(
                    cached_step3,
                    dev_unit_states=dev_unit_states,
                    initial_file_hashes=resumed_initial_file_hashes,
                    cwd=cwd,
                    quiet=quiet,
                    source="step_outputs",
                    current_cycle=current_cycle,
                    cycle_start_hashes=resumed_cycle_start_hashes,
                )
                if demoted == NOT_A_BUG_TERMINAL_SUCCESS_ON_RESUME:
                    # Honor the inline cycle-waste-breaker terminal-success
                    # path on resume. The cached cycle counter and step
                    # outputs are left untouched (we are about to exit) so the
                    # post-success commit/cleanup/CI branch sees the same
                    # state it would after an inline break.
                    resume_terminal_success = True
                elif demoted is not cached_step3 and demoted != cached_step3:
                    step_outputs["3"] = demoted

            # Issue #467: Validate cached state — correct last_completed_step
            # if any cached step outputs have "FAILED:" prefix.
            last_completed_step = validate_cached_state(
                last_completed_step, step_outputs, quiet=quiet
            )

            _check_staleness(loaded_state, cwd)

            # Issue #1001: If Step 9 was the last completed step, branch on its
            # cached output rather than unconditionally advancing the cycle.
            # Prefer the retry output (stored under "9_retry") when present —
            # otherwise a retry that emitted ALL_TESTS_PASS but was interrupted
            # before the post-Step-9 pause could be misread as a tokenless "9"
            # and silently advance into a fresh cycle.
            if last_completed_step >= 9:
                if _cached_step9_resume_action is not None:
                    resume_action = _cached_step9_resume_action
                else:
                    step9_cached = _resolve_cached_step9_output(step_outputs)
                    resume_action = _post_step9_resume_action(
                        step9_cached, current_cycle, max_cycles, console
                    )
                if resume_action == "ADVANCE_CYCLE":
                    current_cycle += 1
                    last_completed_step = 0
                    step_outputs = {}  # Clear outputs for new cycle
                    # Cycle rollover invalidates the restored snapshot; it
                    # belongs to the just-completed cycle. Null it so the new
                    # cycle body recaptures fresh hashes.
                    resumed_cycle_start_hashes = None
                    cycle_baseline_unverified = False
                elif resume_action == "MAX_CYCLES_REACHED":
                    # Defer surfacing the failure until after `success` and
                    # `final_message` are initialized below — mirrors the
                    # path used by _apply_step9_resolved_token's
                    # MAX_CYCLES_REACHED handler (final_message set, outer
                    # loop skipped, post-loop failure handler runs).
                    _resume_deferred_action = "MAX_CYCLES_REACHED"
                elif resume_action == "SUCCESS_FALL_THROUGH":
                    # Step 9 already declared success but workflow was
                    # interrupted before commit/Step 11/Step 10. Defer
                    # setting `success=True` until after its initialization
                    # so we fall through to the success path (commit, code
                    # cleanup, CI validation).
                    _resume_deferred_action = "SUCCESS_FALL_THROUGH"
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

    # Snapshot file state before workflow (for hash-based commit detection).
    # On resume, prefer the snapshot saved with the workflow state — recapturing
    # here would include prior cycles' edits and break direct-edit detection.
    if resumed_initial_file_hashes is not None:
        initial_file_hashes = resumed_initial_file_hashes
    else:
        initial_file_hashes = _get_file_hashes(cwd)

    # Capture initial commit SHA for full diff in Step 11
    if resumed_initial_sha:
        initial_sha = resumed_initial_sha
    else:
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

    def _persist_resume_reverification_state() -> None:
        nonlocal github_comment_id

        state_data_resume = {
            "workflow": workflow_name,
            "issue_url": issue_url,
            "issue_number": issue_number,
            "current_cycle": current_cycle,
            "last_completed_step": last_completed_step,
            "step_outputs": step_outputs.copy(),
            "dev_unit_states": dev_unit_states.copy(),
            "total_cost": total_cost,
            "model_used": model_used,
            "changed_files": changed_files.copy(),
            "skipped_steps": {str(k): v for k, v in skipped_steps.items()},
            "last_saved_at": datetime.now().isoformat(),
            "github_comment_id": github_comment_id,
            "step_comments": sorted(step_comments_set),
            "initial_file_hashes": dict(initial_file_hashes),
            "initial_sha": initial_sha,
            # Persist None when the resumed cycle's baseline is unverified
            # (legacy state / pre-snapshot interrupt) — otherwise the next
            # resume would trust the fresh post-edit snapshot and immediately
            # terminal-success.
            "cycle_start_hashes": (
                None if cycle_baseline_unverified
                else (
                    dict(resumed_cycle_start_hashes)
                    if isinstance(resumed_cycle_start_hashes, dict)
                    else None
                )
            ),
        }
        try:
            new_gh_id = save_workflow_state(
                cwd,
                issue_number,
                workflow_name,
                state_data_resume,
                state_dir,
                repo_owner,
                repo_name,
                use_github_state,
                github_comment_id,
            )
            if new_gh_id:
                github_comment_id = new_gh_id
        except Exception as save_exc:
            logger.debug(
                "Best-effort resume-reverify state save failed: %s",
                save_exc,
                exc_info=True,
            )

    # Issue #1033: a prior run can persist Step 2's raw ALL_TESTS_PASS before
    # independent verification. Re-check cached pass tokens before the resume
    # skip at the top of the inner loop can trust them.
    if resumed_from_state and last_completed_step >= 2:
        step2_cached_token = _classify_step_output(
            step_outputs.get("2", ""), step_num=2
        )
        if step2_cached_token in ("ALL_TESTS_PASS", "LOCAL_TESTS_PASS"):
            test_files = _extract_test_files(
                issue_content, changed_files, cwd, initial_file_hashes
            )
            verified = False
            verify_output = "no test files found for independent verification"
            if test_files:
                verified, verify_output = _verify_tests_independently(test_files, cwd)
                if _fallback_scan_was_capped and verified:
                    verified = False
                    verify_output += (
                        f"\nFALLBACK_CAPPED: Only {len(test_files)} of potentially "
                        "hundreds of test files were verified; cannot confirm full "
                        "suite pass."
                    )
            else:
                console.print(
                    "[bold red]No test files found for cached Step 2 resume "
                    "verification. Cannot trust cached pass.[/bold red]"
                )

            if verified:
                console.print("[green]Cached Step 2 pass verified on resume.[/green]")
                if last_completed_step == 2 and _resume_deferred_action is None:
                    success = True
                    final_message = (
                        "All tests passed (cached Step 2 pass independently "
                        "verified on resume)."
                    )
            else:
                console.print(
                    "[bold red]Cached Step 2 pass failed independent "
                    "verification on resume.[/bold red]"
                )
                step_outputs["2"] = (
                    f"FAILED: VERIFICATION_FAILED_ON_RESUME: {verify_output}"
                )
                last_completed_step = 1
                _resume_deferred_action = None
                _persist_resume_reverification_state()

    # Issue #1001 round 11: save-before-verify race.
    # The inner-loop state save at line ~2049 persists step_outputs["9"] with
    # the LLM's raw output BEFORE the independent verification at line ~2061 /
    # _apply_step9_resolved_token at line ~2154 runs. A process pause in that
    # window can leave disk state with ALL_TESTS_PASS even though verification
    # would have failed. Re-run _verify_tests_independently on resume to close
    # the race BEFORE treating the cycle as terminal. On failure, demote the
    # resume action to ADVANCE_CYCLE (or MAX_CYCLES_REACHED if budget
    # exhausted) and overwrite step_outputs["9"] with a
    # FAILED: VERIFICATION_FAILED_ON_RESUME: prefix so the cached state
    # reflects reality.
    if _resume_deferred_action == "SUCCESS_FALL_THROUGH":
        test_files = _extract_test_files(
            issue_content, changed_files, cwd, initial_file_hashes
        )
        if test_files:
            verified, verify_output = _verify_tests_independently(test_files, cwd)
            # Mirror the cap-downgrade in _apply_step9_resolved_token for
            # symmetry with the initial Step 9 verification path.
            if _fallback_scan_was_capped and verified:
                verified = False
                verify_output += (
                    f"\nFALLBACK_CAPPED: Only {len(test_files)} of potentially "
                    "hundreds of test files were verified; cannot confirm full "
                    "suite pass."
                )
            if not verified:
                console.print(
                    "[yellow]Resume re-verification: cached Step 9 success no "
                    "longer verified by independent pytest run; advancing "
                    "cycle.[/yellow]"
                )
                step_outputs["9"] = (
                    f"FAILED: VERIFICATION_FAILED_ON_RESUME: {verify_output}"
                )

                _persist_resume_reverification_state()

                if current_cycle < max_cycles:
                    current_cycle += 1
                    last_completed_step = 0
                    step_outputs = {}  # ADVANCE_CYCLE: clear for new cycle
                    resumed_cycle_start_hashes = None
                    cycle_baseline_unverified = False
                    _resume_deferred_action = None
                else:
                    _resume_deferred_action = "MAX_CYCLES_REACHED"
        # else: no test files — match the initial-flow fallback (no
        # independent verification possible). Trust the cached token, fall
        # through to the existing SUCCESS_FALL_THROUGH handling below.

    # Issue #1001: Apply deferred resume action now that `success` and
    # `final_message` exist. Mirrors how the in-cycle Step 9 handler
    # surfaces these tokens via _apply_step9_resolved_token.
    if _resume_deferred_action == "SUCCESS_FALL_THROUGH":
        success = True
        final_message = "All tests passed after fixes (resumed)."
    elif _resume_deferred_action == "MAX_CYCLES_REACHED":
        final_message = "Max cycles reached."

    # Resume-time cycle-waste-breaker terminal success (Issue #1034): if the
    # resume guard detected the inline cycle-waste-breaker condition for the
    # cached Step 3 NOT_A_BUG, skip the inner workflow and fall straight into
    # the success branch (commit, Step 11 cleanup, CI) just like the inline
    # path at lines 2127-2134.
    if resume_terminal_success:
        success = True
        final_message = NOT_A_BUG_TERMINAL_SUCCESS_MESSAGE
        if not quiet:
            console.print(
                f"[yellow]NOT_A_BUG with prior direct edits and no new progress "
                f"this cycle (resumed cycle {current_cycle}) — treating prior fix "
                f"as terminal.[/yellow]"
            )

    try:
        # Outer Loop
        if current_cycle == 0:
            current_cycle = 1

        while current_cycle <= max_cycles and not success:
            console.print(f"\n[bold cyan][Cycle {current_cycle}/{max_cycles}] Starting fix cycle...[/bold cyan]")

            # Snapshot file hashes at cycle start for convergence detection (5b).
            # Issue #1034 (codex P2 follow-up): on resume, reuse the restored
            # snapshot so the in-cycle progress check sees what the prior
            # session captured. Only the FIRST iteration of the outer loop
            # consumes the resumed snapshot — subsequent cycles must
            # recapture fresh hashes (otherwise cycles 3, 4, ... would diff
            # against the stale cycle-2 snapshot).
            if resumed_cycle_start_hashes is not None:
                cycle_start_hashes = resumed_cycle_start_hashes
                resumed_cycle_start_hashes = None
            else:
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

                # Skip redundant diagnosis steps when pdd-bug already analyzed (Issue #830).
                # Issue #1034: Re-evaluate any cached Step 3 NOT_A_BUG token from
                # bug_step_outputs symmetrically with the resume-time step_outputs
                # guard, before short-circuiting Step 3.
                if str(step_num) in bug_step_outputs and current_cycle == 1:
                    if step_num == 3:
                        cached_bug3 = bug_step_outputs.get("3", "")
                        # This branch only runs at current_cycle==1, so the
                        # cycle-waste-breaker terminal-success path inside the
                        # helper (which requires current_cycle > 1) is
                        # irrelevant here. Pass current_cycle=None and
                        # cycle_start_hashes=None explicitly to keep the helper
                        # signature consistent and avoid trusting an
                        # unrelated outer-loop snapshot.
                        demoted_bug3 = _reevaluate_step3_not_a_bug_on_resume(
                            cached_bug3,
                            dev_unit_states=dev_unit_states,
                            initial_file_hashes=initial_file_hashes,
                            cwd=cwd,
                            quiet=quiet,
                            source="bug_step_outputs",
                            current_cycle=None,
                            cycle_start_hashes=None,
                        )
                        if demoted_bug3 != cached_bug3:
                            # Drop the suppressed entry from both caches and fall
                            # through to run Step 3 fresh.
                            bug_step_outputs.pop("3", None)
                            # If we pre-populated step_outputs["3"] from this stale
                            # bug-state entry, clear it so the step actually runs.
                            if step_outputs.get("3") == cached_bug3:
                                step_outputs.pop("3", None)
                        else:
                            console.print(f"[bold][Step {step_num}/9] Reusing pdd-bug analysis[/bold]")
                            last_completed_step = step_num
                            continue
                    else:
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
                    reasoning_time=reasoning_time,
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
                        reasoning_time=reasoning_time,
                    )
                    step_cost += retry_cost

                # 4. Store Output & Accumulate
                # Only mark step completed if it succeeded; failed steps get "FAILED:" prefix
                # and last_completed_step stays at previous step (ensures resume re-runs failed step)
                if step_success:
                    step_outputs[str(step_num)] = step_output
                    last_completed_step = step_num
                    try:
                        _report_body = extract_step_report(step_output)
                        if not _report_body:
                            _report_body = (
                                f"_Step {step_num} completed; no `<step_report>` "
                                "block returned by agent. Raw output retained in "
                                "workflow state._"
                            )
                        _step_desc = STEP_DESCRIPTIONS.get(step_num, "")
                        _comment_body = (
                            f"## Step {step_num}/11: {_step_desc}\n\n{_report_body}"
                        )
                        post_step_comment_once(
                            repo_owner=repo_owner,
                            repo_name=repo_name,
                            issue_number=issue_number,
                            step_num=current_cycle * 10000 + step_num,
                            body=_comment_body,
                            posted_steps=step_comments_set,
                            cwd=cwd,
                        )
                    except Exception as _exc:  # pylint: disable=broad-except
                        console.print(f"[yellow]post_step_comment_once failed: {_exc}[/yellow]")
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
                    "github_comment_id": github_comment_id,
                    "step_comments": sorted(step_comments_set),
                    # Workflow-start snapshot — restored on resume so direct-edit
                    # detection survives interruption.
                    "initial_file_hashes": dict(initial_file_hashes),
                    "initial_sha": initial_sha,
                    # Current-cycle start snapshot (Issue #1034 codex P2 follow-up):
                    # persisted so the resume-time cycle-waste-breaker can prove
                    # no in-cycle progress before authorizing terminal success.
                    # NOTE: distinguish `{}` (clean-tree baseline; any file
                    # present later in the cycle is in-cycle progress) from
                    # `None` (truly missing / post-rollover sentinel). The
                    # truthy check `if cycle_start_hashes else None` would
                    # collapse `{}` to `None` and trick resume into thinking
                    # the baseline is missing, recapturing the post-edit tree
                    # and mis-reporting no progress.
                    # Persist None when the resumed cycle's baseline is
                    # unverified (legacy state / pre-snapshot interrupt) —
                    # the in-memory cycle_start_hashes was either restored
                    # from a stale prior session save or freshly captured
                    # post-edit; either way the next resume must not trust
                    # it.
                    "cycle_start_hashes": (
                        None if cycle_baseline_unverified
                        else (
                            dict(cycle_start_hashes)
                            if isinstance(cycle_start_hashes, dict)
                            else None
                        )
                    ),
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
                    has_direct_edits = bool(_detect_meaningful_changes(cwd, initial_file_hashes))
                    if has_fixed_units or has_direct_edits:
                        # Cycle-waste safeguard: if only direct edits (no PDD fix) and
                        # this cycle made no meaningful progress, treat the prior fix as
                        # terminal and exit successfully instead of looping.
                        has_cycle_progress = bool(
                            _detect_meaningful_changes(cwd, cycle_start_hashes)
                        )
                        if (
                            has_direct_edits
                            and not has_fixed_units
                            and not has_cycle_progress
                            and current_cycle > 1
                            and not cycle_baseline_unverified
                        ):
                            console.print(
                                "[yellow]NOT_A_BUG with prior direct edits and no new progress "
                                "this cycle — treating prior fix as terminal.[/yellow]"
                            )
                            success = True
                            final_message = "Direct-edit fix applied in a prior cycle; Step 3 classifies remaining state as not a bug."
                            break
                        if cycle_baseline_unverified:
                            console.print(
                                "[yellow]Resumed cycle baseline unverified (no saved cycle_start_hashes); "
                                "refusing terminal-success and falling through to continue the cycle.[/yellow]"
                            )
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
                            reasoning_time=reasoning_time,
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
            has_direct_edits = bool(_detect_meaningful_changes(cwd, initial_file_hashes))
            if step_num == 3 and _classify_step_output(step_outputs.get("3", ""), step_num=3) == "NOT_A_BUG" and not has_fixed_units and not has_direct_edits:
                break

            # Check if workflow was stopped due to missing loop control token or max cycles
            if final_message:
                break
            
            # Prepare for next cycle.
            # Issue #1034 (codex P2 follow-up): null the local snapshot
            # BEFORE mutating cycle counters. An interrupt that lands
            # after current_cycle/last_completed_step are advanced but
            # before this assignment would otherwise be saved by the
            # KeyboardInterrupt/Exception handlers (which read locals())
            # as the new cycle's snapshot — stale, and the resume-time
            # rollover guard (which only discards when
            # last_completed_step >= 9) would not catch it because
            # last_completed_step is already 0 by then. The next
            # iteration's recapture (line ~1905) is the authoritative
            # source for the new cycle.
            cycle_start_hashes = None
            current_cycle += 1
            last_completed_step = 0
            step_outputs = {} # Clear outputs for next cycle
            # The next cycle's body recaptures cycle_start_hashes fresh
            # at outer-loop entry, giving the inline cycle-waste-breaker
            # a verifiable baseline. The resume-time legacy-state flag
            # can be cleared here.
            cycle_baseline_unverified = False

            state_data["current_cycle"] = current_cycle
            state_data["last_completed_step"] = 0
            state_data["step_outputs"] = {}
            state_data["last_saved_at"] = datetime.now().isoformat()
            # Issue #1034 codex P2 follow-up: the just-completed cycle's
            # cycle_start_hashes is stale for the next cycle. Clear it so
            # any resume from this transitional state falls back to the
            # conservative demote-and-rerun-Step-3 path instead of
            # diffing against the wrong cycle's snapshot. The next cycle's
            # body recaptures a fresh snapshot.
            state_data["cycle_start_hashes"] = None

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
                    reasoning_time=reasoning_time,
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

                checkup_success, checkup_message, checkup_cost, checkup_model = (
                    _run_final_checkup_on_pr(
                        issue_url=issue_url,
                        issue_number=issue_number,
                        repo_owner=repo_owner,
                        repo_name=repo_name,
                        cwd=cwd,
                        verbose=verbose,
                        quiet=quiet,
                        timeout_adder=timeout_adder,
                        use_github_state=use_github_state,
                        reasoning_time=reasoning_time,
                        ci_step_template=step10_template,
                        ci_validation_timeout=E2E_FIX_STEP_TIMEOUTS[10] + timeout_adder,
                    )
                )
                total_cost += checkup_cost
                if checkup_model:
                    model_used = checkup_model
                if not checkup_success:
                    return False, checkup_message, total_cost, model_used, changed_files
                if checkup_message not in {
                    "No open PR found for current branch; skipping final checkup",
                }:
                    final_message = checkup_message

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
        # Capture the workflow-start snapshot and current-cycle snapshot if
        # they were initialized; an interrupt before initialization leaves
        # these as locals that may not exist, so guard with locals().get().
        _interrupt_initial_hashes = locals().get("initial_file_hashes")
        _interrupt_initial_sha = locals().get("initial_sha")
        _interrupt_cycle_start_hashes = locals().get("cycle_start_hashes")
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
            "github_comment_id": github_comment_id,
            "step_comments": sorted(step_comments_set),
            # Issue #1034 codex P2 follow-up: persist workflow-start and
            # cycle-start snapshots so resume after an interrupt still has
            # the data needed for direct-edit detection and the cycle-waste-
            # breaker in-cycle-progress proof.
            "initial_file_hashes": (
                dict(_interrupt_initial_hashes)
                if isinstance(_interrupt_initial_hashes, dict)
                else None
            ),
            "initial_sha": _interrupt_initial_sha if isinstance(_interrupt_initial_sha, str) else None,
            # If the cycle was running on an unverified baseline, save None
            # so the next resume re-detects "unverified" via the missing-
            # snapshot path rather than trusting a stale post-edit local.
            "cycle_start_hashes": (
                None
                if locals().get("cycle_baseline_unverified", False)
                else (
                    dict(_interrupt_cycle_start_hashes)
                    if isinstance(_interrupt_cycle_start_hashes, dict)
                    else None
                )
            ),
        }
        save_workflow_state(
            cwd, issue_number, workflow_name, state_data, state_dir, repo_owner, repo_name, use_github_state, github_comment_id
        )
        raise

    except Exception as e:
        console.print(f"\n[bold red]Fatal error: {e}[/bold red]")
        try:
            # Same locals().get() guard as the KeyboardInterrupt handler:
            # the exception may fire before initial_file_hashes etc. are
            # initialized.
            _exc_initial_hashes = locals().get("initial_file_hashes")
            _exc_initial_sha = locals().get("initial_sha")
            _exc_cycle_start_hashes = locals().get("cycle_start_hashes")
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
                "github_comment_id": github_comment_id,
                "step_comments": sorted(step_comments_set),
                # Issue #1034 codex P2 follow-up: persist workflow-start and
                # cycle-start snapshots so resume after a fatal exception
                # still has the data needed for direct-edit detection and
                # the cycle-waste-breaker in-cycle-progress proof.
                "initial_file_hashes": (
                    dict(_exc_initial_hashes)
                    if isinstance(_exc_initial_hashes, dict)
                    else None
                ),
                "initial_sha": _exc_initial_sha if isinstance(_exc_initial_sha, str) else None,
                # If the cycle was running on an unverified baseline, save
                # None so the next resume re-detects "unverified" via the
                # missing-snapshot path rather than trusting a stale post-
                # edit local.
                "cycle_start_hashes": (
                    None
                    if locals().get("cycle_baseline_unverified", False)
                    else (
                        dict(_exc_cycle_start_hashes)
                        if isinstance(_exc_cycle_start_hashes, dict)
                        else None
                    )
                ),
            }
            save_workflow_state(
                cwd, issue_number, workflow_name, state_data, state_dir, repo_owner, repo_name, use_github_state, github_comment_id
            )
        except Exception:
            pass
        return False, f"Stopped at cycle {current_cycle} step {last_completed_step}: {str(e)}", total_cost, model_used, changed_files
