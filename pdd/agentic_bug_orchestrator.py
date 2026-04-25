from __future__ import annotations

import logging
import os
import re
import shlex
import shutil
import subprocess
from collections import defaultdict
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
logger = logging.getLogger(__name__)

# Per-Step Timeouts (Workflow specific)
BUG_STEP_TIMEOUTS: Dict[int, float] = {
    1: 240.0,    # Duplicate Check
    2: 400.0,    # Docs Check
    3: 400.0,    # Triage
    4: 400.0,    # API Research
    5: 600.0,    # Reproduce (Complex)
    6: 600.0,    # Root Cause (Complex)
    7: 600.0,    # Prompt Classification (may auto-fix prompts)
    8: 340.0,    # Test Plan
    9: 1000.0,   # Generate Unit Test (Most Complex)
    10: 600.0,   # Verify Unit Test
    11: 2000.0,  # E2E Test (Complex - needs to discover env & run tests)
    12: 240.0,   # Create PR
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


def _resolve_main_ref(git_root: Path) -> str:
    """Resolve the main branch ref for use as worktree base.

    Returns a commit hash when a named ref is found, or the literal
    string "HEAD" as a last resort.  Checks origin/main, origin/master,
    main, master (in that order).
    """
    for ref in ("origin/main", "origin/master", "main", "master"):
        result = subprocess.run(
            ["git", "rev-parse", "--verify", ref],
            cwd=git_root, capture_output=True, text=True,
        )
        if result.returncode == 0:
            return result.stdout.strip()
    # Last resort — current HEAD
    return "HEAD"


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
            # Resolve main branch as base — avoids leaking unrelated commits
            # when user runs pdd bug from a non-main branch.
            base_ref = _resolve_main_ref(git_root)
            cmd = ["git", "worktree", "add", "-b", branch_name, str(worktree_path), base_ref]
        subprocess.run(
            cmd,
            cwd=git_root,
            capture_output=True,
            check=True
        )
        # Reset branch to main HEAD if we reused an undeletable branch
        if reset_after_attach:
            main_ref = _resolve_main_ref(git_root)
            subprocess.run(
                ["git", "reset", "--hard", main_ref],
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


def _count_planned_tests(step8_output: str) -> int:
    """Count planned tests from Step 8's PLANNED_TEST_COUNT marker.

    Falls back to counting '#### Test N:' headers if marker is absent.
    """
    match = re.search(r"PLANNED_TEST_COUNT:\s*(\d+)", step8_output)
    if match:
        return int(match.group(1))
    # Fallback: count markdown headers (for older runs without marker)
    return len(re.findall(r"####\s+Test\s+\d+:", step8_output))


def _count_generated_tests(file_paths: List[str], cwd: Path) -> Tuple[int, int]:
    """Count test functions in files on disk.

    Returns (total_test_functions, stub_count).
    A stub is a test function whose body is only a docstring, pass, or ellipsis.
    Uses regex heuristic — no AST parsing needed.
    """
    # Matches def test_xxx(...): followed by lines that are only
    # whitespace, docstrings, pass, or ... (i.e. a stub body)
    stub_pattern = re.compile(
        r"(?:async\s+)?def\s+test_\w+\s*\([^)]*\)[^:]*:\s*\n"
        r"(?:\s*(?:#[^\n]*)?\n)*"                # optional blank/comment lines
        r'(?:\s*(?:"""[\s\S]*?"""|\'\'\'[\s\S]*?\'\'\')\s*\n)?'  # optional docstring
        r"(?:\s*(?:pass|\.\.\.)\s*\n?)*"          # only pass/... remaining
        r"\s*(?=\n\S|\n*$)",                      # followed by dedent or EOF
    )
    total = 0
    stubs = 0
    for fpath in file_paths:
        abs_path = (cwd / fpath) if not Path(fpath).is_absolute() else Path(fpath)
        if not abs_path.exists():
            continue
        content = abs_path.read_text()
        total += len(re.findall(r"(?:async\s+)?def\s+test_", content))
        stubs += len(stub_pattern.findall(content))
    return total, stubs


def _parse_changed_files(output: str, marker: str) -> List[str]:
    """Extract file paths from marker lines (multiple lines and comma-separated)."""
    files = []
    for match in re.finditer(rf"{marker}:\s*(.*)", output):
        files.extend([f.strip() for f in match.group(1).split(",") if f.strip()])
    return files


def _parse_fix_locations(step6_output: str) -> List[str]:
    """Extract fix locations from Step 6's FIX_LOCATIONS marker.

    Returns a deduplicated list of file paths (stripped of whitespace and backticks).
    Reuses _parse_changed_files for the core parsing logic.
    """
    raw = _parse_changed_files(step6_output, "FIX_LOCATIONS")
    seen: set[str] = set()
    deduped: List[str] = []
    for f in raw:
        cleaned = f.strip("`")
        if cleaned and cleaned not in seen:
            seen.add(cleaned)
            deduped.append(cleaned)
    return deduped


def _parse_expansion_items(step6_output: str) -> str:
    """Extract expansion items from Step 6's EXPANSION_ITEMS marker.

    Returns a deduplicated comma-separated string of expansion items, or "none"
    if the marker is absent, empty, or explicitly "none" (SCOPE_MATCH / NO_PROPOSED_FIX).
    """
    match = re.search(r"EXPANSION_ITEMS:\s*(.+)", step6_output)
    if not match:
        return "none"
    raw = match.group(1).strip()
    if not raw or raw.lower() == "none":
        return "none"
    seen: set[str] = set()
    deduped: List[str] = []
    for item in raw.split(","):
        cleaned = item.strip()
        if cleaned and cleaned not in seen:
            seen.add(cleaned)
            deduped.append(cleaned)
    return ", ".join(deduped) if deduped else "none"


# Maximum number of unclassified grep matches to process.
_MAX_GREP_RESULTS = 50

# Directories to exclude from grep searches.
_GREP_EXCLUDE_DIRS = (
    ".git", ".pdd", "node_modules", "__pycache__", ".venv", "venv",
    "dist", "build", ".tox", ".mypy_cache", ".pytest_cache",
)

# Extensions to exclude from grep — these are data/config/doc formats where
# code-pattern matches are noise, not bugs.
_GREP_SKIP_EXTENSIONS = {
    ".csv", ".json", ".jsonl", ".yaml", ".yml", ".toml", ".ini", ".xml",
    ".md", ".rst", ".txt", ".log", ".html", ".css", ".less", ".sass",
    ".scss", ".svg", ".graphql", ".prisma", ".proto", ".hbs", ".ejs",
    ".pug", ".twig", ".jinja2", ".tex",
}


def _get_code_extensions() -> list[str]:
    """Read code-bearing file extensions from PDD's language_format.csv.

    Returns glob patterns like ['*.py', '*.js', ...] for use with grep --include.
    Falls back to a minimal hardcoded set if the CSV is unavailable.
    """
    try:
        from .path_resolution import get_default_resolver
        resolver = get_default_resolver()
        csv_path = resolver.resolve_data_file("data/language_format.csv")
        with open(csv_path) as f:
            extensions: set[str] = set()
            for i, line in enumerate(f):
                if i == 0:
                    continue  # skip header
                parts = line.strip().split(",")
                if len(parts) >= 3:
                    ext = parts[2].strip()
                    if ext and ext.startswith(".") and ext not in _GREP_SKIP_EXTENSIONS:
                        extensions.add(ext)
        if extensions:
            return sorted(f"*{ext}" for ext in extensions)
    except Exception:
        pass
    # Fallback: common code extensions if CSV is unavailable
    return [
        "*.py", "*.js", "*.ts", "*.tsx", "*.jsx", "*.rb", "*.go",
        "*.java", "*.rs", "*.swift", "*.kt", "*.c", "*.cpp", "*.h",
        "*.hpp", "*.cs", "*.sh", "*.php", "*.scala", "*.ex", "*.erl",
    ]


def _parse_pattern_search(step6_output: str) -> Optional[str]:
    """Extract the PATTERN_SEARCH regex from Step 6 output.

    Returns the first PATTERN_SEARCH value, stripped of whitespace, backticks,
    and trailing comments (e.g. "# broad pattern"), or None if no marker is
    present.
    """
    match = re.search(r"PATTERN_SEARCH:\s*(.*)", step6_output)
    if not match:
        return None
    pattern = match.group(1).strip().strip("`")
    # Strip trailing comment — LLM may write: PATTERN_SEARCH: \.glob\( # broad pattern
    # The \s+#\s+ requirement (spaces on both sides) avoids corrupting regex
    # character classes like [a-z#] where # has no surrounding spaces.
    pattern = re.sub(r"\s+#\s+.*$", "", pattern)
    return pattern if pattern else None


def _sanitize_grep_pattern(pattern: str) -> Optional[str]:
    """Validate and sanitize a grep pattern from LLM output.

    Returns the pattern if safe, or None if it should be rejected.
    """
    if not pattern or len(pattern) < 3:
        return None
    # Reject pure wildcards that would match everything
    if pattern.strip() in (".*", ".+", ".?", ".*?", ".+?"):
        return None
    # Reject shell metacharacters (defense in depth — subprocess.run with
    # shell=False doesn't interpret these, but reject them anyway).
    # Note: | is valid regex alternation and safe with shell=False.
    dangerous_chars = set(";&$`\n\r")
    if dangerous_chars.intersection(pattern):
        return None
    # Reject patterns longer than 200 chars (likely malformed)
    if len(pattern) > 200:
        return None
    return pattern


def _extract_match_context(
    matches: List[Tuple[str, int, str]],
    work_dir: Path,
    context_before: int = 30,
    context_after: int = 10,
) -> Dict[str, str]:
    """Read surrounding code around grep matches.

    For each match, reads the source file and extracts a window of
    [line - context_before, line + context_after].  Overlapping windows
    within the same file are merged.

    Args:
        matches: List of (filepath, line_number, matching_line) tuples.
        work_dir: Working directory (repo root).
        context_before: Lines to include before the match (default 30).
        context_after: Lines to include after the match (default 10).

    Returns:
        Dict mapping filepath to formatted context string with line numbers.
    """
    # Group matches by file
    matches_by_file: Dict[str, List[int]] = defaultdict(list)
    for filepath, line_num, _ in matches:
        matches_by_file[filepath].append(line_num)

    result: Dict[str, str] = {}
    for filepath, line_nums in matches_by_file.items():
        abs_path = work_dir / filepath
        try:
            file_lines = abs_path.read_text().splitlines()
        except (OSError, UnicodeDecodeError):
            result[filepath] = ""
            continue

        if not file_lines:
            result[filepath] = ""
            continue

        total_lines = len(file_lines)

        # Compute ranges and merge overlapping ones
        ranges: List[Tuple[int, int]] = []
        for ln in sorted(line_nums):
            start = max(1, ln - context_before)
            end = min(total_lines, ln + context_after)
            if ranges and start <= ranges[-1][1] + 1:
                # Merge with previous range
                ranges[-1] = (ranges[-1][0], max(ranges[-1][1], end))
            else:
                ranges.append((start, end))

        # Format context with line numbers
        sections: List[str] = []
        for start, end in ranges:
            lines_out = []
            for i in range(start, end + 1):
                lines_out.append(f"{i:>6}  {file_lines[i - 1]}")
            sections.append("\n".join(lines_out))

        result[filepath] = "\n...\n".join(sections)

    return result


def _verify_pattern_completeness(
    pattern: str,
    fix_locations: List[str],
    work_dir: Path,
) -> Tuple[List[Tuple[str, int, str]], str]:
    """Run a deterministic grep and find matches missing from FIX_LOCATIONS.

    Args:
        pattern: A grep-compatible regex pattern (already sanitized).
        fix_locations: File paths listed in FIX_LOCATIONS by the LLM.
        work_dir: Working directory (repo root) to search in.

    Returns:
        (unclassified_matches, grep_summary) where unclassified_matches is a
        list of (filepath, line_number, content) tuples for matches in files
        NOT in fix_locations, and grep_summary is a human-readable log.
    """
    safe_pattern = _sanitize_grep_pattern(pattern)
    if not safe_pattern:
        return [], f"Pattern rejected by sanitizer: {pattern!r}"

    cmd = [
        "grep", "-rEnI",
    ]
    for exclude_dir in _GREP_EXCLUDE_DIRS:
        cmd.append(f"--exclude-dir={exclude_dir}")
    for ext_glob in _get_code_extensions():
        cmd.append(f"--include={ext_glob}")
    cmd.extend([
        "--",  # terminate options so pattern can't be parsed as a flag
        safe_pattern,
        ".",
    ])

    try:
        result = subprocess.run(
            cmd,
            cwd=work_dir,
            capture_output=True,
            text=True,
            timeout=30,
        )
    except subprocess.TimeoutExpired:
        return [], f"Grep timed out after 30s for pattern: {safe_pattern!r}"
    except (OSError, FileNotFoundError):
        return [], "grep binary not found"

    # Exit code 2 means grep rejected the regex as invalid.
    # Exit code 1 means no matches found (not an error).
    if result.returncode == 2:
        err = result.stderr.strip().splitlines()[0] if result.stderr.strip() else "invalid regex"
        return [], f"Grep rejected pattern {safe_pattern!r}: {err}"

    # Normalize fix_locations for comparison.
    # Bare names from the LLM (sync_main.py) match any grep path with that
    # basename. Full paths (pdd/sync_main.py) only match exact paths or bare
    # names — they do NOT match other_dir/sync_main.py (different file).
    fix_full_paths: set[str] = set()
    fix_bare_names: set[str] = set()
    for f in fix_locations:
        cleaned = f.removeprefix("./").removeprefix("/")
        fix_full_paths.add(cleaned)
        if "/" not in cleaned:
            fix_bare_names.add(cleaned)

    def _is_in_fix_locations(filepath: str) -> bool:
        """Check if a grep-found filepath is already in FIX_LOCATIONS."""
        if filepath in fix_full_paths:
            return True
        base = Path(filepath).name
        # A bare name in fix_locations covers any matching filepath
        if base in fix_bare_names:
            return True
        # A full path in fix_locations does NOT cover a different-dir file
        # with the same basename (pdd/utils.py does not cover tests/utils.py)
        return False

    # Parse grep -n output: ./file.py:123:matching line content
    all_matches: List[Tuple[str, int, str]] = []
    for line in result.stdout.strip().splitlines():
        line = line.strip().removeprefix("./")
        if not line:
            continue
        parts = line.split(":", 2)
        if len(parts) >= 3:
            filepath = parts[0]
            try:
                line_num = int(parts[1])
            except ValueError:
                continue
            content = parts[2]
            all_matches.append((filepath, line_num, content))

    # Filter to matches from files NOT already in FIX_LOCATIONS
    unclassified_all: List[Tuple[str, int, str]] = []
    unclassified_files: set[str] = set()
    for filepath, line_num, content in all_matches:
        if not _is_in_fix_locations(filepath):
            unclassified_all.append((filepath, line_num, content))
            unclassified_files.add(filepath)

    total_files = len({m[0] for m in all_matches})
    summary_parts = [
        f"Grep found {total_files} file(s) matching pattern {safe_pattern!r}",
        f", FIX_LOCATIONS lists {len(fix_locations)} file(s)",
        f", {len(unclassified_files)} unclassified file(s)",
    ]

    return unclassified_all, "".join(summary_parts)


def _parse_classification_evidence(
    retry_output: str,
) -> Tuple[List[str], List[str]]:
    """Parse NEEDS_FIX / SAFE_EVIDENCE markers from retry LLM output.

    Returns:
        (needs_fix_files, safe_files) — deduplicated lists of file paths.
    """
    needs_fix: List[str] = []
    safe: List[str] = []
    seen: set[str] = set()

    for match in re.finditer(r"NEEDS_FIX:\s*(.*)", retry_output):
        filepath = match.group(1).strip().strip("`")
        if filepath and filepath not in seen:
            needs_fix.append(filepath)
            seen.add(filepath)

    for match in re.finditer(r"SAFE_EVIDENCE:\s*(.*)", retry_output):
        raw = match.group(1).strip().strip("`")
        # Format: filepath | line_number | reason
        parts = raw.split("|", 2)
        filepath = parts[0].strip().strip("`")
        if filepath and filepath not in seen:
            safe.append(filepath)
            seen.add(filepath)

    return needs_fix, safe


def _merge_fix_locations(
    original_fix_locs: List[str],
    needs_fix: List[str],
    safe: List[str],
    unclassified_filenames: List[str],
) -> List[str]:
    """Merge grep verification results into FIX_LOCATIONS using union semantics.

    Rules:
    - Original FIX_LOCATIONS are immutable (never removed)
    - New NEEDS_FIX files are added
    - Unclassified files (no evidence either way) default to NEEDS_FIX
    - SAFE_EVIDENCE files are excluded UNLESS they were in the original list

    Path normalization: the LLM may return basenames (agentic_update.py) while
    grep returns full paths (pdd/agentic_update.py). Basename matching is used
    to check if a file was *classified* by the LLM (so it doesn't get the
    conservative default), but full-path comparison is used for deduplication
    in the merged list. This ensures tests/utils.py and pdd/utils.py are both
    added even when the LLM classified bare "utils.py".
    """
    merged: List[str] = list(dict.fromkeys(original_fix_locs))
    merged_set: set[str] = set(merged)

    def _same_file(a: str, b: str) -> bool:
        """Check if two paths refer to the same file.

        Exact match first, then basename match only when at least one side
        has no directory component (bare name like 'foo.py').
        """
        if a == b:
            return True
        a_bare = "/" not in a
        b_bare = "/" not in b
        if (a_bare or b_bare) and Path(a).name == Path(b).name:
            return True
        return False

    def _in_merged(candidate: str) -> bool:
        """Check if candidate is already represented in the merged list.

        A full path (pdd/utils.py) is only covered by another full path
        with the same directory, or by an exact match. A bare name in
        merged does NOT prevent adding a more-specific full path — the
        full path wins because it's unambiguous.
        """
        if candidate in merged_set:
            return True
        candidate_has_dir = "/" in candidate
        candidate_base = Path(candidate).name
        for m in merged_set:
            m_has_dir = "/" in m
            if candidate_has_dir and m_has_dir:
                # Both have dirs: only exact match counts (handled above)
                continue
            if not candidate_has_dir and m_has_dir:
                # Bare candidate, full-path in merged: covered if basenames match
                if candidate_base == Path(m).name:
                    return True
            # Full-path candidate, bare in merged: NOT covered — full path
            # is more specific and should be added alongside or instead.
        return False

    # Add NEEDS_FIX files that aren't already in merged.
    for f in needs_fix:
        if not _in_merged(f):
            merged.append(f)
            merged_set.add(f)

    # Build a set of basenames the LLM explicitly classified (needs_fix OR safe).
    # A bare "utils.py" in this set means the LLM looked at some utils.py file,
    # so any unclassified utils.py should NOT get the conservative default.
    # But if there are multiple utils.py in different directories, classification
    # of one doesn't mean the others were examined — so we track which specific
    # full paths were classified.
    classified_paths: set[str] = set(needs_fix) | set(safe)
    classified_basenames: set[str] = set()
    for p in classified_paths:
        if "/" not in p:
            classified_basenames.add(p)

    def _is_classified(fname: str) -> bool:
        """Check if fname was classified by the LLM."""
        if fname in classified_paths:
            return True
        # If the LLM used a bare name and fname has a directory,
        # it's a match only if exactly one file shares that basename.
        # With multiple files sharing a basename, we can't know which
        # one the LLM meant, so we treat them all as unclassified
        # (conservative default applies).
        base = Path(fname).name
        if base in classified_basenames:
            matching_unclassified = [
                f for f in unclassified_filenames if Path(f).name == base
            ]
            # If only one file has this basename, the LLM's bare name
            # unambiguously refers to it.
            return len(matching_unclassified) <= 1
        return False

    for fname in unclassified_filenames:
        if not _is_classified(fname) and not _in_merged(fname):
            merged.append(fname)
            merged_set.add(fname)

    return merged


def _verify_fix_location_coverage(
    fix_locations: List[str], test_files: List[str], work_dir: Path
) -> List[str]:
    """Check that generated test files reference all fix_location modules.

    Converts each fix_location path to a dotted module path and checks if any
    test file contains a reference to it (import, patch target, string literal).

    Returns a list of fix_locations that have NO coverage in any test file.
    """
    if len(fix_locations) <= 1:
        return []  # Single-file bugs don't need cross-file coverage

    uncovered: List[str] = []
    # Read all test file contents once
    test_contents: List[str] = []
    for tf in test_files:
        abs_path = (work_dir / tf) if not Path(tf).is_absolute() else Path(tf)
        try:
            test_contents.append(abs_path.read_text())
        except OSError:
            continue

    for fix_loc in fix_locations:
        # Convert path to module: pdd/commands/generate.py -> pdd.commands.generate
        module_path = fix_loc.replace("/", ".").removesuffix(".py")
        # Also check for the slash-separated path without extension
        path_no_ext = fix_loc.removesuffix(".py")
        # Word-boundary regex for the bare filename — avoids false positives
        # where e.g. "generate" matches "generate_report" or "generated"
        basename = Path(fix_loc).stem
        basename_re = re.compile(r"\b" + re.escape(basename) + r"\b")

        found = False
        for content in test_contents:
            if module_path in content or path_no_ext in content or basename_re.search(content):
                found = True
                break
        if not found:
            uncovered.append(fix_loc)

    return uncovered


def _validate_repro_path(raw_path: str, base_dir: Path) -> Optional[Path]:
    """Validate a REPRO_FILES_CREATED path is safe (no traversal/absolute paths).

    Returns the resolved Path if safe, or None if the path is absolute,
    contains traversal segments, or resolves outside base_dir.
    """
    if not raw_path or os.path.isabs(raw_path):
        return None
    resolved = (base_dir / raw_path).resolve()
    if not resolved.is_relative_to(base_dir.resolve()):
        return None
    return resolved


def _extract_repro_test_content(output: str, cwd: Path) -> str:
    """Parse REPRO_FILES_CREATED from step 5 output and read file contents.

    Returns the concatenated content of all referenced files that exist on disk,
    or an empty string if no marker is found or no files exist.
    """
    repro_files = _parse_changed_files(output, "REPRO_FILES_CREATED")
    if not repro_files:
        return ""
    contents: List[str] = []
    for rf in repro_files:
        rf_path = _validate_repro_path(rf, cwd)
        if rf_path and rf_path.exists():
            try:
                contents.append(rf_path.read_text())
            except (OSError, UnicodeDecodeError) as exc:
                console.print(f"[yellow]Warning: failed to read reproduction test {rf}: {exc}[/yellow]")
    return "\n".join(contents)


def _copy_repro_files_to_worktree(
    step5_output: str, cwd: Path, worktree_path: Path
) -> List[str]:
    """Copy Step 5 reproduction test files from cwd into the worktree.

    Returns list of all valid relative paths (for staging), regardless of
    whether a copy was needed. Step 5 runs before the worktree exists, so
    files are in cwd. This ensures they physically exist in the worktree
    for commit, regardless of whether the Step 9 LLM incorporates them.
    """
    repro_files = _parse_changed_files(step5_output, "REPRO_FILES_CREATED")
    staged: List[str] = []
    for rf in repro_files:
        src_path = _validate_repro_path(rf, cwd)
        dst_path = _validate_repro_path(rf, worktree_path)
        if not src_path or not dst_path or not src_path.exists():
            continue
        try:
            dst_path.parent.mkdir(parents=True, exist_ok=True)
            if not dst_path.exists():
                shutil.copy2(str(src_path), str(dst_path))
            staged.append(rf)
        except OSError as exc:
            console.print(f"[yellow]Warning: failed to copy reproduction test {rf} to worktree: {exc}[/yellow]")
    return staged


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


def detect_structural_test_patterns(
    file_path: str,
    start_line: Optional[int] = None,
) -> List[str]:
    """Scan a test file for structural/non-behavioral test patterns.

    Returns a list of human-readable violation descriptions. Empty list means
    the file is clean.

    Args:
        file_path: Path to the test file to scan.
        start_line: If provided, only report violations on lines at or after
            this 1-based line number.  Lines before ``start_line`` are still
            scanned for source-variable tracking (so a ``read_text()`` call
            in old code followed by ``assert "x" in var`` in new code is
            caught), but violations on those pre-existing lines are
            suppressed.  If ``start_line`` exceeds the file length, no
            violations are reported (the loop naturally finishes without
            matching) — the intended behaviour when Step 9 doesn't append.
            Used to avoid false positives when appending new tests to a
            file that already contains flagged patterns (issue #990).

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

    # Effective start line for reporting violations.  Lines before this are
    # still scanned for variable tracking but violations are suppressed.
    #
    # Do NOT clamp when start_line > len(lines): that was the #774 off-by-one.
    # The normal "no new lines appended" case is start_line == len(lines) + 1,
    # and the loop only iterates up to len(lines) — so any start_line past the
    # end naturally suppresses all violations (the intended behaviour).  The
    # old clamp treated "past the end" as "file shrank, rescan everything",
    # which false-flagged pre-existing patterns whenever Step 9 left the file
    # untouched (the exact pdd_cloud #1064 failure mode).
    if start_line is not None and start_line > 1:
        effective_start = start_line
    else:
        effective_start = 1

    # Track whether inspect.getsource or inspect.signature is used in
    # reportable lines (at or after ``effective_start``).  These flags gate
    # source-string-matching violations so a pre-existing getsource before
    # ``effective_start`` does not suppress new violations after it.
    has_getsource_reportable = False
    has_signature_reportable = False

    for i, line in enumerate(lines, 1):
        stripped = line.strip()

        # Detect inspect.getsource usage
        if "inspect.getsource" in stripped:
            # Exclude comments
            if not stripped.startswith("#"):
                if i >= effective_start:
                    has_getsource_reportable = True
                    violations.append(
                        f"Line {i}: inspect.getsource — reads source code as string "
                        f"for structural assertion instead of testing behavior"
                    )

        # Detect inspect.signature usage
        if "inspect.signature" in stripped:
            if not stripped.startswith("#"):
                if i >= effective_start:
                    has_signature_reportable = True
                    violations.append(
                        f"Line {i}: inspect.signature — inspects function signature "
                        f"instead of calling the function and asserting on behavior"
                    )

        # Detect hasattr as the primary assertion
        if re.match(r"\s*assert\s+hasattr\s*\(", line):
            if i >= effective_start:
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

    # Track path variable assignments like:
    #   arch_path = Path(tmpdir) / "architecture.json"
    #   arch_path = worktree_path / "architecture.json"
    #   p = Path(tmpdir) / subdir / "file.json"
    #   config = Path("config.yaml")
    # So when we later see arch_path.read_text(), we can resolve the filename.
    # Alt 1: Path-join operator / before quoted filename.  Requires the char
    #   before / to be ) or a word char or ] (i.e. Python path-join, not
    #   string concat like  "/" + "endpoint").  Greedy .* so multi-segment
    #   paths (Path(x) / subdir / "file") match the last /.
    # Alt 2: Direct Path("filename") construction.
    path_var_pattern = re.compile(
        r'(\w+)\s*=\s*.*[\w)\]]\s*/\s*["\']([^"\']+)["\']'
        r'|(\w+)\s*=\s*Path\s*\(\s*["\']([^"\']+)["\']\s*\)',
    )
    path_var_filenames: dict = {}  # var_name -> filename
    for line in lines:
        pm = path_var_pattern.search(line)
        if pm and not line.strip().startswith("#"):
            var_name = pm.group(1) or pm.group(3)
            filename = pm.group(2) or pm.group(4)
            if var_name and filename:
                path_var_filenames[var_name] = filename

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

            # Check if reading from a tracked path variable (e.g. arch_path.read_text())
            # full_expr may be "arch_path" or "json.loads(arch_path" etc.
            # Check if ANY tracked path variable appears as a word in the expression.
            _skip_path_var = False
            for pvar, pfilename in path_var_filenames.items():
                if re.search(r'\b' + re.escape(pvar) + r'\b', full_expr):
                    if _is_non_source_file(pfilename):
                        _skip_path_var = True
                        break
            if _skip_path_var:
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
            if i < effective_start:
                continue
            stripped = line.strip()
            if stripped.startswith("#"):
                continue
            for var in source_var_names:
                # assert "keyword" in var  or  assert "keyword" not in var
                if re.search(
                    rf'assert\s+.*\bin\s+{re.escape(var)}\b', stripped
                ):
                    # Only flag if not already flagged by getsource/signature
                    # in the reportable range (not pre-existing lines).
                    if not has_getsource_reportable and not has_signature_reportable:
                        violations.append(
                            f"Line {i}: source string matching — asserts keyword "
                            f"presence in file/source content instead of testing behavior"
                        )

    return violations


def _scan_step9_file_for_new_patterns(
    file_path: Union[str, Path],
    pre_snapshot: Optional[str],
) -> List[str]:
    """Return only structural violations introduced since the pre-Step-9 snapshot.

    Distinguishes "unchanged" from "rewritten" by content comparison, not by
    line count alone — line counts can match exactly while content differs
    (the gltanaka review of pdd_cloud #1064 surfaced this).

    Args:
        file_path: Path to the file as it stands now (post-Step 9).
        pre_snapshot: Full file content captured before Step 9 ran, or
            ``None`` if the file did not exist pre-Step 9.

    Behaviour:
        - ``pre_snapshot is None`` -> file is brand new, full scan.
        - ``current == pre_snapshot`` -> file is byte-identical, return ``[]``
          (this is the unchanged case that was being false-flagged).
        - pre-snapshot is a strict line-prefix of current -> pure append,
          scan only appended lines (preserves issue #990 optimisation).
        - any other change (rewrite shorter, rewrite same length, or a
          rewrite that happens to extend the file) -> full scan, so real
          violations introduced by the rewrite are still caught.
    """
    path = Path(file_path)

    if pre_snapshot is None:
        return detect_structural_test_patterns(str(path))

    try:
        current = path.read_text()
    except (OSError, UnicodeDecodeError):
        return []

    if current == pre_snapshot:
        return []

    pre_lines = pre_snapshot.splitlines()
    cur_lines = current.splitlines()
    if (
        len(cur_lines) >= len(pre_lines)
        and cur_lines[: len(pre_lines)] == pre_lines
    ):
        return detect_structural_test_patterns(
            str(path), start_line=len(pre_lines) + 1
        )

    return detect_structural_test_patterns(str(path))


def _extract_violation_snippets(
    file_violations: dict,
    work_dir: Path,
) -> str:
    """Read actual violating code lines from generated test files.

    Parses line numbers from violation strings, reads the source files,
    and returns formatted snippets with context around each violation.
    Falls back to plain violation list if files can't be read.

    Args:
        file_violations: Mapping of file path -> list of violation strings
            for that file. Keeps violations associated with their source file
            so snippets are never pulled from the wrong file.
        work_dir: Working directory to resolve relative file paths against.
    """
    snippets: List[str] = []
    for fpath, violations in file_violations.items():
        abs_path = (work_dir / fpath) if not Path(fpath).is_absolute() else Path(fpath)
        if not abs_path.exists():
            logger.warning("File %s not found for violation snippets", abs_path)
            for v in violations:
                snippets.append(f"  - {v}")
            continue
        try:
            file_lines = abs_path.read_text().splitlines()
        except OSError as e:
            logger.warning("Could not read %s for violation snippets: %s", abs_path, e)
            for v in violations:
                snippets.append(f"  - {v}")
            continue
        except UnicodeDecodeError as e:
            logger.warning("Could not decode %s for violation snippets: %s", abs_path, e)
            for v in violations:
                snippets.append(f"  - {v}")
            continue
        for v in violations:
            m = re.match(r"Line (\d+):", v)
            if not m:
                snippets.append(f"  - {v}")
                continue
            line_num = int(m.group(1))
            start = max(0, line_num - 3)
            end = min(len(file_lines), line_num + 2)
            snippet_lines = []
            for idx in range(start, end):
                marker = ">>>" if idx == line_num - 1 else "   "
                snippet_lines.append(f"  {marker} {idx + 1}: {file_lines[idx]}")
            if snippet_lines:
                snippets.append(f"{v}\n" + "\n".join(snippet_lines))
            else:
                snippets.append(f"  - {v}")
    return "\n\n".join(snippets)


def _cleanup_backups_with_regression_guard(
    backed_up: List[Tuple[Path, Path]],
    quiet: bool = False,
) -> List[Path]:
    """Clean up .bak files after successful retry, restoring any that show
    content-size regression (>50% line loss).

    Returns list of paths that were restored from backup.
    """
    restored: List[Path] = []
    for original, backup in backed_up:
        try:
            if backup.exists() and original.exists():
                backup_lines = len(backup.read_text().splitlines())
                new_lines = len(original.read_text().splitlines())
                if backup_lines > 0 and new_lines < backup_lines * 0.5:
                    backup.rename(original)
                    logger.warning(
                        "Content regression in %s (%d→%d lines), "
                        "restored from backup — original structural "
                        "violations may still be present",
                        original.name, backup_lines, new_lines,
                    )
                    if not quiet:
                        console.print(
                            f"[red]  → Content regression detected in {original.name} "
                            f"({new_lines} lines < {backup_lines * 0.5:.0f} threshold), "
                            f"restoring from backup.[/red]"
                        )
                    restored.append(original)
                else:
                    backup.unlink()
            elif backup.exists():
                backup.unlink()
        except (OSError, UnicodeDecodeError):
            pass  # Best-effort cleanup
    return restored


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
    use_github_state: bool = True,
    reasoning_time: Optional[float] = None,
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
        "step5_reproduction_tests": "",
        "fix_locations": "none",
        "step6_expansion_items": "none",
        "step9_test_verification": "",
    }
    
    # Populate context with previous step outputs
    for s_key, s_out in step_outputs.items():
        context[f"step{s_key}_output"] = s_out

    # Re-extract files from step 5.5/7/9 outputs if available
    changed_files: List[str] = []
    
    # Step 5
    if "step5_output" in context:
        s5_out = context["step5_output"]
        context["step5_reproduction_tests"] = _extract_repro_test_content(s5_out, cwd)
        repro_files = _parse_changed_files(s5_out, "REPRO_FILES_CREATED")
        changed_files.extend(repro_files)

    # Step 5.5
    if "step5.5_output" in context:
        s55_out = context["step5.5_output"]
        prompt_fixed = _parse_changed_files(s55_out, "PROMPT_FIXED")
        changed_files.extend(prompt_fixed)

    # Step 6: re-extract fix locations and expansion items for downstream steps
    if "step6_output" in context:
        fix_locs = _parse_fix_locations(context["step6_output"])
        context["fix_locations"] = ", ".join(fix_locs) if fix_locs else "none"
        context["step6_expansion_items"] = _parse_expansion_items(context["step6_output"])

    # Step 7
    if "step7_output" in context:
        s7_out = context["step7_output"]
        prompt_fixed = _parse_changed_files(s7_out, "PROMPT_FIXED")
        created = _parse_changed_files(s7_out, "FILES_CREATED")
        modified = _parse_changed_files(s7_out, "FILES_MODIFIED")
        changed_files.extend(prompt_fixed + created + modified)

    # Step 9
    if "step9_output" in context:
        s9_out = context["step9_output"]
        created = _parse_changed_files(s9_out, "FILES_CREATED")
        modified = _parse_changed_files(s9_out, "FILES_MODIFIED")
        changed_files.extend(created + modified)

    # Step 11
    if "step11_output" in context:
        s11_out = context["step11_output"]
        e2e_created = _parse_changed_files(s11_out, "E2E_FILES_CREATED")
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

    if last_completed_step > 0 and start_step <= 12 and not quiet:
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
    if start_step >= 5 and start_step <= 12:
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

        # Copy Step 5 reproduction tests into worktree on resume
        if worktree_path and "5" in step_outputs:
            repro_copied = _copy_repro_files_to_worktree(
                step_outputs["5"], cwd, worktree_path
            )
            if repro_copied:
                changed_files.extend(repro_copied)
                changed_files = list(set(changed_files))
                context["files_to_stage"] = ", ".join(changed_files)
                if not quiet:
                    console.print(f"[blue]Copied {len(repro_copied)} Step 5 reproduction test(s) to worktree[/blue]")

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

            # Copy Step 5 reproduction tests into the worktree
            if worktree_path and context.get("step5_output"):
                repro_copied = _copy_repro_files_to_worktree(
                    context["step5_output"], cwd, worktree_path
                )
                if repro_copied:
                    changed_files.extend(repro_copied)
                    changed_files = list(set(changed_files))
                    context["files_to_stage"] = ", ".join(changed_files)
                    if not quiet:
                        console.print(f"[blue]Copied {len(repro_copied)} Step 5 reproduction test(s) to worktree[/blue]")

        # Skip E2E if flagged
        if step_num == 11 and skip_e2e:
            if not quiet:
                console.print("Skipping Step 11 (E2E): unit tests provide sufficient coverage")
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

        # Snapshot filesystem BEFORE step 7 (prompt classification) runs (for fallback detection)
        pre_step7_prompt_files: List[str] = []
        if step_num == 7:
            pre_step7_prompt_files = _get_modified_and_untracked(current_work_dir)

        # Snapshot filesystem BEFORE step 9 (generate) runs (for fallback detection)
        pre_step7_files: List[str] = []
        # Snapshot full content (not just line counts) so the structural test
        # guard can distinguish "unchanged" from "rewritten with same/fewer
        # lines" — a distinction line counts alone can't make.  See the
        # gltanaka review of pdd_cloud #1064: a rewrite that happens to land
        # on the same line count would silently skip violation detection.
        pre_step9_snapshots: Dict[str, str] = {}
        if step_num == 9:
            pre_step7_files = _get_modified_and_untracked(current_work_dir)
            # Snapshot existing test files so the structural test guard can
            # skip pre-existing patterns (issues #990, #1026).
            #
            # Walk the whole worktree, not just {worktree}/tests/ — real
            # projects have tests scattered across many locations (e.g.
            # backend/tests/, extensions/*/tests/, frontend/e2e/tests/).
            # Matching the #1026 convention: test_*.py, *_test.py, conftest.py.
            # Check excludes against parts RELATIVE to worktree so dir names
            # like ".pdd" don't match parent-path components when the worktree
            # itself lives under ".pdd/worktrees/...".
            _snapshot_excludes = {
                ".git", ".venv", "venv", ".env", "env",
                "node_modules", "__pycache__", ".pdd",
                ".pytest_cache", ".mypy_cache", ".ruff_cache",
                ".tox", ".nox", "dist", "build", ".next",
            }
            for py_file in current_work_dir.rglob("*.py"):
                try:
                    rel_parts = py_file.relative_to(current_work_dir).parts
                except ValueError:
                    rel_parts = py_file.parts
                if any(part in _snapshot_excludes for part in rel_parts):
                    continue
                py_file_name = py_file.name
                if not (
                    py_file_name.startswith("test_")
                    or py_file_name.endswith("_test.py")
                    or py_file_name == "conftest.py"
                ):
                    continue
                try:
                    pre_step9_snapshots[str(py_file.resolve())] = py_file.read_text()
                except (OSError, UnicodeDecodeError):
                    pass

        # Pre-Step 12: deterministic file staging (#912)
        # Stage all tracked changed_files before Step 12 dispatch so the LLM
        # cannot selectively omit files. Follows _commit_and_push() precedent
        # in agentic_e2e_fix_orchestrator.py (line 788).
        if step_num == 12 and changed_files:
            for filepath in changed_files:
                stage_result = subprocess.run(
                    ["git", "add", filepath],
                    cwd=current_work_dir,
                    capture_output=True,
                    text=True,
                )
                if stage_result.returncode != 0 and not quiet:
                    console.print(f"[yellow]Warning: failed to stage {filepath}: {stage_result.stderr.strip()}[/yellow]")

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
            reasoning_time=reasoning_time,
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

        # FAST_TRACK: skip Steps 4-5 when issue is pre-diagnosed (issue #836)
        if step_num == 3 and "FAST_TRACK:" in step_output:
            fast_track_match = re.search(r"FAST_TRACK:\s*(.+)", step_output)
            fast_track_summary = fast_track_match.group(1).strip() if fast_track_match else "Pre-diagnosed by issue author"
            context["step4_output"] = f"Step 4 skipped (fast-track): Issue was pre-diagnosed by the author. Root cause: {fast_track_summary}"
            context["step5_output"] = f"Step 5 skipped (fast-track): Issue was pre-diagnosed by the author. Root cause: {fast_track_summary}"
            state["step_outputs"]["4"] = context["step4_output"]
            state["step_outputs"]["5"] = context["step5_output"]
            state["last_completed_step"] = 5
            last_completed_step = 5
            # Recalculate start_step so the loop skips 4 and 5
            start_step = 6
            save_workflow_state(cwd, issue_number, "bug", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
            if not quiet:
                console.print(f"[cyan]  → Fast-track: skipping Steps 4-5 (issue pre-diagnosed)[/cyan]")
            continue

        files_extracted = False

        # Step-specific handling
        if step_num == 5:
            context["step5_reproduction_tests"] = _extract_repro_test_content(step_output, current_work_dir)
            repro_files = _parse_changed_files(step_output, "REPRO_FILES_CREATED")
            if repro_files:
                changed_files.extend(repro_files)
                changed_files = list(set(changed_files))
                context["files_to_stage"] = ", ".join(changed_files)

        if step_num == 6:
            fix_locs = _parse_fix_locations(step_output)
            if fix_locs:
                context["fix_locations"] = ", ".join(fix_locs)
            else:
                context["fix_locations"] = "none"
                logger.warning(
                    "Step 6 output missing FIX_LOCATIONS marker — "
                    "downstream call-boundary checks will be skipped"
                )
            expansion = _parse_expansion_items(step_output)
            context["step6_expansion_items"] = expansion
            if expansion == "none" and "EXPANSION_ITEMS:" not in step_output:
                logger.warning(
                    "Step 6 output missing EXPANSION_ITEMS marker — "
                    "scope expansion check will be skipped for downstream steps"
                )

            # Deterministic grep verification for repeating-pattern bugs.
            pattern_search = _parse_pattern_search(step_output)
            if pattern_search and fix_locs:
                unclassified, grep_summary = _verify_pattern_completeness(
                    pattern_search, fix_locs, current_work_dir
                )
                if not quiet:
                    console.print(f"  → Pattern search: {grep_summary}")

                if unclassified:
                    unclassified_filenames = sorted({m[0] for m in unclassified})
                    if not quiet:
                        console.print(
                            f"[yellow]  → {len(unclassified_filenames)} file(s) found by grep but "
                            f"missing from FIX_LOCATIONS, retrying Step 6[/yellow]"
                        )
                        for uf in unclassified_filenames[:10]:
                            console.print(f"[yellow]    • {uf}[/yellow]")
                        if len(unclassified_filenames) > 10:
                            console.print(
                                f"[yellow]    ... and {len(unclassified_filenames) - 10} more[/yellow]"
                            )

                    # Cap files sent to context extraction / LLM retry.
                    # Prioritize source files so pdd/ files are always included.
                    def _file_priority(filepath: str) -> int:
                        if filepath.startswith("pdd/") or "/pdd/" in filepath:
                            return 0
                        if filepath.startswith("tests/") or "/tests/" in filepath:
                            return 1
                        return 2

                    context_files = sorted(unclassified_filenames, key=_file_priority)
                    overflow_files: List[str] = []
                    if len(context_files) > _MAX_GREP_RESULTS:
                        overflow_files = context_files[_MAX_GREP_RESULTS:]
                        context_files = context_files[:_MAX_GREP_RESULTS]
                        if not quiet:
                            console.print(
                                f"[yellow]  → Capping context extraction to "
                                f"{_MAX_GREP_RESULTS} files ({len(overflow_files)} "
                                f"overflow file(s) will be logged but not added)[/yellow]"
                            )
                            for of in overflow_files[:5]:
                                console.print(f"[yellow]    (overflow) {of}[/yellow]")
                            if len(overflow_files) > 5:
                                console.print(
                                    f"[yellow]    ... and {len(overflow_files) - 5} more[/yellow]"
                                )
                    context_file_set = set(context_files)
                    # Only files within the cap are sent for classification.
                    # Overflow files are NOT added to unclassified_filenames —
                    # they bypass classification entirely, so applying the
                    # conservative NEEDS_FIX default would poison Step 9's
                    # coverage check with unreviewed files.
                    unclassified_filenames = context_files
                    context_matches = [m for m in unclassified if m[0] in context_file_set]

                    # Extract surrounding code context for each match
                    context_by_file = _extract_match_context(
                        context_matches, current_work_dir
                    )

                    # Build retry addendum with context windows
                    file_sections = []
                    for filepath in sorted(context_by_file):
                        ctx = context_by_file[filepath]
                        if ctx:
                            file_sections.append(
                                f"=== {filepath} ===\n{ctx}"
                            )

                    pattern_addendum = (
                        "\n\n% IMPORTANT — UNCLASSIFIED PATTERN MATCHES\n"
                        "Your previous analysis identified a repeating-pattern bug and listed "
                        f"these FIX_LOCATIONS: {', '.join(fix_locs)}\n\n"
                        f"A deterministic grep for `{pattern_search}` found additional "
                        f"matches in files not in your FIX_LOCATIONS. Below is the code "
                        f"context around each match. The vulnerability may be ABOVE or "
                        f"BELOW the matching line (e.g., a pattern variable constructed "
                        f"without escaping several lines before it is passed to the call).\n\n"
                        + "\n\n".join(file_sections)
                        + "\n\n"
                        "For EACH file above:\n"
                        "1. Examine the code context provided. If insufficient, READ the file.\n"
                        "2. Determine if this code has the same vulnerability as the files "
                        "already in FIX_LOCATIONS.\n"
                        "3. Output EXACTLY ONE of:\n"
                        "   NEEDS_FIX: filepath\n"
                        "   SAFE_EVIDENCE: filepath | line_number | reason why this usage is safe\n\n"
                        "RULES:\n"
                        "- Files without explicit SAFE_EVIDENCE default to NEEDS_FIX\n"
                        "- To mark SAFE, you MUST cite a specific line that makes the usage safe\n"
                        "- Do NOT remove any files from the original FIX_LOCATIONS\n"
                    )

                    retry_success, retry_output, retry_cost, retry_model = run_agentic_task(
                        instruction=formatted_prompt + pattern_addendum,
                        cwd=current_work_dir,
                        verbose=verbose,
                        quiet=quiet,
                        timeout=timeout,
                        label="step6",
                        max_retries=DEFAULT_MAX_RETRIES,
                        reasoning_time=reasoning_time,
                    )
                    total_cost += retry_cost
                    model_used = retry_model
                    state["total_cost"] = total_cost
                    state["model_used"] = model_used

                    if retry_success:
                        needs_fix, safe = _parse_classification_evidence(retry_output)

                        # MERGE semantics: original UNION new_needs_fix UNION defaults
                        # Uses _merge_fix_locations for basename normalization so
                        # "agentic_update.py" (LLM) and "pdd/agentic_update.py" (grep)
                        # are treated as the same file.
                        merged = _merge_fix_locations(
                            fix_locs, needs_fix, safe, unclassified_filenames
                        )

                        # Log which unclassified files were defaulted to NEEDS_FIX
                        if not quiet:
                            classified_basenames = {Path(f).name for f in needs_fix} | {Path(f).name for f in safe}
                            for fname in unclassified_filenames:
                                if Path(fname).name not in classified_basenames:
                                    console.print(
                                        f"[yellow]    → {fname} has no classification "
                                        f"evidence, defaulting to NEEDS_FIX[/yellow]"
                                    )

                    else:
                        # Retry failed (rate limit, network error, LLM failure).
                        # Apply conservative default: all grep-discovered files
                        # are added to FIX_LOCATIONS since we can't classify them.
                        merged = _merge_fix_locations(
                            fix_locs, [], [], unclassified_filenames
                        )
                        if not quiet:
                            for fname in unclassified_filenames:
                                console.print(
                                    f"[yellow]    → {fname} unclassified (retry failed), "
                                    f"defaulting to NEEDS_FIX[/yellow]"
                                )

                    context["fix_locations"] = ", ".join(merged)
                    # Preserve original root cause analysis for downstream steps (7, 8).
                    # Append a FIX_LOCATIONS line so _parse_fix_locations picks up
                    # the verified set on resume. _parse_fix_locations uses finditer
                    # + dedup, so the second line's superset is handled correctly.
                    step_output = step_output + f"\n\n% Updated after grep verification\nFIX_LOCATIONS: {', '.join(merged)}"
                    context["step6_output"] = step_output

                    if not quiet:
                        console.print(
                            f"  → Updated FIX_LOCATIONS: {len(merged)} file(s) "
                            f"(was {len(fix_locs)})"
                        )

        if step_num == 7:
            defect_type_match = re.search(r"DEFECT_TYPE:\s*(code|prompt)", step_output)
            if defect_type_match:
                defect_type = defect_type_match.group(1)
                if defect_type == "prompt":
                    prompt_fixed = _parse_changed_files(step_output, "PROMPT_FIXED")
                    if prompt_fixed:
                        changed_files.extend(prompt_fixed)
                        changed_files = list(set(changed_files))
                        context["files_to_stage"] = ", ".join(changed_files)
                        files_extracted = True
                    else:
                        # Filesystem fallback: detect modified .prompt files (#966)
                        post_step7_files = _get_modified_and_untracked(current_work_dir)
                        new_prompt_files = [
                            f for f in post_step7_files
                            if f not in pre_step7_prompt_files and f.endswith(".prompt")
                        ]
                        if new_prompt_files:
                            changed_files.extend(new_prompt_files)
                            changed_files = list(set(changed_files))
                            context["files_to_stage"] = ", ".join(changed_files)
                            files_extracted = True
                    # Warn if DEFECT_TYPE is prompt but no .prompt files detected
                    prompt_in_changed = any(f.endswith(".prompt") for f in changed_files)
                    if not prompt_in_changed and not quiet:
                        console.print("[yellow]Warning: DEFECT_TYPE is 'prompt' but no .prompt files detected in changed_files[/yellow]")

        if step_num == 8:
            # Parse planned test count for Step 9 prompt injection
            planned = _count_planned_tests(step_output)
            context["planned_test_count"] = str(planned) if planned > 0 else "all"

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

            # Structural test guard: scan generated files for banned patterns.
            # Only check lines added by Step 9, not pre-existing content (#990).
            file_violations: dict = {}  # fpath -> [violations]
            retry_extracted: List[str] = []
            cv_extracted: List[str] = []
            all_violations: List[str] = []
            for fpath in extracted:
                abs_path = (current_work_dir / fpath) if not Path(fpath).is_absolute() else Path(fpath)
                pre_snapshot = pre_step9_snapshots.get(str(abs_path.resolve()))
                violations = _scan_step9_file_for_new_patterns(
                    str(abs_path), pre_snapshot
                )
                if violations:
                    file_violations[fpath] = violations
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
                violation_snippets = _extract_violation_snippets(
                    file_violations, current_work_dir
                )
                retry_addendum = (
                    "\n\n% IMPORTANT — STRUCTURAL TEST REJECTION\n"
                    "Your previous attempt was REJECTED because it contains structural tests.\n"
                    "Here are the specific violations with the actual offending code:\n\n"
                    f"{violation_snippets}\n\n"
                    "% Example rewrite — BAD vs GOOD:\n\n"
                    "BAD (structural — reads source, checks keywords):\n"
                    "```python\n"
                    "def test_handles_signal():\n"
                    "    source = inspect.getsource(module.main)\n"
                    "    assert 'signal' in source\n"
                    "```\n\n"
                    "GOOD (behavioral — calls function, asserts on outcome):\n"
                    "```python\n"
                    "def test_handles_signal():\n"
                    "    result = module.main()\n"
                    "    assert result is not None\n"
                    "```\n\n"
                    "BAD (structural — reads file content, checks for definition):\n"
                    "```python\n"
                    "def test_function_exists():\n"
                    '    content = Path("pdd/module.py").read_text()\n'
                    '    assert "def target_func" in content\n'
                    "```\n\n"
                    "GOOD (behavioral — imports and calls the function):\n"
                    "```python\n"
                    "def test_function_exists():\n"
                    "    output = module.target_func(test_input)\n"
                    "    assert output == expected_value\n"
                    "```\n\n"
                    "You MUST rewrite ALL tests as BEHAVIORAL. Each test must CALL a function "
                    "and assert on return values, side effects, or exceptions. Do NOT use "
                    "inspect.getsource, inspect.signature, hasattr assertions, or "
                    "source string matching.\n\n"
                    "% CRITICAL: The rejected test files have been renamed. "
                    "Write completely new test files from scratch. "
                    "Do NOT attempt to read or reuse any previous test code."
                )

                # Back up first-attempt files so the LLM generates fresh.
                # If retry fails, originals are restored (no data loss).
                # Only touch files that resolve under current_work_dir (path
                # traversal guard — LLM-emitted paths are untrusted).
                base_dir = current_work_dir.resolve()
                backed_up: List[Tuple[Path, Path]] = []
                for fpath in extracted:
                    try:
                        candidate = (base_dir / Path(fpath)).resolve()
                    except OSError:
                        continue
                    try:
                        candidate.relative_to(base_dir)
                    except ValueError:
                        if not quiet:
                            console.print(
                                f"[yellow]Warning: refusing to touch path outside worktree: {candidate}[/yellow]"
                            )
                        continue
                    try:
                        if candidate.exists():
                            backup = candidate.with_suffix(candidate.suffix + ".bak")
                            candidate.rename(backup)
                            backed_up.append((candidate, backup))
                    except OSError as e:
                        if not quiet:
                            console.print(f"[yellow]Warning: failed to back up {candidate}: {e}[/yellow]")

                retry_success, retry_output, retry_cost, retry_model = run_agentic_task(
                    instruction=formatted_prompt + retry_addendum,
                    cwd=current_work_dir,
                    verbose=verbose,
                    quiet=quiet,
                    timeout=timeout,
                    label="step9",
                    max_retries=DEFAULT_MAX_RETRIES,
                    reasoning_time=reasoning_time,
                )
                total_cost += retry_cost
                model_used = retry_model
                state["total_cost"] = total_cost
                state["model_used"] = model_used
                step_success = retry_success

                if not retry_success:
                    # Restore original files so the worktree isn't left empty
                    for original, backup in backed_up:
                        try:
                            if backup.exists():
                                backup.rename(original)
                        except OSError as e:
                            logger.warning("Failed to restore %s from backup: %s", original, e)
                    if not quiet:
                        console.print(
                            "[red]  → Retry of step 9 failed; original files restored.[/red]"
                        )
                else:
                    # Retry succeeded — check for content-size regression
                    # before cleanup (#1026).
                    _cleanup_backups_with_regression_guard(
                        backed_up, quiet=quiet,
                    )
                    # Re-extract files from retry
                    retry_created = _parse_changed_files(retry_output, "FILES_CREATED")
                    retry_modified = _parse_changed_files(retry_output, "FILES_MODIFIED")
                    retry_extracted = retry_created + retry_modified
                    if retry_extracted:
                        changed_files.extend(retry_extracted)
                        changed_files = list(set(changed_files))
                        context["files_to_stage"] = ", ".join(changed_files)

                    # Re-scan retry output for structural patterns.
                    # Retry files were backed up (.bak) and rewritten from scratch,
                    # so scan from line 1 — there is no pre-existing content to skip.
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

            # Cross-validation: compare Step 8 planned test count vs Step 9 generated count
            step8_output = context.get("step8_output", "")
            planned_count = _count_planned_tests(step8_output)
            if planned_count > 0:
                all_extracted = list(set(extracted + retry_extracted))
                total_generated, stub_count = _count_generated_tests(all_extracted, current_work_dir)
                real_count = total_generated - stub_count

                if real_count < planned_count:
                    if not quiet:
                        detail = f"{total_generated} tests" if stub_count == 0 else f"{real_count} real tests ({stub_count} stubs)"
                        console.print(
                            f"[yellow]  → Cross-validation: generated {detail} "
                            f"but Step 8 planned {planned_count}, retrying[/yellow]"
                        )

                    missing_addendum = (
                        f"\n\n% IMPORTANT: Your previous attempt only generated {real_count} "
                        f"of {planned_count} planned tests. Re-read the Step 8 plan above and "
                        f"generate ALL {planned_count} tests with real assertions. "
                        f"Do NOT generate stub functions with only pass or ellipsis."
                    )

                    cv_success, cv_output, cv_cost, cv_model = run_agentic_task(
                        instruction=formatted_prompt + missing_addendum,
                        cwd=current_work_dir,
                        verbose=verbose,
                        quiet=quiet,
                        timeout=timeout,
                        label="step9",
                        max_retries=DEFAULT_MAX_RETRIES,
                        reasoning_time=reasoning_time,
                    )
                    total_cost += cv_cost
                    model_used = cv_model
                    state["total_cost"] = total_cost
                    state["model_used"] = model_used

                    cv_extracted: List[str] = []
                    if cv_success:
                        cv_created = _parse_changed_files(cv_output, "FILES_CREATED")
                        cv_modified = _parse_changed_files(cv_output, "FILES_MODIFIED")
                        cv_extracted = cv_created + cv_modified
                        if not cv_extracted:
                            post_files = _get_modified_and_untracked(current_work_dir)
                            cv_extracted = [f for f in post_files if f not in pre_step7_files]
                        if cv_extracted:
                            changed_files.extend(cv_extracted)
                            changed_files = list(set(changed_files))
                            context["files_to_stage"] = ", ".join(changed_files)

                        step_output = cv_output
                        context["step9_output"] = cv_output

                    # Log final count (whether retry helped or not)
                    final_all = list(set(all_extracted + cv_extracted))
                    final_total, final_stubs = _count_generated_tests(final_all, current_work_dir)
                    final_real = final_total - final_stubs
                    if final_real < planned_count and not quiet:
                        console.print(
                            f"[yellow]  → After retry: {final_real} of "
                            f"{planned_count} tests (proceeding with warning)[/yellow]"
                        )

            # Deterministic fix-location coverage check (replaces LLM-based Step 10 check)
            fix_locs_str = context.get("fix_locations", "none")
            if fix_locs_str != "none":
                fix_locs_list = [f.strip() for f in fix_locs_str.split(",") if f.strip()]
                # Gather all test files generated so far (including retries)
                all_test_files = list(set(extracted + retry_extracted + cv_extracted))
                uncovered = _verify_fix_location_coverage(
                    fix_locs_list, all_test_files, current_work_dir
                )
                if uncovered:
                    if not quiet:
                        console.print(
                            f"[yellow]  → Fix-location coverage gap: no tests reference "
                            f"{', '.join(uncovered)}, retrying Step 9[/yellow]"
                        )
                    coverage_addendum = (
                        "\n\n% IMPORTANT — MISSING FIX-LOCATION COVERAGE\n"
                        "Your previous attempt only generated tests for SOME of the fix locations.\n"
                        f"The fix locations are: {fix_locs_str}\n"
                        f"Missing test coverage for: {', '.join(uncovered)}\n\n"
                        "You MUST generate tests that cover ALL fix locations. For multi-file bugs, "
                        "mock the callee and verify the caller passes correct arguments, AND test "
                        "the callee directly. Each fix location file must appear in at least one "
                        "test (via import, patch target, or direct invocation)."
                    )
                    cov_success, cov_output, cov_cost, cov_model = run_agentic_task(
                        instruction=formatted_prompt + coverage_addendum,
                        cwd=current_work_dir,
                        verbose=verbose,
                        quiet=quiet,
                        timeout=timeout,
                        label="step9",
                        max_retries=DEFAULT_MAX_RETRIES,
                        reasoning_time=reasoning_time,
                    )
                    total_cost += cov_cost
                    model_used = cov_model
                    state["total_cost"] = total_cost
                    state["model_used"] = model_used

                    cov_retry_extracted: List[str] = []
                    if cov_success:
                        cov_created = _parse_changed_files(cov_output, "FILES_CREATED")
                        cov_modified = _parse_changed_files(cov_output, "FILES_MODIFIED")
                        cov_retry_extracted = cov_created + cov_modified
                        if cov_retry_extracted:
                            changed_files.extend(cov_retry_extracted)
                            changed_files = list(set(changed_files))
                            context["files_to_stage"] = ", ".join(changed_files)

                        # Scan coverage-retry files for structural test patterns (#990: skip pre-existing)
                        cov_violations: List[str] = []
                        for fpath in cov_retry_extracted:
                            abs_path = (current_work_dir / fpath) if not Path(fpath).is_absolute() else Path(fpath)
                            pre_snapshot = pre_step9_snapshots.get(str(abs_path.resolve()))
                            v = _scan_step9_file_for_new_patterns(str(abs_path), pre_snapshot)
                            if v:
                                cov_violations.extend(v)
                        if cov_violations and not quiet:
                            console.print(
                                "[yellow]  → Coverage retry contains structural patterns "
                                "(proceeding with warning):[/yellow]"
                            )
                            for v in cov_violations:
                                console.print(f"[yellow]    • {v}[/yellow]")

                        step_output = cov_output
                        context["step9_output"] = cov_output

                    # Log whether retry fixed the gap
                    still_uncovered = _verify_fix_location_coverage(
                        fix_locs_list,
                        list(set(all_test_files + cov_retry_extracted)),
                        current_work_dir,
                    )
                    if still_uncovered and not quiet:
                        console.print(
                            f"[yellow]  → After retry, still missing coverage for: "
                            f"{', '.join(still_uncovered)} (proceeding with warning)[/yellow]"
                        )

        # Deterministic subprocess verification for Step 9 generated tests (#960).
        # _verify_e2e_tests already has correct TDD semantics: failures = expected
        # (tests should fail on buggy code), setup/import errors = bad.
        # Without this, Step 9 tests only get structural pattern scanning but are
        # never actually executed — broken tests ship to the PR undetected.
        if step_num == 9 and extracted:
            verify_ok, verify_output = _verify_e2e_tests(extracted, current_work_dir)
            context["step9_test_verification"] = verify_output
            if not quiet:
                if verify_ok:
                    console.print(f"  → Step 9 test verification passed: {verify_output}")
                else:
                    console.print(f"[yellow]  → Step 9 test verification issue: {verify_output}[/yellow]")

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
