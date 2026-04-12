"""
Orchestrator for the 13-step agentic change workflow.
Runs each step as a separate agentic task, accumulates context, tracks progress/cost,
and supports resuming from saved state. Includes a review loop (steps 11-12).
"""

import glob
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple, Any

from rich.console import Console
from rich.markup import escape

from pdd.agentic_common import (
    run_agentic_task,
    load_workflow_state,
    save_workflow_state,
    clear_workflow_state,
    substitute_template_variables,
    validate_cached_state,
    DEFAULT_MAX_RETRIES,
    post_step_comment,
    set_agentic_progress,
    clear_agentic_progress,
)
from pdd.load_prompt_template import load_prompt_template
from pdd.sync_order import (
    build_dependency_graph,
    topological_sort,
    get_affected_modules,
    generate_sync_order_script,
    extract_module_from_include,
)
from pdd.construct_paths import _find_pddrc_file, _load_pddrc_config, _detect_context
from pdd.get_extension import get_extension
from pdd.preprocess import preprocess
from pdd.architecture_sync import _merge_interface_signatures, register_untracked_prompts

# Initialize console for rich output
console = Console()

# Per-Step Timeouts (Workflow specific)
CHANGE_STEP_TIMEOUTS: Dict[int, float] = {
    1: 240.0,   # Duplicate Check
    2: 240.0,   # Docs Comparison
    3: 340.0,   # Research
    4: 340.0,   # Clarify
    5: 340.0,   # Docs Changes
    6: 340.0,   # Identify Dev Units
    7: 340.0,   # Architecture Review
    8: 600.0,   # Analyze Prompt Changes (Complex)
    9: 1000.0,  # Implement Changes (Most Complex)
    10: 340.0,  # Architecture Update
    11: 340.0,  # Identify Issues
    12: 600.0,  # Fix Issues (Complex)
    13: 340.0,  # Create PR
}

MAX_REVIEW_ITERATIONS = 5


def _review_loop_no_issues(output: str) -> bool:
    """Detect 'no issues found' in step 11 output.

    LLMs don't reliably emit exact magic tokens (see #865, #868).
    Uses case-insensitive matching with semantic variants so the review
    loop exits early even when the LLM doesn't emit the exact phrase.
    """
    lower = output.lower()
    if "no issues found" in lower:
        return True
    variants = [
        "no issues identified",
        "no issues detected",
        "no issues remain",
        "no remaining issues",
        "all checks passed",
        "everything looks good",
        "no problems found",
        "no problems detected",
        "no issues to fix",
        "no issues to report",
    ]
    return any(v in lower for v in variants)


def _sanitize_architecture_dependencies(worktree_path: Path) -> None:
    """Remove corrupted dependency values from architecture.json after step 10."""
    arch_path = worktree_path / "architecture.json"
    if not arch_path.exists():
        return
    try:
        with open(arch_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        changed = False
        for entry in data:
            if not isinstance(entry, dict):
                continue
            deps = entry.get("dependencies", [])
            clean = [
                d for d in deps
                if isinstance(d, str) and d.endswith(".prompt") and "\n" not in d and len(d) <= 100
            ]
            if clean != deps:
                entry["dependencies"] = clean
                changed = True
        if changed:
            with open(arch_path, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
    except (json.JSONDecodeError, OSError):
        pass


def _scope_architecture_to_changed_files(
    worktree_path: Path,
    previous_architecture: Optional[List[Dict[str, Any]]],
    changed_files: List[str],
) -> None:
    """Revert architecture.json entries for files not in changed_files to their previous state.

    After Step 10, the LLM may mutate entries for modules it was never asked to
    touch (reason, dependencies, interface signatures, etc.). This function
    enforces scope by replacing out-of-scope entries with their pre-Step-10
    versions and removing entries that didn't exist before and aren't in scope.
    """
    arch_path = worktree_path / "architecture.json"
    if not arch_path.exists() or previous_architecture is None:
        return

    try:
        with open(arch_path, "r", encoding="utf-8") as f:
            current_architecture = json.load(f)
    except (json.JSONDecodeError, OSError):
        return

    # Build a set of filenames that are in scope from changed_files.
    # changed_files may contain paths like "pdd/prompts/foo_python.prompt",
    # "prompts/foo_python.prompt", "pdd/prompts/commands/foo_python.prompt",
    # or "architecture.json".
    #
    # We add both the basename and the relative path under "prompts/"
    # so that subdirectory prompts (e.g. "commands/maintenance_python.prompt")
    # match their architecture.json filename field.
    in_scope_filenames: set = set()
    for fp in changed_files:
        normalized = fp.replace("\\", "/")
        prompts_idx = normalized.rfind("prompts/")
        if prompts_idx != -1:
            rel = normalized[prompts_idx + len("prompts/"):]
        else:
            rel = normalized
        basename = rel.rsplit("/", 1)[-1] if "/" in rel else rel
        if basename.endswith(".prompt"):
            in_scope_filenames.add(basename)
            if rel != basename:
                in_scope_filenames.add(rel)

    # Build lookup from previous architecture by filename and filepath
    prev_by_filename: Dict[str, Dict[str, Any]] = {}
    prev_by_filepath: Dict[str, Dict[str, Any]] = {}
    for entry in previous_architecture:
        if not isinstance(entry, dict):
            continue
        fn = entry.get("filename")
        fp = entry.get("filepath")
        if fn:
            prev_by_filename[fn] = entry
        if fp:
            prev_by_filepath[fp] = entry

    scoped: List[Dict[str, Any]] = []
    for entry in current_architecture:
        if not isinstance(entry, dict):
            scoped.append(entry)
            continue

        filename = entry.get("filename", "")
        filepath = entry.get("filepath", "")

        # Determine if this entry is in scope
        entry_in_scope = filename in in_scope_filenames

        if entry_in_scope:
            # Changed file — keep LLM's mutations
            scoped.append(entry)
        else:
            # Out of scope — look up previous version
            prev_entry = prev_by_filename.get(filename)
            if prev_entry is None and filepath:
                prev_entry = prev_by_filepath.get(filepath)
            if prev_entry is not None:
                # Revert to previous
                scoped.append(prev_entry)
            # else: entry didn't exist before AND isn't in scope — drop it (hallucination)

    try:
        with open(arch_path, "w", encoding="utf-8") as f:
            json.dump(scoped, f, indent=2)
    except OSError:
        pass

def _validate_architecture_filepaths(
    worktree_path: Path,
) -> List[str]:
    """Validate and auto-correct architecture.json filepath entries.

    For each entry with a ``filepath`` field, checks whether the file exists
    relative to *worktree_path*.  When a file is not found at the declared
    path but *is* found at the PDD-conventional location
    (``pdd/<module_name>.py`` derived from the ``filename`` field), the
    filepath is corrected in-place.  Returns a list of human-readable
    warning strings describing any mismatches (corrected or not).
    """
    arch_path = worktree_path / "architecture.json"
    if not arch_path.exists():
        return []

    try:
        with open(arch_path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (json.JSONDecodeError, OSError):
        return []

    warnings: List[str] = []
    changed = False

    for entry in data:
        if not isinstance(entry, dict):
            continue
        filepath = entry.get("filepath")
        if not filepath:
            continue

        full_path = worktree_path / filepath
        if full_path.exists():
            continue  # filepath is valid

        # Try to derive the conventional PDD path from the filename field.
        # filename is like "ci_drift_heal_python.prompt" -> module "ci_drift_heal" -> "pdd/ci_drift_heal.py"
        # Only Python modules can be reliably mapped to pdd/<name>.py; other
        # languages (shell, typescript, etc.) have different conventions.
        filename = entry.get("filename", "")
        conventional_path = None
        if filename.endswith(".prompt"):
            # Strip the language suffix (e.g. "_python.prompt", "_shell.prompt")
            stem = filename[:-len(".prompt")]
            # Remove the last _<language> suffix
            parts = stem.rsplit("_", 1)
            if len(parts) == 2:
                module_name, lang_suffix = parts
                # Only derive pdd/<module>.py for Python modules
                if lang_suffix == "python":
                    conventional_path = f"pdd/{module_name}.py"

        if conventional_path and (worktree_path / conventional_path).exists():
            warnings.append(
                f"architecture.json: filepath '{filepath}' does not exist; "
                f"corrected to '{conventional_path}'"
            )
            entry["filepath"] = conventional_path
            changed = True
        else:
            warnings.append(
                f"architecture.json: filepath '{filepath}' for entry "
                f"'{filename}' does not exist on disk"
            )

    if changed:
        try:
            with open(arch_path, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
        except OSError:
            pass

    return warnings


def _sanitize_architecture_interfaces(
    worktree_path: Path,
    previous_architecture: Optional[List[Dict[str, Any]]],
) -> List[str]:
    """Preserve existing interface parameters after Step 10 direct architecture edits."""
    arch_path = worktree_path / "architecture.json"
    if not arch_path.exists() or not previous_architecture:
        return []

    try:
        with open(arch_path, "r", encoding="utf-8") as f:
            current_architecture = json.load(f)
    except (json.JSONDecodeError, OSError):
        return []

    old_by_filename = {
        entry.get("filename"): entry
        for entry in previous_architecture
        if isinstance(entry, dict) and entry.get("filename")
    }
    old_by_filepath = {
        entry.get("filepath"): entry
        for entry in previous_architecture
        if isinstance(entry, dict) and entry.get("filepath")
    }

    warnings: List[str] = []
    changed = False

    for entry in current_architecture:
        if not isinstance(entry, dict):
            continue

        old_entry = None
        filename = entry.get("filename")
        filepath = entry.get("filepath")
        if filename:
            old_entry = old_by_filename.get(filename)
        if old_entry is None and filepath:
            old_entry = old_by_filepath.get(filepath)
        if not isinstance(old_entry, dict):
            continue

        merged_interface, merge_warnings = _merge_interface_signatures(
            old_entry.get("interface"),
            entry.get("interface"),
        )
        if merged_interface != entry.get("interface"):
            entry["interface"] = merged_interface
            changed = True
        warnings.extend(merge_warnings)

    if changed:
        try:
            with open(arch_path, "w", encoding="utf-8") as f:
                json.dump(current_architecture, f, indent=2)
        except OSError:
            return []

    return warnings

def _get_git_root(cwd: Path) -> Optional[Path]:
    """Get repo root via git rev-parse."""
    if not cwd.exists():
        return None
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=cwd,
            capture_output=True,
            text=True,
            check=True
        )
        return Path(result.stdout.strip())
    except subprocess.CalledProcessError:
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
    return "HEAD"


def _setup_worktree(cwd: Path, issue_number: int, quiet: bool) -> Tuple[Optional[Path], Optional[str]]:
    """
    Create an isolated git worktree for the issue.
    Returns (worktree_path, error_message).
    """
    git_root = _get_git_root(cwd)
    if not git_root:
        return None, "Not a git repository"

    branch_name = f"change/issue-{issue_number}"
    worktree_rel_path = Path(".pdd") / "worktrees" / f"change-issue-{issue_number}"
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

    # Check if a remote branch exists with prior work to preserve
    remote_ref = f"origin/{branch_name}"
    remote_exists = False
    try:
        subprocess.run(
            ["git", "fetch", "origin", branch_name],
            cwd=git_root, capture_output=True, check=True
        )
        subprocess.run(
            ["git", "show-ref", "--verify", f"refs/remotes/{remote_ref}"],
            cwd=git_root, capture_output=True, check=True
        )
        remote_exists = True
    except subprocess.CalledProcessError as e:
        # Distinguish "branch doesn't exist on remote" (exit code 128 with
        # "couldn't find remote ref") from transient network/auth errors.
        stderr = ""
        if e.stderr:
            stderr = e.stderr if isinstance(e.stderr, str) else e.stderr.decode(errors="replace")
        if "couldn't find remote ref" in stderr or "not found" in stderr.lower():
            pass  # Branch doesn't exist remotely — expected on first run
        elif stderr:
            if not quiet:
                console.print(f"[yellow]Warning: git fetch failed for {branch_name}: {stderr.strip()}[/yellow]")

    # Clean up local branch if it exists
    branch_exists = _branch_exists(cwd, branch_name)
    if branch_exists:
        success, _err = _delete_branch(cwd, branch_name)
        if success:
            branch_exists = False

    # Create worktree — reuse remote branch if it has prior work
    try:
        worktree_path.parent.mkdir(parents=True, exist_ok=True)
        if branch_exists:
            # Branch couldn't be deleted (e.g. currently checked out) — use existing
            # --force required: git refuses to checkout a branch already in use
            subprocess.run(
                ["git", "worktree", "add", "--force", str(worktree_path), branch_name],
                cwd=git_root, capture_output=True, check=True
            )
        elif remote_exists:
            # Remote branch has prior work — start from it instead of HEAD
            subprocess.run(
                ["git", "worktree", "add", "-b", branch_name, str(worktree_path), remote_ref],
                cwd=git_root, capture_output=True, check=True
            )
            if not quiet:
                console.print(f"[blue]Reusing remote branch {branch_name} (preserving prior changes)[/blue]")
        else:
            # No prior work — create new branch from main
            base_ref = _resolve_main_ref(git_root)
            subprocess.run(
                ["git", "worktree", "add", "-b", branch_name, str(worktree_path), base_ref],
                cwd=git_root, capture_output=True, check=True
            )
        if not quiet:
            console.print(f"[blue]Working in worktree: {worktree_path}[/blue]")
        return worktree_path, None
    except subprocess.CalledProcessError as e:
        return None, f"Git worktree creation failed: {e}"

def _parse_changed_files(output: str) -> List[str]:
    """Extract file paths from FILES_CREATED, FILES_MODIFIED, or DIRECT_EDITS lines."""
    files = []
    # Look for FILES_CREATED: path, path
    created_match = re.search(r"FILES_CREATED:\s*(.*)", output)
    if created_match:
        files.extend([f.strip().strip("*").strip() for f in created_match.group(1).split(",") if f.strip()])

    # Look for FILES_MODIFIED: path, path
    modified_match = re.search(r"FILES_MODIFIED:\s*(.*)", output)
    if modified_match:
        files.extend([f.strip().strip("*").strip() for f in modified_match.group(1).split(",") if f.strip()])

    # Look for ARCHITECTURE_FILES_MODIFIED: path, path (Step 10)
    arch_match = re.search(r"ARCHITECTURE_FILES_MODIFIED:\s*(.*)", output)
    if arch_match:
        files.extend([f.strip().strip("*").strip() for f in arch_match.group(1).split(",") if f.strip()])

    # Look for DIRECT_EDITS: path, path (Step 9 - direct code edits for files without prompts)
    direct_edits_match = re.search(r"DIRECT_EDITS:\s*(.*)", output)
    if direct_edits_match:
        files.extend([f.strip().strip("*").strip() for f in direct_edits_match.group(1).split(",") if f.strip()])

    return list(set(files)) # Deduplicate


def _parse_direct_edit_candidates(step6_output: str) -> List[str]:
    """
    Parse Step 6 output for 'Direct Edit Candidates' table.
    Extract file paths from the first column of each row.
    Returns empty list if no table found.
    """
    candidates = []
    # Look for the Direct Edit Candidates table section
    # Format: | file_path | edit_type | markers |
    table_pattern = r"### Direct Edit Candidates[^\n]*\n\|[^\n]+\n\|[-\s|]+\n((?:\|[^\n]+\n)*)"
    table_match = re.search(table_pattern, step6_output, re.IGNORECASE)
    if table_match:
        rows = table_match.group(1).strip().split("\n")
        for row in rows:
            if row.strip().startswith("|"):
                # Extract first column (file path)
                cols = [c.strip() for c in row.split("|")]
                if len(cols) >= 2 and cols[1]:  # cols[0] is empty due to leading |
                    file_path = cols[1].strip().strip("`")
                    if file_path and not file_path.startswith("-"):
                        candidates.append(file_path)
    return candidates

def _detect_worktree_changes(worktree_path: Path, direct_edit_candidates: Optional[List[str]] = None) -> List[str]:
    """
    Detect actual file changes in worktree using git status.
    Fallback for when LLM output lacks FILES_CREATED/FILES_MODIFIED markers.
    Only returns prompt and documentation files (matching step 9 scope),
    plus any files in the direct_edit_candidates list.
    """
    try:
        result = subprocess.run(
            ["git", "status", "--porcelain"],
            cwd=worktree_path,
            capture_output=True, text=True, check=True
        )
        files = []
        allowed_extensions = {".prompt", ".md"}
        direct_edit_set = set(direct_edit_candidates or [])
        for line in result.stdout.splitlines():
            if not line.strip():
                continue
            # git status --porcelain format: "XY filename" (2 status chars + space + path)
            filepath = line[3:].strip().split(" -> ")[-1]
            # Skip temp files from run_agentic_task
            if filepath.startswith(".agentic_prompt_"):
                continue
            # Include prompt/doc files (step 9 scope) OR direct edit candidates
            if any(filepath.endswith(ext) for ext in allowed_extensions):
                files.append(filepath)
            elif filepath in direct_edit_set or any(filepath.endswith(c) for c in direct_edit_set):
                files.append(filepath)
        return files
    except Exception:
        return []

def _check_hard_stop(step_num: int, output: str) -> Optional[str]:
    """Check output for hard stop conditions.

    Clarification steps (4, 7) require the explicit STOP_CONDITION: tag.
    Other steps use case-insensitive substring matching as a fallback.
    A universal STOP_CONDITION: tag is recognized on any step.
    """
    if not output:
        return None
    stop_match = re.search(r'STOP_CONDITION:\s*(.+)', output, re.IGNORECASE)
    output_lower = output.lower()

    if step_num == 1 and "duplicate of #" in output_lower:
        return "Issue is a duplicate"
    if step_num == 2 and "already implemented" in output_lower:
        return "Already implemented"
    if step_num == 4:
        if stop_match and "clarification" in stop_match.group(1).lower():
            return "Clarification needed"
        return None
    if step_num == 6 and "no dev units found" in output_lower:
        return "No dev units found"
    if step_num == 7:
        if stop_match and "architectural" in stop_match.group(1).lower():
            return "Architectural decision needed"
        return None
    if step_num == 8 and "no changes required" in output_lower:
        return "No changes needed"
    if step_num == 9:
        if "fail:" in output_lower:
            return "Implementation failed"
    # Universal fallback: any STOP_CONDITION tag on an unhandled step
    if stop_match:
        return stop_match.group(1).strip()
    return None



# Steps where a hard stop is a "clarification" request (user may respond, step should re-run)
_CLARIFICATION_STEPS = {4, 7}


def _fetch_issue_updated_at(repo_owner: str, repo_name: str, issue_number: int) -> str:
    """Re-fetch issue updated_at from GitHub API.

    Used after a clarification stop to capture the timestamp AFTER
    the bot's own comment, so stale detection doesn't false-trigger.
    """
    try:
        result = subprocess.run(
            ["gh", "api", f"repos/{repo_owner}/{repo_name}/issues/{issue_number}",
             "--jq", ".updated_at"],
            capture_output=True, text=True, check=False, timeout=15,
        )
        if result.returncode == 0 and result.stdout.strip():
            return result.stdout.strip()
        console.print(
            f"[yellow]Warning: Failed to re-fetch issue updated_at "
            f"(rc={result.returncode}): {result.stderr.strip()}[/yellow]"
        )
    except subprocess.TimeoutExpired:
        console.print("[yellow]Warning: Timed out re-fetching issue updated_at[/yellow]")
    except OSError as e:
        console.print(f"[yellow]Warning: OSError re-fetching issue updated_at: {e}[/yellow]")
    return ""


def _get_state_dir(cwd: Path) -> Path:
    """Get the state directory relative to git root."""
    root = _get_git_root(cwd) or cwd
    return root / ".pdd" / "change-state"

def _load_pddrc_context(cwd: Path) -> Dict[str, str]:
    """
    Load .pddrc configuration and return context keys for step templates.

    Returns dict with: language, source_dir, test_dir, example_dir, ext, lang
    Falls back to sensible defaults if no .pddrc found.
    """
    defaults = {
        "language": "python",
        "source_dir": "src/",
        "test_dir": "tests/",
        "example_dir": "context/",
        "ext": "py",
        "lang": "_python",
    }

    try:
        pddrc_path = _find_pddrc_file(cwd)
        if not pddrc_path:
            return defaults

        config = _load_pddrc_config(pddrc_path)
        if not config:
            return defaults

        # Detect the appropriate context
        context_name = _detect_context(cwd, config)
        contexts = config.get("contexts", {})
        ctx_config = contexts.get(context_name, contexts.get("default", {}))

        # Config values may be at top level or nested under "defaults"
        ctx_defaults = ctx_config.get("defaults", ctx_config)

        language = ctx_defaults.get("default_language", defaults["language"])
        source_dir = ctx_defaults.get("generate_output_path", defaults["source_dir"])
        test_dir = ctx_defaults.get("test_output_path", defaults["test_dir"])
        example_dir = ctx_defaults.get("example_output_path", defaults["example_dir"])

        # Derive ext from language
        ext = get_extension(language) if language else defaults["ext"]
        if ext.startswith("."):
            ext = ext[1:]  # Remove leading dot if present

        # Derive lang suffix
        lang = f"_{language}" if language else defaults["lang"]

        return {
            "language": language,
            "source_dir": source_dir,
            "test_dir": test_dir,
            "example_dir": example_dir,
            "ext": ext,
            "lang": lang,
        }
    except Exception:
        # On any error, return defaults
        return defaults


def _build_dependency_context(prompts_dir: Path, quiet: bool = False) -> str:
    """
    Build a formatted string describing the module dependency graph.

    This is used to provide Step 6 with structured dependency information
    so it can identify transitively affected modules.

    Args:
        prompts_dir: Path to the prompts directory
        quiet: Whether to suppress logging

    Returns:
        Formatted string describing dependencies, or empty string if unavailable
    """
    if not prompts_dir.exists():
        return ""

    try:
        graph = build_dependency_graph(prompts_dir)
        if not graph:
            return ""

        # Build reverse dependencies (module -> list of modules that depend on it)
        reverse_deps: Dict[str, List[str]] = {}
        for module, deps in graph.items():
            for dep in deps:
                if dep not in reverse_deps:
                    reverse_deps[dep] = []
                reverse_deps[dep].append(module)

        # Format as readable text for the LLM
        lines = []
        lines.append("## Module Dependency Graph")
        lines.append("")
        lines.append("When a module is modified, all modules that depend on it (directly or transitively) may also need updates.")
        lines.append("")

        # Show modules with dependents (these are the ones that matter for ripple effects)
        modules_with_dependents = {k: v for k, v in reverse_deps.items() if v}
        if modules_with_dependents:
            lines.append("### Modules and their dependents (modules that will be affected if changed):")
            lines.append("")
            # Sort by number of dependents (most impactful first)
            for module in sorted(modules_with_dependents.keys(),
                               key=lambda m: len(modules_with_dependents[m]),
                               reverse=True)[:30]:  # Limit to top 30
                dependents = modules_with_dependents[module]
                lines.append(f"- **{module}** → affects: {', '.join(sorted(dependents)[:10])}")
                if len(dependents) > 10:
                    lines.append(f"  (and {len(dependents) - 10} more)")

        lines.append("")
        lines.append(f"Total modules tracked: {len(graph)}")

        return "\n".join(lines)

    except Exception as e:
        if not quiet:
            console.print(f"[yellow]Warning: Could not build dependency context: {e}[/yellow]")
        return ""


def _check_existing_pr(repo_owner: str, repo_name: str, issue_number: int) -> Optional[str]:
    """Check if an open PR already exists for this issue's branch.

    Returns the PR URL if found, None otherwise.
    """
    branch = f"change/issue-{issue_number}"
    try:
        result = subprocess.run(
            ["gh", "pr", "list", "--repo", f"{repo_owner}/{repo_name}",
             "--search", f"head:{branch}", "--state", "open",
             "--json", "url", "--limit", "1"],
            capture_output=True, text=True, check=False, timeout=30,
        )
        if result.returncode != 0:
            return None
        data = json.loads(result.stdout)
        if data and isinstance(data, list) and data[0].get("url"):
            return data[0]["url"]
    except (subprocess.TimeoutExpired, json.JSONDecodeError, Exception):
        pass
    return None


def run_agentic_change_orchestrator(
    issue_url: str,
    issue_content: str,
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    issue_author: str,
    issue_title: str,
    issue_updated_at: str = "",
    *,
    cwd: Path,
    verbose: bool = False,
    quiet: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Orchestrates the 13-step agentic change workflow.
    
    Returns:
        (success, final_message, total_cost, model_used, changed_files)
    """

    # Ensure any stale agentic progress from previous runs is cleared.
    clear_agentic_progress()
    
    if not quiet:
        console.print(f"Implementing change for issue #{issue_number}: \"{issue_title}\"")

    state_dir = _get_state_dir(cwd)

    # Load state
    state, loaded_gh_id = load_workflow_state(
        cwd, issue_number, "change", state_dir, repo_owner, repo_name, use_github_state
    )

    # Guard: if an open PR already exists for this issue, return early
    existing_pr = _check_existing_pr(repo_owner, repo_name, issue_number)
    if existing_pr:
        if not quiet:
            console.print(f"[yellow]PR already exists for issue #{issue_number}: {existing_pr}[/yellow]")
        return True, f"PR already exists: {existing_pr}", 0.0, "unknown", []

    # Check for stale state: if issue was updated since state was saved, start fresh
    if state is not None and issue_updated_at:
        stored_updated_at = state.get("issue_updated_at")
        if stored_updated_at and stored_updated_at != issue_updated_at:
            # Issue was modified - state is stale
            if not quiet:
                console.print("[yellow]Issue was updated since last run - starting fresh[/yellow]")
            clear_workflow_state(cwd, issue_number, "change", state_dir, repo_owner, repo_name, use_github_state)
            state = None
            loaded_gh_id = None

    # Initialize variables from state or defaults
    if state is not None:
        last_completed_step = state.get("last_completed_step", 0)
        step_outputs = state.get("step_outputs", {})
        total_cost = state.get("total_cost", 0.0)
        model_used = state.get("model_used", "unknown")
        github_comment_id = loaded_gh_id
        worktree_path_str = state.get("worktree_path")
        worktree_path = Path(worktree_path_str) if worktree_path_str else None
        # Ensure issue_updated_at is in state for future staleness checks
        if issue_updated_at:
            state["issue_updated_at"] = issue_updated_at

        # Issue #467: Validate cached state — correct last_completed_step
        # if any cached step outputs have "FAILED:" prefix.
        last_completed_step = validate_cached_state(
            last_completed_step, step_outputs, quiet=quiet
        )
    else:
        state = {"step_outputs": {}, "issue_updated_at": issue_updated_at, "last_completed_step": 0}
        last_completed_step = 0
        step_outputs = state["step_outputs"]
        total_cost = 0.0
        model_used = "unknown"
        github_comment_id = None
        worktree_path = None
    
    pddrc_context = _load_pddrc_context(cwd)

    context = {
        "issue_url": issue_url,
        "issue_content": issue_content,
        "repo_owner": repo_owner,
        "repo_name": repo_name,
        "issue_number": issue_number,
        "issue_author": issue_author,
        "issue_title": issue_title,
        **pddrc_context,
    }
    
    for s_num, s_out in step_outputs.items():
        context[f"step{s_num}_output"] = s_out

    changed_files = []
    
    if "step9_output" in context:
        s9_out = context["step9_output"]
        extracted_files = _parse_changed_files(s9_out)
        changed_files.extend(extracted_files)
        created_match = re.search(r"FILES_CREATED:\s*(.*)", s9_out)
        modified_match = re.search(r"FILES_MODIFIED:\s*(.*)", s9_out)
        context["files_created"] = created_match.group(1).strip() if created_match else ""
        context["files_modified"] = modified_match.group(1).strip() if modified_match else ""
    
    if "step10_output" in context:
        s10_out = context["step10_output"]
        arch_files = _parse_changed_files(s10_out)
        new_files = [f for f in arch_files if f not in changed_files]
        changed_files.extend(new_files)

    if changed_files:
        context["files_to_stage"] = ", ".join(changed_files)

    start_step = last_completed_step + 1
    
    if last_completed_step > 0 and not quiet:
        console.print(f"Resuming change workflow for issue #{issue_number}")
        console.print(f"   Steps 1-{last_completed_step} already complete (cached)")
        console.print(f"   Starting from Step {start_step}")

    steps_config = [
        (1, "duplicate", "Search for duplicate issues"),
        (2, "docs", "Check if already implemented"),
        (3, "research", "Research to clarify specifications"),
        (4, "clarify", "Verify requirements are clear"),
        (5, "docs_change", "Analyze documentation changes needed"),
        (6, "devunits", "Identify dev units involved"),
        (7, "architecture", "Review architecture"),
        (8, "analyze", "Analyze prompt changes"),
        (9, "implement", "Implement the prompt changes"),
        (10, "architecture_update", "Update architecture metadata"),
    ]

    current_work_dir = cwd

    if start_step >= 9:
        if worktree_path and worktree_path.exists():
             if not quiet:
                console.print(f"[blue]Reusing existing worktree: {worktree_path}[/blue]")
             current_work_dir = worktree_path
             context["worktree_path"] = str(worktree_path)
        else:
            wt_path, err = _setup_worktree(cwd, issue_number, quiet)
            if not wt_path:
                return False, f"Failed to restore worktree: {err}", total_cost, model_used, []
            worktree_path = wt_path
            current_work_dir = worktree_path
            state["worktree_path"] = str(worktree_path)
            context["worktree_path"] = str(worktree_path)

    consecutive_provider_failures = 0
    previous_architecture = None

    for step_num, name, description in steps_config:
        if step_num < start_step:
            continue

        # Record progress so KeyboardInterrupt can report how far we got.
        completed_list = list(range(1, step_num)) if step_num > 1 else []
        set_agentic_progress(
            workflow="change",
            current_step=step_num,
            total_steps=13,
            step_name=description,
            completed_steps=completed_list,
        )

        previous_architecture = None

        # Before Step 6, build dependency context to help identify transitively affected modules
        if step_num == 6:
            prompts_dir = cwd / "prompts"
            if prompts_dir.exists():
                dep_context = _build_dependency_context(prompts_dir, quiet=quiet)
                context["dependency_context"] = dep_context
            else:
                context["dependency_context"] = ""

        if step_num == 9:
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
                except subprocess.CalledProcessError:
                    pass

                wt_path, err = _setup_worktree(cwd, issue_number, quiet)
                if not wt_path:
                    return False, f"Failed to create worktree: {err}", total_cost, model_used, []
                worktree_path = wt_path
                current_work_dir = worktree_path
                state["worktree_path"] = str(worktree_path)
                context["worktree_path"] = str(worktree_path)

        if not quiet:
            console.print(f"[bold][Step {step_num}/13][/bold] {description}...")

        # Snapshot architecture.json before Step 10 so we can revert out-of-scope mutations
        if step_num == 10 and worktree_path:
            arch_path = worktree_path / "architecture.json"
            if arch_path.exists():
                try:
                    with open(arch_path, "r", encoding="utf-8") as f:
                        previous_architecture = json.load(f)
                except (json.JSONDecodeError, OSError):
                    previous_architecture = None

        template_name = f"agentic_change_step{step_num}_{name}_LLM"
        prompt_template = load_prompt_template(template_name)
        if not prompt_template:
            return False, f"Missing prompt template: {template_name}", total_cost, model_used, []

        # Preprocess to expand <include> tags and escape curly braces
        # Exclude context keys from escaping so they can be substituted
        exclude_keys = list(context.keys())
        prompt_template = preprocess(prompt_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys)

        formatted_prompt = substitute_template_variables(prompt_template, context)

        timeout = CHANGE_STEP_TIMEOUTS.get(step_num, 340.0) + timeout_adder
        step_success, step_output, step_cost, step_model = run_agentic_task(
            instruction=formatted_prompt,
            cwd=current_work_dir,
            verbose=verbose,
            quiet=quiet,
            timeout=timeout,
            label=f"step{step_num}",
            max_retries=DEFAULT_MAX_RETRIES,
        )

        total_cost += step_cost
        model_used = step_model
        state["total_cost"] = total_cost
        state["model_used"] = model_used

        if not step_success:
            # Track consecutive provider failures for early abort
            if "All agent providers failed" in step_output:
                consecutive_provider_failures += 1
                if consecutive_provider_failures >= 3:
                    post_step_comment(
                        repo_owner=repo_owner, repo_name=repo_name,
                        issue_number=issue_number, step_num=step_num,
                        total_steps=13, description=description,
                        output=step_output, cwd=cwd,
                    )
                    state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"
                    save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
                    return False, f"Aborting: {consecutive_provider_failures} consecutive steps failed — agent providers unavailable", total_cost, model_used, []
            else:
                consecutive_provider_failures = 0

            stop_reason = _check_hard_stop(step_num, step_output)
            if stop_reason:
                post_step_comment(
                    repo_owner=repo_owner, repo_name=repo_name,
                    issue_number=issue_number, step_num=step_num,
                    total_steps=13, description=description,
                    output=step_output, cwd=cwd,
                )
                if not quiet:
                    console.print(f"[yellow]Investigation stopped at Step {step_num}: {stop_reason}[/yellow]")
                # Clarification steps save step_num - 1 so the step re-runs on resume
                state["last_completed_step"] = step_num - 1 if step_num in _CLARIFICATION_STEPS else step_num
                state["step_outputs"][str(step_num)] = step_output
                # Refresh issue_updated_at after clarification (bot comment changes the timestamp)
                if step_num in _CLARIFICATION_STEPS:
                    refreshed = _fetch_issue_updated_at(repo_owner, repo_name, issue_number)
                    if refreshed:
                        state["issue_updated_at"] = refreshed
                save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
                return False, f"Stopped at step {step_num}: {stop_reason}", total_cost, model_used, changed_files
            console.print(f"[yellow]Warning: Step {step_num} reported failure but continuing...[/yellow]")

        stop_reason = _check_hard_stop(step_num, step_output)
        if stop_reason:
            post_step_comment(
                repo_owner=repo_owner, repo_name=repo_name,
                issue_number=issue_number, step_num=step_num,
                total_steps=13, description=description,
                output=step_output, cwd=cwd,
            )
            if not quiet:
                console.print(f"[yellow]Investigation stopped at Step {step_num}: {stop_reason}[/yellow]")
            # Clarification steps save step_num - 1 so the step re-runs on resume
            state["last_completed_step"] = step_num - 1 if step_num in _CLARIFICATION_STEPS else step_num
            state["step_outputs"][str(step_num)] = step_output
            # Refresh issue_updated_at after clarification (bot comment changes the timestamp)
            if step_num in _CLARIFICATION_STEPS:
                refreshed = _fetch_issue_updated_at(repo_owner, repo_name, issue_number)
                if refreshed:
                    state["issue_updated_at"] = refreshed
            save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
            return False, f"Stopped at step {step_num}: {stop_reason}", total_cost, model_used, changed_files

        # Step 6: Extract direct edit candidates (files without prompts that need scoped edits)
        if step_num == 6:
            direct_edit_candidates = _parse_direct_edit_candidates(step_output)
            context["direct_edit_candidates"] = direct_edit_candidates
            if direct_edit_candidates and not quiet:
                console.print(f"[blue]Found {len(direct_edit_candidates)} direct edit candidate(s)[/blue]")

        if step_num == 9:
            extracted_files = _parse_changed_files(step_output)
            if not extracted_files and worktree_path:
                # Fallback: check worktree for actual file changes
                # Pass direct_edit_candidates so those files are also detected
                dec = context.get("direct_edit_candidates", [])
                extracted_files = _detect_worktree_changes(worktree_path, dec)
                if extracted_files and not quiet:
                    console.print(f"[yellow]Note: Detected {len(extracted_files)} changed file(s) in worktree (LLM output lacked markers)[/yellow]")
            changed_files = extracted_files
            context["files_to_stage"] = ", ".join(changed_files)
            created_match = re.search(r"FILES_CREATED:\s*(.*)", step_output)
            modified_match = re.search(r"FILES_MODIFIED:\s*(.*)", step_output)
            direct_edits_match = re.search(r"DIRECT_EDITS:\s*(.*)", step_output)
            context["files_created"] = created_match.group(1).strip() if created_match else ""
            context["files_modified"] = modified_match.group(1).strip() if modified_match else ""
            context["direct_edits"] = direct_edits_match.group(1).strip() if direct_edits_match else ""
            if not changed_files:
                # Save step output for debugging before failing
                # Issue #467: Mark as FAILED instead of using step_num - 1
                state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"
                # Don't advance last_completed_step — keep it at its current value
                save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
                return False, "Stopped at step 9: Implementation produced no file changes", total_cost, model_used, []

        if step_num == 10:
            arch_files = _parse_changed_files(step_output)
            new_files = [f for f in arch_files if f not in changed_files]
            changed_files.extend(new_files)
            context["files_to_stage"] = ", ".join(changed_files)
            if worktree_path:
                _scope_architecture_to_changed_files(
                    worktree_path, previous_architecture, changed_files
                )
                _sanitize_architecture_dependencies(worktree_path)
                filepath_warnings = _validate_architecture_filepaths(worktree_path)
                interface_warnings = _sanitize_architecture_interfaces(
                    worktree_path,
                    previous_architecture,
                )
                all_warnings = filepath_warnings + interface_warnings
                if all_warnings:
                    if not quiet:
                        for warning in all_warnings:
                            console.print(f"[yellow]Warning: {warning}[/yellow]")
                    step_output = (
                        step_output.rstrip()
                        + "\n\nORCHESTRATOR_POSTCHECK_WARNINGS:\n"
                        + "\n".join(f"- {warning}" for warning in all_warnings)
                    )

                # Auto-register untracked prompts (safety net for Step 10 LLM rule 5(b)
                # fallthrough). Scope is narrowed to prompts TOUCHED BY THIS WORKFLOW:
                # any .prompt file in changed_files (Step 9 FILES_CREATED/MODIFIED plus
                # Step 10's own arch_files). We must NOT auto-register prompts outside
                # the workflow's scope — that would silently sweep repo-wide arch.json
                # drift into this PR and could write incorrect metadata for prompts
                # with non-standard paths (e.g. frontend/components/*.prompt, where
                # _infer_filepath would produce a wrong Python-style filepath).
                only_files: set = set()
                for fp in changed_files:
                    normalized = fp.replace("\\", "/")
                    prompts_idx = normalized.rfind("prompts/")
                    if prompts_idx == -1:
                        continue
                    rel = normalized[prompts_idx + len("prompts/"):]
                    if rel.endswith(".prompt"):
                        only_files.add(rel)

                if only_files:
                    try:
                        reg_result = register_untracked_prompts(
                            prompts_dir=worktree_path / "prompts",
                            architecture_path=worktree_path / "architecture.json",
                            dry_run=False,
                            only_files=only_files,
                        )
                        registered = reg_result.get("registered", [])
                        if registered:
                            reg_list = ", ".join(registered)
                            step_output += f"\n\nORCHESTRATOR_AUTO_REGISTERED: {reg_list}"
                            if not quiet:
                                console.print(f"[blue]Auto-registered untracked prompts in arch.json: {reg_list}[/blue]")
                    except Exception:
                        pass

        context[f"step{step_num}_output"] = step_output
        if step_success:
            consecutive_provider_failures = 0
            state["step_outputs"][str(step_num)] = step_output
            state["last_completed_step"] = step_num
        else:
            state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"

        save_result = save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
        if save_result:
            github_comment_id = save_result
            state["github_comment_id"] = github_comment_id

        if not quiet:
            lines = step_output.strip().split('\n')
            brief = lines[-1] if lines else "Done"
            if len(brief) > 80: brief = brief[:77] + "..."
            console.print(f"   -> {escape(brief)}")
            if step_success:
                console.print(f"  \u2192 Step {step_num} complete.")

    if "files_to_stage" not in context:
        s9_out = context.get("step9_output", "")
        s10_out = context.get("step10_output", "")
        c_files = _parse_changed_files(s9_out)
        c_files.extend(_parse_changed_files(s10_out))
        changed_files = list(set(c_files))
        context["files_to_stage"] = ", ".join(changed_files)

    review_iteration = state.get("review_iteration", 0)
    previous_fixes = state.get("previous_fixes", "")
    
    if last_completed_step < 13:
        while review_iteration < MAX_REVIEW_ITERATIONS:
            review_iteration += 1
            state["review_iteration"] = review_iteration
            if not quiet:
                console.print(f"[bold][Step 11/13][/bold] Identifying issues (iteration {review_iteration}/{MAX_REVIEW_ITERATIONS})...")
            s11_template = load_prompt_template("agentic_change_step11_identify_issues_LLM")
            context["review_iteration"] = review_iteration
            context["previous_fixes"] = previous_fixes
            # Preprocess to escape curly braces in included content
            exclude_keys = list(context.keys())
            s11_template = preprocess(s11_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys)
            s11_prompt = substitute_template_variables(s11_template, context)
            timeout11 = CHANGE_STEP_TIMEOUTS.get(11, 340.0) + timeout_adder
            s11_success, s11_output, s11_cost, s11_model = run_agentic_task(
                instruction=s11_prompt, cwd=current_work_dir, verbose=verbose, quiet=quiet, timeout=timeout11, label=f"step11_iter{review_iteration}", max_retries=DEFAULT_MAX_RETRIES,
            )
            total_cost += s11_cost; model_used = s11_model; state["total_cost"] = total_cost
            if _review_loop_no_issues(s11_output):
                if not quiet: console.print("   -> No issues found. Proceeding to PR.")
                context["step11_output"] = s11_output; break
            if not quiet: console.print("   -> Issues found. Proceeding to fix.")
            if not quiet:
                console.print(f"[bold][Step 12/13][/bold] Fixing issues (iteration {review_iteration}/{MAX_REVIEW_ITERATIONS})...")
            s12_template = load_prompt_template("agentic_change_step12_fix_issues_LLM")
            context["step11_output"] = s11_output
            # Preprocess to escape curly braces in included content
            exclude_keys = list(context.keys())
            s12_template = preprocess(s12_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys)
            s12_prompt = substitute_template_variables(s12_template, context)
            timeout12 = CHANGE_STEP_TIMEOUTS.get(12, 600.0) + timeout_adder
            s12_success, s12_output, s12_cost, s12_model = run_agentic_task(
                instruction=s12_prompt, cwd=current_work_dir, verbose=verbose, quiet=quiet, timeout=timeout12, label=f"step12_iter{review_iteration}", max_retries=DEFAULT_MAX_RETRIES,
            )
            total_cost += s12_cost; model_used = s12_model; state["total_cost"] = total_cost
            previous_fixes += f"\n\nIteration {review_iteration}:\n{s12_output}"
            state["previous_fixes"] = previous_fixes
            save_result = save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
            if save_result: github_comment_id = save_result; state["github_comment_id"] = github_comment_id
        if review_iteration >= MAX_REVIEW_ITERATIONS:
            console.print("[yellow]Warning: Maximum review iterations reached. Proceeding to PR creation.[/yellow]")

    sync_order_script = ""; sync_order_list = "No modules to sync"
    files_to_stage_str = context.get("files_to_stage", "")
    file_list = [f.strip() for f in files_to_stage_str.split(",") if f.strip()]
    modified_modules: Set[str] = set()
    for file_path in file_list:
        if file_path.endswith(".prompt") and ("/prompts/" in file_path or file_path.startswith("prompts/")):
            module = extract_module_from_include(file_path)
            if module: modified_modules.add(module)

    if worktree_path:
        prompts_dir = worktree_path / "prompts"
        if prompts_dir.exists() and modified_modules:
            try:
                graph = build_dependency_graph(prompts_dir)
                sorted_modules, cycles = topological_sort(graph)
                if cycles and not quiet:
                    console.print(f"[yellow]Warning: Circular dependencies detected: {cycles}[/yellow]")
                cyclic_modules = set(cycles[0]) if cycles else set()
                affected = get_affected_modules(sorted_modules, modified_modules, graph, cyclic_modules)
                if affected:
                    # Generate clean command list for PR body (not full bash script)
                    sync_order_list = "\n".join([f"pdd sync {m}" for m in affected])

                    # Write change-specific script to .pdd/ (NOT sync_order.sh which
                    # may contain the full repo module list — overwriting it destroys
                    # the original, as seen in issue #571).
                    pdd_dir = cwd / ".pdd"
                    pdd_dir.mkdir(parents=True, exist_ok=True)
                    user_script_path = pdd_dir / "sync_order_change.sh"
                    generate_sync_order_script(affected, user_script_path, worktree_path=None)
                    sync_order_script = str(user_script_path)

                    if not quiet:
                        console.print(f"\n[bold]Sync commands (run after merge):[/bold]")
                        for module in affected:
                            console.print(f"  pdd sync {module}")
                        console.print(f"[green]Sync script saved to: {user_script_path}[/green]")
            except Exception as e:
                if not quiet: console.print(f"[yellow]Warning: Could not generate sync order: {e}[/yellow]")

    context["sync_order_script"] = sync_order_script; context["sync_order_list"] = sync_order_list

    # Identify test files for affected modules (#377 Bug B)
    impacted_tests: List[str] = []
    test_dir_name = pddrc_context.get("test_dir", "tests/").rstrip("/")
    test_base = cwd / test_dir_name
    if test_base.exists():
        for f in changed_files:
            # Extract module basename from prompt or source filenames
            basename = Path(f).stem
            # Strip common suffixes to get the module name
            for suffix in ("_python", "_typescript", "_go", "_rust", "_java"):
                if basename.endswith(suffix):
                    basename = basename[: -len(suffix)]
                    break
            # Look for matching test files
            for test_file in test_base.glob(f"test_{glob.escape(basename)}*"):
                rel = str(test_file.relative_to(cwd))
                if rel not in impacted_tests:
                    impacted_tests.append(rel)
    if impacted_tests:
        context["impacted_tests"] = "\n".join(impacted_tests)
        if not quiet:
            console.print(f"\n[bold]Impacted test files ({len(impacted_tests)}):[/bold]")
            for tf in impacted_tests:
                console.print(f"  {tf}")
    else:
        context["impacted_tests"] = "No impacted test files identified"

    if last_completed_step < 13:
        if not quiet: console.print("[bold][Step 13/13][/bold] Create PR and link to issue...")
        s13_template = load_prompt_template("agentic_change_step13_create_pr_LLM")
        # Preprocess to escape curly braces in included content
        exclude_keys = list(context.keys())
        s13_template = preprocess(s13_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys)
        s13_prompt = substitute_template_variables(s13_template, context)
        timeout13 = CHANGE_STEP_TIMEOUTS.get(13, 340.0) + timeout_adder
        s13_success, s13_output, s13_cost, s13_model = run_agentic_task(
            instruction=s13_prompt, cwd=current_work_dir, verbose=verbose, quiet=quiet, timeout=timeout13, label="step13", max_retries=DEFAULT_MAX_RETRIES,
        )
        total_cost += s13_cost; model_used = s13_model; state["total_cost"] = total_cost
        if not s13_success:
             post_step_comment(repo_owner, repo_name, issue_number, 13, 13, "Create PR and link to issue", s13_output, cwd)
             console.print("[red]Step 13 (PR Creation) failed.[/red]")
             save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
             return False, "PR Creation failed", total_cost, model_used, changed_files
        pr_url = "Unknown"; url_match = re.search(r"https://github.com/\S+/pull/\d+", s13_output)
        if url_match: pr_url = url_match.group(0)
        if not quiet:
            console.print("\n[green]Change workflow complete[/green]")
            console.print(f"   Total cost: ${total_cost:.4f}")
            console.print(f"   Files changed: {', '.join(changed_files)}")
            console.print(f"   PR: {pr_url}")
            console.print(f"   Review iterations: {review_iteration}")
            console.print("\nNext steps:")
            console.print("   1. Review and merge the PR")
            console.print("   2. Run `./sync_order.sh` after merge (or see PR for manual commands)")
        has_failed_steps = any(
            str(v).startswith("FAILED:") for v in state.get("step_outputs", {}).values()
        )
        if not has_failed_steps:
            clear_workflow_state(cwd, issue_number, "change", state_dir, repo_owner, repo_name, use_github_state)
        # Clear progress on successful completion so future runs start clean.
        clear_agentic_progress()
        return True, f"PR Created: {pr_url}", total_cost, model_used, changed_files
    return True, "Workflow already completed", total_cost, model_used, changed_files
