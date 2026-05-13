"""Orchestrator for the 13-step agentic change workflow.

Implements the `pdd change` workflow: takes a GitHub issue and produces a PR
with prompt/code changes, running each step as a separate agentic task with
state persistence, review loops, and worktree isolation.
"""

from __future__ import annotations

import json
import os
import re
import shlex
import shutil
import stat
import subprocess
import sys
import threading
from collections import defaultdict, deque
from datetime import datetime
from pathlib import Path
from typing import Any, Deque, Dict, List, Optional, Set, Tuple

from rich.console import Console

from pdd.agentic_common import (
    DEFAULT_MAX_RETRIES,
    clear_agentic_progress,
    clear_workflow_state,
    extract_step_report,
    load_workflow_state,
    normalize_step_comments_state,
    post_step_comment,
    post_step_comment_once,
    run_agentic_task,
    save_workflow_state,
    set_agentic_progress,
    substitute_template_variables,
    validate_cached_state,
)
from pdd.load_prompt_template import load_prompt_template
from pdd.preprocess import preprocess
from pdd.architecture_sync import (
    _merge_interface_signatures,
    register_untracked_prompts,
)
from pdd.construct_paths import (
    _detect_context,
    _find_pddrc_file,
    _load_pddrc_config,
)
from pdd.get_extension import get_extension


console = Console()

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

CHANGE_STEP_TIMEOUTS: Dict[int, float] = {
    1: 240.0,
    2: 240.0,
    3: 340.0,
    4: 340.0,
    5: 340.0,
    6: 340.0,
    7: 340.0,
    8: 600.0,
    9: 1000.0,
    10: 600.0,
    11: 340.0,
    12: 600.0,
    13: 340.0,
}

STEP_NAMES: Dict[int, str] = {
    1: "Duplicate Check",
    2: "Docs Comparison",
    3: "Research",
    4: "Clarify",
    5: "Docs Changes",
    6: "Identify Dev Units",
    7: "Architecture Review",
    8: "Analyze Prompt Changes",
    9: "Implement Changes",
    10: "Architecture Update",
    11: "Identify Issues",
    12: "Fix Issues",
    13: "Create PR",
}

STEP_TEMPLATE_NAMES: Dict[int, str] = {
    1: "agentic_change_step1_duplicate_LLM",
    2: "agentic_change_step2_docs_LLM",
    3: "agentic_change_step3_research_LLM",
    4: "agentic_change_step4_clarify_LLM",
    5: "agentic_change_step5_docs_change_LLM",
    6: "agentic_change_step6_devunits_LLM",
    7: "agentic_change_step7_architecture_LLM",
    8: "agentic_change_step8_analyze_LLM",
    9: "agentic_change_step9_implement_LLM",
    10: "agentic_change_step10_architecture_update_LLM",
    11: "agentic_change_step11_identify_issues_LLM",
    12: "agentic_change_step12_fix_issues_LLM",
    13: "agentic_change_step13_create_pr_LLM",
}

MAX_REVIEW_ITERATIONS = 5
MAX_CONSECUTIVE_PROVIDER_FAILURES = 3
_PREFLIGHT_MAX_HEAL_MODULES = 10
_PREFLIGHT_CHDIR_LOCK = threading.Lock()


# ---------------------------------------------------------------------------
# Helper: Project configuration (.pddrc)
# ---------------------------------------------------------------------------

def _load_pddrc_context(cwd: Path) -> Dict[str, str]:
    """Load .pddrc context for prompt template variables."""
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
        context_name = _detect_context(cwd, config)

        # Extract context's defaults
        contexts = config.get("contexts", {}) if isinstance(config, dict) else {}
        ctx = contexts.get(context_name, {}) if isinstance(contexts, dict) else {}
        ctx_defaults = ctx.get("defaults", {}) if isinstance(ctx, dict) else {}

        language = ctx_defaults.get("default_language", defaults["language"])
        source_dir = ctx_defaults.get("generate_output_path", defaults["source_dir"])
        test_dir = ctx_defaults.get("test_output_path", defaults["test_dir"])
        example_dir = ctx_defaults.get("example_output_path", defaults["example_dir"])

        ext = get_extension(language)
        if ext.startswith("."):
            ext = ext[1:]
        lang = f"_{language}"

        return {
            "language": language,
            "source_dir": source_dir,
            "test_dir": test_dir,
            "example_dir": example_dir,
            "ext": ext or defaults["ext"],
            "lang": lang,
        }
    except Exception:
        return defaults


# ---------------------------------------------------------------------------
# Helper: Git operations
# ---------------------------------------------------------------------------

def _run_git(args: List[str], cwd: Path, capture: bool = True, timeout: float = 60.0) -> subprocess.CompletedProcess:
    """Run a git command."""
    return subprocess.run(
        ["git", *args],
        cwd=str(cwd),
        capture_output=capture,
        text=True,
        timeout=timeout,
    )


def _get_git_root(cwd: Path) -> Optional[Path]:
    """Get the repository root via git rev-parse --show-toplevel."""
    try:
        result = _run_git(["rev-parse", "--show-toplevel"], cwd)
        if result.returncode == 0:
            return Path(result.stdout.strip())
    except Exception:
        pass
    return None


def _resolve_main_ref(git_root: Path) -> str:
    """Resolve the main branch ref for use as worktree base."""
    candidates = ["origin/main", "origin/master", "main", "master"]
    for ref in candidates:
        try:
            result = _run_git(["rev-parse", "--verify", ref], git_root)
            if result.returncode == 0:
                return result.stdout.strip()
        except Exception:
            continue
    return "HEAD"


def _worktree_exists(cwd: Path, worktree_path: Path) -> bool:
    """Check if path is in `git worktree list --porcelain` output."""
    try:
        result = _run_git(["worktree", "list", "--porcelain"], cwd)
        if result.returncode != 0:
            return False
        target = str(worktree_path.resolve())
        for line in result.stdout.splitlines():
            if line.startswith("worktree "):
                wt_path = line.split(" ", 1)[1].strip()
                try:
                    if str(Path(wt_path).resolve()) == target:
                        return True
                except Exception:
                    continue
    except Exception:
        pass
    return False


def _branch_exists(cwd: Path, branch: str) -> bool:
    """Check if a local branch exists."""
    try:
        result = _run_git(["show-ref", "--verify", f"refs/heads/{branch}"], cwd)
        return result.returncode == 0
    except Exception:
        return False


def _remove_worktree(cwd: Path, worktree_path: Path) -> Tuple[bool, str]:
    """Remove an existing worktree."""
    try:
        result = _run_git(["worktree", "remove", "--force", str(worktree_path)], cwd)
        if result.returncode == 0:
            return True, ""
        return False, result.stderr.strip() or "git worktree remove failed"
    except Exception as e:
        return False, str(e)


def _delete_branch(cwd: Path, branch: str) -> Tuple[bool, str]:
    """Delete a local branch."""
    try:
        result = _run_git(["branch", "-D", branch], cwd)
        if result.returncode == 0:
            return True, ""
        return False, result.stderr.strip() or "git branch -D failed"
    except Exception as e:
        return False, str(e)


def _setup_worktree(
    cwd: Path, issue_number: int, quiet: bool
) -> Tuple[Optional[Path], Optional[str]]:
    """Create an isolated git worktree for the change workflow."""
    git_root = _get_git_root(cwd)
    if not git_root:
        return None, "Not in a git repository"

    worktree_path = git_root / ".pdd" / "worktrees" / f"change-issue-{issue_number}"
    branch_name = f"change/issue-{issue_number}"

    # If worktree already exists, remove it
    if _worktree_exists(git_root, worktree_path):
        ok, err = _remove_worktree(git_root, worktree_path)
        if not ok and not quiet:
            console.print(f"[yellow]Warning removing existing worktree: {err}[/yellow]")

    # If directory exists but is not a worktree, remove it
    if worktree_path.exists():
        try:
            shutil.rmtree(worktree_path)
        except Exception as e:
            return None, f"Failed to remove existing directory: {e}"

    # Ensure parent directory exists
    worktree_path.parent.mkdir(parents=True, exist_ok=True)

    main_ref = _resolve_main_ref(git_root)

    if _branch_exists(git_root, branch_name):
        # Try to delete the branch first
        deleted, _del_err = _delete_branch(git_root, branch_name)
        if deleted:
            # Create new branch from main ref
            try:
                result = _run_git(
                    ["worktree", "add", "-b", branch_name, str(worktree_path), main_ref],
                    git_root,
                )
                if result.returncode != 0:
                    return None, result.stderr.strip() or "git worktree add failed"
            except Exception as e:
                return None, str(e)
        else:
            # Branch couldn't be deleted (perhaps in use); use existing
            try:
                result = _run_git(
                    ["worktree", "add", "--force", str(worktree_path), branch_name],
                    git_root,
                )
                if result.returncode != 0:
                    return None, result.stderr.strip() or "git worktree add --force failed"
            except Exception as e:
                return None, str(e)
    else:
        # Create new branch from main ref
        try:
            result = _run_git(
                ["worktree", "add", "-b", branch_name, str(worktree_path), main_ref],
                git_root,
            )
            if result.returncode != 0:
                return None, result.stderr.strip() or "git worktree add failed"
        except Exception as e:
            return None, str(e)

    return worktree_path, None


def _detect_worktree_changes(
    worktree_path: Path,
    direct_edit_candidates: Optional[List[str]] = None,
) -> List[str]:
    """Detect file changes in worktree via git status --porcelain."""
    candidates = set(direct_edit_candidates or [])
    changed: List[str] = []
    try:
        result = _run_git(["status", "--porcelain"], worktree_path)
        if result.returncode != 0:
            return []
        for line in result.stdout.splitlines():
            if not line.strip():
                continue
            # Format: XY path  (or XY orig -> path for renames)
            status = line[:2]
            rest = line[3:].strip() if len(line) > 3 else ""
            if "->" in rest:
                rest = rest.split("->", 1)[1].strip()
            # Strip surrounding quotes
            if rest.startswith('"') and rest.endswith('"'):
                rest = rest[1:-1]
            if not rest:
                continue
            # Skip temp files
            if ".agentic_prompt_" in rest:
                continue
            basename = Path(rest).name
            if rest.endswith(".prompt") or rest.endswith(".md"):
                changed.append(rest)
            elif rest in candidates or basename in candidates:
                changed.append(rest)
            elif candidates and any(rest.endswith(c) or c.endswith(rest) for c in candidates):
                changed.append(rest)
        # Dedupe preserve order
        seen: Set[str] = set()
        dedup: List[str] = []
        for f in changed:
            if f not in seen:
                seen.add(f)
                dedup.append(f)
        return dedup
    except Exception:
        return []


# ---------------------------------------------------------------------------
# Helper: GitHub operations
# ---------------------------------------------------------------------------

def _check_existing_pr(
    repo_owner: str, repo_name: str, issue_number: int
) -> Optional[str]:
    """Check if an open PR already exists for change/issue-{N}."""
    branch = f"change/issue-{issue_number}"
    try:
        result = subprocess.run(
            [
                "gh",
                "pr",
                "list",
                "--repo",
                f"{repo_owner}/{repo_name}",
                "--head",
                branch,
                "--state",
                "open",
                "--json",
                "url",
            ],
            capture_output=True,
            text=True,
            timeout=30,
        )
        if result.returncode != 0:
            return None
        data = json.loads(result.stdout or "[]")
        if isinstance(data, list) and data:
            entry = data[0]
            if isinstance(entry, dict) and "url" in entry:
                return entry["url"]
    except Exception:
        return None
    return None


def _fetch_issue_updated_at(
    repo_owner: str, repo_name: str, issue_number: int
) -> str:
    """Fetch current updated_at timestamp for the GitHub issue."""
    try:
        result = subprocess.run(
            [
                "gh",
                "api",
                f"repos/{repo_owner}/{repo_name}/issues/{issue_number}",
                "--jq",
                ".updated_at",
            ],
            capture_output=True,
            text=True,
            timeout=30,
        )
        if result.returncode == 0:
            return result.stdout.strip()
    except Exception:
        pass
    return ""


# ---------------------------------------------------------------------------
# Helper: Output parsing
# ---------------------------------------------------------------------------

def _parse_files_marker(output: str, marker: str) -> List[str]:
    """Parse a `MARKER: path1, path2` line from output."""
    if not output:
        return []
    pattern = re.compile(rf"^{re.escape(marker)}[ \t]*:[ \t]*(.+)$", re.MULTILINE)
    files: List[str] = []
    for match in pattern.finditer(output):
        line = match.group(1).strip()
        if not line or line.lower() in ("none", "n/a", "(none)"):
            continue
        for part in line.split(","):
            p = part.strip()
            if p and p.lower() not in ("none", "n/a"):
                files.append(p)
    # Dedupe preserve order
    seen: Set[str] = set()
    out: List[str] = []
    for f in files:
        if f not in seen:
            seen.add(f)
            out.append(f)
    return out


def _parse_direct_edit_candidates(step6_output: str) -> List[str]:
    """Parse the 'Direct Edit Candidates' table from Step 6 output."""
    if not step6_output:
        return []
    # Find a header that mentions Direct Edit Candidates
    header_re = re.compile(r"direct edit candidates", re.IGNORECASE)
    m = header_re.search(step6_output)
    if not m:
        return []
    # Take everything after the header
    tail = step6_output[m.end():]
    candidates: List[str] = []
    for line in tail.splitlines():
        line = line.rstrip()
        if not line.lstrip().startswith("|"):
            # Stop at first non-table line after we've started
            if candidates:
                break
            continue
        # Skip table separator lines (---)
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if not cells:
            continue
        first = cells[0]
        if not first or set(first) <= set("-: "):
            continue
        # Skip header rows
        if first.lower() in ("file", "file path", "path", "filename"):
            continue
        # Strip backticks
        first = first.strip("`").strip()
        if first:
            candidates.append(first)
    # Dedupe
    seen: Set[str] = set()
    out: List[str] = []
    for c in candidates:
        if c not in seen:
            seen.add(c)
            out.append(c)
    return out


# ---------------------------------------------------------------------------
# Helper: Hard stop detection
# ---------------------------------------------------------------------------

def _check_hard_stop(step_num: int, output: str) -> Optional[str]:
    """Check if a step's output indicates a hard stop. Returns the reason or None."""
    if not output:
        return None

    # Universal STOP_CONDITION tag
    stop_tag = re.search(r"STOP_CONDITION\s*:\s*(.+)", output)
    if stop_tag:
        reason = stop_tag.group(1).strip().splitlines()[0]

        # Steps 4 and 7 ONLY stop via this tag
        if step_num == 4:
            if "clarif" in reason.lower():
                return f"Clarification needed: {reason}"
        elif step_num == 7:
            if "architectural" in reason.lower() or "architecture" in reason.lower():
                return f"Architectural decision needed: {reason}"
        else:
            return reason

    if step_num == 1:
        if re.search(r"Duplicate of #\d+", output):
            return "Issue is a duplicate of an existing issue"
    elif step_num == 2:
        if re.search(r"^(?:\*\*)?(?:status|result)[:\s*]*already implemented",
                     output, re.MULTILINE | re.IGNORECASE):
            return "Issue is already implemented"
    elif step_num == 6:
        if re.search(r"^(?:\*\*)?(?:status|result)[:\s*]*no dev units found",
                     output, re.MULTILINE | re.IGNORECASE):
            return "No dev units found"
    elif step_num == 8:
        if re.search(r"^(?:\*\*)?(?:status|result)[:\s*]*no changes required",
                     output, re.MULTILINE | re.IGNORECASE):
            return "No changes required"
    elif step_num == 9:
        if "FAIL:" in output:
            # Extract the FAIL reason
            m = re.search(r"FAIL:\s*(.+)", output)
            return f"Implementation failed: {m.group(1).strip() if m else 'unknown'}"

    return None


def _is_provider_failure(output: str) -> bool:
    """Check if output indicates all providers failed."""
    return bool(output) and "All agent providers failed" in output


def _review_loop_no_issues(output: str) -> bool:
    """Case-insensitive check for 'no issues found' in output."""
    return bool(output) and "no issues found" in output.lower()


# ---------------------------------------------------------------------------
# Helper: Architecture sanitization
# ---------------------------------------------------------------------------

def _sanitize_architecture_dependencies(worktree_path: Path) -> None:
    """Remove corrupted dependency values from architecture.json."""
    arch_path = worktree_path / "architecture.json"
    if not arch_path.exists():
        return
    try:
        data = json.loads(arch_path.read_text(encoding="utf-8"))
    except Exception:
        return

    def _clean_deps(deps: Any) -> List[str]:
        if not isinstance(deps, list):
            return []
        cleaned: List[str] = []
        for d in deps:
            if not isinstance(d, str):
                continue
            if "\n" in d:
                continue
            if len(d) > 100:
                continue
            if not d.endswith(".prompt"):
                continue
            cleaned.append(d)
        return cleaned

    modules = data["modules"] if isinstance(data, dict) and isinstance(data.get("modules"), list) else data
    if not isinstance(modules, list):
        return
    changed = False
    for entry in modules:
        if isinstance(entry, dict) and "dependencies" in entry:
            new_deps = _clean_deps(entry.get("dependencies"))
            if new_deps != entry.get("dependencies"):
                entry["dependencies"] = new_deps
                changed = True
    if changed:
        try:
            arch_path.write_text(
                json.dumps(data, indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
        except Exception:
            pass


def _sanitize_architecture_interfaces(
    worktree_path: Path,
    previous_architecture: Optional[Any],
) -> List[str]:
    """Merge dropped interface signatures and return any warnings."""
    warnings: List[str] = []
    arch_path = worktree_path / "architecture.json"
    if not arch_path.exists() or previous_architecture is None:
        return warnings
    try:
        current = json.loads(arch_path.read_text(encoding="utf-8"))
    except Exception:
        return warnings

    def _entries(d: Any) -> List[Dict[str, Any]]:
        if isinstance(d, dict) and isinstance(d.get("modules"), list):
            return d["modules"]
        if isinstance(d, list):
            return d
        return []

    old_entries = _entries(previous_architecture)
    new_entries = _entries(current)
    old_by_filename = {
        e.get("filename"): e for e in old_entries if isinstance(e, dict) and e.get("filename")
    }
    changed = False
    for entry in new_entries:
        if not isinstance(entry, dict):
            continue
        fn = entry.get("filename")
        old_entry = old_by_filename.get(fn) if fn else None
        if not old_entry:
            continue
        old_iface = old_entry.get("interface")
        new_iface = entry.get("interface")
        if not isinstance(new_iface, dict):
            continue
        merged, merge_warnings = _merge_interface_signatures(old_iface, new_iface)
        warnings.extend(merge_warnings)
        if merged != new_iface:
            entry["interface"] = merged
            changed = True
    if changed:
        try:
            arch_path.write_text(
                json.dumps(current, indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
        except Exception:
            pass
    return warnings


# ---------------------------------------------------------------------------
# Helper: Dependency context (for Step 6)
# ---------------------------------------------------------------------------

def _build_dependency_context(prompts_dir: Path, quiet: bool = False) -> str:
    """Build a formatted dependency graph for Step 6."""
    if not prompts_dir.exists():
        return ""
    try:
        from pdd.sync_order import build_dependency_graph

        graph = build_dependency_graph(prompts_dir)
        if not graph:
            return ""
        # Reverse graph: module -> dependents
        reverse: Dict[str, Set[str]] = defaultdict(set)
        for mod, deps in graph.items():
            for d in deps:
                reverse[d].add(mod)
        # Sort by number of dependents desc
        sorted_mods = sorted(reverse.items(), key=lambda x: (-len(x[1]), x[0]))[:30]
        lines = ["## Module Dependency Graph", ""]
        for mod, dependents in sorted_mods:
            dep_list = sorted(dependents)[:10]
            lines.append(f"- **{mod}** ({len(dependents)} dependents): {', '.join(dep_list)}")
        return "\n".join(lines)
    except Exception as e:
        if not quiet:
            console.print(f"[yellow]Warning: dependency context build failed: {e}[/yellow]")
        return ""


# ---------------------------------------------------------------------------
# Helper: Pre-flight drift heal (Step 8.5)
# ---------------------------------------------------------------------------

def _preflight_drift_heal(
    worktree_path: Path,
    quiet: bool = False,
    timeout_per_module: float = 300.0,
    max_modules: int = _PREFLIGHT_MAX_HEAL_MODULES,
) -> Tuple[List[str], List[str], List[str]]:
    """Heal modules whose prompts are stale relative to their code.

    Contained to the worktree. Single-pass (no fixed-point loop).
    Returns (healed_basenames, failed_basenames, healed_prompt_paths).
    """
    healed: List[str] = []
    failed: List[str] = []
    healed_prompts: List[str] = []

    with _PREFLIGHT_CHDIR_LOCK:
        try:
            from pdd.ci_drift_heal import detect_drift  # type: ignore
        except Exception as e:
            if not quiet:
                console.print(
                    f"[yellow]Pre-flight drift heal: detect_drift import failed ({e}); skipping.[/yellow]"
                )
            return healed, failed, healed_prompts

        original_cwd = os.getcwd()
        try:
            os.chdir(str(worktree_path))
            try:
                drift_result = detect_drift()
            except Exception as e:
                if not quiet:
                    console.print(
                        f"[yellow]Pre-flight drift heal: detect_drift failed ({e}); skipping.[/yellow]"
                    )
                return healed, failed, healed_prompts

            # Expected: (prompt_drifts, example_drifts)
            try:
                prompt_drifts, _example_drifts = drift_result
            except Exception:
                prompt_drifts = drift_result if isinstance(drift_result, list) else []

            # Filter for operation == "update"
            update_drifts = []
            for d in prompt_drifts or []:
                op = getattr(d, "operation", None)
                if op is None and isinstance(d, dict):
                    decision = d.get("decision") or {}
                    op = decision.get("operation") if isinstance(decision, dict) else None
                if op == "update":
                    update_drifts.append(d)

            if not update_drifts:
                if not quiet:
                    console.print(
                        "[Step 8.5/13] Pre-flight drift check: all prompts in sync with code."
                    )
                return healed, failed, healed_prompts

            # Cap fan-out
            def _drift_basename(d: Any) -> str:
                bn = getattr(d, "basename", None)
                if bn:
                    return bn
                if isinstance(d, dict):
                    return d.get("basename") or d.get("module") or "unknown"
                return "unknown"

            update_drifts.sort(key=_drift_basename)
            if len(update_drifts) > max_modules:
                deferred = [_drift_basename(d) for d in update_drifts[max_modules:]]
                if not quiet:
                    console.print(
                        f"[yellow]Pre-flight: {len(update_drifts)} drifts detected; "
                        f"healing first {max_modules}, deferring {len(deferred)} to CI: "
                        f"{', '.join(deferred[:10])}{'...' if len(deferred) > 10 else ''}[/yellow]"
                    )
                update_drifts = update_drifts[:max_modules]

            # Build heal env
            heal_env = os.environ.copy()
            heal_env.update({
                "PDD_FORCE": "1",
                "CI": "1",
                "NO_COLOR": "1",
                "PDD_FORCE_LOCAL": "1",
                "PDD_SKIP_LOCAL_MODELS": "1",
                "PDD_RESTORE_PROTECTED_PATHS_ON_FAILURE": "1",
            })

            for drift in update_drifts:
                basename = _drift_basename(drift)
                code_path = getattr(drift, "code_path", None)
                if code_path is None and isinstance(drift, dict):
                    code_path = drift.get("code_path")
                prompt_path = getattr(drift, "prompt_path", None)
                if prompt_path is None and isinstance(drift, dict):
                    prompt_path = drift.get("prompt_path")

                if not code_path:
                    failed.append(basename)
                    continue

                try:
                    if not quiet:
                        console.print(f"[blue]Pre-flight heal: pdd update {code_path}[/blue]")
                    proc = subprocess.run(
                        [sys.executable, "-m", "pdd", "update", str(code_path)],
                        cwd=str(worktree_path),
                        capture_output=True,
                        text=True,
                        timeout=timeout_per_module,
                        env=heal_env,
                    )
                    if proc.returncode == 0:
                        healed.append(basename)
                        if prompt_path:
                            healed_prompts.append(str(prompt_path))
                    else:
                        failed.append(basename)
                        if not quiet:
                            err_tail = (proc.stderr or "").strip().splitlines()[-3:]
                            console.print(
                                f"[yellow]Heal failed for {basename} (rc={proc.returncode}): "
                                f"{' | '.join(err_tail)}[/yellow]"
                            )
                except subprocess.TimeoutExpired:
                    failed.append(basename)
                    if not quiet:
                        console.print(f"[yellow]Heal timeout for {basename}[/yellow]")
                except Exception as e:
                    failed.append(basename)
                    if not quiet:
                        console.print(f"[yellow]Heal error for {basename}: {e}[/yellow]")
        finally:
            try:
                os.chdir(original_cwd)
            except Exception:
                pass

    return healed, failed, healed_prompts


# ---------------------------------------------------------------------------
# Helper: Doc-sync contract verifier (Step 10.5)
# ---------------------------------------------------------------------------

def _verify_doc_sync_contract(
    discovered_docs: List[str],
    step10_output: str,
) -> Tuple[List[str], List[str], List[str], List[str], List[str]]:
    """Verify that every discovered doc appears in EXACTLY ONE bucket.

    Returns (modified, conflicted, unchanged, silently_dropped, overlapping).
    """
    modified = _parse_files_marker(step10_output, "ASSOCIATED_DOCS_MODIFIED")
    conflicted = _parse_files_marker(step10_output, "ASSOCIATED_DOCS_CONFLICTS")
    unchanged = _parse_files_marker(step10_output, "ASSOCIATED_DOCS_UNCHANGED")

    silently_dropped: List[str] = []
    overlapping: List[str] = []

    mod_set = set(modified)
    conf_set = set(conflicted)
    unch_set = set(unchanged)

    for doc in discovered_docs:
        buckets = sum([doc in mod_set, doc in conf_set, doc in unch_set])
        if buckets == 0:
            silently_dropped.append(doc)
        elif buckets > 1:
            overlapping.append(doc)

    return modified, conflicted, unchanged, silently_dropped, overlapping


# ---------------------------------------------------------------------------
# Helper: Truncation for console
# ---------------------------------------------------------------------------

def _last_line(output: str, max_len: int = 80) -> str:
    if not output:
        return ""
    for line in reversed(output.splitlines()):
        if line.strip():
            line = line.strip()
            if len(line) > max_len:
                line = line[: max_len - 3] + "..."
            return line
    return ""


def _format_template(prompt_template: str, context: Dict[str, Any]) -> str:
    """Preprocess (expand includes) then substitute template variables."""
    try:
        processed = preprocess(
            prompt_template,
            recursive=True,
            double_curly_brackets=True,
            exclude_keys=list(context.keys()),
        )
    except Exception:
        processed = prompt_template
    return substitute_template_variables(processed, context)


# ---------------------------------------------------------------------------
# Main orchestrator
# ---------------------------------------------------------------------------

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
    use_github_state: bool = True,
) -> Tuple[bool, str, float, str, List[str]]:
    """Run the 13-step agentic change workflow.

    Returns (success, final_message, total_cost, model_used, changed_files).
    """
    cwd = Path(cwd).resolve()
    total_cost = 0.0
    model_used = "unknown"
    changed_files: List[str] = []

    # ---- Existing PR guard ----
    try:
        existing_pr = _check_existing_pr(repo_owner, repo_name, issue_number)
    except Exception:
        existing_pr = None
    if existing_pr:
        if not quiet:
            console.print(f"[yellow]PR already exists: {existing_pr}[/yellow]")
        return True, f"PR already exists: {existing_pr}", 0.0, "unknown", []

    # ---- Header ----
    if not quiet:
        console.print(
            f"\n[bold cyan]Implementing change for issue #{issue_number}: "
            f'"{issue_title}"[/bold cyan]\n'
        )

    # ---- Clear stale progress, then track ----
    try:
        clear_agentic_progress()
    except Exception:
        pass

    # ---- State setup ----
    state_dir = cwd / ".pdd" / "change-state"
    git_root = _get_git_root(cwd)
    if git_root:
        state_dir = git_root / ".pdd" / "change-state"

    try:
        loaded = load_workflow_state(
            cwd=cwd,
            issue_number=issue_number,
            workflow="change",
            state_dir=state_dir,
            repo_owner=repo_owner,
            repo_name=repo_name,
            use_github_state=use_github_state,
        )
    except Exception as e:
        if not quiet:
            console.print(f"[yellow]State load failed: {e}; starting fresh.[/yellow]")
        loaded = None

    state: Dict[str, Any] = {}
    github_comment_id: Optional[str] = None
    if loaded:
        if isinstance(loaded, tuple) and len(loaded) == 2:
            state, github_comment_id = loaded
        elif isinstance(loaded, dict):
            state = loaded
            github_comment_id = state.get("github_comment_id")
        else:
            state = {}

    if not isinstance(state, dict):
        state = {}

    # ---- Stale state detection ----
    if state and issue_updated_at:
        prior_updated = state.get("issue_updated_at", "")
        if prior_updated and prior_updated != issue_updated_at:
            if not quiet:
                console.print(
                    "[yellow]Issue was updated since last run; clearing state and starting fresh.[/yellow]"
                )
            try:
                clear_workflow_state(
                    cwd=cwd,
                    issue_number=issue_number,
                    workflow="change",
                    state_dir=state_dir,
                    repo_owner=repo_owner,
                    repo_name=repo_name,
                    use_github_state=use_github_state,
                )
            except Exception:
                pass
            state = {}
            github_comment_id = None

    # ---- Initialize state defaults ----
    state.setdefault("workflow", "change")
    state.setdefault("issue_url", issue_url)
    state.setdefault("issue_number", issue_number)
    state.setdefault("step_outputs", {})
    state.setdefault("total_cost", 0.0)
    state.setdefault("model_used", "unknown")
    state.setdefault("review_iteration", 0)
    state.setdefault("previous_fixes", "")
    state["issue_updated_at"] = issue_updated_at or state.get("issue_updated_at", "")

    # Normalize step_comments
    step_comments_set: Set[int] = normalize_step_comments_state(state.get("step_comments"))
    state["step_comments"] = sorted(step_comments_set)

    # Validate cached state to find true last successful step
    try:
        last_completed = validate_cached_state(state)
    except Exception:
        last_completed = state.get("last_completed_step", 0) or 0
    state["last_completed_step"] = last_completed
    start_step = (last_completed or 0) + 1

    total_cost = float(state.get("total_cost", 0.0) or 0.0)
    model_used = state.get("model_used", "unknown") or "unknown"

    # Recover changed_files from state
    if "changed_files" in state and isinstance(state["changed_files"], list):
        changed_files = list(state["changed_files"])

    if start_step > 1 and not quiet:
        console.print(
            f"[blue]Resuming from step {start_step} (steps 1-{last_completed} cached)[/blue]"
        )

    # ---- Build initial context ----
    pddrc_context = _load_pddrc_context(cwd)
    context: Dict[str, Any] = {
        "issue_url": issue_url,
        "issue_content": issue_content,
        "repo_owner": repo_owner,
        "repo_name": repo_name,
        "issue_number": str(issue_number),
        "issue_author": issue_author,
        "issue_title": issue_title,
        **pddrc_context,
    }

    # Replay cached step outputs into context
    for n_str, output in state.get("step_outputs", {}).items():
        try:
            n = int(n_str)
        except Exception:
            continue
        if isinstance(output, str) and not output.startswith("FAILED:"):
            context[f"step{n}_output"] = output

    # ---- Helpers for state ----
    def _save_state() -> None:
        nonlocal github_comment_id
        try:
            state["total_cost"] = total_cost
            state["model_used"] = model_used
            state["changed_files"] = list(changed_files)
            state["step_comments"] = sorted(step_comments_set)
            result = save_workflow_state(
                cwd=cwd,
                issue_number=issue_number,
                workflow="change",
                state=state,
                state_dir=state_dir,
                repo_owner=repo_owner,
                repo_name=repo_name,
                use_github_state=use_github_state,
                github_comment_id=github_comment_id,
            )
            if isinstance(result, str):
                github_comment_id = result
                state["github_comment_id"] = result
            elif isinstance(result, dict) and "comment_id" in result:
                github_comment_id = result["comment_id"]
                state["github_comment_id"] = result["comment_id"]
        except Exception as e:
            if not quiet:
                console.print(f"[yellow]Warning: state save failed: {e}[/yellow]")

    def _post_success_comment(step_num: int, step_output: str, current_work_dir: Path) -> None:
        """Per-step success-comment hook (best-effort)."""
        try:
            report_body = extract_step_report(step_output)
            if report_body is None:
                return
            try:
                ok = post_step_comment_once(
                    repo_owner,
                    repo_name,
                    issue_number,
                    step_num,
                    report_body,
                    step_comments_set,
                    current_work_dir,
                )
            except Exception as e:
                if not quiet:
                    console.print(f"[yellow]post_step_comment_once failed: {e}[/yellow]")
                ok = False
            # Persist canonical sorted form unconditionally
            try:
                state["step_comments"] = sorted(step_comments_set)
                _save_state()
            except Exception:
                pass
            if not ok and not quiet:
                console.print(
                    f"[yellow]Warning: step {step_num} success comment not posted[/yellow]"
                )
        except Exception as e:
            if not quiet:
                console.print(f"[yellow]Step success-comment hook error: {e}[/yellow]")

    def _hard_stop(step_num: int, reason: str, current_work_dir: Path) -> Tuple[bool, str, float, str, List[str]]:
        """Handle a hard-stop: post comment, save state, return failure tuple."""
        if not quiet:
            console.print(
                f"\n[bold yellow]Investigation stopped at Step {step_num}: {reason}[/bold yellow]"
            )

        # Clarification steps re-run on resume
        if step_num in (4, 7):
            state["last_completed_step"] = step_num - 1

        try:
            post_step_comment(
                repo_owner=repo_owner,
                repo_name=repo_name,
                issue_number=issue_number,
                step_num=step_num,
                step_name=STEP_NAMES.get(step_num, f"Step {step_num}"),
                output=reason,
                cwd=current_work_dir,
                is_failure=True,
            )
        except Exception as e:
            if not quiet:
                console.print(f"[yellow]Failed to post stop comment: {e}[/yellow]")

        _save_state()

        # Refresh issue_updated_at after clarification stops
        if step_num in (4, 7):
            try:
                fresh = _fetch_issue_updated_at(repo_owner, repo_name, issue_number)
                if fresh:
                    state["issue_updated_at"] = fresh
                    _save_state()
            except Exception:
                pass

        try:
            clear_agentic_progress()
        except Exception:
            pass

        return (
            False,
            f"Stopped at step {step_num}: {reason}",
            total_cost,
            model_used,
            changed_files,
        )

    # ---- Working directory tracking ----
    current_work_dir = cwd
    worktree_path: Optional[Path] = None
    if state.get("worktree_path"):
        wt_candidate = Path(state["worktree_path"])
        if wt_candidate.exists():
            worktree_path = wt_candidate
            current_work_dir = wt_candidate
            context["worktree_path"] = str(wt_candidate)

    consecutive_provider_failures = 0
    files_created: List[str] = []
    files_modified: List[str] = []
    direct_edits: List[str] = []

    # ---- Recover prior step files info from cached step9 output ----
    if "9" in state.get("step_outputs", {}):
        cached9 = state["step_outputs"]["9"]
        if isinstance(cached9, str) and not cached9.startswith("FAILED:"):
            files_created = _parse_files_marker(cached9, "FILES_CREATED")
            files_modified = _parse_files_marker(cached9, "FILES_MODIFIED")
            direct_edits = _parse_files_marker(cached9, "DIRECT_EDITS")
            context["files_created"] = ", ".join(files_created) or "None"
            context["files_modified"] = ", ".join(files_modified) or "None"
            context["direct_edits"] = ", ".join(direct_edits) or "None"
            if not changed_files:
                merged = list(files_created) + list(files_modified) + list(direct_edits)
                seen: Set[str] = set()
                for f in merged:
                    if f and f not in seen:
                        seen.add(f)
                        changed_files.append(f)
            context["files_to_stage"] = ", ".join(changed_files) or "None"

    # ---- Recover direct_edit_candidates from cached step6 output ----
    if "6" in state.get("step_outputs", {}):
        cached6 = state["step_outputs"]["6"]
        if isinstance(cached6, str) and not cached6.startswith("FAILED:"):
            context["direct_edit_candidates"] = _parse_direct_edit_candidates(cached6)

    # =====================================================================
    # MAIN STEP LOOP (steps 1-10)
    # =====================================================================
    for step_num in range(1, 11):
        step_name = STEP_NAMES[step_num]
        completed_steps = list(range(1, step_num))

        try:
            set_agentic_progress(
                workflow="change",
                current_step=step_num,
                total_steps=13,
                step_name=step_name,
                completed_steps=completed_steps,
            )
        except Exception:
            pass

        # Check cache
        cached_output = state.get("step_outputs", {}).get(str(step_num))
        if (
            step_num < start_step
            and isinstance(cached_output, str)
            and not cached_output.startswith("FAILED:")
        ):
            context[f"step{step_num}_output"] = cached_output
            if not quiet:
                console.print(f"[dim][Step {step_num}/13] {step_name}: cached[/dim]")
                console.print(f"  → Step {step_num} complete.")
            # Check for hard stop in cached output (resume sanity)
            stop_reason = _check_hard_stop(step_num, cached_output)
            if stop_reason:
                return _hard_stop(step_num, stop_reason, current_work_dir)
            # Step-specific cached recovery
            if step_num == 6:
                context["direct_edit_candidates"] = _parse_direct_edit_candidates(cached_output)
            continue

        # ---- Pre-step-9: setup worktree ----
        if step_num == 9 and worktree_path is None:
            # Warn if not on main/master
            try:
                br_result = _run_git(["rev-parse", "--abbrev-ref", "HEAD"], cwd)
                current_branch = br_result.stdout.strip() if br_result.returncode == 0 else ""
                if current_branch and current_branch not in ("main", "master") and not quiet:
                    console.print(
                        f"[yellow]Note: Creating branch from HEAD ({current_branch}), "
                        "not origin/main. PR will include commits from this branch. "
                        "Run from main for independent changes.[/yellow]"
                    )
            except Exception:
                pass
            wt, err = _setup_worktree(cwd, issue_number, quiet)
            if not wt:
                try:
                    clear_agentic_progress()
                except Exception:
                    pass
                return (
                    False,
                    f"Failed to create worktree: {err}",
                    total_cost,
                    model_used,
                    changed_files,
                )
            worktree_path = wt
            current_work_dir = wt
            context["worktree_path"] = str(wt)
            state["worktree_path"] = str(wt)
            if not quiet:
                console.print(f"[blue]Working in worktree: {wt}[/blue]")

            # ---- Step 8.5: Pre-flight drift heal ----
            already_healed = (
                state.get("preflight_drift_healed") is True
                and state.get("preflight_healed_worktree") == str(worktree_path)
            )
            if not already_healed:
                if not quiet:
                    console.print(f"[Step 8.5/13] Pre-flight drift heal...")
                try:
                    healed, failed_h, healed_prompts = _preflight_drift_heal(
                        worktree_path, quiet=quiet
                    )
                except Exception as e:
                    if not quiet:
                        console.print(f"[yellow]Pre-flight heal error: {e}[/yellow]")
                    healed, failed_h, healed_prompts = [], [], []
                state["preflight_drift_healed"] = True
                state["preflight_healed_worktree"] = str(worktree_path)
                state["preflight_healed_modules"] = healed
                state["preflight_failed_heal_modules"] = failed_h
                state["preflight_healed_prompt_paths"] = healed_prompts
                context["preflight_healed_modules"] = ", ".join(healed) if healed else "None"
                context["preflight_failed_heal_modules"] = (
                    ", ".join(failed_h) if failed_h else "None"
                )
                _save_state()
            else:
                context["preflight_healed_modules"] = (
                    ", ".join(state.get("preflight_healed_modules", [])) or "None"
                )
                context["preflight_failed_heal_modules"] = (
                    ", ".join(state.get("preflight_failed_heal_modules", [])) or "None"
                )

        # ---- Pre-step-6: dependency context ----
        if step_num == 6:
            prompts_dir = (worktree_path or cwd) / "prompts"
            try:
                dep_ctx = _build_dependency_context(prompts_dir, quiet=quiet)
            except Exception:
                dep_ctx = ""
            context["dependency_context"] = dep_ctx or "(no dependency graph available)"

        # ---- Pre-step-10: associated documents discovery ----
        previous_architecture: Optional[Any] = None
        if step_num == 10 and worktree_path and worktree_path.exists():
            # Snapshot architecture.json
            arch_path = worktree_path / "architecture.json"
            if arch_path.exists():
                try:
                    previous_architecture = json.loads(arch_path.read_text(encoding="utf-8"))
                except Exception:
                    previous_architecture = None

            # Build modified_prompts from authoritative changed-file set
            sources: List[str] = []
            sources.extend(files_created)
            sources.extend(files_modified)
            for s in (context.get("files_to_stage") or "").split(","):
                s = s.strip()
                if s:
                    sources.append(s)
            sources.extend(changed_files)
            # If still empty, do worktree fallback detection
            if not sources:
                detected = _detect_worktree_changes(
                    worktree_path,
                    _parse_direct_edit_candidates(context.get("step6_output", "")),
                )
                sources.extend(detected)

            modified_prompts: Set[Path] = set()
            for s in sources:
                if not s.endswith(".prompt"):
                    continue
                p = (worktree_path / s).resolve()
                modified_prompts.add(p)

            # Add healed prompts
            for hp in state.get("preflight_healed_prompt_paths", []) or []:
                try:
                    p = Path(hp).resolve()
                    if p.suffix == ".prompt":
                        modified_prompts.add(p)
                except Exception:
                    pass

            assoc_docs: List[str] = []
            if modified_prompts:
                try:
                    from pdd.sync_order import discover_associated_documents

                    assoc_docs = discover_associated_documents(
                        modified_prompts=modified_prompts,
                        prompts_dir=worktree_path / "prompts",
                        architecture_path=arch_path if arch_path.exists() else None,
                        max_depth=3,
                    )
                except Exception as e:
                    if not quiet:
                        console.print(
                            f"[yellow]Associated-docs discovery failed: {e}[/yellow]"
                        )
                    assoc_docs = []
            context["associated_documents"] = ", ".join(assoc_docs) if assoc_docs else "None"
            context["_associated_documents_discovered"] = list(assoc_docs)

        # ---- Load prompt template ----
        template_name = STEP_TEMPLATE_NAMES[step_num]
        if not quiet:
            console.print(f"[Step {step_num}/13] {step_name}...")

        try:
            template = load_prompt_template(template_name)
        except Exception as e:
            if not quiet:
                console.print(f"[red]Failed to load template {template_name}: {e}[/red]")
            template = None

        if not template:
            err = f"Could not load template {template_name}"
            state.setdefault("step_outputs", {})[str(step_num)] = f"FAILED: {err}"
            _save_state()
            try:
                clear_agentic_progress()
            except Exception:
                pass
            return (False, err, total_cost, model_used, changed_files)

        formatted = _format_template(template, context)

        # ---- Run agentic task ----
        timeout = CHANGE_STEP_TIMEOUTS.get(step_num, 340.0) + timeout_adder
        try:
            result = run_agentic_task(
                instruction=formatted,
                cwd=current_work_dir,
                verbose=verbose,
                quiet=quiet,
                timeout=timeout,
                label=f"step{step_num}",
                max_retries=DEFAULT_MAX_RETRIES,
            )
        except Exception as e:
            if not quiet:
                console.print(f"[red]Step {step_num} exception: {e}[/red]")
            state.setdefault("step_outputs", {})[str(step_num)] = f"FAILED: {e}"
            _save_state()
            try:
                clear_agentic_progress()
            except Exception:
                pass
            return (False, f"Step {step_num} crashed: {e}", total_cost, model_used, changed_files)

        # Unpack result (success, output, cost, model)
        success = False
        step_output = ""
        step_cost = 0.0
        step_model = model_used
        try:
            if isinstance(result, tuple):
                if len(result) >= 4:
                    success, step_output, step_cost, step_model = result[0], result[1], result[2], result[3]
                elif len(result) == 3:
                    success, step_output, step_cost = result
                elif len(result) == 2:
                    success, step_output = result
        except Exception:
            pass

        try:
            total_cost += float(step_cost or 0.0)
        except Exception:
            pass
        if step_model and step_model != "unknown":
            model_used = step_model

        if not isinstance(step_output, str):
            step_output = str(step_output) if step_output else ""

        # Track consecutive provider failures
        if _is_provider_failure(step_output):
            consecutive_provider_failures += 1
        else:
            consecutive_provider_failures = 0

        if consecutive_provider_failures >= MAX_CONSECUTIVE_PROVIDER_FAILURES:
            msg = (
                f"Aborting: {consecutive_provider_failures} consecutive steps failed "
                "— agent providers unavailable"
            )
            if not quiet:
                console.print(f"[red]{msg}[/red]")
            try:
                post_step_comment(
                    repo_owner=repo_owner,
                    repo_name=repo_name,
                    issue_number=issue_number,
                    step_num=step_num,
                    step_name=step_name,
                    output=msg,
                    cwd=current_work_dir,
                    is_failure=True,
                )
            except Exception:
                pass
            state.setdefault("step_outputs", {})[str(step_num)] = f"FAILED: {step_output}"
            _save_state()
            try:
                clear_agentic_progress()
            except Exception:
                pass
            return (False, msg, total_cost, model_used, changed_files)

        # Store output
        state.setdefault("step_outputs", {})[str(step_num)] = (
            step_output if success else f"FAILED: {step_output}"
        )
        context[f"step{step_num}_output"] = step_output

        # Check hard stop conditions
        stop_reason = _check_hard_stop(step_num, step_output)

        if not quiet:
            tail = _last_line(step_output)
            if tail:
                console.print(f"  -> {tail}")

        # ---- Step 6 post-processing ----
        if step_num == 6 and success:
            context["direct_edit_candidates"] = _parse_direct_edit_candidates(step_output)

        # ---- Step 9 post-processing ----
        if step_num == 9 and success:
            files_created = _parse_files_marker(step_output, "FILES_CREATED")
            files_modified = _parse_files_marker(step_output, "FILES_MODIFIED")
            direct_edits = _parse_files_marker(step_output, "DIRECT_EDITS")

            # Fallback: detect from worktree
            if not (files_created or files_modified or direct_edits) and worktree_path:
                detected = _detect_worktree_changes(
                    worktree_path, context.get("direct_edit_candidates")
                )
                # Treat all detected as modified for downstream context
                files_modified = detected

            # Build changed_files
            seen: Set[str] = set()
            changed_files = []
            for f in (files_created + files_modified + direct_edits):
                if f and f not in seen:
                    seen.add(f)
                    changed_files.append(f)

            context["files_created"] = ", ".join(files_created) or "None"
            context["files_modified"] = ", ".join(files_modified) or "None"
            context["direct_edits"] = ", ".join(direct_edits) or "None"
            context["files_to_stage"] = ", ".join(changed_files) or "None"

        # ---- Step 10 post-processing ----
        if step_num == 10 and success and worktree_path:
            arch_files = _parse_files_marker(step_output, "ARCHITECTURE_FILES_MODIFIED")
            docs_modified = _parse_files_marker(step_output, "ASSOCIATED_DOCS_MODIFIED")
            docs_conflicts = _parse_files_marker(step_output, "ASSOCIATED_DOCS_CONFLICTS")
            docs_unchanged = _parse_files_marker(step_output, "ASSOCIATED_DOCS_UNCHANGED")

            for f in arch_files + docs_modified:
                if f and f not in changed_files:
                    changed_files.append(f)

            if docs_conflicts and not quiet:
                console.print(
                    f"[yellow]Associated docs flagged as conflicts (need human review): "
                    f"{', '.join(docs_conflicts)}[/yellow]"
                )
            if docs_unchanged and not quiet:
                console.print(
                    f"[dim]Associated docs unchanged: {', '.join(docs_unchanged)}[/dim]"
                )

            context["files_to_stage"] = ", ".join(changed_files) or "None"

            # ---- Sanitize architecture.json ----
            try:
                _sanitize_architecture_dependencies(worktree_path)
            except Exception as e:
                if not quiet:
                    console.print(f"[yellow]Arch dep sanitize failed: {e}[/yellow]")
            try:
                merge_warnings = _sanitize_architecture_interfaces(
                    worktree_path, previous_architecture
                )
                if merge_warnings:
                    step_output += "\n\nORCHESTRATOR_POSTCHECK_WARNINGS:\n"
                    for w in merge_warnings:
                        step_output += f"- {w}\n"
                    state["step_outputs"][str(step_num)] = step_output
                    context[f"step{step_num}_output"] = step_output
            except Exception as e:
                if not quiet:
                    console.print(f"[yellow]Arch interface sanitize failed: {e}[/yellow]")

            # ---- Auto-register untracked prompts (scoped) ----
            try:
                only_files: Set[str] = set()
                for f in changed_files:
                    if not f:
                        continue
                    norm = f.replace("\\", "/")
                    idx = norm.rfind("prompts/")
                    if idx == -1:
                        continue
                    rel = norm[idx + len("prompts/"):]
                    if rel.endswith(".prompt"):
                        only_files.add(rel)
                if only_files:
                    reg_result = register_untracked_prompts(
                        prompts_dir=worktree_path / "prompts",
                        architecture_path=worktree_path / "architecture.json",
                        dry_run=False,
                        only_files=only_files,
                    )
                    if reg_result.get("registered"):
                        reg_list = ", ".join(reg_result["registered"])
                        step_output += f"\n\nORCHESTRATOR_AUTO_REGISTERED: {reg_list}"
                        state["step_outputs"][str(step_num)] = step_output
                        context[f"step{step_num}_output"] = step_output
                        if not quiet:
                            console.print(
                                f"[blue]Auto-registered untracked prompts in arch.json: "
                                f"{reg_list}[/blue]"
                            )
            except Exception as e:
                if not quiet:
                    console.print(f"[yellow]Auto-register failed: {e}[/yellow]")

            # ---- Step 10.5: Doc-sync contract verifier ----
            discovered_docs = context.get("_associated_documents_discovered", []) or []
            if discovered_docs:
                try:
                    (
                        _mod,
                        _conf,
                        _unch,
                        silently_dropped,
                        overlapping,
                    ) = _verify_doc_sync_contract(discovered_docs, step_output)
                except Exception as e:
                    if not quiet:
                        console.print(f"[yellow]Doc-sync verifier failed: {e}[/yellow]")
                    silently_dropped, overlapping = [], []

                if silently_dropped or overlapping:
                    warning_lines = ["", "ORCHESTRATOR_POSTCHECK_WARNINGS:"]
                    for d in silently_dropped:
                        warning_lines.append(f"- Associated doc silently dropped by Step 10: {d}")
                    for d in overlapping:
                        warning_lines.append(
                            f"- Associated doc placed in multiple buckets by Step 10: {d}"
                        )
                    if silently_dropped:
                        warning_lines.append(
                            f"DOC_SYNC_SILENT_DROPS: {', '.join(silently_dropped)}"
                        )
                    if overlapping:
                        warning_lines.append(
                            f"DOC_SYNC_BUCKET_OVERLAPS: {', '.join(overlapping)}"
                        )
                    step_output += "\n".join(warning_lines)
                    state["step_outputs"][str(step_num)] = step_output
                    context[f"step{step_num}_output"] = step_output

                    # Strict mode?
                    strict_env = os.environ.get("PDD_STRICT_DOC_SYNC", "").lower()
                    if strict_env in ("1", "true", "yes"):
                        violations = []
                        if silently_dropped:
                            violations.append(
                                f"silent drops: {', '.join(silently_dropped)}"
                            )
                        if overlapping:
                            violations.append(
                                f"bucket overlaps: {', '.join(overlapping)}"
                            )
                        if not quiet:
                            console.print(
                                f"[bold red]ABORT: PDD_STRICT_DOC_SYNC violation: "
                                f"{'; '.join(violations)}[/bold red]"
                            )
                        state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"
                        _save_state()
                        try:
                            clear_agentic_progress()
                        except Exception:
                            pass
                        return (
                            False,
                            f"Stopped at step 10: PDD_STRICT_DOC_SYNC {'; '.join(violations)}",
                            total_cost,
                            model_used,
                            changed_files,
                        )

        # ---- Update last_completed_step on success ----
        if success and not stop_reason:
            state["last_completed_step"] = step_num

        _save_state()

        # ---- Post per-step success comment ----
        if success and not stop_reason:
            _post_success_comment(step_num, step_output, current_work_dir)

        if not quiet:
            console.print(f"  → Step {step_num} complete.")

        # ---- Hard stop? ----
        if stop_reason:
            return _hard_stop(step_num, stop_reason, current_work_dir)

        # ---- Soft failure: log and continue ----
        if not success:
            if not quiet:
                console.print(
                    f"[yellow]Warning: Step {step_num} reported failure but no hard stop matched; continuing.[/yellow]"
                )

    # =====================================================================
    # REVIEW LOOP (steps 11-12)
    # =====================================================================
    review_iteration = int(state.get("review_iteration", 0) or 0)
    previous_fixes = state.get("previous_fixes", "") or ""

    while review_iteration < MAX_REVIEW_ITERATIONS:
        review_iteration += 1
        state["review_iteration"] = review_iteration
        context["review_iteration"] = str(review_iteration)
        context["previous_fixes"] = previous_fixes or "(none)"

        # ---- Step 11 ----
        try:
            set_agentic_progress(
                workflow="change",
                current_step=11,
                total_steps=13,
                step_name=f"{STEP_NAMES[11]} (iter {review_iteration})",
                completed_steps=list(range(1, 11)),
            )
        except Exception:
            pass

        if not quiet:
            console.print(
                f"[Step 11/13] {STEP_NAMES[11]} (iteration {review_iteration}/{MAX_REVIEW_ITERATIONS})..."
            )

        try:
            template11 = load_prompt_template(STEP_TEMPLATE_NAMES[11])
        except Exception:
            template11 = None
        if not template11:
            if not quiet:
                console.print("[red]Failed to load step 11 template[/red]")
            break
        formatted11 = _format_template(template11, context)
        try:
            result11 = run_agentic_task(
                instruction=formatted11,
                cwd=current_work_dir,
                verbose=verbose,
                quiet=quiet,
                timeout=CHANGE_STEP_TIMEOUTS[11] + timeout_adder,
                label=f"step11_iter{review_iteration}",
                max_retries=DEFAULT_MAX_RETRIES,
            )
        except Exception as e:
            if not quiet:
                console.print(f"[red]Step 11 exception: {e}[/red]")
            break

        success11 = False
        out11 = ""
        cost11 = 0.0
        model11 = model_used
        if isinstance(result11, tuple):
            if len(result11) >= 4:
                success11, out11, cost11, model11 = result11[0], result11[1], result11[2], result11[3]
            elif len(result11) >= 2:
                success11, out11 = result11[0], result11[1]
        try:
            total_cost += float(cost11 or 0.0)
        except Exception:
            pass
        if model11 and model11 != "unknown":
            model_used = model11
        if not isinstance(out11, str):
            out11 = str(out11) if out11 else ""

        context["step11_output"] = out11
        state.setdefault("step_outputs", {})["11"] = out11 if success11 else f"FAILED: {out11}"
        if success11:
            state["last_completed_step"] = 11
        _save_state()

        if success11:
            _post_success_comment(11, out11, current_work_dir)

        if not quiet:
            tail = _last_line(out11)
            if tail:
                console.print(f"  -> {tail}")
            console.print(f"  → Step 11 complete.")

        if _review_loop_no_issues(out11):
            if not quiet:
                console.print(
                    f"[green]Review iteration {review_iteration}: no issues found.[/green]"
                )
            break

        # ---- Step 12 ----
        try:
            set_agentic_progress(
                workflow="change",
                current_step=12,
                total_steps=13,
                step_name=f"{STEP_NAMES[12]} (iter {review_iteration})",
                completed_steps=list(range(1, 12)),
            )
        except Exception:
            pass

        if not quiet:
            console.print(
                f"[Step 12/13] {STEP_NAMES[12]} (iteration {review_iteration})..."
            )

        try:
            template12 = load_prompt_template(STEP_TEMPLATE_NAMES[12])
        except Exception:
            template12 = None
        if not template12:
            if not quiet:
                console.print("[red]Failed to load step 12 template[/red]")
            break
        formatted12 = _format_template(template12, context)
        try:
            result12 = run_agentic_task(
                instruction=formatted12,
                cwd=current_work_dir,
                verbose=verbose,
                quiet=quiet,
                timeout=CHANGE_STEP_TIMEOUTS[12] + timeout_adder,
                label=f"step12_iter{review_iteration}",
                max_retries=DEFAULT_MAX_RETRIES,
            )
        except Exception as e:
            if not quiet:
                console.print(f"[red]Step 12 exception: {e}[/red]")
            break

        success12 = False
        out12 = ""
        cost12 = 0.0
        model12 = model_used
        if isinstance(result12, tuple):
            if len(result12) >= 4:
                success12, out12, cost12, model12 = result12[0], result12[1], result12[2], result12[3]
            elif len(result12) >= 2:
                success12, out12 = result12[0], result12[1]
        try:
            total_cost += float(cost12 or 0.0)
        except Exception:
            pass
        if model12 and model12 != "unknown":
            model_used = model12
        if not isinstance(out12, str):
            out12 = str(out12) if out12 else ""

        context["step12_output"] = out12
        state.setdefault("step_outputs", {})["12"] = out12 if success12 else f"FAILED: {out12}"
        if success12:
            state["last_completed_step"] = 12

        previous_fixes += f"\n\nIteration {review_iteration}:\n{out12}"
        state["previous_fixes"] = previous_fixes
        _save_state()

        if success12:
            _post_success_comment(12, out12, current_work_dir)

        if not quiet:
            tail = _last_line(out12)
            if tail:
                console.print(f"  -> {tail}")
            console.print(f"  → Step 12 complete.")

    if review_iteration >= MAX_REVIEW_ITERATIONS:
        if not quiet:
            console.print(
                f"[yellow]Warning: Maximum review iterations ({MAX_REVIEW_ITERATIONS}) "
                "reached; proceeding to PR creation.[/yellow]"
            )

    # =====================================================================
    # SYNC ORDER GENERATION
    # =====================================================================
    sync_order_script_path = ""
    sync_order_list = "No modules to sync"
    try:
        from pdd.sync_order import (
            build_dependency_graph,
            extract_module_from_include,
            generate_sync_order_script,
            get_affected_modules,
            topological_sort,
        )

        prompts_dir_root = worktree_path or cwd
        prompts_dir = prompts_dir_root / "prompts"
        if prompts_dir.exists():
            graph = build_dependency_graph(prompts_dir)
            sorted_mods, cycles = topological_sort(graph)
            if cycles and not quiet:
                console.print(
                    f"[yellow]Warning: Circular dependencies detected: {cycles}[/yellow]"
                )

            modified_modules: Set[str] = set()
            for f in changed_files:
                if not f:
                    continue
                norm = f.replace("\\", "/")
                if "prompts/" not in norm or not norm.endswith(".prompt"):
                    continue
                basename = Path(norm).name
                mod = extract_module_from_include(basename)
                if mod:
                    modified_modules.add(mod)

            cyclic_set: Set[str] = set()
            for cyc in cycles:
                for c in cyc:
                    cyclic_set.add(c)

            affected = get_affected_modules(sorted_mods, modified_modules, graph, cyclic_set)

            if affected:
                # Generate clean sync command list
                sync_lines = [f"pdd sync {shlex.quote(m)}" for m in affected]
                sync_order_list = "\n".join(sync_lines)

                # Write sync_order.sh in user's CWD AND worktree root
                target_paths = [cwd / "sync_order.sh"]
                if worktree_path:
                    target_paths.append(worktree_path / "sync_order.sh")
                for tp in target_paths:
                    try:
                        generate_sync_order_script(affected, tp, worktree_path)
                    except Exception as e:
                        if not quiet:
                            console.print(
                                f"[yellow]Failed to write {tp}: {e}[/yellow]"
                            )
                # Add worktree's sync_order.sh to changed_files
                if worktree_path:
                    if "sync_order.sh" not in changed_files:
                        changed_files.append("sync_order.sh")
                sync_order_script_path = str(cwd / "sync_order.sh")
    except Exception as e:
        if not quiet:
            console.print(f"[yellow]Sync order generation failed: {e}[/yellow]")

    context["sync_order_script"] = sync_order_script_path
    context["sync_order_list"] = sync_order_list
    context["files_to_stage"] = ", ".join(changed_files) or "None"

    # =====================================================================
    # IMPACTED TESTS
    # =====================================================================
    test_dir_str = pddrc_context.get("test_dir", "tests/")
    test_dir = (worktree_path or cwd) / test_dir_str
    impacted_tests: List[str] = []
    lang_suffix = pddrc_context.get("lang", "_python")
    try:
        if test_dir.exists():
            for f in changed_files:
                if not f:
                    continue
                base = Path(f).stem
                # Strip language suffix
                if base.endswith(lang_suffix):
                    base = base[: -len(lang_suffix)]
                # Search for test_{base}*
                for tf in test_dir.rglob(f"test_{base}*"):
                    try:
                        rel = tf.relative_to(worktree_path or cwd).as_posix()
                    except Exception:
                        rel = str(tf)
                    if rel not in impacted_tests:
                        impacted_tests.append(rel)
    except Exception:
        pass
    context["impacted_tests"] = ", ".join(impacted_tests) if impacted_tests else "None"

    # =====================================================================
    # STEP 13: Create PR
    # =====================================================================
    cached13 = state.get("step_outputs", {}).get("13")
    if isinstance(cached13, str) and not cached13.startswith("FAILED:"):
        if not quiet:
            console.print(f"[dim][Step 13/13] {STEP_NAMES[13]}: cached[/dim]")
            console.print(f"  → Step 13 complete.")
        step13_output = cached13
    else:
        try:
            set_agentic_progress(
                workflow="change",
                current_step=13,
                total_steps=13,
                step_name=STEP_NAMES[13],
                completed_steps=list(range(1, 13)),
            )
        except Exception:
            pass

        if not quiet:
            console.print(f"[Step 13/13] {STEP_NAMES[13]}...")

        try:
            template13 = load_prompt_template(STEP_TEMPLATE_NAMES[13])
        except Exception:
            template13 = None

        if not template13:
            if not quiet:
                console.print("[red]Failed to load step 13 template[/red]")
            try:
                clear_agentic_progress()
            except Exception:
                pass
            return (
                False,
                "Failed to load step 13 template",
                total_cost,
                model_used,
                changed_files,
            )

        formatted13 = _format_template(template13, context)
        try:
            result13 = run_agentic_task(
                instruction=formatted13,
                cwd=current_work_dir,
                verbose=verbose,
                quiet=quiet,
                timeout=CHANGE_STEP_TIMEOUTS[13] + timeout_adder,
                label="step13",
                max_retries=DEFAULT_MAX_RETRIES,
            )
        except Exception as e:
            if not quiet:
                console.print(f"[red]Step 13 exception: {e}[/red]")
            try:
                clear_agentic_progress()
            except Exception:
                pass
            return (
                False,
                f"Step 13 crashed: {e}",
                total_cost,
                model_used,
                changed_files,
            )

        success13 = False
        step13_output = ""
        cost13 = 0.0
        model13 = model_used
        if isinstance(result13, tuple):
            if len(result13) >= 4:
                success13, step13_output, cost13, model13 = (
                    result13[0],
                    result13[1],
                    result13[2],
                    result13[3],
                )
            elif len(result13) >= 2:
                success13, step13_output = result13[0], result13[1]
        try:
            total_cost += float(cost13 or 0.0)
        except Exception:
            pass
        if model13 and model13 != "unknown":
            model_used = model13
        if not isinstance(step13_output, str):
            step13_output = str(step13_output) if step13_output else ""

        state.setdefault("step_outputs", {})["13"] = (
            step13_output if success13 else f"FAILED: {step13_output}"
        )
        if success13:
            state["last_completed_step"] = 13
        _save_state()

        if success13:
            _post_success_comment(13, step13_output, current_work_dir)

        if not quiet:
            tail = _last_line(step13_output)
            if tail:
                console.print(f"  -> {tail}")
            console.print(f"  → Step 13 complete.")

        if not success13:
            try:
                clear_agentic_progress()
            except Exception:
                pass
            return (
                False,
                f"Step 13 (PR creation) failed",
                total_cost,
                model_used,
                changed_files,
            )

    # =====================================================================
    # FINAL SUMMARY
    # =====================================================================
    # Try to extract PR URL
    pr_url = ""
    pr_match = re.search(
        r"https://github\.com/[\w.-]+/[\w.-]+/pull/\d+", step13_output or ""
    )
    if pr_match:
        pr_url = pr_match.group(0)

    if not quiet:
        console.print()
        console.print(f"[bold green]Change workflow complete[/bold green]")
        console.print(f"  Total cost: ${total_cost:.4f}")
        console.print(f"  Model: {model_used}")
        console.print(f"  Files changed: {len(changed_files)}")
        for f in changed_files:
            console.print(f"    - {f}")
        if pr_url:
            console.print(f"  PR: {pr_url}")
        console.print(f"  Review iterations: {review_iteration}")
        if sync_order_script_path:
            console.print(f"\n[bold]Next steps:[/bold]")
            console.print(f"  Review the PR, then run: bash {sync_order_script_path}")

    # Clear state on success
    try:
        clear_workflow_state(
            cwd=cwd,
            issue_number=issue_number,
            workflow="change",
            state_dir=state_dir,
            repo_owner=repo_owner,
            repo_name=repo_name,
            use_github_state=use_github_state,
        )
    except Exception:
        pass

    try:
        clear_agentic_progress()
    except Exception:
        pass

    final_message = pr_url or "Change workflow completed successfully"
    return (True, final_message, total_cost, model_used, changed_files)
""