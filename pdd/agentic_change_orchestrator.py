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
import threading
import time
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set, Tuple, Any

from rich.console import Console
from rich.markup import escape

from pdd.agentic_common import (
    branch_checked_out_worktree,
    clean_restart_fallback_branch,
    current_worktree_branch,
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
    extract_step_report,
    post_step_comment_once,
    normalize_step_comments_state,
    drain_step_steers,
    issue_update_should_clear_workflow_state,
    apply_clarification_steers_on_resume,
    ensure_issue_steer_cursor_seeded,
)
from pdd.load_prompt_template import load_prompt_template
from pdd.sync_order import (
    build_dependency_graph,
    topological_sort,
    get_affected_modules,
    generate_sync_order_script,
    extract_module_from_include,
    discover_associated_documents,
)
from pdd.construct_paths import _find_pddrc_file, _load_pddrc_config, _detect_context
from pdd.get_extension import get_extension
from pdd.preprocess import preprocess
from pdd.architecture_registry import extract_modules
from pdd.architecture_sync import _merge_interface_signatures, register_untracked_prompts
from pdd.pre_checkup_gate import run_pre_checkup_gate
from pdd.user_story_tests import (
    generate_user_story,
    run_user_story_tests,
    discover_story_files,
    _contract_path_for_story,
    _parse_story_prompt_metadata,
    _read_story,
)

# Initialize console for rich output
console = Console()

PROVIDER_FAILURE_BACKOFF_SECONDS = 30.0

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
    10: 600.0,  # Architecture Update + Associated Document Updates
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


_STEP_ARTIFACT_STEMS = {
    11: "11_review",
    12: "12_fix",
}

_DECISION_JSON_STEPS = {1, 2, 4, 6, 7, 9, 10, 11, 12, 13}
_JSON_RETRY_UNSAFE_STEPS = {9, 10, 12, 13}
_PROVIDER_RETRY_UNSAFE_STEPS = {9, 10, 12, 13}


def _step_artifact_stem(step_num: int, name: str) -> str:
    """Return the authoritative JSON/Markdown artifact stem for a step."""
    return _STEP_ARTIFACT_STEMS.get(step_num, f"{step_num:02d}_{name}")


def _decision_json_filename(step_num: int, name: str) -> Optional[str]:
    if step_num not in _DECISION_JSON_STEPS:
        return None
    return f"{_step_artifact_stem(step_num, name)}.json"


def _allow_json_repair_rerun(step_num: int) -> bool:
    """Return whether a missing JSON artifact can be repaired by rerunning."""
    return step_num not in _JSON_RETRY_UNSAFE_STEPS


def _single_provider_attempt_for_step(step_num: int) -> bool:
    """Return whether provider retries are unsafe for this step."""
    return step_num in _PROVIDER_RETRY_UNSAFE_STEPS


def _artifacts_dir_path(work_dir: Path, issue_number: int) -> Path:
    return Path(work_dir) / ".pdd" / "change" / f"issue-{issue_number}"


def _artifacts_dir_for(work_dir: Path, issue_number: int) -> Path:
    """Return and create the per-issue structured artifact directory."""
    artifacts_dir = _artifacts_dir_path(work_dir, issue_number)
    artifacts_dir.mkdir(parents=True, exist_ok=True)
    return artifacts_dir


def _reset_artifacts_dir(work_dir: Path, issue_number: int) -> None:
    """Remove stale structured artifacts for a fresh non-resume run."""
    shutil.rmtree(_artifacts_dir_path(work_dir, issue_number), ignore_errors=True)


def _clear_step_artifacts(artifacts_dir: Path, step_num: int, name: str) -> None:
    """Remove artifacts a step attempt is expected to rewrite."""
    stem = _step_artifact_stem(step_num, name)
    for suffix in (".json", ".md"):
        try:
            (Path(artifacts_dir) / f"{stem}{suffix}").unlink()
        except FileNotFoundError:
            pass
        except OSError:
            pass


def _read_step_json(artifacts_dir: Path, filename: str) -> Optional[dict]:
    """Return parsed step JSON, or None on missing/unreadable/unparseable."""
    try:
        data = json.loads((Path(artifacts_dir) / filename).read_text(encoding="utf-8"))
    except Exception:
        return None
    return data if isinstance(data, dict) else None


def _read_step_md(artifacts_dir: Path, filename: str) -> Optional[str]:
    """Return stripped step Markdown, or None on missing/unreadable/empty."""
    try:
        text = (Path(artifacts_dir) / filename).read_text(encoding="utf-8").strip()
    except Exception:
        return None
    return text or None


def _json_list(data: Optional[dict], key: str) -> List[str]:
    value = data.get(key) if isinstance(data, dict) else None
    if not isinstance(value, list):
        return []
    result: List[str] = []
    for item in value:
        if isinstance(item, str):
            item = item.strip()
            if item:
                result.append(item)
    return result


def _dedupe_preserve_order(items: Sequence[str]) -> List[str]:
    seen: Set[str] = set()
    ordered: List[str] = []
    for item in items:
        if item and item not in seen:
            seen.add(item)
            ordered.append(item)
    return ordered


def _manual_review_lines_from_json(data: Optional[dict]) -> str:
    entries = data.get("manual_review") if isinstance(data, dict) else None
    if not isinstance(entries, list):
        return ""
    lines: List[str] = []
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        path = str(entry.get("path") or "").strip()
        reason = str(entry.get("reason") or "").strip()
        if path and reason:
            lines.append(f"MANUAL_REVIEW: {path} — {reason}")
        elif path:
            lines.append(f"MANUAL_REVIEW: {path}")
    return "\n".join(_dedupe_preserve_order(lines))


def _step9_changed_files_from_json(data: dict) -> Tuple[List[str], List[str], List[str], List[str]]:
    """Return (changed, created, modified, direct_edits) from Step 9 JSON."""
    modified = _json_list(data, "files_modified")
    created = _json_list(data, "files_created")
    direct_edits = _json_list(data, "direct_edits")
    changed = _dedupe_preserve_order([*modified, *created, *direct_edits])
    return changed, created, modified, direct_edits


def _step10_changed_files_from_json(data: dict) -> List[str]:
    return _dedupe_preserve_order(
        [
            *_json_list(data, "architecture_files_modified"),
            *_json_list(data, "associated_docs_modified"),
        ]
    )


def _hard_stop_from_json_with_presence(
    step_num: int, artifacts_dir: Path, name: str
) -> Tuple[bool, Optional[str], List[str]]:
    """Map a hard-stop step JSON status to the legacy stop reason.

    Returns ``(json_present, stop_reason, direct_edit_candidates)`` so callers
    can distinguish a valid ``proceed`` JSON from a missing JSON fallback.
    """
    data = _read_step_json(artifacts_dir, f"{_step_artifact_stem(step_num, name)}.json")
    if not _valid_step_json(step_num, data):
        return False, None, []
    status = str(data.get("status") or "").strip().lower()
    direct_edit_candidates = _json_list(data, "direct_edit_candidates")

    if status == "proceed":
        return True, None, direct_edit_candidates
    if step_num == 1 and status == "duplicate":
        return True, "Issue is a duplicate", direct_edit_candidates
    if step_num == 2 and status == "already_done":
        return True, "Already implemented", direct_edit_candidates
    if step_num == 4:
        if status == "needs_clarification":
            return True, "Clarification needed", direct_edit_candidates
        if status == "route_bug":
            rationale = str(data.get("rationale") or "").strip()
            if rationale:
                return True, f"Runtime bug route needed: {rationale}", direct_edit_candidates
            return True, "Runtime bug route needed: use pdd bug followed by pdd fix", direct_edit_candidates
    if step_num == 6 and status == "no_dev_units":
        return True, "No dev units found", direct_edit_candidates
    if step_num == 7 and status == "needs_decision":
        return True, "Architectural decision needed", direct_edit_candidates
    return True, None, direct_edit_candidates


def _hard_stop_from_json(step_num: int, artifacts_dir: Path, name: str) -> Optional[str]:
    return _hard_stop_from_json_with_presence(step_num, artifacts_dir, name)[1]


def _step13_result_from_json_or_output(
    data: Optional[dict], output: str
) -> Tuple[str, str]:
    """Return (status, pr_url), preferring Step 13 JSON over prose regex."""
    if isinstance(data, dict):
        status = str(data.get("status") or "").strip() or "unknown"
        if status == "blocked":
            return status, "Unknown"
        pr_url = str(data.get("pr_url") or "").strip()
        if pr_url:
            return status, pr_url
    url_match = re.search(r"https://github.com/\S+/pull/\d+", output or "")
    return "unknown", url_match.group(0) if url_match else "Unknown"


def _valid_pr_url(value: Any, repo_owner: str = "", repo_name: str = "") -> bool:
    url = str(value or "").strip()
    if repo_owner and repo_name:
        return bool(
            re.fullmatch(
                rf"https://github\.com/{re.escape(repo_owner)}/{re.escape(repo_name)}/pull/\d+",
                url,
                flags=re.IGNORECASE,
            )
        )
    return bool(
        re.fullmatch(
            r"https://github\.com/[^/\s]+/[^/\s]+/pull/\d+",
            url,
        )
    )


def _git_head_oid(cwd: Path) -> Optional[str]:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )
    except (subprocess.TimeoutExpired, OSError):
        return None
    if result.returncode != 0:
        return None
    oid = result.stdout.strip()
    return oid if re.fullmatch(r"[0-9a-fA-F]{40}", oid) else None


def _remote_branch_oid(head_branch: str, cwd: Path) -> Optional[str]:
    try:
        result = subprocess.run(
            ["git", "ls-remote", "origin", f"refs/heads/{head_branch}"],
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )
    except (subprocess.TimeoutExpired, OSError):
        return None
    if result.returncode != 0:
        return None
    first = result.stdout.strip().split(None, 1)[0] if result.stdout.strip() else ""
    return first if re.fullmatch(r"[0-9a-fA-F]{40}", first) else None


def _pr_number_from_url(pr_url: str, repo_owner: str, repo_name: str) -> Optional[str]:
    match = re.fullmatch(
        rf"https://github\.com/{re.escape(repo_owner)}/{re.escape(repo_name)}/pull/(\d+)",
        str(pr_url or "").strip(),
        flags=re.IGNORECASE,
    )
    return match.group(1) if match else None


def _gh_pr_list_candidates(
    base_args: Sequence[str], cwd: Optional[Path] = None
) -> List[dict]:
    """Return PR list entries from a supported bounded gh query."""
    try:
        result = subprocess.run(
            [*base_args, "--limit", "1000"],
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )
        if result.returncode != 0:
            return []
        data = json.loads(result.stdout)
    except (subprocess.TimeoutExpired, json.JSONDecodeError, OSError):
        return []
    if not isinstance(data, list):
        return []
    return [item for item in data if isinstance(item, dict)]


def _pr_url_matches_current_head(
    repo_owner: str,
    repo_name: str,
    pr_url: str,
    head_branch: str,
    base_branch: str,
    cwd: Path,
) -> bool:
    """Return true only when the PR URL points at this branch and local HEAD."""
    pr_number = _pr_number_from_url(pr_url, repo_owner, repo_name)
    if not pr_number:
        return False
    local_oid = _git_head_oid(cwd)
    remote_oid = _remote_branch_oid(head_branch, cwd)
    if not local_oid or not remote_oid or local_oid.lower() != remote_oid.lower():
        return False
    try:
        result = subprocess.run(
            [
                "gh",
                "pr",
                "view",
                pr_number,
                "--repo",
                f"{repo_owner}/{repo_name}",
                "--json",
                "url,headRefName,headRefOid,baseRefName,state",
            ],
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )
        if result.returncode != 0:
            return False
        data = json.loads(result.stdout)
    except (subprocess.TimeoutExpired, json.JSONDecodeError, OSError):
        return False
    if not isinstance(data, dict):
        return False
    if str(data.get("url") or "").strip().rstrip("/") != str(pr_url).strip().rstrip("/"):
        return False
    if str(data.get("headRefName") or "").strip() != head_branch:
        return False
    if str(data.get("baseRefName") or "").strip() != base_branch:
        return False
    if str(data.get("state") or "").strip().upper() != "OPEN":
        return False
    pr_oid = str(data.get("headRefOid") or "").strip()
    return bool(pr_oid) and pr_oid.lower() == local_oid.lower()


def _open_pr_for_head_branch(
    repo_owner: str,
    repo_name: str,
    head_branch: str,
    base_branch: str,
    cwd: Path,
) -> Optional[dict]:
    """Return open PR metadata for the exact head branch, if one exists."""
    data = _gh_pr_list_candidates(
        [
            "gh",
            "pr",
            "list",
            "--repo",
            f"{repo_owner}/{repo_name}",
            "--head",
            head_branch,
            "--state",
            "open",
            "--json",
            "number,url,headRefName,headRefOid,baseRefName,state",
        ],
        cwd=cwd,
    )
    if not data:
        return None
    local_oid = _git_head_oid(cwd)
    remote_oid = _remote_branch_oid(head_branch, cwd)
    if not local_oid or not remote_oid or remote_oid.lower() != local_oid.lower():
        return None
    for pr in data:
        if not isinstance(pr, dict) or not _valid_pr_url(
            pr.get("url"), repo_owner, repo_name
        ):
            continue
        pr_oid = str(pr.get("headRefOid") or "").strip()
        if str(pr.get("state") or "").strip().upper() != "OPEN":
            continue
        if str(pr.get("headRefName") or "").strip() != head_branch:
            continue
        if str(pr.get("baseRefName") or "").strip() != base_branch:
            continue
        if pr_oid and pr_oid.lower() == local_oid.lower():
            return pr
    return None


def _valid_step_json(step_num: int, data: Optional[dict]) -> bool:
    if not isinstance(data, dict):
        return False
    path_list_fields_by_step = {
        1: ("duplicates",),
        4: ("questions",),
        6: ("direct_edit_candidates",),
        7: ("questions",),
        9: ("files_modified", "files_created", "direct_edits"),
        10: (
            "architecture_files_modified",
            "associated_docs_modified",
            "associated_docs_conflicts",
            "associated_docs_unchanged",
        ),
    }
    for key in path_list_fields_by_step.get(step_num, ()):
        if key not in data:
            continue
        value = data.get(key)
        if not isinstance(value, list):
            return False
        if any(not isinstance(item, str) or not item.strip() for item in value):
            return False
    if step_num in {9, 11, 12} and "manual_review" in data:
        manual_review = data.get("manual_review")
        if not isinstance(manual_review, list):
            return False
        for item in manual_review:
            if not isinstance(item, dict):
                return False
            path = item.get("path")
            reason = item.get("reason", "")
            if not isinstance(path, str) or not path.strip():
                return False
            if reason is not None and not isinstance(reason, str):
                return False
    required_fields_by_step = {
        1: ("duplicates",),
        4: ("questions",),
        6: ("direct_edit_candidates",),
        9: ("files_modified", "files_created", "direct_edits", "manual_review"),
        10: (
            "architecture_files_modified",
            "associated_docs_modified",
            "associated_docs_conflicts",
            "associated_docs_unchanged",
        ),
        11: ("manual_review",),
        12: ("manual_review",),
    }
    for key in required_fields_by_step.get(step_num, ()):
        if key not in data:
            return False
    status_sets = {
        1: {"proceed", "duplicate"},
        2: {"proceed", "already_done"},
        4: {"proceed", "needs_clarification", "route_bug"},
        6: {"proceed", "no_dev_units"},
        7: {"proceed", "needs_decision"},
        9: {"changed", "no_change_needed", "failed"},
        11: {"clean", "issues_found"},
        12: {"fixed_issues", "partial"},
        13: {"pr_created", "pr_updated", "blocked"},
    }
    allowed_statuses = status_sets.get(step_num)
    if allowed_statuses is not None:
        status = str(data.get("status") or "").strip()
        if status not in allowed_statuses:
            return False
        if step_num == 13 and status in {"pr_created", "pr_updated"}:
            return _valid_pr_url(data.get("pr_url"))
        return True
    return True


def _comment_body_from_artifact(
    artifacts_dir: Path,
    stem: str,
    output: str,
    fallback: str,
) -> str:
    return _read_step_md(artifacts_dir, f"{stem}.md") or extract_step_report(output) or fallback


def _sanitize_architecture_dependencies(worktree_path: Path) -> None:
    """Remove corrupted dependency values from architecture.json after step 10."""
    arch_path = worktree_path / "architecture.json"
    if not arch_path.exists():
        return
    try:
        with open(arch_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        modules = extract_modules(data)
        changed = False
        for entry in modules:
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
            # Preserve on-disk format: if original was dict-format, write back as dict
            if isinstance(data, dict) and isinstance(data.get("modules"), list):
                data["modules"] = modules
            else:
                data = modules
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
            raw_arch = json.load(f)
    except (json.JSONDecodeError, OSError):
        return

    current_modules = extract_modules(raw_arch)

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
    for entry in current_modules:
        filename = entry.get("filename", "")
        filepath = entry.get("filepath", "")

        entry_in_scope = filename in in_scope_filenames

        if entry_in_scope:
            scoped.append(entry)
        else:
            prev_entry = prev_by_filename.get(filename)
            if prev_entry is None and filepath:
                prev_entry = prev_by_filepath.get(filepath)
            if prev_entry is not None:
                scoped.append(prev_entry)

    try:
        if isinstance(raw_arch, dict) and isinstance(raw_arch.get("modules"), list):
            raw_arch["modules"] = scoped
            write_data = raw_arch
        else:
            write_data = scoped
        with open(arch_path, "w", encoding="utf-8") as f:
            json.dump(write_data, f, indent=2)
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
            raw_arch = json.load(f)
    except (json.JSONDecodeError, OSError):
        return []

    modules = extract_modules(raw_arch)
    warnings: List[str] = []
    changed = False

    for entry in modules:
        filepath = entry.get("filepath")
        if not filepath:
            continue

        full_path = worktree_path / filepath
        if full_path.exists():
            continue

        filename = entry.get("filename", "")
        conventional_path = None
        if filename.endswith(".prompt"):
            stem = filename[:-len(".prompt")]
            parts = stem.rsplit("_", 1)
            if len(parts) == 2:
                module_name, lang_suffix = parts
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
            if isinstance(raw_arch, dict) and isinstance(raw_arch.get("modules"), list):
                raw_arch["modules"] = modules
                write_data = raw_arch
            else:
                write_data = modules
            with open(arch_path, "w", encoding="utf-8") as f:
                json.dump(write_data, f, indent=2)
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
            raw_arch = json.load(f)
    except (json.JSONDecodeError, OSError):
        return []

    current_modules = extract_modules(raw_arch)

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

    for entry in current_modules:
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
            if isinstance(raw_arch, dict) and isinstance(raw_arch.get("modules"), list):
                raw_arch["modules"] = current_modules
                write_data = raw_arch
            else:
                write_data = current_modules
            with open(arch_path, "w", encoding="utf-8") as f:
                json.dump(write_data, f, indent=2)
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


def _resolve_main_ref_name(git_root: Path) -> str:
    """Return the human-readable ref name (e.g. 'origin/main') that resolved.

    Same probe order as _resolve_main_ref, but returns the name of the ref
    instead of its commit SHA — useful for display purposes such as the
    Step 0 startup comment where a SHA is opaque to the reader.
    """
    for ref in ("origin/main", "origin/master", "main", "master"):
        result = subprocess.run(
            ["git", "rev-parse", "--verify", ref],
            cwd=git_root, capture_output=True, text=True,
        )
        if result.returncode == 0:
            return ref
    return "HEAD"


def _normalize_pr_base_branch(ref_name: str) -> str:
    """Convert a resolved git ref name into a GitHub PR base branch name."""
    if ref_name.startswith("origin/"):
        return ref_name.split("/", 1)[1]
    if ref_name and ref_name != "HEAD":
        return ref_name
    return "main"


def _setup_worktree(
    cwd: Path,
    issue_number: int,
    quiet: bool,
    *,
    clean_restart: bool = False,
) -> Tuple[Optional[Path], Optional[str]]:
    """
    Create an isolated git worktree for the issue.

    Default behavior preserves cross-machine resume by reusing
    ``origin/change/issue-{N}`` as the base when that branch already
    exists remotely (so the second machine inherits the first machine's
    prior work). Under ``clean_restart=True`` (issue #1149) the helper
    MUST instead force the base to ``_resolve_main_ref(git_root)`` and
    skip remote-reuse entirely, while still fetching the old branch for
    Step 13 ``--force-with-lease`` safety, so a stopped or wrong-model
    run's artifacts on the existing remote branch cannot leak into the
    fresh restart.

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

    # Under clean_restart we must NOT inherit the prior remote branch's
    # commits as our base. Still fetch the remote branch when present so
    # Step 13's `git push --force-with-lease` has lease information, but
    # keep `remote_exists` false so the create-from-main path runs.
    remote_ref = f"origin/{branch_name}"
    remote_exists = False
    try:
        lease_refspec = f"+refs/heads/{branch_name}:refs/remotes/origin/{branch_name}"
        subprocess.run(
            ["git", "fetch", "origin", lease_refspec],
            cwd=git_root, capture_output=True, check=True
        )
        if not clean_restart:
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
    fallback_branch: Optional[str] = None
    branch_exists = _branch_exists(cwd, branch_name)
    if branch_exists:
        success, _err = _delete_branch(cwd, branch_name)
        if success:
            branch_exists = False
        elif clean_restart:
            # Under clean_restart we cannot fall through to the
            # "reuse existing local branch" path below — that would
            # base the fresh restart on whatever the previous run
            # left on the local change/issue-{N} branch, violating
            # the Req 15 base-ref guarantee.
            #
            # The common cause is a stale worktree registration: prune
            # and retry the delete first (resolves it without a fallback).
            subprocess.run(
                ["git", "worktree", "prune"],
                cwd=git_root, capture_output=True,
            )
            success, _err = _delete_branch(cwd, branch_name)
            if success:
                branch_exists = False
            else:
                # Still locked. Only fall back when the branch is genuinely
                # checked out in ANOTHER live worktree (issue #1596: the
                # GitHub App executor's). Use a fresh unique fallback branch
                # off origin/main so the locked worktree is left untouched.
                holder = branch_checked_out_worktree(git_root, branch_name)
                if holder and Path(holder).resolve() != worktree_path.resolve():
                    fallback_branch = clean_restart_fallback_branch(branch_name)
                    # The fallback name is stable across retries of the same
                    # job (JOB_ID-derived), so a prior attempt may have left
                    # this branch behind after its worktree was removed. Delete
                    # it (best effort) so we recreate it fresh from main rather
                    # than failing `git worktree add -b` on a name clash.
                    _delete_branch(cwd, fallback_branch)
                    # Fetch the FALLBACK branch's own tracking ref (not the
                    # canonical one) so Step 13's `git push --force-with-lease
                    # origin {head_branch}` has lease info. On a same-job retry
                    # in a fresh clone, origin/{fallback} already exists but the
                    # local tracking ref does not — without this fetch the push
                    # is rejected with "stale info". Best effort.
                    fallback_lease = (
                        f"+refs/heads/{fallback_branch}:refs/remotes/origin/{fallback_branch}"
                    )
                    try:
                        subprocess.run(
                            ["git", "fetch", "origin", fallback_lease],
                            cwd=git_root, capture_output=True, check=True
                        )
                    except subprocess.CalledProcessError:
                        pass
                    branch_exists = False
                    if not quiet:
                        console.print(
                            f"[bold cyan]Clean restart: branch {branch_name!r} is locked by "
                            f"worktree {holder} — creating fresh fallback branch "
                            f"{fallback_branch!r} from main instead.[/bold cyan]"
                        )
                else:
                    return None, (
                        f"Cannot perform clean restart: local branch {branch_name!r} "
                        "could not be deleted (it is likely checked out in another "
                        "worktree). Remove that worktree first, then retry."
                    )

    # Resolve base ref once. Under clean_restart, refuse to silently
    # use the literal "HEAD" fallback (the user's CURRENT branch) —
    # that would be exactly the "never the current HEAD" violation
    # Requirement 15 calls out. Fail loudly instead.
    base_ref = _resolve_main_ref(git_root)
    if clean_restart and base_ref == "HEAD":
        return None, (
            "Cannot perform clean restart: no main/master ref resolves "
            "(checked origin/main, origin/master, main, master). Refusing "
            "to base the fresh worktree on the current HEAD, which would "
            "drag the user's working branch into the restart."
        )

    # Create worktree — reuse remote branch if it has prior work (normal
    # resume path). Under clean_restart, remote_exists is forced False
    # above so this falls through to the create-from-main branch.
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
            # No prior work — create new branch from main. Under a #1596
            # fallback the canonical branch is locked by another worktree, so
            # create the unique fallback branch instead.
            create_branch = fallback_branch or branch_name
            subprocess.run(
                ["git", "worktree", "add", "-b", create_branch, str(worktree_path), base_ref],
                cwd=git_root, capture_output=True, check=True
            )
            if clean_restart and not quiet:
                console.print(
                    f"[bold cyan]Clean restart: created worktree from {base_ref!s} "
                    f"(ignoring any existing {remote_ref}).[/bold cyan]"
                )
        if not quiet:
            console.print(f"[blue]Working in worktree: {worktree_path}[/blue]")
        return worktree_path, None
    except subprocess.CalledProcessError as e:
        return None, f"Git worktree creation failed: {e}"

_PARSE_CHANGED_FILES_TERMINATORS = (
    "FILES_CREATED",
    "FILES_MODIFIED",
    "ARCHITECTURE_FILES_MODIFIED",
    "ASSOCIATED_DOCS_MODIFIED",
    "ASSOCIATED_DOCS_CONFLICTS",
    "ASSOCIATED_DOCS_UNCHANGED",
    "DIRECT_EDITS",
    "MANUAL_REVIEW",
    "ORCHESTRATOR_POSTCHECK_WARNINGS",
    "DOC_SYNC_SILENT_DROPS",
    "DOC_SYNC_BUCKET_OVERLAPS",
    "STOP_CONDITION",
)


def _collect_manual_review_lines(*sources: str) -> str:
    """Collect ``MANUAL_REVIEW: ...`` lines from one or more text sources,
    de-duped while preserving first-seen order. Returns ``"None"`` when no
    flags are present so the Step 13 template renders a stable placeholder.
    """
    seen: Set[str] = set()
    ordered: List[str] = []
    for src in sources:
        if not src:
            continue
        for line in src.splitlines():
            stripped = line.strip()
            while stripped and stripped[0] in "-*•":
                stripped = stripped[1:].lstrip()
            if stripped.upper().startswith("MANUAL_REVIEW:") and stripped not in seen:
                seen.add(stripped)
                ordered.append(stripped)
    return "\n".join(ordered) if ordered else "None"


def _find_marker_start(line: str, prefix: str) -> Optional[int]:
    """Return the index just after ``prefix:`` in ``line`` if it appears at a
    word boundary, else None. Word boundary means the character before
    ``prefix`` is not alphanumeric/underscore — this prevents ``MY_FILES_MODIFIED:``
    from matching ``FILES_MODIFIED:``.
    """
    idx = line.find(prefix)
    while idx != -1:
        if idx == 0 or not (line[idx - 1].isalnum() or line[idx - 1] == "_"):
            return idx + len(prefix)
        idx = line.find(prefix, idx + 1)
    return None


def _truncate_at_inline_terminator(
    text: str, terminators: Sequence[str], skip_prefix: str
) -> str:
    """Trim ``text`` at the first inline occurrence of any terminator marker,
    skipping ``skip_prefix`` (the marker we're currently inside, so a repeat
    of our own marker still terminates but our entry-point doesn't).
    """
    earliest: Optional[int] = None
    for term in terminators:
        term_prefix = f"{term}:"
        end_after = _find_marker_start(text, term_prefix)
        if end_after is None:
            continue
        # _find_marker_start returns the index AFTER the colon; the marker
        # itself starts at end_after - len(term_prefix).
        marker_start = end_after - len(term_prefix)
        if earliest is None or marker_start < earliest:
            earliest = marker_start
    if earliest is None:
        return text
    return text[:earliest].rstrip()


def _extract_marker_paths(marker: str, output: str) -> List[str]:
    """Walk lines after ``marker:`` until blank or another known marker.

    Multi-line payloads are supported (LLMs wrap long lists across lines).
    The marker is also detected when it appears mid-line (e.g.
    ``Implementation done. FILES_MODIFIED: a.py, b.py``); in that case the
    section starts at the marker and ends at the line break, matching the
    behavior of the prior single-line regex parser.
    """
    prefix = f"{marker}:"
    other_terminators = tuple(
        t for t in _PARSE_CHANGED_FILES_TERMINATORS if t != marker
    )
    lines = output.splitlines()
    payload_lines: List[str] = []
    in_section = False
    for line in lines:
        lstrip = line.lstrip()
        if not in_section:
            start_idx = _find_marker_start(line, prefix)
            if start_idx is None:
                continue
            in_section = True
            # When the marker started inline (mid-line), the remainder of
            # the line may also contain another marker (e.g.
            # ``Done. FILES_MODIFIED: a.py DIRECT_EDITS: b.md``). Truncate
            # at the next inline terminator so we don't swallow the next
            # section's tag/value as a path.
            first = _truncate_at_inline_terminator(
                line[start_idx:], other_terminators, prefix
            ).strip()
            if first:
                payload_lines.append(first)
            continue
        stripped = line.strip()
        if not stripped:
            break
        # Preserve any prefix text before an inline terminator on a
        # continuation line. ``b.py ARCHITECTURE_FILES_MODIFIED: arch.json``
        # contributes ``b.py`` to FILES_MODIFIED's payload, then ends the
        # section — losing ``b.py`` would silently drop a real file from
        # downstream Step 10 doc discovery.
        truncated = _truncate_at_inline_terminator(
            line, other_terminators, prefix
        )
        if truncated != line:
            if truncated.strip():
                payload_lines.append(truncated)
            break
        payload_lines.append(line)

    entries: List[str] = []
    for raw_line in payload_lines:
        s = raw_line.strip()
        # Strip leading bullets per line so "- README.md" yields "README.md".
        while s and s[0] in "-*•":
            s = s[1:].lstrip()
        for part in s.split(","):
            piece = part.strip()
            # Re-strip bullets per entry so a single inline list like
            # ``- a.md, - b.md, • c.md`` normalizes each comma-piece.
            while piece and piece[0] in "-*•":
                piece = piece[1:].lstrip()
            # Strip surrounding markdown emphasis / code ticks so
            # ``**README.md**`` and ```README.md``` both normalize cleanly.
            piece = piece.strip("*`").strip()
            if piece:
                entries.append(piece)
    return entries


def _parse_changed_files(output: str) -> List[str]:
    """Extract file paths from FILES_CREATED, FILES_MODIFIED, or DIRECT_EDITS lines.

    Multi-line marker payloads are supported (the LLM frequently wraps long
    lists across lines). All markers share the same line-walker shape; see
    ``_extract_marker_paths``.
    """
    files: List[str] = []
    files.extend(_extract_marker_paths("FILES_CREATED", output))
    files.extend(_extract_marker_paths("FILES_MODIFIED", output))
    files.extend(_extract_marker_paths("ARCHITECTURE_FILES_MODIFIED", output))
    files.extend(_extract_marker_paths("ASSOCIATED_DOCS_MODIFIED", output))

    # Log ASSOCIATED_DOCS_CONFLICTS as warnings (docs that need manual review).
    conflict_list = _extract_marker_paths("ASSOCIATED_DOCS_CONFLICTS", output)
    if conflict_list:
        console.print(
            f"[yellow]Associated docs flagged for manual review: {', '.join(conflict_list)}[/yellow]"
        )

    files.extend(_extract_marker_paths("DIRECT_EDITS", output))

    return list(set(files))  # Deduplicate


def _prompt_paths_from_changed_file_entries(
    entries: Sequence[str],
    worktree_path: Path,
) -> Set[Path]:
    """Return changed prompt paths resolved against the workflow worktree.

    Step 9 has two successful reporting paths: explicit ``FILES_*`` markers
    and the worktree fallback. Step 10 associated-document discovery must use
    the authoritative changed-file set from both paths, not only the marker
    payloads.
    """
    prompt_paths: Set[Path] = set()
    for raw in entries:
        for part in str(raw).split(","):
            fp = part.strip().strip("*`").strip()
            if not fp:
                continue
            normalized = fp.replace("\\", "/")
            if not normalized.endswith(".prompt"):
                continue
            path = Path(normalized)
            prompt_paths.add(path if path.is_absolute() else worktree_path / path)
    return prompt_paths


def _story_prompt_files_for_change(
    changed_files: Sequence[str],
    worktree_path: Path,
) -> List[Path]:
    """Return existing non-runtime prompt files changed by this workflow."""
    prompt_paths: List[Path] = []
    seen: Set[str] = set()
    for prompt_path in _prompt_paths_from_changed_file_entries(changed_files, worktree_path):
        if prompt_path.name.lower().endswith("_llm.prompt"):
            continue
        if not prompt_path.exists() or not prompt_path.is_file():
            continue
        key = str(prompt_path.resolve()).lower()
        if key in seen:
            continue
        prompt_paths.append(prompt_path)
        seen.add(key)
    return sorted(prompt_paths, key=lambda p: str(p).lower())


def _common_prompt_root(prompt_files: Sequence[Path], worktree_path: Path) -> Optional[Path]:
    """Return a shared prompts directory for metadata, when one is clear."""
    roots: Set[Path] = set()
    for prompt_file in prompt_files:
        resolved = prompt_file.resolve()
        parts = resolved.parts
        prompt_indexes = [i for i, part in enumerate(parts) if part == "prompts"]
        if not prompt_indexes:
            continue
        index = prompt_indexes[-1]
        roots.add(Path(*parts[: index + 1]))
    if len(roots) == 1:
        return next(iter(roots))
    default_root = worktree_path / "prompts"
    if default_root.exists():
        return default_root
    return None


def _format_rel(path: Path, root: Path) -> str:
    """Format a path relative to root when possible."""
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return path.as_posix()


_VALID_STORY_POLICIES = ("off", "warn", "strict")
_DEFAULT_STORY_POLICY = "warn"


def _resolve_story_policy() -> str:
    """Resolve the agentic-change user-story policy: ``off | warn | strict``.

    Controlled by ``PDD_STORY_POLICY`` (issue #1454). The prompt-story workflow
    must be opt-in-safe before any default strict enforcement, so unknown/empty
    values fall back to the safe default (``warn``): create/reuse + link +
    validate and REPORT coverage, but never block the change PR. ``off`` skips
    creation and checking entirely; ``strict`` blocks the PR when a changed
    prompt still has no passing linked story.
    """
    raw = (os.environ.get("PDD_STORY_POLICY") or "").strip().lower()
    if raw in _VALID_STORY_POLICIES:
        return raw
    return _DEFAULT_STORY_POLICY


def _find_linked_stories_for_prompts(
    prompt_files: Sequence[Path],
    stories_dir: Path,
) -> Tuple[Dict[Path, List[Path]], List[Path]]:
    """Map each changed prompt to existing stories that already link it.

    A story "covers" a changed prompt when its ``pdd-story-prompts`` metadata
    references that prompt (matched by filename). Returns
    ``(prompt_to_stories, uncovered_prompts)`` so the caller can reuse existing
    coverage and only GENERATE a new story for prompts that have none — avoiding
    the duplicate ``story__<slug>_1.md`` coverage #1454 calls out.
    """
    prompt_to_stories: Dict[Path, List[Path]] = {p: [] for p in prompt_files}
    changed_by_name: Dict[str, Path] = {p.name.lower(): p for p in prompt_files}
    for story_path in discover_story_files(str(stories_dir)):
        try:
            refs = _parse_story_prompt_metadata(_read_story(story_path))
        except OSError:
            continue
        for ref in refs:
            matched = changed_by_name.get(Path(ref.strip()).name.lower())
            if matched is not None and story_path not in prompt_to_stories[matched]:
                prompt_to_stories[matched].append(story_path)
    uncovered = [p for p in prompt_files if not prompt_to_stories[p]]
    return prompt_to_stories, uncovered


def _generate_user_story_artifacts_for_change(
    *,
    issue_url: str,
    changed_files: Sequence[str],
    worktree_path: Path,
    strength: float,
    temperature: float,
    time_budget: float,
    verbose: bool,
    quiet: bool,
) -> Tuple[List[str], str, float, str, Optional[str]]:
    """Create/reuse, link, and validate story coverage before Step 13 makes the PR.

    Returns ``(story_files_to_stage, pr_summary, cost, model, block_message)``
    (issue #1454). The summary is rendered into the PR body so reviewers can see
    which coverage was reused/created and whether the linked stories pass.
    ``block_message`` is non-None only under ``strict`` policy when a changed
    prompt still has no passing linked story; the caller hard-blocks on it.
    """
    policy = _resolve_story_policy()
    if policy == "off":
        # `off` skips creation and checking entirely (#1454).
        return (
            [],
            "### User Stories\n- Skipped: story policy is `off` (`PDD_STORY_POLICY=off`).",
            0.0,
            "",
            None,
        )

    prompt_files = _story_prompt_files_for_change(changed_files, worktree_path)
    if not prompt_files:
        return [], "None", 0.0, "", None

    stories_dir = worktree_path / "user_stories"
    prompts_dir = _common_prompt_root(prompt_files, worktree_path)

    total_cost = 0.0
    model_used = ""
    files_to_stage: List[str] = []
    summary_lines: List[str] = ["### User Stories", f"- Policy: `{policy}`"]
    # Stories whose linked coverage we will validate (reused + newly generated).
    linked_story_paths: List[Path] = []

    # 1) Reuse existing linked stories; only generate for the rest (#1454).
    prompt_to_stories, uncovered = _find_linked_stories_for_prompts(
        prompt_files, stories_dir
    )
    reused = sorted(
        {s for stories in prompt_to_stories.values() for s in stories},
        key=lambda p: str(p).lower(),
    )
    for story_path in reused:
        linked_story_paths.append(story_path)
        rel = _format_rel(story_path, worktree_path)
        summary_lines.append(f"- `{rel}` — reused existing linked story")
        if not quiet:
            console.print(f"[green]Reusing existing user story:[/green] {rel}")

    # 2) Generate one issue-derived story for the prompts with no coverage yet.
    still_uncovered: List[Path] = list(uncovered)
    if uncovered:
        uncovered_refs = [_format_rel(p, prompts_dir or worktree_path) for p in uncovered]
        try:
            success, message, cost, model, story_file, linked_prompts = generate_user_story(
                prompt_files=[str(p) for p in uncovered],
                issue=issue_url,
                stories_dir=str(stories_dir),
                prompts_dir=str(prompts_dir) if prompts_dir else None,
                strength=strength,
                temperature=temperature,
                time=time_budget,
                verbose=verbose,
            )
        except Exception as exc:  # pylint: disable=broad-except
            # Story generation is best-effort: a failure in issue resolution,
            # provider code, or file I/O must never abort the change workflow
            # after the pre-PR gate. Degrade to a PR-body warning instead.
            success, message, cost, model = False, str(exc), 0.0, ""
            linked_prompts = []
        total_cost += cost
        model_used = model_used or model
        if success:
            story_path = Path(story_file)
            still_uncovered = []
            linked_story_paths.append(story_path)
            story_rel = _format_rel(story_path, worktree_path)
            files_to_stage.append(story_rel)
            linked = linked_prompts or uncovered_refs
            line = (
                f"- `{story_rel}` — issue-derived story linked to: "
                f"{', '.join(f'`{p}`' for p in linked)}"
            )
            # The two-file model writes a sibling AI contract under contracts/;
            # stage it too so the contract travels with the change PR rather than
            # landing as an untracked local file.
            contract_path = _contract_path_for_story(story_path)
            if contract_path.exists():
                contract_rel = _format_rel(contract_path, worktree_path)
                files_to_stage.append(contract_rel)
                line += f"\n- `{contract_rel}` — generated machine-checkable contract"
            summary_lines.append(line)
            if not quiet:
                console.print(f"[green]Generated user story:[/green] {story_rel}")
        else:
            summary_lines.append(
                f"- Story generation skipped for `{', '.join(uncovered_refs)}`: {message}"
            )
            if not quiet:
                console.print(f"[yellow]User story generation skipped: {message}[/yellow]")

    # 3) Validate ONLY the linked story/prompt subset and report (#1454).
    failing_stories: List[str] = []
    validation_error: Optional[str] = None
    if linked_story_paths:
        try:
            passed, results, vcost, vmodel = run_user_story_tests(
                stories_dir=str(stories_dir),
                prompts_dir=str(prompts_dir) if prompts_dir else None,
                story_files=sorted(set(linked_story_paths), key=lambda p: str(p).lower()),
                strength=strength,
                temperature=temperature,
                time=time_budget,
                verbose=verbose,
                quiet=quiet,
            )
            total_cost += vcost
            model_used = model_used or vmodel
            failing_stories = [
                _format_rel(Path(str(r.get("story"))), worktree_path)
                for r in results
                if not r.get("passed")
            ]
            if passed:
                summary_lines.append(
                    f"- Validation: ✅ all {len(results)} linked story check(s) passed"
                )
            else:
                summary_lines.append(
                    f"- Validation: ❌ {len(failing_stories)} of {len(results)} "
                    f"linked story check(s) failed: {', '.join(f'`{s}`' for s in failing_stories)}"
                )
        except Exception as exc:  # pylint: disable=broad-except
            # Validation is best-effort under warn; never abort the workflow.
            # Under strict, however, an unrunnable validator must NOT fail open:
            # remember the error so the policy gate below can block on it, since
            # we cannot prove the linked stories pass.
            validation_error = str(exc)
            summary_lines.append(f"- Validation skipped: {exc}")
            if not quiet:
                console.print(f"[yellow]Story validation skipped: {exc}[/yellow]")

    # 4) Enforce the policy. `warn` only reports; `strict` blocks when a changed
    #    prompt still has no passing linked story.
    block_message: Optional[str] = None
    problems: List[str] = []
    if still_uncovered:
        uncovered_names = [
            _format_rel(p, prompts_dir or worktree_path) for p in still_uncovered
        ]
        problems.append(f"no linked story for: {', '.join(uncovered_names)}")
    if failing_stories:
        problems.append(f"failing linked story check(s): {', '.join(failing_stories)}")
    if validation_error:
        # A validation that could not run leaves coverage unproven; treat it as a
        # problem so strict policy blocks (warn only reports it, below).
        problems.append(f"validation failed/skipped: {validation_error}")
    if problems:
        joined = "; ".join(problems)
        if policy == "strict":
            block_message = f"strict story policy ({joined})"
            summary_lines.append(f"- ⛔ Blocking (strict policy): {joined}")
        else:
            summary_lines.append(f"- ⚠️ Warning (non-blocking): {joined}")

    return files_to_stage, "\n".join(summary_lines), total_cost, model_used, block_message


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
        # Issue #1080: text-mode --porcelain output is lossy for paths
        # containing spaces, quotes, or the literal " -> " substring.
        # Use the structured -z parser instead.
        from pdd.git_porcelain import parse_porcelain_z
        result = subprocess.run(
            ["git", "status", "--porcelain=v1", "-z", "--untracked-files=all"],
            cwd=worktree_path,
            capture_output=True, check=True
        )
        entries = parse_porcelain_z(result.stdout)
        files = []
        allowed_extensions = {".prompt", ".md"}
        direct_edit_set = set(direct_edit_candidates or [])
        for entry in entries:
            filepath = entry.path
            if not filepath:
                continue
            # Skip temp files from run_agentic_task
            if filepath.startswith(".agentic_prompt_") or "/.agentic_prompt_" in filepath:
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

    Clarification steps (4, 7) require explicit machine-readable markers.
    Other stop-capable steps use case-insensitive substring matching as a
    fallback. Step 8 is prompt-change analysis only and must continue to Step 9
    because code/docs direct edits may still be pending.
    """
    if not output:
        return None
    stop_match = re.search(r'STOP_CONDITION:\s*(.+)', output, re.IGNORECASE)
    output_lower = output.lower()

    if step_num == 1 and "duplicate of #" in output_lower:
        return "Issue is a duplicate"
    if step_num == 2 and re.search(r"^(?:\*\*)?(?:status|result)[:\s*]*already implemented", output_lower, re.MULTILINE):
        return "Already implemented"
    if step_num == 4:
        route_redirect = re.search(
            r"^[ \t]*ROUTE_REDIRECT:[ \t]*bug_fix[ \t]*$",
            output,
            re.IGNORECASE | re.MULTILINE,
        )
        if route_redirect:
            rationale_match = re.search(
                r"^[ \t]*ROUTE_RATIONALE:[ \t]*(.+)$",
                output,
                re.IGNORECASE | re.MULTILINE,
            )
            rationale = rationale_match.group(1).strip() if rationale_match else ""
            if rationale:
                return f"Runtime bug route needed: {rationale}"
            return "Runtime bug route needed: use pdd bug followed by pdd fix"
        if stop_match and "clarification" in stop_match.group(1).lower():
            return "Clarification needed"
        if stop_match and "runtime bug route" in stop_match.group(1).lower():
            return "Runtime bug route needed: use pdd bug followed by pdd fix"
        return None
    if step_num == 6 and re.search(r"^(?:\*\*)?(?:status|result)[:\s*]*no dev units found", output_lower, re.MULTILINE):
        return "No dev units found"
    if step_num == 7:
        if stop_match and "architectural" in stop_match.group(1).lower():
            return "Architectural decision needed"
        return None
    if step_num == 8:
        return None
    if step_num == 9:
        if "fail:" in output_lower:
            return "Implementation failed"
    # Universal fallback: any STOP_CONDITION tag on an unhandled step
    if stop_match:
        return stop_match.group(1).strip()
    return None



# Steps where a hard stop is a "clarification" request (user may respond, step should re-run)
_CLARIFICATION_STEPS = {4, 7}


# ---------------------------------------------------------------------------
# Step 8.5 — Pre-flight drift heal
# ---------------------------------------------------------------------------

# Process-wide lock guarding the os.chdir window in _preflight_drift_heal.
# detect_drift() reads from CWD; chdir is process-global, so concurrent
# orchestrator runs in the same process would stomp each other's cwd. The
# lock serializes the (chdir, detect_drift, chdir-back) critical section.
_PREFLIGHT_CHDIR_LOCK = threading.Lock()

_PREFLIGHT_MAX_HEAL_MODULES = 10


def _preflight_drift_heal(
    worktree_path: Path,
    quiet: bool = False,
    timeout_per_module: float = 300.0,
    max_modules: int = _PREFLIGHT_MAX_HEAL_MODULES,
) -> Tuple[List[str], List[str], List[str]]:
    """Detect and heal stale prompts before `pdd change` rewrites them.

    If a module's code has drifted from its prompt (code edited directly
    without updating the prompt), the prompt describes the *previous* code.
    Any `pdd change` operation would then reason from a stale prompt and
    produce bad output.

    This runs ``sync_determine_operation`` on every prompt in the worktree
    (hash-only, no LLM) to find modules with ``operation == "update"`` (prompt
    stale vs code), and runs ``pdd update <code_path>`` on each one *in the
    worktree* to realign the prompt before Step 9 rewrites it.

    Args:
        worktree_path: Path to the isolated git worktree where the change will
            run. Healing happens inside the worktree so that if any
            `pdd update` produces a bad prompt rewrite it is contained to the
            worktree and does not touch the user's main tree.
        quiet: If True, suppress console output.
        timeout_per_module: Hard cap on subprocess timeout for each `pdd update`.
        max_modules: Cap on how many drifted modules this pass will heal. With
            ``timeout_per_module`` defaulting to 300s, an unbounded fan-out
            could spend hours before Step 9 starts. When the drift list
            exceeds this cap, the alphabetically-first ``max_modules`` are
            healed and the remainder are deferred to the CI auto-heal pipeline
            (which runs on every resulting PR). The cap is intentionally
            generous — most realistic ``pdd change`` worktrees see 0–3 drifted
            modules; double-digit drift is the pathological case.

    Returns:
        Tuple of (healed_modules, failed_modules, healed_prompt_paths).
        ``healed_modules`` and ``failed_modules`` are basenames; the third
        element is the list of prompt-file paths (as recorded in
        ``DriftInfo.prompt_path``) that were rewritten by ``pdd update``.
        Surfacing the healed *prompt paths* lets the Step 10 discovery sweep
        re-run ``discover_associated_documents`` against the new prompt
        content, so any docs reachable from the just-healed prompt's
        ``<include>`` graph still go through the doc-sync contract — closing
        the gap where Step 8.5 mutations otherwise bypassed Steps 10/10.5.

        A module counts as "healed" if `pdd update` returned exit 0; "failed"
        if it returned non-zero or raised. Failure does not abort the workflow:
        the change proceeds against the unhealed prompt (Step 9's LLM may still
        succeed, and pretending drift is not present is no worse than before).

    Scope:
        The drift list is snapshotted once via `detect_drift()` and iterated.
        If healing module A causes module B's dependency graph to change (e.g.
        A's interface is rewritten and B includes A), B's drift state is not
        re-evaluated in this pass. The cascade case is intentionally delegated
        to the CI auto-heal pipeline (`ci_drift_heal.py`, the same primitive
        called here) which runs on every resulting PR — duplicating that loop
        inside this function would re-implement an existing safety net.
    """
    if not worktree_path.exists():
        return [], [], []

    try:
        from pdd.ci_drift_heal import detect_drift
    except (ImportError, ModuleNotFoundError) as exc:
        if not quiet:
            console.print(
                f"[yellow]⚠ Pre-flight drift heal unavailable ({exc}); "
                "continuing without pre-flight heal.[/yellow]"
            )
        return [], [], []

    # detect_drift() reads from CWD; ci_drift_heal's public API doesn't accept
    # a cwd argument so we must chdir into the worktree. chdir is process-
    # global, so serialize the (chdir → detect_drift → chdir-back) window
    # behind a module lock to prevent concurrent orchestrator runs in the
    # same process from clobbering each other's cwd.
    original_cwd = Path.cwd()
    prompt_drifts: List = []
    with _PREFLIGHT_CHDIR_LOCK:
        try:
            os.chdir(worktree_path)
            try:
                prompt_drifts, _example_drifts = detect_drift()
            except Exception as exc:
                if not quiet:
                    console.print(
                        f"[yellow]⚠ Pre-flight drift detection raised ({exc}); "
                        "continuing without pre-flight heal.[/yellow]"
                    )
                return [], [], []
        finally:
            os.chdir(original_cwd)

    if not prompt_drifts:
        if not quiet:
            console.print(
                "[blue][Step 8.5/13][/blue] Pre-flight drift check: "
                "all prompts in sync with code."
            )
        return [], [], []

    drifted_names = sorted({d.basename for d in prompt_drifts})

    # Reviewer 4th-pass: cap fan-out. With timeout_per_module=300s,
    # heading into a worktree with N drifted modules costs N × 5 min in
    # the worst case — unbounded for very large repos. Heal the first
    # ``max_modules`` (alphabetical for determinism) and defer the rest
    # to the CI auto-heal pipeline that runs on every resulting PR.
    deferred_names: List[str] = []
    if len(drifted_names) > max_modules:
        deferred_names = drifted_names[max_modules:]
        kept = set(drifted_names[:max_modules])
        prompt_drifts = [d for d in prompt_drifts if d.basename in kept]
        drifted_names = sorted(kept)

    if not quiet:
        console.print(
            f"[yellow][Step 8.5/13][/yellow] Pre-flight drift check: "
            f"{len(drifted_names)} module(s) drifted — healing before change: "
            f"{', '.join(drifted_names)}"
        )
        if deferred_names:
            console.print(
                f"   [yellow]⚠[/yellow] {len(deferred_names)} additional drifted "
                f"module(s) deferred to CI auto-heal (cap={max_modules}): "
                f"{', '.join(deferred_names)}"
            )

    # Reviewer 3rd-pass: the heal subprocess runs in a headless Cloud Run
    # worker; stdin is piped so pdd.auto_update's isatty() auto-detect
    # usually picks up "non-interactive" — but the production CI auto-heal
    # path (ci_drift_heal._build_ci_env) also sets explicit guardrails to
    # skip local LM Studio calls, force non-TTY behavior, and restore
    # protected paths if pdd sync/update times out mid-mutation. Mirror
    # those guardrails here so Step 8.5 is as defensive as the CI heal
    # path it shares the detect_drift primitive with.
    heal_env = os.environ.copy()
    heal_env.setdefault("PDD_FORCE", "1")
    heal_env.setdefault("CI", "1")
    heal_env.setdefault("NO_COLOR", "1")
    heal_env.setdefault("PDD_FORCE_LOCAL", "1")
    heal_env.setdefault("PDD_SKIP_LOCAL_MODELS", "1")
    heal_env.setdefault("PDD_RESTORE_PROTECTED_PATHS_ON_FAILURE", "1")

    healed: List[str] = []
    failed: List[str] = []
    healed_prompts: List[str] = []
    for drift in prompt_drifts:
        if not drift.code_path:
            failed.append(drift.basename)
            continue
        try:
            # Use sys.executable + -m pdd so the heal subprocess uses the
            # same Python venv as the orchestrator. A bare ["pdd", ...]
            # would pick up whatever pdd binary is on PATH, which can be
            # a different version when devs have a global install plus a
            # project-local one.
            result = subprocess.run(
                [sys.executable, "-m", "pdd", "update", "--sync-metadata", drift.code_path],
                cwd=str(worktree_path),
                capture_output=True,
                text=True,
                timeout=timeout_per_module,
                env=heal_env,
            )
            if result.returncode == 0:
                healed.append(drift.basename)
                if drift.prompt_path:
                    healed_prompts.append(drift.prompt_path)
                if not quiet:
                    console.print(f"   [green]✓[/green] healed {drift.basename}")
            else:
                # Issue #1006: metadata-finalization failures are NOT advisory
                combined = (result.stderr or "") + "\n" + (result.stdout or "")
                if (
                    "metadata finalization failed" in combined
                    or "metadata staging verification failed" in combined
                    or "[metadata-sync]" in combined
                ):
                    raise RuntimeError(
                        f"preflight metadata finalization failed for "
                        f"{drift.basename}: {combined.strip()}"
                    )
                failed.append(drift.basename)
                if not quiet:
                    tail = result.stderr.strip().splitlines()[-1:] or ["(no stderr)"]
                    console.print(
                        f"   [red]✗[/red] heal failed {drift.basename}: "
                        f"{escape(tail[0])}"
                    )
        except subprocess.TimeoutExpired:
            failed.append(drift.basename)
            if not quiet:
                console.print(
                    f"   [red]✗[/red] heal timed out for {drift.basename}"
                )
        except RuntimeError:
            # Issue #1006: metadata finalization failures must propagate.
            raise
        except Exception as exc:
            failed.append(drift.basename)
            if not quiet:
                console.print(
                    f"   [red]✗[/red] heal raised for {drift.basename}: {exc}"
                )

    if not quiet:
        console.print(
            f"   → Pre-flight heal complete: "
            f"{len(healed)} healed, {len(failed)} failed."
        )
    return healed, failed, healed_prompts


# ---------------------------------------------------------------------------
# Step 10.5 — Post-Step-10 associated-document contract verifier
# ---------------------------------------------------------------------------



def _verify_doc_sync_contract(
    discovered_docs: List[str],
    step10_output: str,
    step10_json: Optional[dict] = None,
) -> Tuple[List[str], List[str], List[str], List[str], List[str]]:
    """Enforce the associated-document contract after Step 10.

    The contract: every doc in *discovered_docs* (from Step 10's pre-call to
    ``discover_associated_documents``) must appear in Step 10's output under
    EXACTLY ONE of:
      - ``ASSOCIATED_DOCS_MODIFIED:``  — LLM edited the doc
      - ``ASSOCIATED_DOCS_CONFLICTS:`` — LLM flagged it for manual review
      - ``ASSOCIATED_DOCS_UNCHANGED:`` — LLM determined it was already consistent

    Two classes of contract violation are caught:

    1. **Silent drops** — a discovered doc appears in none of the three
       buckets. The LLM forgot it. Downstream consumers (review loops, PR
       bodies) never learn the doc was skipped.

    2. **Overlap (contradictory state)** — a discovered doc appears in two or
       more buckets (e.g. both ``MODIFIED`` and ``UNCHANGED``). The LLM made
       inconsistent claims about the same file. Treating such a doc as
       "handled" lets a real state conflict ride through to the PR.

    The Step 10 prompt must instruct the LLM to emit exactly one marker per
    doc; otherwise this verifier false-positives on every doc.

    Scope:
        The contract only protects docs the static discovery (`<include>`
        graph + architecture BFS) actually found. Docs that *should* be
        referenced via `<include>` but aren't tagged are invisible here —
        catching that class of gap requires semantic auto-deps discovery,
        which is tracked separately as future work.

    Args:
        discovered_docs: The list the orchestrator passed in via
            ``context["associated_documents"]``. Pass ``[]`` when no docs were
            discovered (the contract is trivially satisfied).
        step10_output: Raw Step 10 LLM output text.

    Returns:
        Tuple of (modified, conflicted, unchanged, silently_dropped, overlapping).
        Both *silently_dropped* and *overlapping* are alarms — the former lists
        discovered docs the LLM never addressed, the latter lists discovered
        docs the LLM placed in more than one bucket simultaneously.
    """
    if not discovered_docs:
        return [], [], [], [], []

    # Reviewer 4th-pass fixes (bugs 1 + 2):
    #   (a) Multi-line marker values, UNINDENTED continuation. The prior
    #       regex `[^\n]*(?:\n[ \t]+[^\n]*)*` required continuation lines
    #       to start with whitespace. LLMs frequently wrap a long list
    #       without indenting the next line — those entries vanished
    #       silently and were re-flagged as silent drops. Replaced with a
    #       line-by-line walk that stops at a blank line or another known
    #       marker, regardless of indentation.
    #   (b) Bulleted list with no commas (e.g. "MARKER:\n  - a.md\n  - b.md").
    #       Joining lines with " " before splitting on "," produced a
    #       single entry "- a.md   - b.md" which `_strip_entry` could only
    #       partially un-bullet. Strip the leading bullet *per line* before
    #       splitting on comma, so each line is its own potential entry.
    # The verifier and ``_extract_marker_paths`` share marker-walking
    # semantics by design — if they ever disagree on what Step 10 emitted
    # the orchestrator's bookkeeping silently diverges from the contract.
    if isinstance(step10_json, dict):
        modified = _json_list(step10_json, "associated_docs_modified")
        conflicted = _json_list(step10_json, "associated_docs_conflicts")
        unchanged = _json_list(step10_json, "associated_docs_unchanged")
    else:
        modified = _extract_marker_paths("ASSOCIATED_DOCS_MODIFIED", step10_output)
        conflicted = _extract_marker_paths("ASSOCIATED_DOCS_CONFLICTS", step10_output)
        unchanged = _extract_marker_paths("ASSOCIATED_DOCS_UNCHANGED", step10_output)

    def _normalize(p: str) -> str:
        # Normalize backslashes to forward slashes BEFORE pathlib so a
        # windows-style 'docs\\foo.md' matches a posix 'docs/foo.md'.
        return Path(p.replace("\\", "/")).as_posix()

    mod_norm = {_normalize(p) for p in modified}
    conf_norm = {_normalize(p) for p in conflicted}
    unch_norm = {_normalize(p) for p in unchanged}
    handled: Set[str] = mod_norm | conf_norm | unch_norm

    silently_dropped = [
        d for d in discovered_docs
        if _normalize(d) not in handled
    ]

    # A doc is in overlap if its normalized form appears in 2+ of the three
    # buckets. Preserves the discovered-list ordering for deterministic output.
    overlapping = [
        d for d in discovered_docs
        if sum(
            1 for bucket in (mod_norm, conf_norm, unch_norm)
            if _normalize(d) in bucket
        ) >= 2
    ]

    return modified, conflicted, unchanged, silently_dropped, overlapping


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

        # Derive ext from language; keep parsed .pddrc paths even if extension
        # lookup cannot resolve local package data in a test or constrained env.
        try:
            ext = get_extension(language) if language else defaults["ext"]
        except Exception:
            ext = defaults["ext"]
        if not ext:
            ext = defaults["ext"]
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

    Matches the canonical ``change/issue-{N}`` head AND any
    ``change/issue-{N}-job-*`` clean-restart fallback head (issue #1596), so a
    later normal run does not open a duplicate PR for a fallback branch.
    Returns the PR URL if found, else None.

    GitHub's ``head:`` search is a PREFIX match, so ``head:change/issue-{N}``
    also returns unrelated heads like ``change/issue-{N}0``; the results are
    filtered precisely in Python.
    """
    canonical = f"change/issue-{issue_number}"
    fallback_prefix = f"{canonical}-job-"
    try:
        result = subprocess.run(
            ["gh", "pr", "list", "--repo", f"{repo_owner}/{repo_name}",
             "--search", f"head:{canonical}", "--state", "open",
             "--json", "url,headRefName", "--limit", "30"],
            capture_output=True, text=True, check=False, timeout=30,
        )
        if result.returncode != 0:
            return None
        data = json.loads(result.stdout)
        if data and isinstance(data, list):
            for pr in data:
                head = pr.get("headRefName", "")
                if head == canonical or head.startswith(fallback_prefix):
                    if pr.get("url"):
                        return pr["url"]
    except (subprocess.TimeoutExpired, json.JSONDecodeError, Exception):
        pass
    return None


def _check_existing_pr_candidates(
    repo_owner: str,
    repo_name: str,
    issue_number: int,
) -> List[dict]:
    """Return open PR metadata candidates for canonical/fallback issue branches."""
    canonical = f"change/issue-{issue_number}"
    fallback_prefix = f"{canonical}-job-"
    data = _gh_pr_list_candidates(
        [
            "gh",
            "pr",
            "list",
            "--repo",
            f"{repo_owner}/{repo_name}",
            "--search",
            f"head:{canonical}",
            "--state",
            "open",
            "--json",
            "number,url,headRefName,headRefOid,baseRefName,state",
        ]
    )
    candidates: List[dict] = []
    for pr in data:
        if not isinstance(pr, dict):
            continue
        head = str(pr.get("headRefName") or "")
        if (head == canonical or head.startswith(fallback_prefix)) and _valid_pr_url(
            pr.get("url"), repo_owner, repo_name
        ):
            candidates.append(pr)
    return candidates


def _existing_pr_matches_remote_head(
    repo_owner: str,
    repo_name: str,
    pr: dict,
    base_branch: str,
    cwd: Path,
) -> bool:
    """Validate existing-PR guard metadata against its remote branch state."""
    if not isinstance(pr, dict):
        return False
    pr_url = str(pr.get("url") or "").strip()
    head_branch = str(pr.get("headRefName") or "").strip()
    if not _valid_pr_url(pr_url, repo_owner, repo_name):
        return False
    if str(pr.get("state") or "").strip().upper() != "OPEN":
        return False
    if str(pr.get("baseRefName") or "").strip() != base_branch:
        return False
    remote_oid = _remote_branch_oid(head_branch, cwd)
    pr_oid = str(pr.get("headRefOid") or "").strip()
    if not remote_oid:
        return False
    return bool(pr_oid) and pr_oid.lower() == remote_oid.lower()


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
    reasoning_time: Optional[float] = None,
    clean_restart: bool = False,
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

    # Clean Restart (Req 15, issue #1149): discard persisted local + GitHub
    # state up front so the rest of this function sees an empty slate. This
    # MUST run BEFORE load_workflow_state so the reload returns None and the
    # existing-PR guard / stale-state / cached-worktree paths cannot resume
    # the previous run's branch.
    if clean_restart:
        try:
            clear_workflow_state(
                cwd, issue_number, "change", state_dir,
                repo_owner, repo_name, use_github_state,
            )
        except Exception as e:
            if not quiet:
                console.print(
                    f"[yellow]Warning: clean_restart pre-clear failed (continuing with fresh in-memory state): {e}[/yellow]"
                )
        if not quiet:
            console.print(
                f"[bold cyan]Clean restart requested for issue #{issue_number} — discarded persisted state.[/bold cyan]"
            )

    # Load state
    state, loaded_gh_id = load_workflow_state(
        cwd, issue_number, "change", state_dir, repo_owner, repo_name, use_github_state
    )

    # Compute effective flag: CLI flag OR persisted flag from a prior clean-restart
    # invocation that stopped mid-run. A plain `pdd change` resume after a failed
    # clean-restart Step 13 must still skip the PR guard and use force-push semantics
    # in worktree setup — both of which require the persisted flag, not just the CLI one.
    effective_clean_restart = clean_restart or bool((state or {}).get("clean_restart", False))

    # Guard: if an open PR already exists for this issue, return early.
    # Skipped under clean_restart (Req 15) because the caller explicitly wants
    # to ignore the previously generated change/issue-{N} branch / PR.
    if not effective_clean_restart:
        existing_pr_base_branch = _normalize_pr_base_branch(
            _resolve_main_ref_name(_get_git_root(cwd) or cwd)
        )
        existing_pr = None
        for existing_pr_meta in _check_existing_pr_candidates(
            repo_owner, repo_name, issue_number
        ):
            if _existing_pr_matches_remote_head(
                repo_owner,
                repo_name,
                existing_pr_meta,
                existing_pr_base_branch,
                cwd,
            ):
                existing_pr = str(existing_pr_meta.get("url") or "").strip()
                break
        if existing_pr:
            if not quiet:
                console.print(f"[yellow]PR already exists for issue #{issue_number}: {existing_pr}[/yellow]")
            return True, f"PR already exists: {existing_pr}", 0.0, "unknown", []

    # Check for stale state: if issue was updated since state was saved, start fresh.
    # Skipped only when the CLI --clean-restart flag is set (not when the persisted
    # flag is inherited via effective_clean_restart): the CLI flag guarantees the
    # pre-clear already ran and state is empty, so the comparison is meaningless.
    # On a persisted-clean-restart resume (clean_restart=False CLI, state has
    # clean_restart=True) we MUST still run this check — the user may have added
    # issue comments between the stopped run and the resume, and the cached step
    # outputs from the stopped run would otherwise ignore those new comments.
    if not clean_restart and state is not None and issue_updated_at:
        stored_updated_at = state.get("issue_updated_at")
        if stored_updated_at and stored_updated_at != issue_updated_at:
            if issue_update_should_clear_workflow_state(
                state,
                stored_updated_at,
                issue_updated_at,
                repo_owner,
                repo_name,
                issue_number,
                cwd=cwd,
                clarification_step_numbers=_CLARIFICATION_STEPS,
            ):
                if not quiet:
                    console.print(
                        "[yellow]Issue was updated since last run - starting fresh[/yellow]"
                    )
                clear_workflow_state(
                    cwd, issue_number, "change", state_dir,
                    repo_owner, repo_name, use_github_state,
                )
                state = None
                loaded_gh_id = None
            elif not quiet:
                console.print(
                    "[cyan]Issue was updated (new comments) — continuing saved workflow[/cyan]"
                )
                state["issue_updated_at"] = issue_updated_at

    # Initialize variables from state or defaults.
    # Under clean_restart, defensively ignore any state that survived the
    # pre-clear (e.g. a race against another worker that re-wrote the
    # comment after clear_workflow_state ran) so this run cannot resume
    # from a stale step-output cache or reuse the previous worktree path.
    if state is not None and not clean_restart:
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
        if effective_clean_restart:
            state["clean_restart"] = True

    # Normalize step comments tracking (Set[int] of step indices already posted)
    step_comments_set = normalize_step_comments_state(state.get("step_comments"))
    state["step_comments"] = sorted(step_comments_set)
    step_json_outputs = state.setdefault("step_json_outputs", {})
    for step_key in list(step_json_outputs):
        try:
            step_key_num = int(step_key)
        except (TypeError, ValueError):
            continue
        cached_output = str(step_outputs.get(step_key, ""))
        if step_key_num > last_completed_step or cached_output.startswith("FAILED:"):
            step_json_outputs.pop(step_key, None)
    manual_review_json_lines: List[str] = []
    if _valid_step_json(9, step_json_outputs.get("9")):
        manual_line = _manual_review_lines_from_json(step_json_outputs.get("9"))
        manual_review_json_lines = manual_line.splitlines() if manual_line else []
        state["manual_review_json_lines"] = manual_review_json_lines
    else:
        manual_review_json_lines = []
        state["manual_review_json_lines"] = manual_review_json_lines
    review_manual_review_json_lines: List[str] = list(
        state.get("review_manual_review_json_lines") or []
    )
    review_state_invalidated = (
        last_completed_step < 10
        or any(
            str(step_outputs.get(str(step), "")).startswith("FAILED:")
            for step in (9, 10, 11, 12)
        )
    )
    if review_state_invalidated:
        state["review_iteration"] = 0
        state["previous_fixes"] = ""
        state["review_manual_review_json_lines"] = []
        review_manual_review_json_lines = []

    if ensure_issue_steer_cursor_seeded(
        repo_owner, repo_name, issue_number, state, cwd=cwd, quiet=quiet
    ):
        seed_save = save_workflow_state(
            cwd,
            issue_number,
            "change",
            state,
            state_dir,
            repo_owner,
            repo_name,
            use_github_state,
            github_comment_id,
            dedupe=effective_clean_restart,
        )
        if seed_save:
            github_comment_id = seed_save
            state["github_comment_id"] = github_comment_id

    pddrc_context = _load_pddrc_context(cwd)

    steer_generation_before = state.get("steer_generation", 0)
    issue_content = apply_clarification_steers_on_resume(
        issue_content,
        state,
        repo_owner,
        repo_name,
        issue_number,
        _CLARIFICATION_STEPS,
        cwd=cwd,
        quiet=quiet,
    )
    if state.get("steer_generation", 0) != steer_generation_before:
        save_result = save_workflow_state(
            cwd,
            issue_number,
            "change",
            state,
            state_dir,
            repo_owner,
            repo_name,
            use_github_state,
            github_comment_id,
            dedupe=effective_clean_restart,
        )
        if save_result:
            github_comment_id = save_result
            state["github_comment_id"] = github_comment_id

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
        try:
            s_num_int = int(s_num)
        except (TypeError, ValueError):
            s_num_int = 0
        if s_num_int > last_completed_step or str(s_out).startswith("FAILED:"):
            continue
        context[f"step{s_num}_output"] = s_out

    cached_step6_output = str(context.get("step6_output", ""))
    if (
        last_completed_step >= 6
        and cached_step6_output
        and not cached_step6_output.startswith("FAILED:")
    ):
        s6_json = step_json_outputs.get("6")
        if _valid_step_json(6, s6_json):
            context["direct_edit_candidates"] = _json_list(
                s6_json, "direct_edit_candidates"
            )
        else:
            context["direct_edit_candidates"] = _parse_direct_edit_candidates(
                cached_step6_output
            )

    changed_files = []
    
    if "step9_output" in context:
        s9_out = context["step9_output"]
        s9_json = step_json_outputs.get("9")
        if _valid_step_json(9, s9_json):
            extracted_files, files_created, files_modified, direct_edits = (
                _step9_changed_files_from_json(s9_json)
            )
            context["files_created"] = ", ".join(files_created)
            context["files_modified"] = ", ".join(files_modified)
            context["direct_edits"] = ", ".join(direct_edits)
            manual_line = _manual_review_lines_from_json(s9_json)
            manual_review_json_lines = manual_line.splitlines() if manual_line else []
            state["manual_review_json_lines"] = manual_review_json_lines
        else:
            extracted_files = _parse_changed_files(s9_out)
            context["files_created"] = ", ".join(_extract_marker_paths("FILES_CREATED", s9_out))
            context["files_modified"] = ", ".join(_extract_marker_paths("FILES_MODIFIED", s9_out))
        if not extracted_files and worktree_path and worktree_path.exists():
            # Resume case for the successful Step 9 fallback path: the LLM
            # omitted FILES_* markers, so the only authoritative source is
            # the worktree's current git status.
            extracted_files = _detect_worktree_changes(
                worktree_path,
                _parse_direct_edit_candidates(context.get("step6_output", "")),
            )
        changed_files.extend(extracted_files)
    
    if "step10_output" in context:
        s10_out = context["step10_output"]
        s10_json = step_json_outputs.get("10")
        arch_files = (
            _step10_changed_files_from_json(s10_json)
            if _valid_step_json(10, s10_json)
            else _parse_changed_files(s10_out)
        )
        new_files = [f for f in arch_files if f not in changed_files]
        changed_files.extend(new_files)

    if changed_files:
        context["files_to_stage"] = ", ".join(changed_files)

    start_step = last_completed_step + 1

    if start_step == 1 or clean_restart:
        _reset_artifacts_dir(cwd, issue_number)

    if last_completed_step > 0 and not quiet:
        console.print(f"Resuming change workflow for issue #{issue_number}")
        console.print(f"   Steps 1-{last_completed_step} already complete (cached)")
        console.print(f"   Starting from Step {start_step}")

    # Req 16 (issue #1149): post a one-shot startup comment so the issue
    # reader can see, at a glance, whether this run is resuming or
    # clean-starting, the model in use, and the base branch / command.
    # Uses step_num=0 so post_step_comment_once dedupes correctly across
    # resumes. Failure to post is log-and-continue: gh CLI missing or a
    # network blip MUST NOT take the workflow down.
    try:
        if clean_restart:
            mode_label = "Clean restart"
        elif start_step > 1:
            mode_label = f"Resuming from step {start_step}"
        else:
            mode_label = "Starting fresh"

        git_root_for_baseref = _get_git_root(cwd) or cwd
        base_ref_label = _resolve_main_ref_name(git_root_for_baseref)

        startup_body = (
            f"## Step 0/13: Workflow Startup\n\n"
            f"- **Mode**: {mode_label}\n"
            f"- **Base branch**: {base_ref_label}\n"
            f"- **Command**: pdd-issue (full change → sync flow)\n"
        )
        post_step_comment_once(
            repo_owner=repo_owner,
            repo_name=repo_name,
            issue_number=issue_number,
            step_num=0,
            body=startup_body,
            posted_steps=step_comments_set,
            cwd=cwd,
        )
        state["step_comments"] = sorted(step_comments_set)
    except Exception as e:
        if not quiet:
            console.print(f"[yellow]Warning: startup comment post failed (continuing): {e}[/yellow]")

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
            wt_path, err = _setup_worktree(cwd, issue_number, quiet, clean_restart=effective_clean_restart)
            if not wt_path:
                return False, f"Failed to restore worktree: {err}", total_cost, model_used, []
            worktree_path = wt_path
            current_work_dir = worktree_path
            state["worktree_path"] = str(worktree_path)
            context["worktree_path"] = str(worktree_path)

    consecutive_provider_failures = 0
    previous_architecture = None

    def _issue_step_steers():
        nonlocal github_comment_id
        step_steers = drain_step_steers(
            repo_owner,
            repo_name,
            issue_number,
            state,
            cwd=cwd,
            quiet=quiet,
        )
        if step_steers:
            refreshed_at = _fetch_issue_updated_at(
                repo_owner, repo_name, issue_number
            )
            if refreshed_at:
                state["issue_updated_at"] = refreshed_at
            elif issue_updated_at:
                state["issue_updated_at"] = issue_updated_at
            save_result = save_workflow_state(
                cwd,
                issue_number,
                "change",
                state,
                state_dir,
                repo_owner,
                repo_name,
                use_github_state,
                github_comment_id,
                dedupe=effective_clean_restart,
            )
            if save_result:
                github_comment_id = save_result
                state["github_comment_id"] = github_comment_id
        return step_steers

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

                wt_path, err = _setup_worktree(cwd, issue_number, quiet, clean_restart=effective_clean_restart)
                if not wt_path:
                    return False, f"Failed to create worktree: {err}", total_cost, model_used, []
                worktree_path = wt_path
                current_work_dir = worktree_path
                state["worktree_path"] = str(worktree_path)
                context["worktree_path"] = str(worktree_path)
                if start_step == 1 or clean_restart:
                    _reset_artifacts_dir(worktree_path, issue_number)

            # Step 8.5: pre-flight drift heal — run once per worktree (so heals
            # are contained to the worktree and can't touch the user's main
            # tree). Idempotency is tied to the worktree path, not the
            # workflow: if the worktree is recreated between runs (e.g. user
            # deletes `.pdd/worktrees/change-issue-{N}/` after a strict-mode
            # abort), we MUST re-heal because the new worktree starts clean
            # without the previous heal's effects.
            worktree_path_str = str(worktree_path) if worktree_path else None
            already_healed_worktree = state.get("preflight_healed_worktree")
            if (
                worktree_path
                and worktree_path.exists()
                and (
                    not state.get("preflight_drift_healed")
                    or already_healed_worktree != worktree_path_str
                )
            ):
                healed, failed_heal, healed_prompts = _preflight_drift_heal(
                    worktree_path=worktree_path,
                    quiet=quiet,
                )
                state["preflight_drift_healed"] = True
                state["preflight_healed_worktree"] = worktree_path_str
                state["preflight_healed_modules"] = healed
                state["preflight_failed_heal_modules"] = failed_heal
                # Reviewer 5th-pass (F2): record the healed *prompt paths*
                # too. Step 10's discovery sweep below merges these with
                # Step 9's modified prompts so docs reachable from a
                # just-healed prompt's <include> graph still go through
                # the doc-sync contract.
                state["preflight_healed_prompt_paths"] = healed_prompts
                context["preflight_healed_modules"] = ", ".join(healed) if healed else "None"
                context["preflight_failed_heal_modules"] = (
                    ", ".join(failed_heal) if failed_heal else "None"
                )

        if not quiet:
            console.print(f"[bold][Step {step_num}/13][/bold] {description}...")

        # Before Step 10: discover associated documents for the LLM to update
        if step_num == 10 and worktree_path and worktree_path.exists():
            # Use the authoritative changed-file set for Step 10 discovery.
            # In the Step 9 fallback path, `files_created`/`files_modified`
            # are empty because the LLM omitted markers, but `changed_files`
            # and `files_to_stage` contain the worktree-detected prompt(s).
            modified_prompt_paths: Set[Path] = _prompt_paths_from_changed_file_entries(
                [
                    context.get("files_created", ""),
                    context.get("files_modified", ""),
                    context.get("files_to_stage", ""),
                    *changed_files,
                ],
                worktree_path,
            )

            # Reviewer 5th-pass (F2): include preflight-healed prompts so
            # any <include>doc.md</include> they hold reaches the doc-sync
            # contract. Without this, Step 8.5 mutations bypass Steps
            # 10/10.5 and a healed prompt's docs can land in the PR via
            # `git add -A` without ever passing through verification.
            for prompt_path_str in state.get("preflight_healed_prompt_paths", []) or []:
                p = Path(prompt_path_str)
                if not p.is_absolute():
                    p = worktree_path / p
                if p.exists():
                    modified_prompt_paths.add(p)

            if modified_prompt_paths:
                try:
                    docs = discover_associated_documents(
                        modified_prompts=modified_prompt_paths,
                        prompts_dir=worktree_path / "prompts",
                        architecture_path=worktree_path / "architecture.json",
                        max_depth=3,
                    )
                    context["associated_documents"] = ", ".join(docs) if docs else "None"
                    # Store the discovered list for Step 10.5 contract verification
                    context["_associated_documents_discovered"] = docs or []
                except Exception as exc:
                    console.print(f"[yellow]Associated document discovery failed: {exc}[/yellow]")
                    context["associated_documents"] = "None"
                    context["_associated_documents_discovered"] = []
            else:
                context["associated_documents"] = "None"
                context["_associated_documents_discovered"] = []

        # Snapshot architecture.json before Step 10 so we can revert out-of-scope mutations
        if step_num == 10 and worktree_path:
            arch_path = worktree_path / "architecture.json"
            if arch_path.exists():
                try:
                    with open(arch_path, "r", encoding="utf-8") as f:
                        previous_architecture = extract_modules(json.load(f))
                except (json.JSONDecodeError, OSError):
                    previous_architecture = None

        artifacts_dir = _artifacts_dir_for(current_work_dir, issue_number)
        context["artifacts_dir"] = str(artifacts_dir)

        template_name = f"agentic_change_step{step_num}_{name}_LLM"
        prompt_template = load_prompt_template(template_name)
        if not prompt_template:
            return False, f"Missing prompt template: {template_name}", total_cost, model_used, []
        expects_artifacts = "{artifacts_dir}" in prompt_template

        # Preprocess to expand <include> tags and escape curly braces
        # Exclude context keys from escaping so they can be substituted
        exclude = list(context.keys())
        prompt_template = preprocess(prompt_template, recursive=True, double_curly_brackets=True, exclude=exclude)

        formatted_prompt = substitute_template_variables(prompt_template, context)

        timeout = CHANGE_STEP_TIMEOUTS.get(step_num, 340.0) + timeout_adder
        decision_json_name = _decision_json_filename(step_num, name)
        _clear_step_artifacts(artifacts_dir, step_num, name)
        if decision_json_name:
            step_json_outputs.pop(str(step_num), None)
        step_success, step_output, step_cost, step_model = run_agentic_task(
            instruction=formatted_prompt,
            cwd=current_work_dir,
            verbose=verbose,
            quiet=quiet,
            timeout=timeout,
            label=f"step{step_num}",
            max_retries=DEFAULT_MAX_RETRIES,
            reasoning_time=reasoning_time,
            steers=_issue_step_steers() or None,
            single_provider_attempt=_single_provider_attempt_for_step(step_num),
            before_attempt=lambda _provider, _attempt: _clear_step_artifacts(
                artifacts_dir, step_num, name
            ),
        )

        total_cost += step_cost
        model_used = step_model
        state["total_cost"] = total_cost
        state["model_used"] = model_used

        step_json = (
            _read_step_json(artifacts_dir, decision_json_name)
            if decision_json_name
            else None
        )
        initial_step_success = step_success
        initial_step_output = step_output
        json_repair_reran = False
        if (
            decision_json_name
            and expects_artifacts
            and not _valid_step_json(step_num, step_json)
            and _allow_json_repair_rerun(step_num)
        ):
            if not quiet:
                console.print(
                    f"[yellow]Step {step_num} did not write valid {decision_json_name}; rerunning once before prose fallback.[/yellow]"
                )
            json_repair_reran = True
            _clear_step_artifacts(artifacts_dir, step_num, name)
            retry_success, retry_output, retry_cost, retry_model = run_agentic_task(
                instruction=formatted_prompt,
                cwd=current_work_dir,
                verbose=verbose,
                quiet=quiet,
                timeout=timeout,
                label=f"step{step_num}_json_retry",
                max_retries=DEFAULT_MAX_RETRIES,
                reasoning_time=reasoning_time,
                steers=_issue_step_steers() or None,
                single_provider_attempt=_single_provider_attempt_for_step(step_num),
                before_attempt=lambda _provider, _attempt: _clear_step_artifacts(
                    artifacts_dir, step_num, name
                ),
            )
            step_success = retry_success
            step_output = retry_output
            total_cost += retry_cost
            model_used = retry_model
            state["total_cost"] = total_cost
            state["model_used"] = model_used
            step_json = _read_step_json(artifacts_dir, decision_json_name)
        if decision_json_name and not _valid_step_json(step_num, step_json):
            if not quiet and expects_artifacts:
                if json_repair_reran:
                    console.print(
                        f"[yellow]Step {step_num} JSON unavailable after retry; using prose fallback.[/yellow]"
                    )
                else:
                    console.print(
                        f"[yellow]Step {step_num} JSON unavailable; using prose fallback without rerun.[/yellow]"
                    )
            if initial_step_success:
                step_success = initial_step_success
                step_output = initial_step_output
                _clear_step_artifacts(artifacts_dir, step_num, name)
            step_json = None
        if decision_json_name and _valid_step_json(step_num, step_json):
            step_json_outputs[str(step_num)] = step_json

        if not step_success:
            # Track consecutive provider failures for early abort
            if "All agent providers failed" in step_output:
                time.sleep(PROVIDER_FAILURE_BACKOFF_SECONDS)
                consecutive_provider_failures += 1
                if consecutive_provider_failures >= 3:
                    post_step_comment(
                        repo_owner=repo_owner, repo_name=repo_name,
                        issue_number=issue_number, step_num=step_num,
                        total_steps=13, description=description,
                        output=step_output, cwd=cwd,
                    )
                    state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"
                    state["step_comments"] = sorted(step_comments_set)
                    save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id, dedupe=effective_clean_restart)
                    return False, f"Aborting: {consecutive_provider_failures} consecutive steps failed — agent providers unavailable", total_cost, model_used, []
            else:
                consecutive_provider_failures = 0

            json_seen, stop_reason, json_direct_edits = (
                _hard_stop_from_json_with_presence(step_num, artifacts_dir, name)
            )
            if step_num == 6 and json_seen:
                context["direct_edit_candidates"] = json_direct_edits
            if not json_seen:
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
                state["step_comments"] = sorted(step_comments_set)
                save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id, dedupe=effective_clean_restart)
                return False, f"Stopped at step {step_num}: {stop_reason}", total_cost, model_used, changed_files
            console.print(f"[yellow]Warning: Step {step_num} reported failure but continuing...[/yellow]")

        # Step 6 can legitimately find no prompt-backed dev units while still
        # identifying unmanaged direct edit candidates. Parse those before hard
        # stop detection so direct-edit-only runs can continue to Step 8/9.
        if step_num == 6:
            json_seen, _, json_direct_edits = _hard_stop_from_json_with_presence(
                step_num, artifacts_dir, name
            )
            direct_edit_candidates = (
                json_direct_edits
                if json_seen
                else _parse_direct_edit_candidates(step_output)
            )
            context["direct_edit_candidates"] = direct_edit_candidates
            if direct_edit_candidates and not quiet:
                console.print(f"[blue]Found {len(direct_edit_candidates)} direct edit candidate(s)[/blue]")

        json_seen, stop_reason, _ = _hard_stop_from_json_with_presence(
            step_num, artifacts_dir, name
        )
        if not json_seen:
            stop_reason = _check_hard_stop(step_num, step_output)
        if step_num == 6 and stop_reason and context.get("direct_edit_candidates"):
            stop_reason = None
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
            state["step_comments"] = sorted(step_comments_set)
            save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id, dedupe=effective_clean_restart)
            return False, f"Stopped at step {step_num}: {stop_reason}", total_cost, model_used, changed_files

        if step_num == 9:
            if _valid_step_json(9, step_json) and step_json.get("status") == "failed":
                error = str(
                    step_json.get("error")
                    or step_json.get("summary")
                    or "Implementation failed"
                ).strip()
                state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"
                state["step_comments"] = sorted(step_comments_set)
                save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id, dedupe=effective_clean_restart)
                return False, f"Stopped at step 9: {error}", total_cost, model_used, []
            if _valid_step_json(9, step_json) and step_json.get("status") == "no_change_needed":
                state["step_outputs"][str(step_num)] = step_output
                state["last_completed_step"] = step_num
                try:
                    report_body = _comment_body_from_artifact(
                        artifacts_dir,
                        "09_implement",
                        step_output,
                        (
                            "Step 9 completed with no repository changes needed. "
                            "Raw output retained in workflow state."
                        ),
                    )
                    post_step_comment_once(
                        repo_owner=repo_owner,
                        repo_name=repo_name,
                        issue_number=issue_number,
                        step_num=step_num,
                        body=f"## Step 9/13: Implement the prompt changes\n\n{report_body}",
                        posted_steps=step_comments_set,
                        cwd=cwd,
                    )
                except Exception as _exc:
                    console.print(f"[yellow]Warning: failed to post step comment for step {step_num}: {_exc}[/yellow]")
                state["step_comments"] = sorted(step_comments_set)
                clear_workflow_state(
                    cwd,
                    issue_number,
                    "change",
                    state_dir,
                    repo_owner,
                    repo_name,
                    use_github_state,
                )
                clear_agentic_progress()
                return (
                    True,
                    f"No prompt changes needed for issue #{issue_number}",
                    total_cost,
                    model_used,
                    [],
                )
            if _valid_step_json(9, step_json):
                extracted_files, files_created, files_modified, direct_edits = (
                    _step9_changed_files_from_json(step_json)
                )
                context["files_created"] = ", ".join(files_created)
                context["files_modified"] = ", ".join(files_modified)
                context["direct_edits"] = ", ".join(direct_edits)
                manual_line = _manual_review_lines_from_json(step_json)
                manual_review_json_lines = manual_line.splitlines() if manual_line else []
                state["manual_review_json_lines"] = manual_review_json_lines
            else:
                extracted_files = _parse_changed_files(step_output)
                if not extracted_files and re.search(r"\bFAIL:", step_output, re.IGNORECASE):
                    state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"
                    state["step_comments"] = sorted(step_comments_set)
                    save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id, dedupe=effective_clean_restart)
                    return False, "Stopped at step 9: Implementation failed", total_cost, model_used, []
                # Reviewer 6th-pass (F2): same fix as the resume path above —
                # use the multi-line + bullet-aware extractor so Step 10's
                # discovery sweep sees the full list, not the first line.
                context["files_created"] = ", ".join(_extract_marker_paths("FILES_CREATED", step_output))
                context["files_modified"] = ", ".join(_extract_marker_paths("FILES_MODIFIED", step_output))
                context["direct_edits"] = ", ".join(_extract_marker_paths("DIRECT_EDITS", step_output))
            if not extracted_files and worktree_path:
                # Fallback: check worktree for actual file changes
                # Pass direct_edit_candidates so those files are also detected
                dec = context.get("direct_edit_candidates", [])
                extracted_files = _detect_worktree_changes(worktree_path, dec)
                if extracted_files and not quiet:
                    console.print(f"[yellow]Note: Detected {len(extracted_files)} changed file(s) in worktree (LLM output lacked markers)[/yellow]")
            changed_files = extracted_files
            context["files_to_stage"] = ", ".join(changed_files)
            if not changed_files:
                # Save step output for debugging before failing
                # Issue #467: Mark as FAILED instead of using step_num - 1
                state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"
                # Don't advance last_completed_step — keep it at its current value
                state["step_comments"] = sorted(step_comments_set)
                save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id, dedupe=effective_clean_restart)
                return False, "Stopped at step 9: Implementation produced no file changes", total_cost, model_used, []

        if step_num == 10:
            arch_files = (
                _step10_changed_files_from_json(step_json)
                if _valid_step_json(10, step_json)
                else _parse_changed_files(step_output)
            )
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

            # Step 10.5: verify associated-document contract.
            # Every doc discover_associated_documents returned must be either
            # modified, explicitly flagged as a conflict, or declared unchanged
            # — and only ONE of the three per doc. Silent drops (doc in no
            # bucket) and overlaps (doc in multiple buckets) are both workflow
            # regressions the verifier is built to catch before the change ships.
            discovered_docs = context.get("_associated_documents_discovered", [])
            if discovered_docs:
                (
                    _docs_mod,
                    _docs_conflict,
                    _docs_unchanged,
                    dropped,
                    overlapping,
                ) = _verify_doc_sync_contract(
                    discovered_docs=discovered_docs,
                    step10_output=step_output,
                    step10_json=step_json if _valid_step_json(10, step_json) else None,
                )
                violations: List[str] = []
                warning_lines: List[str] = []
                marker_lines: List[str] = []
                if dropped:
                    drop_list = ", ".join(dropped)
                    violations.append(f"silent drops: {drop_list}")
                    warning_lines.extend(
                        f"- Associated doc silently dropped by Step 10: {d}"
                        for d in dropped
                    )
                    marker_lines.append(f"DOC_SYNC_SILENT_DROPS: {drop_list}")
                if overlapping:
                    overlap_list = ", ".join(overlapping)
                    violations.append(f"contradictory state: {overlap_list}")
                    warning_lines.extend(
                        f"- Associated doc placed in multiple buckets by Step 10: {d}"
                        for d in overlapping
                    )
                    marker_lines.append(
                        f"DOC_SYNC_BUCKET_OVERLAPS: {overlap_list}"
                    )

                if violations:
                    step_output = (
                        step_output.rstrip()
                        + "\n\nORCHESTRATOR_POSTCHECK_WARNINGS:\n"
                        + "\n".join(warning_lines)
                        + "\n"
                        + "\n".join(marker_lines)
                    )
                    if not quiet:
                        if dropped:
                            console.print(
                                f"[yellow]Step 10.5 contract check: "
                                f"{len(dropped)} associated doc(s) silently dropped "
                                f"by Step 10 — {', '.join(dropped)}[/yellow]"
                            )
                        if overlapping:
                            console.print(
                                f"[yellow]Step 10.5 contract check: "
                                f"{len(overlapping)} associated doc(s) placed in "
                                f"multiple buckets by Step 10 — "
                                f"{', '.join(overlapping)}[/yellow]"
                            )

                    # Strict mode: when PDD_STRICT_DOC_SYNC=1, any contract
                    # violation (silent drop or overlap) aborts the workflow
                    # instead of being passed to the review loop. Default is
                    # non-strict (warn-only) so the review loop has a chance
                    # to recover.
                    if os.environ.get("PDD_STRICT_DOC_SYNC", "").lower() in ("1", "true", "yes"):
                        if not quiet:
                            console.print(
                                f"[red]PDD_STRICT_DOC_SYNC=1 — aborting on "
                                f"doc-sync contract violation(s).[/red]"
                            )
                        state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"
                        save_workflow_state(
                            cwd, issue_number, "change", state, state_dir,
                            repo_owner, repo_name, use_github_state, github_comment_id,
                            dedupe=effective_clean_restart,
                        )
                        return (
                            False,
                            f"Stopped at step 10: PDD_STRICT_DOC_SYNC {'; '.join(violations)}",
                            total_cost, model_used, changed_files,
                        )

        context[f"step{step_num}_output"] = step_output
        if step_success:
            consecutive_provider_failures = 0
            state["step_outputs"][str(step_num)] = step_output
            state["last_completed_step"] = step_num
            # Trusted per-step success comment (post once per step)
            try:
                report_body = _comment_body_from_artifact(
                    artifacts_dir,
                    _step_artifact_stem(step_num, name),
                    step_output,
                    (
                        f"Step {step_num} completed; no `<step_report>` block returned by agent. "
                        "Raw output retained in workflow state."
                    ),
                )
                body = f"## Step {step_num}/13: {description}\n\n{report_body}"
                post_step_comment_once(
                    repo_owner=repo_owner,
                    repo_name=repo_name,
                    issue_number=issue_number,
                    step_num=step_num,
                    body=body,
                    posted_steps=step_comments_set,
                    cwd=cwd,
                )
            except Exception as _exc:
                console.print(f"[yellow]Warning: failed to post step comment for step {step_num}: {_exc}[/yellow]")
            state["step_comments"] = sorted(step_comments_set)
        else:
            state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"

        save_result = save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id, dedupe=effective_clean_restart)
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
            artifacts_dir = _artifacts_dir_for(current_work_dir, issue_number)
            context["artifacts_dir"] = str(artifacts_dir)
            s11_template = load_prompt_template("agentic_change_step11_identify_issues_LLM")
            context["review_iteration"] = review_iteration
            context["previous_fixes"] = previous_fixes
            s11_expects_artifacts = bool(s11_template and "{artifacts_dir}" in s11_template)
            # Preprocess to escape curly braces in included content
            exclude = list(context.keys())
            s11_template = preprocess(s11_template, recursive=True, double_curly_brackets=True, exclude=exclude)
            s11_prompt = substitute_template_variables(s11_template, context)
            timeout11 = CHANGE_STEP_TIMEOUTS.get(11, 340.0) + timeout_adder
            _clear_step_artifacts(artifacts_dir, 11, "review")
            s11_success, s11_output, s11_cost, s11_model = run_agentic_task(
                instruction=s11_prompt, cwd=current_work_dir, verbose=verbose, quiet=quiet, timeout=timeout11, label=f"step11_iter{review_iteration}", max_retries=DEFAULT_MAX_RETRIES, reasoning_time=reasoning_time, steers=_issue_step_steers() or None,
                before_attempt=lambda _provider, _attempt: _clear_step_artifacts(
                    artifacts_dir, 11, "review"
                ),
            )
            total_cost += s11_cost; model_used = s11_model; state["total_cost"] = total_cost
            initial_s11_success = s11_success
            initial_s11_output = s11_output
            s11_json = _read_step_json(artifacts_dir, "11_review.json")
            if s11_expects_artifacts and not _valid_step_json(11, s11_json):
                if not quiet:
                    console.print("[yellow]Step 11 did not write valid 11_review.json; rerunning once before prose fallback.[/yellow]")
                _clear_step_artifacts(artifacts_dir, 11, "review")
                s11_success, s11_output, s11_cost, s11_model = run_agentic_task(
                    instruction=s11_prompt, cwd=current_work_dir, verbose=verbose, quiet=quiet, timeout=timeout11, label=f"step11_iter{review_iteration}_json_retry", max_retries=DEFAULT_MAX_RETRIES, reasoning_time=reasoning_time, steers=_issue_step_steers() or None,
                    before_attempt=lambda _provider, _attempt: _clear_step_artifacts(
                        artifacts_dir, 11, "review"
                    ),
                )
                total_cost += s11_cost; model_used = s11_model; state["total_cost"] = total_cost
                s11_json = _read_step_json(artifacts_dir, "11_review.json")
            if not _valid_step_json(11, s11_json):
                if not quiet and s11_expects_artifacts:
                    console.print("[yellow]Step 11 JSON unavailable after retry; using prose fallback.[/yellow]")
                if initial_s11_success:
                    s11_success = initial_s11_success
                    s11_output = initial_s11_output
                    _clear_step_artifacts(artifacts_dir, 11, "review")
                s11_json = None
            s11_manual = _manual_review_lines_from_json(s11_json)
            if not s11_manual and s11_json is None:
                s11_manual = _collect_manual_review_lines(s11_output)
            if s11_manual:
                review_manual_review_json_lines = _dedupe_preserve_order(
                    [*review_manual_review_json_lines, *s11_manual.splitlines()]
                )
                state["review_manual_review_json_lines"] = review_manual_review_json_lines
            # Trusted post for Step 11 (iteration-keyed: iter * 100 + 11)
            if s11_success:
                try:
                    s11_iter_key = review_iteration * 100 + 11
                    s11_report = _comment_body_from_artifact(
                        artifacts_dir,
                        "11_review",
                        s11_output,
                        (
                            f"Step 11 (review iteration {review_iteration}) completed; "
                            "no `<step_report>` block returned by agent. "
                            "Raw output retained in workflow state."
                        ),
                    )
                    post_step_comment_once(
                        repo_owner=repo_owner, repo_name=repo_name,
                        issue_number=issue_number, step_num=s11_iter_key,
                        body=f"## Step 11/13: Identify Issues (iter {review_iteration})\n\n{s11_report}",
                        posted_steps=step_comments_set, cwd=cwd,
                    )
                    state["step_comments"] = sorted(step_comments_set)
                except Exception as _exc:
                    console.print(f"[yellow]Warning: failed to post step 11 comment: {_exc}[/yellow]")
            review_clean = (
                str(s11_json.get("status", "")).strip() == "clean"
                if isinstance(s11_json, dict)
                else _review_loop_no_issues(s11_output)
            )
            if review_clean:
                if not quiet: console.print("   -> No issues found. Proceeding to PR.")
                context["step11_output"] = s11_output; break
            if not quiet: console.print("   -> Issues found. Proceeding to fix.")
            if not quiet:
                console.print(f"[bold][Step 12/13][/bold] Fixing issues (iteration {review_iteration}/{MAX_REVIEW_ITERATIONS})...")
            artifacts_dir = _artifacts_dir_for(current_work_dir, issue_number)
            context["artifacts_dir"] = str(artifacts_dir)
            s12_template = load_prompt_template("agentic_change_step12_fix_issues_LLM")
            context["step11_output"] = s11_output
            s12_expects_artifacts = bool(s12_template and "{artifacts_dir}" in s12_template)
            # Preprocess to escape curly braces in included content
            exclude = list(context.keys())
            s12_template = preprocess(s12_template, recursive=True, double_curly_brackets=True, exclude=exclude)
            s12_prompt = substitute_template_variables(s12_template, context)
            timeout12 = CHANGE_STEP_TIMEOUTS.get(12, 600.0) + timeout_adder
            _clear_step_artifacts(artifacts_dir, 12, "fix")
            s12_success, s12_output, s12_cost, s12_model = run_agentic_task(
                instruction=s12_prompt, cwd=current_work_dir, verbose=verbose, quiet=quiet, timeout=timeout12, label=f"step12_iter{review_iteration}", max_retries=DEFAULT_MAX_RETRIES, reasoning_time=reasoning_time, steers=_issue_step_steers() or None,
                single_provider_attempt=_single_provider_attempt_for_step(12),
                before_attempt=lambda _provider, _attempt: _clear_step_artifacts(
                    artifacts_dir, 12, "fix"
                ),
            )
            total_cost += s12_cost; model_used = s12_model; state["total_cost"] = total_cost
            initial_s12_success = s12_success
            initial_s12_output = s12_output
            s12_json_repair_reran = False
            s12_json = _read_step_json(artifacts_dir, "12_fix.json")
            if (
                s12_expects_artifacts
                and not _valid_step_json(12, s12_json)
                and _allow_json_repair_rerun(12)
            ):
                if not quiet:
                    console.print("[yellow]Step 12 did not write valid 12_fix.json; rerunning once before prose fallback.[/yellow]")
                s12_json_repair_reran = True
                _clear_step_artifacts(artifacts_dir, 12, "fix")
                s12_success, s12_output, s12_cost, s12_model = run_agentic_task(
                    instruction=s12_prompt, cwd=current_work_dir, verbose=verbose, quiet=quiet, timeout=timeout12, label=f"step12_iter{review_iteration}_json_retry", max_retries=DEFAULT_MAX_RETRIES, reasoning_time=reasoning_time, steers=_issue_step_steers() or None,
                    single_provider_attempt=_single_provider_attempt_for_step(12),
                    before_attempt=lambda _provider, _attempt: _clear_step_artifacts(
                        artifacts_dir, 12, "fix"
                    ),
                )
                total_cost += s12_cost; model_used = s12_model; state["total_cost"] = total_cost
                s12_json = _read_step_json(artifacts_dir, "12_fix.json")
            if not _valid_step_json(12, s12_json):
                if not quiet and s12_expects_artifacts:
                    if s12_json_repair_reran:
                        console.print("[yellow]Step 12 JSON unavailable after retry; using prose fallback.[/yellow]")
                    else:
                        console.print("[yellow]Step 12 JSON unavailable; using prose fallback without rerun.[/yellow]")
                if initial_s12_success:
                    s12_success = initial_s12_success
                    s12_output = initial_s12_output
                    _clear_step_artifacts(artifacts_dir, 12, "fix")
                s12_json = None
            s12_manual = _manual_review_lines_from_json(s12_json)
            if not s12_manual and s12_json is None:
                s12_manual = _collect_manual_review_lines(s12_output)
            if s12_manual:
                review_manual_review_json_lines = _dedupe_preserve_order(
                    [*review_manual_review_json_lines, *s12_manual.splitlines()]
                )
                state["review_manual_review_json_lines"] = review_manual_review_json_lines
            # Trusted post for Step 12 (iteration-keyed: iter * 100 + 12)
            if s12_success:
                try:
                    s12_iter_key = review_iteration * 100 + 12
                    s12_report = _comment_body_from_artifact(
                        artifacts_dir,
                        "12_fix",
                        s12_output,
                        (
                            f"Step 12 (review iteration {review_iteration}) completed; "
                            "no `<step_report>` block returned by agent. "
                            "Raw output retained in workflow state."
                        ),
                    )
                    post_step_comment_once(
                        repo_owner=repo_owner, repo_name=repo_name,
                        issue_number=issue_number, step_num=s12_iter_key,
                        body=f"## Step 12/13: Fix Issues (iter {review_iteration})\n\n{s12_report}",
                        posted_steps=step_comments_set, cwd=cwd,
                    )
                    state["step_comments"] = sorted(step_comments_set)
                except Exception as _exc:
                    console.print(f"[yellow]Warning: failed to post step 12 comment: {_exc}[/yellow]")
            previous_fixes += f"\n\nIteration {review_iteration}:\n{s12_output}"
            state["previous_fixes"] = previous_fixes
            state["step_comments"] = sorted(step_comments_set)
            save_result = save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id, dedupe=effective_clean_restart)
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

    if worktree_path:
        gate_worktree = worktree_path
    else:
        gate_worktree = Path(current_work_dir)
    if changed_files:
        try:
            gate_success, gate_message, gate_cost = run_pre_checkup_gate(
                worktree=gate_worktree,
                changed_files=changed_files,
                base_ref=None,
                repo_owner=repo_owner,
                repo_name=repo_name,
                issue_number=issue_number,
                quiet=quiet,
                timeout_per_check=CHANGE_STEP_TIMEOUTS.get(12, 600.0) + timeout_adder,
            )
        except Exception as _exc:  # pylint: disable=broad-except
            gate_success = False
            gate_message = f"pre_checkup_gate blocked; phase=infrastructure error: {_exc}"
            gate_cost = 0.0
        total_cost += gate_cost
        state["total_cost"] = total_cost
        if not gate_success:
            # Issue #1293: block before checkup. Do NOT create the PR when the
            # gate finds mechanical breakage or unhealable drift ("block: don't
            # hand off to checkup until green"; the change/feature path must run
            # the gate too). The gate already applies the strict/non-strict
            # distinction internally (per pre_checkup_gate R7: in default mode a
            # non-fatal drift-sync residual is reported but does NOT flip
            # gate_success, while build/smoke failures and fatal drift always
            # do), so the caller hard-blocks whenever gate_success is False — it
            # must NOT re-check PDD_STRICT_DOC_SYNC and downgrade a real failure
            # to an advisory MANUAL_REVIEW note that still ships a broken PR.
            state["step_outputs"]["12.5"] = f"FAILED: {gate_message}"
            save_workflow_state(
                cwd, issue_number, "change", state, state_dir,
                repo_owner, repo_name, use_github_state, github_comment_id,
                dedupe=effective_clean_restart,
            )
            return (
                False,
                f"Stopped at step 12.5: {gate_message}",
                total_cost, model_used, changed_files,
            )
        # Issue #1293/#1243: the gate's drift-sync runs run_metadata_sync, which
        # writes prompt+code-only fingerprints (example/test hashes are null).
        # Step 13's `git add -A` would otherwise commit those degraded
        # fingerprints into the PR, arming the #1243 null-hash auto-heal loop.
        # Restore tracked .pdd/meta so .pdd/meta fingerprint finalization is
        # deferred to the post-merge sync (#1317) — matching the fix path, which
        # filters .pdd/** from its commit. The gate's prompt / example /
        # architecture sync is committed normally (only .pdd/meta is reverted).
        try:
            subprocess.run(
                ["git", "checkout", "--", ".pdd/meta"],
                cwd=gate_worktree,
                capture_output=True,
                text=True,
                timeout=60,
            )
        except Exception:  # pylint: disable=broad-except
            pass

    story_files_to_stage, user_story_summary, story_cost, story_model, story_block_message = (
        _generate_user_story_artifacts_for_change(
            issue_url=issue_url,
            changed_files=changed_files,
            worktree_path=gate_worktree,
            strength=0.2,
            temperature=0.0,
            time_budget=0.25,
            verbose=verbose,
            quiet=quiet,
        )
    )
    total_cost += story_cost
    if story_model:
        model_used = model_used or story_model
    for story_file in story_files_to_stage:
        if story_file not in changed_files:
            changed_files.append(story_file)
    if story_files_to_stage:
        existing_to_stage = [
            f.strip()
            for f in str(context.get("files_to_stage", "") or "").split(",")
            if f.strip()
        ]
        merged_to_stage = existing_to_stage[:]
        for story_file in story_files_to_stage:
            if story_file not in merged_to_stage:
                merged_to_stage.append(story_file)
        context["files_to_stage"] = ", ".join(merged_to_stage)
    context["user_story_summary"] = user_story_summary
    state["total_cost"] = total_cost

    # Issue #1454: under PDD_STORY_POLICY=strict, block before Step 13 when a
    # changed prompt still has no passing linked story. The default policy
    # (`warn`) only reports coverage in the PR body; `off` skips entirely. This
    # block must run only for `strict` — _generate_user_story_artifacts_for_change
    # returns a non-None message exclusively in that case.
    if story_block_message:
        state["step_outputs"]["12.6"] = f"FAILED: {story_block_message}"
        save_workflow_state(
            cwd, issue_number, "change", state, state_dir,
            repo_owner, repo_name, use_github_state, github_comment_id,
            dedupe=effective_clean_restart,
        )
        return (
            False,
            f"Stopped at step 12.6: {story_block_message}",
            total_cost, model_used, changed_files,
        )

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
        # Aggregate MANUAL_REVIEW lines from accepted JSON-derived state.
        # Do not rescan raw Step 9 prose or previous_fixes here: those strings
        # can contain stale lines from attempts whose JSON was superseded.
        # Step 10's ASSOCIATED_DOCS_CONFLICTS bucket is also funneled here:
        # the verifier treats those entries as "handled" (no silent drop),
        # but the spec calls them "left for human", so each conflict path
        # must surface as a MANUAL_REVIEW line in the PR body.
        s10_out = context.get("step10_output", "") or ""
        s10_json = step_json_outputs.get("10")
        s10_conflict_paths = (
            _json_list(s10_json, "associated_docs_conflicts")
            if _valid_step_json(10, s10_json)
            else _extract_marker_paths("ASSOCIATED_DOCS_CONFLICTS", s10_out)
        )
        synthesized_conflict_lines = "\n".join(
            f"MANUAL_REVIEW: {p} — Step 10 ASSOCIATED_DOCS_CONFLICTS, manual edit needed"
            for p in s10_conflict_paths
        )
        step9_manual_review_source = (
            ""
            if _valid_step_json(9, step_json_outputs.get("9"))
            else (context.get("step9_output", "") or "")
        )
        context["manual_review_lines"] = _collect_manual_review_lines(
            step9_manual_review_source,
            synthesized_conflict_lines,
            "\n".join(manual_review_json_lines),
            "\n".join(review_manual_review_json_lines),
        )
        context["clean_restart"] = "true" if effective_clean_restart else "false"
        git_root_for_pr_base = _get_git_root(current_work_dir) or current_work_dir
        context["base_branch"] = _normalize_pr_base_branch(
            _resolve_main_ref_name(git_root_for_pr_base)
        )
        # Thread the worktree's ACTUAL head branch so a #1596 clean-restart
        # fallback branch is pushed/PR'd, not the (locked) canonical name.
        # Defaults to the canonical name → byte-identical when no fallback.
        context["head_branch"] = (
            current_worktree_branch(current_work_dir) or f"change/issue-{issue_number}"
        )
        artifacts_dir = _artifacts_dir_for(current_work_dir, issue_number)
        context["artifacts_dir"] = str(artifacts_dir)
        if not quiet: console.print("[bold][Step 13/13][/bold] Create PR and link to issue...")
        s13_template = load_prompt_template("agentic_change_step13_create_pr_LLM")
        s13_expects_artifacts = bool(s13_template and "{artifacts_dir}" in s13_template)
        # Preprocess to escape curly braces in included content
        exclude = list(context.keys())
        s13_template = preprocess(s13_template, recursive=True, double_curly_brackets=True, exclude=exclude)
        s13_prompt = substitute_template_variables(s13_template, context)
        timeout13 = CHANGE_STEP_TIMEOUTS.get(13, 340.0) + timeout_adder
        _clear_step_artifacts(artifacts_dir, 13, "create_pr")
        s13_success, s13_output, s13_cost, s13_model = run_agentic_task(
            instruction=s13_prompt, cwd=current_work_dir, verbose=verbose, quiet=quiet, timeout=timeout13, label="step13", max_retries=DEFAULT_MAX_RETRIES, reasoning_time=reasoning_time, steers=_issue_step_steers() or None,
            before_attempt=lambda _provider, _attempt: _clear_step_artifacts(
                artifacts_dir, 13, "create_pr"
            ),
            single_provider_attempt=True,
        )
        total_cost += s13_cost; model_used = s13_model; state["total_cost"] = total_cost
        initial_s13_success = s13_success
        initial_s13_output = s13_output
        s13_json = _read_step_json(artifacts_dir, "13_create_pr.json")
        initial_s13_status, initial_s13_pr_url = _step13_result_from_json_or_output(
            None,
            initial_s13_output,
        )
        initial_s13_has_any_pr_url = (
            initial_s13_success
            and initial_s13_pr_url != "Unknown"
        )
        initial_s13_has_pr_url = (
            initial_s13_success
            and _valid_pr_url(initial_s13_pr_url, repo_owner, repo_name)
        )
        s13_uses_accepted_json = _valid_step_json(13, s13_json)
        existing_s13_pr = None
        if s13_expects_artifacts and not initial_s13_has_any_pr_url and not _valid_step_json(13, s13_json):
            existing_s13_pr = _open_pr_for_head_branch(
                repo_owner,
                repo_name,
                context["head_branch"],
                context["base_branch"],
                current_work_dir,
            )
            if existing_s13_pr:
                s13_json = {
                    "status": "pr_updated",
                    "pr_url": existing_s13_pr["url"],
                    "pr_number": existing_s13_pr.get("number"),
                    "summary": "reused existing open PR for head branch",
                }
                s13_success = True
                s13_output = (
                    f"PR Updated: {existing_s13_pr['url']}\n"
                    "Recovered existing open PR for this head branch."
                )
                s13_uses_accepted_json = False
        if initial_s13_has_pr_url and not _valid_step_json(13, s13_json):
            s13_json = {
                "status": (
                    initial_s13_status
                    if initial_s13_status in {"pr_created", "pr_updated"}
                    else "pr_created"
                ),
                "pr_url": initial_s13_pr_url,
            }
            s13_uses_accepted_json = False
        if not _valid_step_json(13, s13_json):
            if not quiet and s13_expects_artifacts:
                console.print("[yellow]Step 13 JSON unavailable; using prose fallback.[/yellow]")
            if initial_s13_success:
                s13_success = initial_s13_success
                s13_output = initial_s13_output
                _clear_step_artifacts(artifacts_dir, 13, "create_pr")
            s13_json = None
            s13_uses_accepted_json = False
        if (
            not initial_s13_has_any_pr_url
            and not (
                isinstance(s13_json, dict)
                and str(s13_json.get("status", "")).strip() in {"pr_created", "pr_updated"}
                and _valid_pr_url(s13_json.get("pr_url"), repo_owner, repo_name)
            )
        ):
            recovered_s13_pr = _open_pr_for_head_branch(
                repo_owner,
                repo_name,
                context["head_branch"],
                context["base_branch"],
                current_work_dir,
            )
            if recovered_s13_pr:
                s13_json = {
                    "status": "pr_updated",
                    "pr_url": recovered_s13_pr["url"],
                    "pr_number": recovered_s13_pr.get("number"),
                    "summary": "recovered existing open PR for head branch",
                }
                step_json_outputs["13"] = s13_json
                s13_success = True
                s13_output = (
                    f"PR Updated: {recovered_s13_pr['url']}\n"
                    "Recovered existing open PR for this head branch."
                )
                s13_uses_accepted_json = False
        s13_status, pr_url = _step13_result_from_json_or_output(s13_json, s13_output)
        if s13_status == "blocked":
             post_step_comment(repo_owner, repo_name, issue_number, 13, 13, "Create PR and link to issue", s13_output, cwd)
             console.print("[red]Step 13 (PR Creation) blocked.[/red]")
             state["step_comments"] = sorted(step_comments_set)
             save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id, dedupe=effective_clean_restart)
             return False, "PR Creation blocked", total_cost, model_used, changed_files
        if not _valid_pr_url(repo_owner=repo_owner, repo_name=repo_name, value=pr_url):
             post_step_comment(repo_owner, repo_name, issue_number, 13, 13, "Create PR and link to issue", s13_output, cwd)
             console.print("[red]Step 13 (PR Creation) did not return a valid PR URL for this repository.[/red]")
             state["step_comments"] = sorted(step_comments_set)
             save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id, dedupe=effective_clean_restart)
             return False, "PR Creation failed: missing valid PR URL", total_cost, model_used, changed_files
        if not _pr_url_matches_current_head(
            repo_owner,
            repo_name,
            pr_url,
            context["head_branch"],
            context["base_branch"],
            current_work_dir,
        ):
             post_step_comment(repo_owner, repo_name, issue_number, 13, 13, "Create PR and link to issue", s13_output, cwd)
             console.print("[red]Step 13 (PR Creation) returned a PR that does not match this branch/head.[/red]")
             state["step_comments"] = sorted(step_comments_set)
             save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id, dedupe=effective_clean_restart)
             return False, "PR Creation failed: PR does not match current branch", total_cost, model_used, changed_files
        s13_success = True
        if _valid_step_json(13, s13_json):
            step_json_outputs["13"] = s13_json
        if not s13_uses_accepted_json:
            _clear_step_artifacts(artifacts_dir, 13, "create_pr")
        # Trusted per-step success comment for Step 13
        try:
            s13_report = _comment_body_from_artifact(
                artifacts_dir,
                "13_create_pr",
                s13_output,
                (
                    "Step 13 completed; no `<step_report>` block returned by agent. "
                    "Raw output retained in workflow state."
                ),
            )
            post_step_comment_once(
                repo_owner=repo_owner, repo_name=repo_name,
                issue_number=issue_number, step_num=13,
                body=f"## Step 13/13: Create PR and link to issue\n\n{s13_report}",
                posted_steps=step_comments_set, cwd=cwd,
            )
            state["step_comments"] = sorted(step_comments_set)
        except Exception as _exc:
            console.print(f"[yellow]Warning: failed to post step 13 comment: {_exc}[/yellow]")
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
