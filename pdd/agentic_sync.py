"""
Agentic sync: LLM-driven module identification and parallel sync orchestration.

Entry point for `pdd sync <github_issue_url>`. Fetches issue content, uses an LLM
to determine which modules need syncing and validate architecture.json dependencies,
then dispatches to the async sync runner for parallel execution.
"""
from __future__ import annotations

import fnmatch
import glob
import json
import logging
import os
import re
import secrets
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Dict, List, NamedTuple, Optional, Tuple

from rich.console import Console

from .agentic_change import _check_gh_cli, _escape_format_braces, _parse_issue_url, _run_gh_command
from .agentic_common import (
    _PROVIDER_ENVIRONMENT_PROVIDERS,
    _PROVIDER_ENVIRONMENT_REASONS,
    _PROVIDER_FAILURE_SINK_ENV,
    _PROVIDER_FAILURE_TOKEN_ENV,
    _consume_provider_failure_sink,
    _publish_provider_failure_sink,
    _sanitize_comment_body,
    build_agentic_task_instruction,
    run_agentic_task,
)
from .agentic_sync_runner import (
    AsyncSyncRunner,
    _architecture_entry_aliases,
    _basename_from_architecture_filename,
    _find_pdd_executable,
    build_dep_graph_from_architecture_data,
)
from .durable_sync_runner import DurableSyncRunner
from .architecture_include_validation import (
    collect_architecture_include_validation_warnings,
    resolve_architecture_prompt_path,
    validate_prompt_contract_context,
)
from .sync_graph_order_consistency import warnings_for_arch_vs_include_sync_order
from .architecture_registry import (
    extract_modules,
    find_architecture_for_project,
    find_project_root as _find_project_root,
)
from .construct_paths import (
    _detect_context_from_basename,
    _extract_prefix_from_prompts_dir,
    _find_nearest_pddrc_for_file,
    _find_pddrc_file,
    _load_pddrc_config,
)
from .json_atomic import atomic_write_json
from .load_prompt_template import load_prompt_template
from .resolved_sync_unit import ResolvedSyncUnit, resolve_sync_unit
from .sync_plan import (
    PlanProvenance,
    SyncPlan,
    SyncPlanCandidate,
    SyncPlanDetails,
    SyncPlanError,
    build_sync_plan,
    canonical_module_id,
)
from .sync_determine_operation import sync_determine_operation
from .sync_main import _detect_languages_with_context
from .sync_order import build_dependency_graph, extract_module_from_include, topological_sort

# Issue #1714: bound agentic-step stall duration well under the 600s
# DEFAULT_TIMEOUT_SECONDS so a silent provider hang (spinner-only output) fails
# fast instead of burning the full per-step budget (~$2.22/hang in the report).
IDENTIFY_MODULES_TIMEOUT_SECONDS: float = 400.0  # module-discovery step
FIX_DRY_RUN_TIMEOUT_SECONDS: float = 240.0  # quick dry-run repair suggestion
# Issue #1714 no-progress watchdog windows. These reasoning/discovery steps run
# no long-lived tools, so a session transcript that stays quiescent this long
# signals a parked/spinner-only stall (the 600s hang in the report), not real
# work — abort well before the hard timeout. Set above the observed healthy run
# time (~221s for identify) so a legitimately slow run can never trip it.
IDENTIFY_MODULES_STALL_SECONDS: float = 240.0
FIX_DRY_RUN_STALL_SECONDS: float = 180.0

console = Console()

_GLOBAL_SYNC_NOOP_OPERATIONS = {"nothing", "all_synced"}
_GLOBAL_SYNC_TIER1_OPERATIONS = {"generate", "auto-deps"}
_SYNC_DETERMINE_LOGGER_NAME = "pdd.sync_determine_operation"

def _is_github_issue_url(s: str) -> bool:
    """Check if a string looks like a GitHub issue URL."""
    return bool(re.search(r"github\.com/.+/issues/\d+", s))


def _is_runtime_llm_template(basename: str) -> bool:
    """Return True if ``basename`` refers to a runtime ``*_LLM.prompt`` template.

    Runtime LLM templates (e.g. ``agentic_sync_identify_modules_LLM``) are
    consumed directly by their owning code module via
    ``load_prompt_template(...)`` and have no language-suffixed sync companion,
    so ``pdd sync <basename>_LLM`` is guaranteed to fail with
    ``"No prompt files found for basename '<basename>_LLM'"``.

    The match is case-sensitive on the final ``/``-separated segment to avoid
    false positives on legitimate basenames containing lowercase ``llm``. Both
    bare basenames (``foo_LLM``) and filename forms (``foo_LLM.prompt``) are
    classified, so callers may pass either shape without pre-stripping.
    """
    if not basename:
        return False
    tail = basename.rsplit("/", 1)[-1]
    if tail.endswith(".prompt"):
        tail = tail[: -len(".prompt")]
    return tail.endswith("_LLM")


def _strip_language_suffix_preserving_path(module: str) -> Optional[str]:
    """Strip a language suffix from the final path component, preserving folders."""
    module_path = Path(module)
    stripped_tail = extract_module_from_include(f"{module_path.name}.prompt")
    if not stripped_tail:
        return None
    parent = module_path.parent
    if parent == Path("."):
        return stripped_tail
    return str(parent / stripped_tail)


def _normalize_modules_for_sync(
    modules: List[str],
    architecture: Optional[List[Dict[str, Any]]],
) -> List[str]:
    """Normalize candidate modules while preserving exact architecture basenames."""
    known_basenames = set(_architecture_module_basenames(architecture or []))

    normalized: List[str] = []
    for module in modules:
        if module in known_basenames:
            normalized.append(module)
            continue

        stripped = _strip_language_suffix_preserving_path(module)
        normalized.append(stripped if stripped else module)

    return list(dict.fromkeys(normalized))


def _parse_changed_modules_env(value: str) -> List[str]:
    """Parse ``PDD_CHANGED_MODULES`` into an order-preserving module list."""
    if not value:
        return []

    modules: List[str] = []
    seen: set[str] = set()
    for raw_part in value.split(","):
        module = raw_part.strip()
        if not module or module in seen:
            continue
        modules.append(module)
        seen.add(module)
    return modules


def _detect_modules_from_branch_diff(project_root: Path) -> List[str]:
    """Detect modules to sync by diffing the current branch against main.

    When on a feature branch created by ``pdd change``, the changed ``.prompt``
    files are exactly the modules that need syncing.  This is deterministic,
    free, and avoids the LLM identification step that can fail when
    architecture.json lacks ``origin`` fields.

    Returns:
        List of basenames (e.g. ``["ci_validation", "commands/fix"]``), or an
        empty list if we're on main/master or the diff cannot be determined.
    """
    try:
        # 1. Get current branch name
        branch_result = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            cwd=project_root, capture_output=True, text=True, check=True,
        )
        branch = branch_result.stdout.strip()
        if branch in ("main", "master", "HEAD"):
            return []

        # 2. Diff against main to find changed files
        diff_result = subprocess.run(
            ["git", "diff", "main...HEAD", "--name-only", "--diff-filter=ACMR"],
            cwd=project_root, capture_output=True, text=True, check=True,
        )
        changed_files = [f.strip() for f in diff_result.stdout.strip().splitlines() if f.strip()]

        # 3. Filter to .prompt files, excluding LLM templates
        prompt_files = [
            f for f in changed_files
            if f.endswith(".prompt")
            and ("/prompts/" in f or f.startswith("prompts/"))
        ]
        prompt_files = [f for f in prompt_files if not f.endswith("_LLM.prompt")]

        # 4. Extract basenames as repo-root-relative module keys.
        #
        # A prompt lives at ``<project>/prompts/<sub>/<name>_<lang>.prompt``. The
        # module key MUST keep BOTH the owning-project prefix (the path before
        # ``prompts/``) and the sub-path under ``prompts/`` so a nested module
        # like ``extensions/github_pdd_app/prompts/src/worker_app_python.prompt``
        # yields ``extensions/github_pdd_app/src/worker_app`` — not the short
        # ``src/worker_app`` that loses the owning project and resolves to the
        # repo root (#1675). The downstream resolver
        # (_resolve_module_cwd_and_target) then maps that full key back to
        # cwd=extensions/github_pdd_app, target=src/worker_app.
        basenames: List[str] = []
        for pf in prompt_files:
            if pf.startswith("prompts/"):
                project_prefix = ""
                relative = pf[len("prompts/"):]
            else:
                marker = "/prompts/"
                idx = pf.find(marker)
                if idx == -1:
                    continue
                project_prefix = pf[: idx + 1]  # keep trailing slash
                relative = pf[idx + len(marker):]
            # Strip language suffix from filename, preserving the sub-path under
            # prompts/ (e.g. "commands/fix_python.prompt" -> "commands/fix").
            rel_path = Path(relative)
            filename_basename = extract_module_from_include(rel_path.name)
            if not filename_basename:
                continue
            if rel_path.parent != Path("."):
                sub = str(rel_path.parent / filename_basename)
            else:
                sub = filename_basename
            basename = f"{project_prefix}{sub}"
            if basename not in basenames:
                basenames.append(basename)

        return basenames
    except (subprocess.CalledProcessError, OSError):
        return []


def _branch_diff_is_runtime_llm_only(project_root: Path) -> bool:
    """Return True iff the branch diff vs. ``main`` consists only of runtime
    ``*_LLM.prompt`` template changes (with at least one such change present).

    Issue #1396: when an issue/PR only modifies runtime ``*_LLM.prompt``
    templates, ``_detect_modules_from_branch_diff`` filters them out and
    returns ``[]``, which is indistinguishable from "no prompt changes".
    Without this check the caller would fall back to the identify-modules LLM
    and spend an LLM call to (correctly) decide there is nothing to sync.
    Detecting the runtime-only case deterministically lets ``run_agentic_sync``
    return a successful no-op without touching the LLM.

    The "runtime-only" contract requires that *every* file in the branch diff
    is a runtime ``*_LLM.prompt`` template under a ``prompts/`` directory. If
    any non-prompt source file (e.g. Python, tests, configs) or a non-LLM
    prompt change is also present, we cannot treat the diff as a no-op and
    must defer to the LLM fallback so that real code/test changes are not
    silently skipped (issue #1396 review feedback).

    Deletions are included in the diff filter (``ACMRD``): a branch that
    deletes a real prompt/code/test/config file is *not* runtime-only even if
    its other changes are limited to ``*_LLM.prompt`` files (issue #1396
    review round 4 feedback).

    Rename/copy records are evaluated with ``--name-status`` so both the old
    and new paths must satisfy the runtime-template predicate. This prevents a
    rename such as ``foo_python.prompt`` -> ``foo_LLM.prompt`` from being
    mistaken for a runtime-only no-op.
    """
    def is_runtime_prompt_path(path: str) -> bool:
        return (
            _is_runtime_llm_template(path)
            and ("/prompts/" in path or path.startswith("prompts/"))
        )

    try:
        branch_result = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            cwd=project_root, capture_output=True, text=True, check=True,
        )
        branch = branch_result.stdout.strip()
        if branch in ("main", "master", "HEAD"):
            return False

        diff_result = subprocess.run(
            ["git", "diff", "main...HEAD", "--name-status", "--diff-filter=ACMRD"],
            cwd=project_root, capture_output=True, text=True, check=True,
        )
        diff_lines = [
            line.strip()
            for line in diff_result.stdout.strip().splitlines()
            if line.strip()
        ]

        if not diff_lines:
            return False
        for line in diff_lines:
            parts = line.split("\t")
            status = parts[0]
            paths = parts[1:]
            if not paths:
                return False
            if status.startswith(("R", "C")) and len(paths) != 2:
                return False
            if not status.startswith(("R", "C")) and len(paths) != 1:
                return False
            if not all(is_runtime_prompt_path(path) for path in paths):
                return False
        return True
    except (subprocess.CalledProcessError, OSError):
        return False


def _augment_architecture_from_pr_branch(
    architecture: Optional[List[Dict[str, Any]]],
    project_root: Path,
    issue_number: int,
) -> Optional[List[Dict[str, Any]]]:
    """Merge new architecture.json entries from the PR branch for this issue.

    When pdd sync runs from main, architecture.json only contains entries for
    modules that exist on main. If pdd-change created new modules on a
    change/issue-N branch, those entries are missing and _filter_invalid_basenames
    will reject them as hallucinations. This function fetches architecture.json
    from the PR branch and adds any entries whose filename is not already present.

    Discovers all architecture.json files (root + nested like frontend/architecture.json)
    using the same discovery mechanism as _load_architecture_json, then fetches each
    from the PR branch via git show.
    """
    if architecture is None:
        return None

    from .architecture_registry import find_architecture_for_project

    # Discover all architecture files on disk (root + subdirs)
    arch_files = find_architecture_for_project(project_root)
    if not arch_files:
        arch_files = [project_root / "architecture.json"]

    existing_filenames = {
        entry.get("filename")
        for entry in architecture
        if isinstance(entry, dict) and entry.get("filename")
    }

    canonical_ref = f"origin/change/issue-{issue_number}"
    fallback_refs: List[str] = []
    try:
        ref_result = subprocess.run(
            [
                "git",
                "for-each-ref",
                "--sort=-committerdate",
                "--format=%(refname:short)",
                f"refs/remotes/origin/change/issue-{issue_number}-job-*",
            ],
            cwd=project_root,
            capture_output=True,
            text=True,
            check=True,
        )
        seen_refs = {canonical_ref}
        for line in ref_result.stdout.splitlines():
            ref = line.strip()
            if ref and ref not in seen_refs:
                fallback_refs.append(ref)
                seen_refs.add(ref)
    except (subprocess.CalledProcessError, OSError):
        pass

    # Consult the newest clean-restart fallback branch (if any) plus the canonical
    # branch. `for-each-ref` is sorted by -committerdate, so fallback_refs[0] is the
    # most recently committed change/issue-N-job-* ref; only that one is used, because
    # each clean-restart attempt creates a fresh job branch and older job branches are
    # abandoned (consulting all of them would revive stale module names and scale the
    # git-show work with the number of accumulated remote refs).
    #
    # The fallback is listed BEFORE canonical so that, when both branches define the
    # same filename, the active clean-restart branch's entry wins the filename-dedup
    # below: clean-restart branches the job fallback from main and deliberately abandons
    # the canonical change/issue-N branch, so canonical's metadata is stale. Canonical is
    # still consulted for entries unique to it, so a plain (non-clean-restart)
    # canonical-only new module is never dropped.
    branch_refs = fallback_refs[:1] + [canonical_ref]

    for arch_path in arch_files:
        try:
            rel_path = arch_path.relative_to(project_root)
        except ValueError:
            continue

        for branch_ref in branch_refs:
            try:
                result = subprocess.run(
                    ["git", "show", f"{branch_ref}:{rel_path.as_posix()}"],
                    cwd=project_root,
                    capture_output=True,
                    text=True,
                    check=True,
                )
                pr_arch = json.loads(result.stdout)
            except (subprocess.CalledProcessError, json.JSONDecodeError, OSError):
                continue

            pr_modules = extract_modules(pr_arch)
            for entry in pr_modules:
                filename = entry.get("filename")
                if not filename or filename in existing_filenames:
                    continue
                architecture.append(entry)
                existing_filenames.add(filename)

    return architecture


def _filter_invalid_basenames(
    modules: List[str],
    architecture: Optional[List[Dict[str, Any]]],
) -> Tuple[List[str], List[str]]:
    """Filter out basenames that don't exist in architecture.json.

    LLMs sometimes hallucinate plausible-sounding basenames (e.g.,
    'agentic_e2e_fix_step1_understand' instead of the real
    'agentic_e2e_fix_step1_unit_tests'). This pre-validation prevents
    hallucinated names from failing dry-run and blocking the entire sync.

    Returns:
        (valid_basenames, invalid_basenames)
    """
    candidate_modules = [m for m in modules if not _is_runtime_llm_template(m)]
    invalid = [m for m in modules if _is_runtime_llm_template(m)]

    if architecture is None:
        return candidate_modules, invalid

    # Build basename counts from architecture.json filenames.
    # A count > 1 means the basename is ambiguous (e.g. "auth" from both
    # commands/auth_python.prompt and server/routes/auth_python.prompt).
    from collections import Counter
    basename_counts: Counter = Counter()
    for entry in architecture:
        if not isinstance(entry, dict):
            continue
        filename = entry.get("filename", "")
        if not filename:
            continue
        # Skip runtime *_LLM.prompt entries entirely — they are not syncable
        # modules and must not contribute either the bare `_LLM` basename or a
        # stripped owner-style basename to known_basenames. Otherwise a
        # hallucinated `<basename>_LLM` (or `<basename>` derived from stripping
        # `_LLM`) would be marked valid by the fallback below.
        if filename.endswith("_LLM.prompt"):
            continue

        # Try standard extraction (handles _python.prompt, _typescript.prompt, etc.)
        basename = extract_module_from_include(filename)
        if basename:
            basename_counts[basename] += 1
        else:
            # Fallback for non-prompt filenames (e.g. "GitHubAppCTA.tsx" from
            # frontend/architecture.json). Strip known code extensions first,
            # then .prompt suffix.
            stem = filename
            for ext in (".tsx", ".ts", ".jsx", ".js", ".py", ".prompt"):
                if stem.endswith(ext):
                    stem = stem[: -len(ext)]
                    break
            if stem:
                basename_counts[stem] += 1

        # Also extract basename from filepath (e.g. "src/app/dashboard/page.tsx"
        # -> "page"). The filename field may use a different convention
        # (e.g. "dashboardPage.tsx") that doesn't match the prompt basename.
        filepath = entry.get("filepath", "")
        if filepath and not filepath.endswith("_LLM.prompt"):
            fp_stem = Path(filepath).stem  # "page" from "page.tsx"
            if fp_stem and fp_stem not in basename_counts:
                basename_counts[fp_stem] += 1

    known_basenames = set(basename_counts.keys())

    valid = []
    for m in candidate_modules:
        if m in known_basenames:
            # Exact match (e.g. "agentic_bug_orchestrator")
            valid.append(m)
        elif "/" in m:
            tail = m.rsplit("/", 1)[-1]
            if tail in known_basenames:
                # Path-qualified basename from branch diff (e.g.
                # "frontend/components/layout/Sidebar"). The directory path
                # already disambiguates even if the bare tail appears multiple
                # times (e.g. both root and frontend architecture have "Sidebar"
                # entries for the same module's prompt and code files).
                valid.append(m)
            else:
                # Tail not found in any architecture entry.
                invalid.append(m)
        else:
            invalid.append(m)
    return valid, invalid


def _architecture_outputs_by_basename(project_root: Path) -> Dict[str, set]:
    """Map each bare module basename to the set of distinct output files it produces.

    Issue #1677: scans every working-tree ``architecture.json`` under ``project_root``
    (root + nested) and resolves each entry's ``filepath`` against ITS OWN architecture
    directory, so identity is compared by real on-disk file. This is what makes
    ambiguity detection correct for the combined multi-architecture view that
    ``load_combined_architecture_data`` concatenates without normalization:

    * the SAME file declared in both a root (``frontend/src/page.tsx``) and a nested
      (``frontend/architecture.json`` -> ``src/page.tsx``) architecture resolves to
      one absolute path -> counted once (not ambiguous); while
    * same-named modules in different sub-projects (``appA/src/page.tsx`` vs
      ``appB/src/page.tsx``, both spelled ``src/page.tsx`` relative to their own
      arch) resolve to different absolute paths -> counted as two (ambiguous).

    Output identity is extension-insensitive so a module that merely exists in two
    languages (``foo.py`` + ``foo.ts``) is one entry, not a false ambiguity. A module
    is identified by its prompt FILENAME basename (``extract_module_from_include``,
    which strips any directory prefix and the language suffix); for an architecture
    entry whose ``filename`` is a non-prompt source file (e.g. ``GitHubAppCTA.tsx`` in
    a frontend ``architecture.json``) the filepath stem is used instead — mirroring
    how ``_filter_invalid_basenames`` derives known basenames. ``*_LLM.prompt`` runtime
    templates are skipped.

    The on-disk architecture is the correct basis: a child ``pdd sync`` (and its
    dry-run validation) resolves the bare name against this same working tree, so the
    name is ambiguous exactly when the working tree maps it to more than one file. PR
    refs are intentionally not consulted — a module that exists only on a remote ref
    cannot be (mis)generated by the child sync anyway, and reading refs would both
    over-flag and reintroduce stale clean-restart entries.
    """
    outputs: Dict[str, set] = {}
    for arch_path in find_architecture_for_project(project_root):
        try:
            data = json.loads(arch_path.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            continue
        arch_dir = arch_path.parent
        for entry in extract_modules(data):
            if not isinstance(entry, dict):
                continue
            filename = entry.get("filename", "") or ""
            if filename.endswith("_LLM.prompt"):
                continue
            filepath = str(entry.get("filepath") or "").strip()
            if not filepath:
                continue
            # Prompt filename -> prompt basename; non-prompt filename -> filepath stem.
            basename = extract_module_from_include(filename) or Path(filepath).stem
            if not basename:
                continue
            candidate = Path(filepath)
            if not candidate.is_absolute():
                candidate = arch_dir / candidate
            identity = candidate.resolve(strict=False).with_suffix("").as_posix()
            outputs.setdefault(basename, set()).add(identity)
    return outputs


def _drop_ambiguous_basenames(
    modules: List[str],
    project_root: Path,
) -> Tuple[List[str], Dict[str, List[str]]]:
    """Drop bare basenames that map to more than one architecture module.

    Issue #1677: a short leaf name such as ``page`` (Next.js) is not a stable
    module identity. If it resolves to several distinct architecture outputs, the
    child ``pdd sync`` job would silently pick one (or write a wrong default path),
    so it must not be dispatched. Path-qualified names (containing ``/``, e.g. the
    ``frontend/app/login/page`` produced by ``_detect_modules_from_branch_diff``)
    are already disambiguated by their directory and are always kept, as are bare
    names that map to a single canonical output (see
    :func:`_architecture_outputs_by_basename`).

    Returns ``(kept, ambiguous)`` where ``ambiguous`` maps each dropped bare name
    to the sorted list of conflicting canonical output paths.
    """
    outputs = _architecture_outputs_by_basename(project_root)
    if not outputs:
        return list(modules), {}

    kept: List[str] = []
    ambiguous: Dict[str, List[str]] = {}
    for module in modules:
        if "/" in module:
            kept.append(module)
            continue
        targets = outputs.get(module, set())
        if len(targets) > 1:
            ambiguous[module] = sorted(targets)
        else:
            kept.append(module)
    return kept, ambiguous


def _load_architecture_json(
    project_root: Path,
    issue_number: Optional[int] = None,
) -> Tuple[Optional[List[Dict[str, Any]]], Path]:
    """
    Load architecture.json from the project root.

    If multiple architecture files exist (root + subdirs), loads and combines them.

    Args:
        project_root: Root directory of the project.
        issue_number: Optional issue number for logging origin info (reserved).

    Returns:
        Tuple of (parsed data or None, path to primary architecture.json).
    """
    from .architecture_registry import load_combined_architecture_data

    _ = issue_number  # reserved for future origin-aware loading
    return load_combined_architecture_data(project_root)


def _sync_determine_operation_readonly(**kwargs: Any) -> Any:
    """Call sync_determine_operation without mutations or info log noise."""
    sync_logger = logging.getLogger(_SYNC_DETERMINE_LOGGER_NAME)
    previous_level = sync_logger.level
    sync_logger.setLevel(logging.WARNING)
    try:
        kwargs["read_only"] = True
        return sync_determine_operation(**kwargs)
    finally:
        sync_logger.setLevel(previous_level)


def _run_readonly_sync_determine_in_cwd(cwd: Path, **kwargs: Any) -> Any:
    """Run read-only sync analysis from the module's resolved cwd."""
    previous_cwd = Path.cwd()
    try:
        os.chdir(cwd)
        return _sync_determine_operation_readonly(**kwargs)
    finally:
        os.chdir(previous_cwd)


class GlobalSyncAnalysis(NamedTuple):
    """Read-only analysis result for no-argument global sync."""

    modules_to_sync: List[str]
    module_cwds: Dict[str, Path]
    module_targets: Dict[str, str]
    estimated_cost: float
    module_operations: Dict[str, List[str]]
    skipped_modules: List[str]
    all_modules: List[str]
    # Per-module context resolved against each module's own .pddrc (#1675).
    # Defaulted so existing positional/keyword constructions stay valid.
    module_contexts: Optional[Dict[str, Optional[str]]] = None
    # Canonical per-module identity (#1675); keyed by scheduler key.
    module_units: Optional[Dict[str, ResolvedSyncUnit]] = None


class GlobalSyncModule(NamedTuple):
    """Scoped global-sync module identity."""

    key: str
    basename: str
    cwd: Path
    architecture_path: Path
    entry: Dict[str, Any]
    aliases: Tuple[Tuple[Path, str], ...] = ()
    dependency_scopes: Tuple[Tuple[Path, Tuple[Any, ...]], ...] = ()
    sync_candidates: Tuple[Tuple[str, Path], ...] = ()


def _architecture_module_basenames(architecture: List[Dict[str, Any]]) -> List[str]:
    """Return syncable architecture module basenames, preserving declaration order."""
    basenames: List[str] = []
    seen = set()
    for entry in architecture:
        if not isinstance(entry, dict):
            continue
        basename = _basename_from_architecture_filename(entry.get("filename", ""))
        if basename and basename not in seen:
            basenames.append(basename)
            seen.add(basename)
    return basenames


def _merge_duplicate_output_dependencies(
    target_entry: Dict[str, Any],
    duplicate_entry: Dict[str, Any],
) -> None:
    """Merge dependency edges from a duplicate-output architecture entry."""
    target_dependencies = target_entry.get("dependencies", [])
    duplicate_dependencies = duplicate_entry.get("dependencies", [])
    if not isinstance(duplicate_dependencies, list):
        return

    merged = list(target_dependencies) if isinstance(target_dependencies, list) else []
    seen = {str(dep) for dep in merged}
    for dependency in duplicate_dependencies:
        dep_key = str(dependency)
        if dep_key not in seen:
            merged.append(dependency)
            seen.add(dep_key)
    target_entry["dependencies"] = merged


def _architecture_sync_modules(project_root: Path) -> Tuple[List[GlobalSyncModule], List[Dict[str, Any]], Path]:
    """Return architecture modules with cwd scope preserved."""
    arch_files = find_architecture_for_project(project_root)
    if not arch_files:
        return [], [], project_root / "architecture.json"

    raw_modules: List[Dict[str, Any]] = []
    architecture: List[Dict[str, Any]] = []
    seen: set[Tuple[Path, str]] = set()
    record_by_output_path: Dict[Path, Dict[str, Any]] = {}

    for arch_path in arch_files:
        try:
            data = json.loads(arch_path.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            continue

        arch_dir = arch_path.parent
        for entry in extract_modules(data):
            basename = _basename_from_architecture_filename(entry.get("filename", ""))
            if not basename:
                continue
            filepath = str(entry.get("filepath") or "").strip()
            if filepath:
                output_path = Path(filepath)
                if not output_path.is_absolute():
                    output_path = arch_dir / output_path
                try:
                    output_path = output_path.resolve(strict=False)
                except OSError:
                    output_path = output_path.absolute()
                existing_record = record_by_output_path.get(output_path)
                if existing_record is not None:
                    _merge_duplicate_output_dependencies(existing_record["entry"], entry)
                    existing_record["aliases"].append((arch_path.resolve(), basename))
                    duplicate_cwd = _resolve_module_cwd(basename, arch_dir)
                    existing_record["sync_candidates"].append((basename, duplicate_cwd))
                    dependencies = entry.get("dependencies", [])
                    if isinstance(dependencies, list):
                        existing_record["dependency_scopes"].append(
                            (arch_path.resolve(), tuple(dependencies))
                        )
                    continue
            dedupe_key = (arch_path.resolve(), basename)
            if dedupe_key in seen:
                continue
            seen.add(dedupe_key)
            architecture.append(entry)
            # Consult _resolve_module_cwd so a nested .pddrc whose context owns
            # this basename wins over the arch file's own directory. The
            # resolver scans subdirectories of arch_dir for .pddrc files and
            # falls back to arch_dir when no nested config claims the basename.
            cwd = _resolve_module_cwd(basename, arch_dir)
            dependencies = entry.get("dependencies", [])
            dependency_scopes = []
            if isinstance(dependencies, list):
                dependency_scopes.append((arch_path.resolve(), tuple(dependencies)))
            record = {
                "basename": basename,
                "cwd": cwd,
                "architecture_path": arch_path,
                "entry": entry,
                "aliases": [(arch_path.resolve(), basename)],
                "dependency_scopes": dependency_scopes,
                "sync_candidates": [(basename, cwd)],
            }
            raw_modules.append(record)
            if filepath:
                record_by_output_path[output_path] = record

    counts: Dict[str, int] = {}
    for record in raw_modules:
        basename = record["basename"]
        counts[basename] = counts.get(basename, 0) + 1

    modules: List[GlobalSyncModule] = []
    for record in raw_modules:
        basename = record["basename"]
        cwd = record["cwd"]
        arch_path = record["architecture_path"]
        entry = record["entry"]
        if counts[basename] > 1:
            try:
                rel_scope = arch_path.parent.resolve().relative_to(project_root.resolve()).as_posix()
            except (OSError, ValueError):
                rel_scope = arch_path.parent.as_posix()
            key = f"{rel_scope or '.'}:{basename}"
        else:
            key = basename
        modules.append(
            GlobalSyncModule(
                key,
                basename,
                cwd,
                arch_path,
                entry,
                tuple(record["aliases"]),
                tuple(record["dependency_scopes"]),
                tuple(record["sync_candidates"]),
            )
        )

    return modules, architecture, arch_files[0]


def _prompt_contract_errors_for_module(
    basename: str,
    cwd: Path,
    project_root: Path,
) -> List[str]:
    """Return deterministic prompt-contract preflight errors for a sync module."""
    candidate_roots: List[Path] = []
    seen_roots: set[Path] = set()
    for candidate in (cwd, _find_project_root(cwd), project_root):
        try:
            root = Path(candidate).resolve()
        except OSError:
            root = Path(candidate)
        if root not in seen_roots:
            candidate_roots.append(root)
            seen_roots.add(root)

    for root in candidate_roots:
        architecture, architecture_path = _load_architecture_json(root)
        if not architecture:
            continue

        matched = False
        errors: List[str] = []
        for entry in extract_modules(architecture):
            if basename not in _architecture_entry_aliases(entry):
                continue
            matched = True
            filename = str(entry.get("filename") or "").strip()
            filepath = str(entry.get("filepath") or "").strip()
            if not filename or not filepath:
                continue

            prompt_path = resolve_architecture_prompt_path(filename, root)
            output_path = Path(filepath)
            if not output_path.is_absolute():
                output_path = root / output_path
            errors.extend(
                validate_prompt_contract_context(
                    prompt_path=prompt_path,
                    output_path=output_path,
                    project_root=root,
                    architecture_path=architecture_path,
                    require_prompt_local_source_context=(
                        _prompt_contract_strict_self_context_required(
                            prompt_path, root
                        )
                    ),
                )
            )

        if matched:
            return errors

    return []


def _prompt_contract_strict_self_context_required(
    prompt_path: Path,
    project_root: Path,
) -> bool:
    """Return True when a prompt changed in git and needs staged stricter checks."""
    try:
        root = Path(project_root).resolve()
        rel_path = Path(prompt_path).resolve().relative_to(root).as_posix()
    except (OSError, ValueError):
        return False

    status = subprocess.run(
        ["git", "status", "--porcelain", "--", rel_path],
        cwd=root,
        capture_output=True,
        text=True,
    )
    if status.returncode == 0 and status.stdout.strip():
        return True

    for base_ref in ("origin/main", "main", "origin/master", "master"):
        merge_base = subprocess.run(
            ["git", "merge-base", "HEAD", base_ref],
            cwd=root,
            capture_output=True,
            text=True,
        )
        if merge_base.returncode != 0:
            continue
        base = merge_base.stdout.strip()
        if not base:
            continue
        diff = subprocess.run(
            ["git", "diff", "--quiet", base, "--", rel_path],
            cwd=root,
        )
        if diff.returncode == 1:
            return True
        if diff.returncode == 0:
            return False

    return False


def _format_prompt_contract_preflight_error(basename: str, errors: List[str]) -> str:
    """Format prompt-contract errors for agentic sync dry-run validation output."""
    return (
        f"{basename}: prompt contract preflight failed:\n"
        + "\n".join(f"- {error}" for error in errors)
    )


def _resolve_module_sync_context(
    basename: str,
    cwd: Path,
) -> Tuple[Optional[str], Path, Dict[str, Path]]:
    """Resolve context, prompts_dir, and prompt languages for a sync basename."""
    pddrc_path = _find_pddrc_file(cwd)
    context_name = None
    prompts_dir = cwd / "prompts"

    if pddrc_path:
        config = _load_pddrc_config(pddrc_path)
        # Pass the found .pddrc so the filesystem fallback in
        # _detect_context_from_basename resolves nested prompts_dir contexts
        # against THIS .pddrc, not one discovered from the process cwd (#1675).
        context_name = _detect_context_from_basename(
            basename, config, pddrc_path=pddrc_path
        )
        defaults = config.get("contexts", {}).get(
            context_name or "default", {}
        ).get("defaults", {})
        prompts_dir_raw = defaults.get("prompts_dir", "prompts")
        if not Path(prompts_dir_raw).is_absolute():
            prompts_dir = pddrc_path.parent / prompts_dir_raw
        else:
            prompts_dir = Path(prompts_dir_raw)

    lang_to_path = _detect_languages_with_context(
        basename, prompts_dir, context_name=context_name
    )
    return context_name, prompts_dir, lang_to_path


def _analyze_global_sync_modules(
    modules: List[GlobalSyncModule],
    project_root: Path,
    *,
    quiet: bool = False,
    budget: Optional[float] = None,
    skip_tests: bool = False,
    skip_verify: bool = False,
    target_coverage: Optional[float] = None,
    context_override: Optional[str] = None,
) -> GlobalSyncAnalysis:
    """Tier 1 global sync analysis: fingerprint-scan all architecture modules."""
    modules_to_sync: List[str] = []
    module_cwds: Dict[str, Path] = {}
    module_targets: Dict[str, str] = {}
    module_contexts: Dict[str, Optional[str]] = {}
    module_units: Dict[str, ResolvedSyncUnit] = {}
    module_operations: Dict[str, List[str]] = {}
    skipped_modules: List[str] = []
    estimated_cost = 0.0
    effective_budget = budget if budget is not None else 10.0
    effective_coverage = target_coverage if target_coverage is not None else 90.0

    for module in modules:
        key = module.key
        basename = module.basename
        cwd = module.cwd
        module_cwds[key] = cwd
        module_targets[key] = basename

        sync_candidates = module.sync_candidates or ((basename, cwd),)
        candidate_errors: List[str] = []
        out_of_scope_skips: List[str] = []
        has_prompt_backed_candidate = False
        multiple_candidates = len(sync_candidates) > 1

        for candidate_basename, candidate_cwd in sync_candidates:
            try:
                context_name, prompts_dir, lang_to_path = _resolve_module_sync_context(
                    candidate_basename, candidate_cwd
                )
            except Exception as exc:
                candidate_errors.append(f"{candidate_basename}: {exc}")
                continue
            if not lang_to_path:
                continue
            has_prompt_backed_candidate = True

            operations: List[str] = []
            needs_sync = False
            candidate_cost = 0.0
            for language in lang_to_path:
                label = f"{candidate_basename}: {language}" if multiple_candidates else language
                try:
                    decision = _run_readonly_sync_determine_in_cwd(
                        candidate_cwd,
                        basename=candidate_basename,
                        language=language,
                        target_coverage=effective_coverage,
                        budget=effective_budget,
                        log_mode=True,
                        prompts_dir=str(prompts_dir),
                        skip_tests=skip_tests,
                        skip_verify=skip_verify,
                        context_override=context_name,
                    )
                except Exception as exc:
                    needs_sync = True
                    operations.append(
                        f"{label}: analysis-error ({exc}); queued for sync"
                    )
                    continue

                operations.append(f"{label}: {decision.operation} - {decision.reason}")
                if decision.operation in _GLOBAL_SYNC_TIER1_OPERATIONS:
                    needs_sync = True
                    candidate_cost += float(decision.estimated_cost or 0.0)
                elif decision.operation not in _GLOBAL_SYNC_NOOP_OPERATIONS:
                    out_of_scope_skips.append(
                        f"{key}: {label} requires {decision.operation}; "
                        "outside Tier 1 prompt-staleness scope"
                    )

            if needs_sync:
                modules_to_sync.append(key)
                module_operations[key] = operations
                module_cwds[key] = candidate_cwd
                module_targets[key] = candidate_basename
                module_contexts[key] = context_name
                module_units[key] = resolve_sync_unit(
                    key,
                    candidate_basename,
                    candidate_cwd,
                    requested_context=context_override,
                    architecture_path=module.architecture_path,
                )
                estimated_cost += candidate_cost
                break

        if key in module_operations:
            continue

        if not has_prompt_backed_candidate:
            if candidate_errors and len(candidate_errors) == len(sync_candidates):
                modules_to_sync.append(key)
                module_operations[key] = [
                    "analysis-error: "
                    + "; ".join(candidate_errors)
                    + "; queued for sync as safe fallback"
                ]
                continue
            skipped_modules.append(f"{key}: no syncable prompt file found")
            continue

        skipped_modules.extend(out_of_scope_skips)

    if not quiet:
        skipped_count = len(modules) - len(modules_to_sync)
        stale_count = len(modules_to_sync)
        if stale_count == 0:
            stale_fragment = f"[green]0 stale module(s)[/green]"
        else:
            stale_fragment = f"{stale_count} stale module(s)"
        console.print(
            f"[bold]Global sync analysis:[/bold] {stale_fragment}, "
            f"{skipped_count} already synced or skipped."
        )

    return GlobalSyncAnalysis(
        modules_to_sync=modules_to_sync,
        module_cwds=module_cwds,
        module_targets=module_targets,
        estimated_cost=estimated_cost,
        module_operations=module_operations,
        skipped_modules=skipped_modules,
        all_modules=[module.key for module in modules],
        module_contexts=module_contexts,
        module_units=module_units,
    )


def _dependency_ordered_modules(
    modules: List[str],
    dep_graph: Dict[str, List[str]],
) -> List[str]:
    """Order modules by dependency graph while preserving input order for ties."""
    if not modules:
        return []
    sorted_modules, _ = topological_sort(dep_graph)
    module_set = set(modules)
    ordered = [m for m in sorted_modules if m in module_set]
    ordered.extend(m for m in modules if m not in ordered)
    return ordered


def _build_scoped_global_dep_graph(
    modules: List[GlobalSyncModule],
    target_keys: List[str],
    project_root: Path,
) -> Tuple[Dict[str, List[str]], List[str]]:
    """Build a dependency graph for scoped global-sync module keys.

    Dep resolution proceeds in two passes:

    1. Same-architecture scope: prefer a module declared in the same
       architecture.json as the depending module.
    2. Cross-architecture fallback: if no same-arch match exists, look across
       all loaded modules by basename. An unambiguous match (exactly one
       module across all archs with that basename) is accepted to preserve
       the prior combined-architecture behaviour. Ambiguous cross-arch
       basenames (multiple matches) emit a warning and drop the edge.
    """
    target_set = set(target_keys)
    module_by_key = {module.key: module for module in modules}
    key_by_scope_basename: Dict[Tuple[Path, str], str] = {}
    # Global basename index used for unambiguous cross-arch fallback.
    keys_by_basename: Dict[str, List[str]] = {}
    for module in modules:
        aliases = module.aliases or (
            (module.architecture_path.resolve(), module.basename),
        )
        for scope_path, alias_basename in aliases:
            scope_key = (scope_path.resolve(), alias_basename)
            key_by_scope_basename.setdefault(scope_key, module.key)
            basename_keys = keys_by_basename.setdefault(alias_basename, [])
            if module.key not in basename_keys:
                basename_keys.append(module.key)
    graph: Dict[str, List[str]] = {key: [] for key in target_keys}
    warnings: List[str] = []

    for key in target_keys:
        module = module_by_key.get(key)
        if module is None:
            continue
        dependency_groups = module.dependency_scopes
        if not dependency_groups:
            deps = module.entry.get("dependencies", [])
            if not isinstance(deps, list):
                continue
            dependency_groups = (
                (module.architecture_path.resolve(), tuple(deps)),
            )
        for dependency_scope, deps in dependency_groups:
            for dep in deps:
                dep_basename = _basename_from_architecture_filename(str(dep))
                if not dep_basename:
                    continue
                dep_key = key_by_scope_basename.get(
                    (dependency_scope.resolve(), dep_basename)
                )
                if dep_key is None:
                    # Same-architecture lookup missed. Fall back to a global
                    # basename lookup so cross-arch edges (preserved by the old
                    # combined-architecture builder) still resolve when the
                    # basename is unambiguous across the loaded modules.
                    candidate_keys = keys_by_basename.get(dep_basename, [])
                    if len(candidate_keys) == 1:
                        dep_key = candidate_keys[0]
                    elif len(candidate_keys) > 1:
                        warnings.append(
                            f"combined architecture data under {project_root}: "
                            f"module '{key}' declares ambiguous cross-arch "
                            f"dependency '{dep}' (basename '{dep_basename}' "
                            f"matches multiple modules: "
                            f"{', '.join(sorted(candidate_keys))}); "
                            "edge omitted from schedule"
                        )
                        continue
                    else:
                        warnings.append(
                            f"combined architecture data under {project_root}: "
                            f"module '{key}' declares unresolved dependency "
                            f"'{dep}'; no module with that filename in the same "
                            "architecture scope; edge omitted from schedule"
                        )
                        continue
                if dep_key == key:
                    continue
                if dep_key in target_set:
                    if dep_key not in graph[key]:
                        graph[key].append(dep_key)
                else:
                    warnings.append(
                        f"combined architecture data under {project_root}: module "
                        f"'{key}' depends on '{dep_key}' (via '{dep}'), which is not "
                        "in the sync target set; edge omitted from schedule"
                    )

    return graph, warnings


_SKIPPED_BUCKET_ORDER: Tuple[str, ...] = (
    "example",
    "test",
    "verify",
    "update",
    "fix",
    "crash",
    "no-prompt fixture",
    "other",
)
_SKIPPED_OPERATION_BUCKETS: Tuple[str, ...] = (
    "example",
    "test",
    "verify",
    "update",
    "fix",
    "crash",
)


def _bucket_skipped_reasons(skipped_modules: List[str]) -> Dict[str, int]:
    """Bucket skipped-module entries by reason for the dry-run roll-up.

    Entries flagged "no syncable prompt file found" go into `no-prompt fixture`;
    entries shaped "{key}: {language} requires {operation}; outside Tier 1 ..."
    bucket by `operation` when it matches a known Tier-1-out-of-scope op,
    otherwise into `other`.
    """
    buckets: Dict[str, int] = {name: 0 for name in _SKIPPED_BUCKET_ORDER}
    for entry in skipped_modules:
        lower = entry.lower()
        if "no syncable prompt file found" in lower:
            buckets["no-prompt fixture"] += 1
            continue
        matched = False
        for op in _SKIPPED_OPERATION_BUCKETS:
            if f"requires {op}" in lower:
                buckets[op] += 1
                matched = True
                break
        if not matched:
            buckets["other"] += 1
    return buckets


def _format_skipped_bucket_summary(skipped_modules: List[str]) -> Optional[str]:
    """Return a stable single-line roll-up of skipped buckets, or None if empty."""
    if not skipped_modules:
        return None
    buckets = _bucket_skipped_reasons(skipped_modules)
    parts = [
        f"{count} {name}"
        for name in _SKIPPED_BUCKET_ORDER
        if (count := buckets.get(name, 0)) > 0
    ]
    if not parts:
        return None
    return "Out of Tier 1 scope: " + ", ".join(parts)


def _print_global_sync_plan(
    analysis: GlobalSyncAnalysis,
    ordered_modules: List[str],
    warnings: List[str],
    budget: Optional[float] = None,
    verbose: bool = False,
) -> None:
    """Render a concise global sync dry-run plan."""
    console.print("[bold]Global sync dry run:[/bold]")
    if len(ordered_modules) == 0:
        console.print("  Tier 1 (prompt staleness): [green]0 module(s) stale[/green]")
    else:
        console.print(f"  Tier 1 (prompt staleness): {len(ordered_modules)} module(s) stale")
    console.print(f"  Total architecture modules scanned: {len(analysis.all_modules)}")
    console.print(f"  Estimated cost: ${analysis.estimated_cost:.2f}")
    if budget is not None:
        console.print(f"  Budget: ${budget:.2f}")
        if analysis.estimated_cost > budget:
            console.print(
                f"  [yellow]Warning: estimated cost exceeds budget by "
                f"${analysis.estimated_cost - budget:.2f}[/yellow]"
            )

    if ordered_modules:
        console.print("  Modules (dependency order):")
        for idx, basename in enumerate(ordered_modules, start=1):
            operations = analysis.module_operations.get(basename, [])
            detail = operations[0] if operations else "queued"
            console.print(f"    {idx}. {basename} ({detail})")
    else:
        console.print("  No modules need syncing.")

    for warning in warnings:
        console.print(f"[yellow]Warning: {warning}[/yellow]")

    if analysis.skipped_modules:
        summary = _format_skipped_bucket_summary(analysis.skipped_modules)
        if summary is not None:
            console.print(f"  [dim]{summary}[/dim]")
        if verbose:
            for skipped in analysis.skipped_modules:
                console.print(f"[yellow]Warning: {skipped}[/yellow]")


def run_global_sync(
    *,
    verbose: bool = False,
    quiet: bool = False,
    budget: Optional[float] = None,
    skip_verify: bool = False,
    skip_tests: bool = False,
    agentic_mode: bool = True,
    no_steer: bool = True,
    max_attempts: Optional[int] = None,
    dry_run: bool = False,
    target_coverage: Optional[float] = None,
    one_session: bool = False,
    local: bool = False,
    timeout_adder: float = 0.0,
    strength: Optional[float] = None,
    temperature: Optional[float] = None,
    context_override: Optional[str] = None,
    compressed_context: bool = False,
) -> Tuple[bool, str, float, str]:
    """Run project-wide Tier 1 global sync from architecture.json."""
    _clear_nested_pddrc_cache()
    project_root = _find_project_root(Path.cwd())
    all_modules, architecture, arch_path = _architecture_sync_modules(project_root)
    if not architecture:
        return (
            False,
            f"No architecture.json found under {project_root}.",
            0.0,
            "global-sync",
        )

    if not all_modules:
        return (
            False,
            f"No syncable prompt modules found in {arch_path}.",
            0.0,
            "global-sync",
        )

    analysis = _analyze_global_sync_modules(
        all_modules,
        project_root,
        quiet=quiet,
        budget=budget,
        skip_tests=skip_tests,
        skip_verify=skip_verify,
        target_coverage=target_coverage,
        context_override=context_override,
    )

    dep_graph, dep_warnings = _build_scoped_global_dep_graph(
        all_modules,
        analysis.modules_to_sync,
        project_root,
    )
    ordered_modules = _dependency_ordered_modules(
        analysis.modules_to_sync, dep_graph
    )

    if dry_run:
        if not quiet:
            _print_global_sync_plan(
                analysis, ordered_modules, dep_warnings, budget, verbose=verbose
            )
        return (
            True,
            f"Global sync dry run: {len(ordered_modules)} module(s) would sync.",
            0.0,
            "global-sync",
        )

    if not ordered_modules:
        return True, "All modules are already synced — nothing to do.", 0.0, "global-sync"

    if budget is not None and budget <= 0:
        return False, "Budget must be greater than $0.00 for global sync.", 0.0, "global-sync"

    if budget is not None and analysis.estimated_cost > budget:
        return (
            False,
            (
                f"Estimated global sync cost ${analysis.estimated_cost:.2f} "
                f"exceeds budget ${budget:.2f}; run with a larger --budget "
                "or inspect with --dry-run."
            ),
            0.0,
            "global-sync",
        )

    for warning in dep_warnings:
        if not quiet:
            console.print(f"[yellow]Warning: {warning}[/yellow]")

    runner = AsyncSyncRunner(
        basenames=ordered_modules,
        dep_graph=dep_graph,
        sync_options={
            "total_budget": budget,
            "skip_verify": skip_verify,
            "skip_tests": skip_tests,
            "agentic": agentic_mode,
            "no_steer": no_steer,
            "max_attempts": max_attempts,
            "one_session": one_session,
            "local": local,
            "target_coverage": target_coverage,
            "timeout_adder": timeout_adder,
            "strength": strength,
            "temperature": temperature,
            "context": context_override,
            "compressed_context": compressed_context,
        },
        github_info=None,
        quiet=quiet,
        verbose=verbose,
        issue_url=None,
        module_cwds=analysis.module_cwds,
        module_targets=analysis.module_targets,
        module_contexts=analysis.module_contexts or {},
        module_units=analysis.module_units or {},
        initial_cost=0.0,
    )
    success, message, cost = runner.run()
    return success, message, cost, "global-sync"


def _is_catchall_match(basename: str, config: Dict[str, Any]) -> bool:
    """Check if a basename match against a .pddrc config is only from catch-all patterns.

    Returns True if the match is purely from wildcard patterns like '**' or '*'
    (i.e., specificity 0 — no meaningful path prefix). These should not be used
    to claim a module belongs to a subdirectory.
    """
    import fnmatch as _fnmatch

    contexts = config.get("contexts", {})
    best_specificity = 0

    for context_name, context_config in contexts.items():
        if context_name == "default":
            continue

        # Check prompts_dir-based matching (always specific if it matches)
        defaults = context_config.get("defaults", {})
        prompts_dir = defaults.get("prompts_dir", "")
        if prompts_dir:
            prefix = _extract_prefix_from_prompts_dir(prompts_dir)
            if prefix and (basename == prefix or basename.startswith(prefix + "/")):
                return False  # prompts_dir match is always specific

        # Check path patterns
        for path_pattern in context_config.get("paths", []):
            pattern_base = path_pattern.rstrip("/**").rstrip("/*")
            if _fnmatch.fnmatch(basename, path_pattern) or \
               basename.startswith(pattern_base + "/") or \
               basename == pattern_base:
                if len(pattern_base) > best_specificity:
                    best_specificity = len(pattern_base)

    return best_specificity == 0


def _is_broad_basename_glob_match(
    basename: str,
    config: Dict[str, Any],
    context_name: str,
) -> bool:
    """Return True when a context matched only by broad basename globs.

    Patterns such as ``*llm*`` in nested example projects are useful inside
    that project, but they are too weak to claim root modules like
    ``llm_model`` unless the nested project actually has that prompt.
    Structured path patterns such as ``src/services/**`` remain authoritative.
    """
    contexts = config.get("contexts", {})
    context_config = contexts.get(context_name, {})
    matched_broad = False

    defaults = context_config.get("defaults", {})
    prompts_dir = defaults.get("prompts_dir", "")
    if prompts_dir:
        prefix = _extract_prefix_from_prompts_dir(prompts_dir)
        if prefix and (basename == prefix or basename.startswith(prefix + "/")):
            return False

    for path_pattern in context_config.get("paths", []):
        pattern_base = path_pattern.rstrip("/**").rstrip("/*")
        matched = (
            fnmatch.fnmatch(basename, path_pattern)
            or basename.startswith(pattern_base + "/")
            or basename == pattern_base
        )
        if not matched:
            continue
        if "/" in path_pattern or not any(ch in path_pattern for ch in "*?["):
            return False
        matched_broad = True

    return matched_broad


def _prompt_exists_for_context(
    candidate_dir: Path,
    config: Dict[str, Any],
    context_name: str,
    basename: str,
) -> bool:
    """Check whether ``candidate_dir`` contains the prompt for ``basename``."""
    context_config = config.get("contexts", {}).get(context_name, {})
    prompts_dir = context_config.get("defaults", {}).get("prompts_dir", "prompts")
    prompt_root = candidate_dir / prompts_dir

    prompt_basename = basename
    prefix = _extract_prefix_from_prompts_dir(prompts_dir) if prompts_dir else ""
    if prefix:
        if basename == prefix:
            prompt_basename = Path(prefix).name
        elif basename.startswith(prefix + "/"):
            prompt_basename = basename[len(prefix) + 1 :]

    if "/" in prompt_basename:
        dir_part, name_part = prompt_basename.rsplit("/", 1)
        prompt_dir = prompt_root / dir_part
    else:
        name_part = prompt_basename
        prompt_dir = prompt_root

    return prompt_dir.is_dir() and any(prompt_dir.glob(f"{glob.escape(name_part)}_*.prompt"))


_NESTED_PDDRC_EXCLUDED_PARTS = {
    "__pycache__",
    "node_modules",
    "venv",
    "env",
}


def _is_ignored_nested_pddrc(project_root: Path, pddrc_path: Path) -> bool:
    """Return True for nested configs in hidden/tooling directories."""
    try:
        parts = pddrc_path.parent.relative_to(project_root).parts
    except ValueError:
        return True

    return any(
        part.startswith(".") or part in _NESTED_PDDRC_EXCLUDED_PARTS
        for part in parts
    )


# Maximum directory depth below project_root scanned for nested .pddrc files.
# Bounded so a deep monorepo (e.g. apps/foo/service/...) is still discovered
# (issue #1675 req 1) without an unbounded full-tree walk.
NESTED_PDDRC_MAX_DEPTH = 6


class AmbiguousModuleOwnerError(ValueError):
    """A bare module basename is specifically claimed by >1 nested project.

    The owning project cannot be determined from the basename alone; the caller
    must qualify it by path so the right project/.pddrc is selected (#1675 req 2).
    """


def _iter_nested_pddrc_paths(
    project_root: Path, max_depth: int = NESTED_PDDRC_MAX_DEPTH
):
    """Yield nested ``.pddrc`` paths under ``project_root``, pruned and bounded.

    Prunes hidden and tooling directories *before* descending and never follows
    symlinks, so a deep tree is scanned cheaply. Order is deterministic (sorted).
    The root ``.pddrc`` is not yielded — only nested ones.
    """

    def _walk(dir_path: Path, depth: int):
        if depth > max_depth:
            return
        try:
            subdirs = sorted(
                p
                for p in dir_path.iterdir()
                if p.is_dir() and not p.is_symlink()
            )
        except OSError:
            return
        for sub in subdirs:
            name = sub.name
            if name.startswith(".") or name in _NESTED_PDDRC_EXCLUDED_PARTS:
                continue
            candidate = sub / ".pddrc"
            if candidate.is_file():
                yield candidate
            yield from _walk(sub, depth + 1)

    yield from _walk(project_root, 1)


# Per-run cache of the (expensive) nested-.pddrc discovery walk, keyed by
# resolved project root. A sync run does not add .pddrc files mid-run, so the
# topology is stable; cleared at the start of each top-level sync entry point so
# it never goes stale across runs (#1675 perf).
_NESTED_PDDRC_CACHE: Dict[Tuple[str, int], Tuple[Path, ...]] = {}


def _clear_nested_pddrc_cache() -> None:
    """Reset the nested-.pddrc discovery cache (call at the start of a sync run)."""
    _NESTED_PDDRC_CACHE.clear()


def _nested_pddrc_paths(
    project_root: Path, max_depth: int = NESTED_PDDRC_MAX_DEPTH
) -> Tuple[Path, ...]:
    """Cached, materialized nested-.pddrc discovery for ``project_root``."""
    key = (str(project_root.resolve()), max_depth)
    cached = _NESTED_PDDRC_CACHE.get(key)
    if cached is None:
        cached = tuple(_iter_nested_pddrc_paths(project_root, max_depth))
        _NESTED_PDDRC_CACHE[key] = cached
    return cached


def _dedup_resolved_paths(paths: List[Path]) -> List[Path]:
    """Return ``paths`` de-duplicated by resolved location, preserving order."""
    seen: set = set()
    out: List[Path] = []
    for p in paths:
        try:
            rp = p.resolve()
        except OSError:
            rp = p
        if rp not in seen:
            seen.add(rp)
            out.append(p)
    return out


def _resolve_module_cwd(
    basename: str,
    project_root: Path,
    *,
    strict_ownership: bool = False,
) -> Path:
    """Determine the correct working directory for a module based on .pddrc discovery.

    Logic:
    1. Scan subdirectories (pruned, bounded-depth walk up to
       ``NESTED_PDDRC_MAX_DEPTH``) for nested .pddrc files whose context patterns
       match the basename. Deepest match wins (nearest-config-wins resolution).
       Skip catch-all matches (e.g. paths: ['**']) from subdirectories —
       they match everything and should not claim ownership of unrelated modules.
    2. Fall back to project_root (which may have its own root .pddrc).

    When ``strict_ownership`` is True and a *bare* basename (no ``/``) is
    specifically claimed by more than one nested project at the deepest matching
    level, raise :class:`AmbiguousModuleOwnerError` instead of silently picking
    one (issue #1675 req 2). Path-qualified basenames disambiguate themselves and
    are never treated as ambiguous.
    """
    root_has_prompt = False
    try:
        _, _, root_lang_to_path = _resolve_module_sync_context(basename, project_root)
        root_has_prompt = bool(root_lang_to_path)
    except Exception:
        root_has_prompt = False

    # 1. Scan nested .pddrc files (pruned, bounded-depth walk). best_match is the
    # deepest specific (nearest-config-wins) claim used for the actual cwd. Under
    # strict ownership we additionally collect every distinct project that OWNS
    # the basename — by a specific .pddrc claim OR by physically holding the
    # prompt — so a bare basename owned by more than one project (at any depth,
    # including the repo root) fails as ambiguous instead of silently resolving
    # to one (issue #1675 req 2). The owner sweep runs only under strict
    # ownership (the targeted dry-run path), so the non-strict global path keeps
    # its exact prior behavior and cost.
    best_match: Optional[Path] = None
    best_depth = -1
    owners: List[Path] = []
    if strict_ownership and root_has_prompt:
        owners.append(project_root)

    for pddrc_path in _nested_pddrc_paths(project_root):
        if _is_ignored_nested_pddrc(project_root, pddrc_path):
            continue
        try:
            config = _load_pddrc_config(pddrc_path)
        except (ValueError, OSError):
            continue
        candidate_dir = pddrc_path.parent

        # Deepest specific claim drives the resolved cwd (unchanged logic).
        detected = _detect_context_from_basename(
            basename, config, pddrc_path=pddrc_path
        )
        specific_claim = False
        if detected and detected != "default" and not _is_catchall_match(
            basename, config
        ):
            if _is_broad_basename_glob_match(basename, config, detected):
                specific_claim = (not root_has_prompt) and _prompt_exists_for_context(
                    candidate_dir, config, detected, basename
                )
            else:
                specific_claim = True

        if specific_claim:
            try:
                candidate_depth = len(candidate_dir.relative_to(project_root).parts)
            except ValueError:
                candidate_depth = -1
            if candidate_depth > best_depth:
                best_match = candidate_dir
                best_depth = candidate_depth

        if strict_ownership:
            owns_prompt = False
            try:
                _, _, nested_lang = _resolve_module_sync_context(
                    basename, candidate_dir
                )
                owns_prompt = bool(nested_lang)
            except Exception:
                owns_prompt = False
            if (specific_claim or owns_prompt) and candidate_dir not in owners:
                owners.append(candidate_dir)

    if strict_ownership and "/" not in basename:
        distinct = _dedup_resolved_paths(owners)
        if len(distinct) > 1:
            names = ", ".join(
                sorted(
                    "(project root)"
                    if d.resolve() == project_root.resolve()
                    else str(d.relative_to(project_root))
                    for d in distinct
                )
            )
            raise AmbiguousModuleOwnerError(
                f"Module basename '{basename}' is owned by multiple projects "
                f"({names}); qualify it by path (e.g. '<dir>/{basename}') so the "
                f"owning project/.pddrc is unambiguous."
            )
        # Nested-only ownership the pattern scan missed (prompt present but no
        # specific context pattern): resolve to that single nested owner instead
        # of falling back to root with the parent context (issue #1675 req 1).
        if best_match is None and len(distinct) == 1:
            only = distinct[0]
            if only.resolve() != project_root.resolve():
                best_match = only

    if best_match is not None:
        return best_match

    # 2. Fall back to project root
    return project_root


def _relativize_target(basename: str, cwd: Path, project_root: Path) -> str:
    """Return the child ``pdd sync`` target for ``basename`` relative to ``cwd``.

    A path-qualified basename (e.g. ``extensions/github_pdd_app/src/worker_app``)
    is repo-root-relative. When its owning cwd is a nested project, the child must
    run ``pdd sync src/worker_app`` from that cwd — not the full path — so strip
    the cwd prefix. Bare basenames and basenames not under ``cwd`` are returned
    unchanged (#1675).
    """
    if "/" not in basename:
        return basename
    try:
        full = (Path(project_root) / basename).resolve()
        return full.relative_to(Path(cwd).resolve()).as_posix()
    except (ValueError, OSError):
        return basename


def _project_owns_target_locally(target: str, cwd: Path) -> bool:
    """Return True only when ``cwd`` PHYSICALLY owns ``target``'s prompt (#1675).

    A project owns a target only if the prompt the target resolves to actually
    lives in that project's own tree — i.e. the nearest ``.pddrc`` to the prompt
    file is the one governing ``cwd``. This rejects the case where a project's
    ``.pddrc`` context merely *points into* another project's prompt tree (e.g. a
    repo-root context whose ``prompts_dir`` reaches into
    ``extensions/github_pdd_app/prompts``): the root can resolve the path but does
    not own the module — the nested project does.
    """
    try:
        _, _, lang_to_path = _resolve_module_sync_context(target, cwd)
    except Exception:
        return False
    if not lang_to_path:
        return False

    cwd_pddrc = _find_pddrc_file(cwd)
    cwd_resolved = Path(cwd).resolve()
    for prompt_path in lang_to_path.values():
        try:
            resolved_prompt = Path(prompt_path).resolve()
        except OSError:
            return False
        if cwd_pddrc is None:
            # No .pddrc governs cwd: the prompt must sit directly under cwd.
            try:
                resolved_prompt.relative_to(cwd_resolved)
            except ValueError:
                return False
            continue
        nearest_pddrc, _ = _find_nearest_pddrc_for_file(resolved_prompt)
        if nearest_pddrc is None or (
            nearest_pddrc.resolve() != Path(cwd_pddrc).resolve()
        ):
            return False
    return True


def _resolve_module_cwd_and_target(
    basename: str, project_root: Path
) -> Tuple[Path, str]:
    """Resolve a module's owning cwd and the target relative to that cwd (#1675).

    Bare basenames go through :func:`_resolve_module_cwd` (with strict ownership,
    so duplicates fail loudly). A path-qualified basename is resolved in two
    steps:

    1. **Full repo-root-relative key** (e.g. ``extensions/github_pdd_app/src/worker_app``,
       as emitted by branch-diff): walk up from the implied prompt location to the
       deepest ancestor directory with a ``.pddrc`` that physically owns the
       cwd-relative target, and relativize the target to it.
    2. **Nested-relative key** (e.g. ``src/worker_app`` from the LLM/manual
       identification, where the prompt actually lives at
       ``extensions/github_pdd_app/prompts/src/worker_app``): no ancestor owns it,
       so scan all nested projects for ones that physically own the key as-is. If
       exactly one project owns it, canonicalize to that project (cwd=owner,
       target=key); if more than one, raise :class:`AmbiguousModuleOwnerError`.

    Falls back to ``(project_root, basename)`` for a root-layout path-qualified
    module that no nested project owns.
    """
    if "/" not in basename:
        cwd = _resolve_module_cwd(basename, project_root, strict_ownership=True)
        return cwd, basename

    # 1. Full repo-root-relative key: deepest ancestor .pddrc that physically
    # owns the cwd-relative target (the prompt actually lives in that project).
    implied_dir = (Path(project_root) / basename).parent
    current = implied_dir
    while True:
        pddrc = current / ".pddrc"
        if (
            current != project_root
            and pddrc.is_file()
            and not _is_ignored_nested_pddrc(project_root, pddrc)
        ):
            target = _relativize_target(basename, current, project_root)
            if _project_owns_target_locally(target, current):
                return current, target
        if current == project_root:
            break
        current = current.parent

    # The key is repo-root-relative: root ownership wins ONLY when the prompt is
    # truly root-local (its nearest .pddrc is the root's), not when a root context
    # merely points into a nested project's prompt tree (#1675).
    if _project_owns_target_locally(basename, project_root):
        return project_root, basename

    # 2. Nested-relative key (LLM/manual): find the unique nested project that
    # physically owns the key as-is, and canonicalize the cwd to it (#1675).
    owners = [
        pddrc_path.parent
        for pddrc_path in _nested_pddrc_paths(project_root)
        if not _is_ignored_nested_pddrc(project_root, pddrc_path)
        and _project_owns_target_locally(basename, pddrc_path.parent)
    ]
    owners = _dedup_resolved_paths(owners)
    if len(owners) > 1:
        names = ", ".join(
            sorted(str(d.relative_to(project_root)) for d in owners)
        )
        raise AmbiguousModuleOwnerError(
            f"Module '{basename}' is owned by multiple projects ({names}); "
            f"qualify it by its full repo-root-relative path so the owning "
            f"project is unambiguous."
        )
    if len(owners) == 1:
        return owners[0], basename

    # Root-layout path-qualified module: run the full path from the repo root.
    return project_root, basename


def _build_targeted_dep_graph(
    architecture: Any,
    modules: List[str],
    project_root: Path,
    source_name: str,
) -> Tuple[Dict[str, List[str]], List[str]]:
    """Build the targeted-sync dependency graph keyed by full module keys (#1675).

    ``modules`` are full repo-root-relative scheduler keys, but a nested
    module's architecture entry is keyed relative to its own ``architecture.json``
    (e.g. ``src/worker_app``). Group the modules by their owning project cwd and
    build each group against that project's OWN architecture over the
    project-relative targets, then remap nodes and edges back to the full keys.
    Grouping by project means:
      * same-project edges (including ``src/service -> src/worker_app``) always
        resolve, even when ``worker_app`` also exists in another project;
      * two distinct projects that resolve the same relative target never
        collapse onto one node (each is in its own group);
      * for bare/root-layout keys the relative target equals the key and the
        root group uses the combined architecture, so it is an identity
        transform — unchanged from the prior behavior.
    Cross-PROJECT dependency edges within one sync are uncommon and fall through
    to the builder's existing "edge omitted from schedule" warning.

    Returns ``(graph, warnings)``.
    """
    info: Dict[str, Tuple[Path, str]] = {}
    for bn in modules:
        try:
            cwd, rel_target = _resolve_module_cwd_and_target(bn, project_root)
        except AmbiguousModuleOwnerError:
            cwd, rel_target = project_root, bn  # surfaced later at dry-run
        info[bn] = (cwd, rel_target)

    cwd_groups: Dict[Path, List[str]] = {}
    for bn in modules:
        cwd_groups.setdefault(info[bn][0].resolve(), []).append(bn)

    root_resolved = project_root.resolve()
    graph: Dict[str, List[str]] = {bn: [] for bn in modules}
    warnings: List[str] = []

    for cwd_resolved, group in cwd_groups.items():
        if cwd_resolved == root_resolved:
            group_arch: Any = architecture
        else:
            group_arch, _ = _load_architecture_json(Path(cwd_resolved))
            if not group_arch:
                group_arch = architecture
        # Relative targets are unique within a single project.
        target_to_key = {info[bn][1]: bn for bn in group}
        result = build_dep_graph_from_architecture_data(
            group_arch,
            [info[bn][1] for bn in group],
            source_name=source_name,
        )
        warnings.extend(result.warnings)
        for bn in group:
            graph[bn] = [
                target_to_key.get(dep, dep)
                for dep in result.graph.get(info[bn][1], [])
            ]

    return graph, warnings


def _run_single_dry_run(
    basename: str,
    cwd: Path,
    quiet: bool = False,
    local: bool = False,
    trusted_failures: Optional[List[Tuple[str, str]]] = None,
) -> Tuple[bool, str]:
    """Run pdd sync <basename> --dry-run from the given cwd.

    Returns:
        Tuple of (success, stderr_output).
    """
    # Use this installed package/interpreter, rather than a PATH-resolved
    # executable that arbitrary test/user code could replace while inheriting
    # the private typed-failure capability.
    cmd = [sys.executable, "-m", "pdd"]

    cmd.append("--force")
    if local:
        cmd.append("--local")
    cmd.extend(["sync", basename, "--dry-run", "--agentic", "--no-steer"])

    env = {
        **os.environ,
        "PDD_FORCE": "1",
        "CI": "1",
        "PDD_AGENTIC_BACKGROUND_SAFE": "1",
    }
    if local:
        env["PDD_FORCE_LOCAL"] = "1"

    try:
        with tempfile.TemporaryDirectory(prefix="pdd-provider-failure-") as channel_dir:
            sink = Path(channel_dir) / "failure.json"
            token = secrets.token_urlsafe(32)
            env[_PROVIDER_FAILURE_SINK_ENV] = str(sink)
            env[_PROVIDER_FAILURE_TOKEN_ENV] = token
            result = subprocess.run(
                cmd,
                cwd=str(cwd),
                capture_output=True,
                text=True,
                timeout=60,
                env=env,
            )
            if result.returncode != 0 and sink.is_file():
                try:
                    payload = json.loads(sink.read_text(encoding="utf-8"))
                except (OSError, json.JSONDecodeError):
                    payload = None
                if (
                    isinstance(payload, dict)
                    and set(payload) == {"version", "kind", "token", "provider", "reason"}
                    and payload.get("version") == 1
                    and payload.get("kind") == "provider_environment_failure"
                    and secrets.compare_digest(str(payload.get("token", "")), token)
                    and payload.get("provider") in _PROVIDER_ENVIRONMENT_PROVIDERS
                    and payload.get("reason") in _PROVIDER_ENVIRONMENT_REASONS
                    and trusted_failures is not None
                ):
                    trusted_failures.append(
                        (str(payload["provider"]), str(payload["reason"]))
                    )
        if result.returncode == 0:
            return True, ""
        output = "\n".join(
            part for part in (result.stdout, result.stderr) if part
        ) or f"Exit code {result.returncode}"
        marker = _extract_provider_environment_marker(output)
        return False, marker or output
    except subprocess.TimeoutExpired:
        return False, "Dry-run timed out after 60s"
    except Exception as e:
        return False, str(e)


def _llm_fix_dry_run_failure(
    basename: str,
    project_root: Path,
    dry_run_error: str,
    quiet: bool = False,
    verbose: bool = False,
    reasoning_time: Optional[float] = None,
    local: bool = False,
    trusted_failures: Optional[List[Tuple[str, str]]] = None,
) -> Tuple[bool, Optional[Path], float, str]:
    """Ask the LLM to suggest the correct cwd/command when dry-run fails.

    Returns:
        Tuple of (success, suggested_cwd_or_None, llm_cost, error_msg).
    """
    prompt_template = load_prompt_template("agentic_sync_fix_dry_run_LLM")
    if not prompt_template:
        return False, None, 0.0, "Failed to load dry-run fix prompt template"

    # Build project tree (top 2 levels)
    try:
        tree_lines = []
        for item in sorted(project_root.iterdir()):
            if item.name.startswith(".") and item.name not in (".pddrc",):
                continue
            tree_lines.append(item.name + ("/" if item.is_dir() else ""))
            if item.is_dir():
                try:
                    for sub in sorted(item.iterdir()):
                        if sub.name.startswith(".") and sub.name not in (".pddrc",):
                            continue
                        tree_lines.append(f"  {sub.name}" + ("/" if sub.is_dir() else ""))
                except PermissionError:
                    pass
        project_tree = "\n".join(tree_lines)
    except Exception:
        project_tree = "(unable to list project structure)"

    # Find all .pddrc locations
    pddrc_locations_list = []
    for pddrc_path in project_root.rglob(".pddrc"):
        try:
            rel = pddrc_path.parent.relative_to(project_root)
            pddrc_locations_list.append(str(rel) if str(rel) != "." else "(project root)")
        except ValueError:
            pddrc_locations_list.append(str(pddrc_path.parent))
    pddrc_locations = "\n".join(f"- {loc}" for loc in pddrc_locations_list) or "- (none found)"

    # Escape curly braces in dynamic content to prevent .format() KeyErrors
    safe_tree = project_tree.replace("{", "{{").replace("}", "}}")
    safe_locations = pddrc_locations.replace("{", "{{").replace("}", "}}")
    safe_error = dry_run_error[:2000].replace("{", "{{").replace("}", "}}")

    prompt = prompt_template.format(
        basename=basename,
        dry_run_error=safe_error,
        project_tree=safe_tree,
        pddrc_locations=safe_locations,
        attempted_cwd=str(project_root),
    )

    llm_result = run_agentic_task(
        instruction=prompt,
        cwd=project_root,
        verbose=verbose,
        quiet=quiet,
        label="agentic_sync_fix_dry_run",
        timeout=FIX_DRY_RUN_TIMEOUT_SECONDS,  # Issue #1714: fail fast on stalls
        stall_timeout=FIX_DRY_RUN_STALL_SECONDS,  # Issue #1714: no-progress abort
        reasoning_time=reasoning_time,
        background_safe=True,
    )
    llm_success, llm_output, llm_cost, _ = llm_result

    if not llm_success:
        trusted_failure = getattr(
            llm_result, "provider_environment_failure", None
        )
        if trusted_failures is not None and isinstance(trusted_failure, tuple):
            trusted_failures.append(trusted_failure)
        marker = _extract_provider_environment_marker(llm_output)
        return False, None, llm_cost, marker or f"LLM failed to suggest fix: {llm_output}"

    # Parse SYNC_CMD from response
    cmd_match = re.search(r"SYNC_CMD:\s*(.+)", llm_output)
    if not cmd_match:
        return False, None, llm_cost, "LLM response did not contain SYNC_CMD marker"

    suggested_cmd = cmd_match.group(1).strip()

    # Safety: reject commands that don't look like a pdd sync invocation
    if "pdd" not in suggested_cmd or "sync" not in suggested_cmd:
        return False, None, llm_cost, f"LLM suggested unexpected command: {suggested_cmd}"

    # Append a pwd marker after the command so we can extract the effective cwd.
    # This avoids fragile regex parsing of cd segments from the command string.
    pwd_marker = "__PDD_EFFECTIVE_CWD__"
    augmented_cmd = f"{suggested_cmd} && echo {pwd_marker} && pwd"

    # Run the suggested command directly via shell from project root.
    # This handles relative cd paths, chained cd's, etc. naturally.
    env = {
        **os.environ,
        "PDD_FORCE": "1",
        "CI": "1",
        "PDD_AGENTIC_BACKGROUND_SAFE": "1",
    }
    if local:
        env["PDD_FORCE_LOCAL"] = "1"
    try:
        result = subprocess.run(
            augmented_cmd,
            shell=True,
            cwd=str(project_root),
            capture_output=True,
            text=True,
            timeout=60,
            env=env,
        )
    except subprocess.TimeoutExpired:
        return False, None, llm_cost, f"LLM suggested command timed out: {suggested_cmd}"
    except Exception as e:
        return False, None, llm_cost, f"Failed to run LLM suggested command: {e}"

    if result.returncode == 0:
        # Extract effective cwd from the pwd output after our marker
        stdout_lines = result.stdout.strip().splitlines()
        effective_cwd = project_root.resolve()
        for i, line in enumerate(stdout_lines):
            if line.strip() == pwd_marker and i + 1 < len(stdout_lines):
                effective_cwd = Path(stdout_lines[i + 1].strip()).resolve()
                break

        # Validate resolved cwd is within project root
        try:
            effective_cwd.relative_to(project_root.resolve())
        except ValueError:
            return (
                False,
                None,
                llm_cost,
                f"LLM command resolves outside project root: {suggested_cmd}",
            )

        return True, effective_cwd, llm_cost, ""
    else:
        err_output = result.stderr or result.stdout or f"Exit code {result.returncode}"
        marker = _extract_provider_environment_marker(err_output)
        return (
            False,
            None,
            llm_cost,
            marker or f"LLM suggested command failed: {err_output[:500]}",
        )


def _run_dry_run_validation(
    modules: List[str],
    project_root: Path,
    quiet: bool = False,
    verbose: bool = False,
    reasoning_time: Optional[float] = None,
    local: bool = False,
    trusted_failures: Optional[List[Tuple[str, str]]] = None,
) -> Tuple[bool, Dict[str, Path], Dict[str, str], List[str], float]:
    """Run dry-run validation for each module with LLM fallback.

    Each module is resolved to one ``(cwd, target)`` identity — the owning
    project cwd and the child ``pdd sync`` target relativized to it (#1675) — and
    EVERY stage (dry-run, prompt-contract preflight, and downstream fingerprint
    filtering / runner via the returned maps) consumes that same identity, so a
    path-qualified module like ``extensions/github_pdd_app/src/worker_app`` runs
    ``pdd sync src/worker_app`` from ``extensions/github_pdd_app``.

    Returns:
        Tuple of (all_valid, module_to_cwd_map, module_to_target_map,
        error_messages, total_llm_cost), keyed by the scheduler basename.
    """
    module_cwds: Dict[str, Path] = {}
    module_targets: Dict[str, str] = {}
    errors: List[str] = []
    total_llm_cost = 0.0

    for basename in modules:
        # 0. Runtime-template pre-check (hard boundary):
        # Skip runtime *_LLM.prompt basenames before invoking any subprocess
        # or LLM fallback. They have no language-suffixed sync companion, so
        # `pdd sync <basename>_LLM` is guaranteed to fail with
        # "No prompt files found for basename '<basename>_LLM'".
        if _is_runtime_llm_template(basename):
            if not quiet:
                console.print(
                    f"[yellow]Skipping runtime LLM template (not syncable): {basename}[/yellow]"
                )
            continue

        # 1. Resolve the owning cwd and the cwd-relative child target together.
        # A bare basename that multiple projects own fails as a clean validation
        # error (#1675 req 2) rather than silently syncing the wrong project.
        try:
            cwd, target = _resolve_module_cwd_and_target(basename, project_root)
        except AmbiguousModuleOwnerError as exc:
            errors.append(f"{basename}: {exc}")
            continue

        # 2. Run dry-run with the resolved target from the owning cwd.
        dry_run_kwargs: Dict[str, Any] = {"quiet": quiet, "local": local}
        if trusted_failures is not None:
            dry_run_kwargs["trusted_failures"] = trusted_failures
        ok, err_output = _run_single_dry_run(target, cwd, **dry_run_kwargs)

        if ok:
            contract_errors = _prompt_contract_errors_for_module(
                target, cwd, project_root
            )
            if contract_errors:
                errors.append(
                    _format_prompt_contract_preflight_error(
                        basename, contract_errors
                    )
                )
                continue
            module_cwds[basename] = cwd
            module_targets[basename] = target
            continue

        provider_marker = _extract_provider_environment_marker(err_output)
        if provider_marker:
            errors.append(provider_marker)
            continue

        # 3. Dry-run failed — try LLM fallback
        if not quiet:
            console.print(
                f"[yellow]Dry-run failed for {basename} from {cwd}, trying LLM fallback...[/yellow]"
            )

        llm_ok, llm_cwd, llm_cost, llm_err = _llm_fix_dry_run_failure(
            basename=basename,
            project_root=project_root,
            dry_run_error=err_output,
            quiet=quiet,
            verbose=verbose,
            reasoning_time=reasoning_time,
            local=local,
            trusted_failures=trusted_failures,
        )
        total_llm_cost += llm_cost

        if llm_ok and llm_cwd is not None:
            # Re-relativize the target to the cwd the LLM fallback resolved.
            llm_target = _relativize_target(basename, llm_cwd, project_root)
            contract_errors = _prompt_contract_errors_for_module(
                llm_target, llm_cwd, project_root
            )
            if contract_errors:
                errors.append(
                    _format_prompt_contract_preflight_error(
                        basename, contract_errors
                    )
                )
                continue
            module_cwds[basename] = llm_cwd
            module_targets[basename] = llm_target
            if not quiet:
                try:
                    rel = Path(".") if llm_cwd == project_root else llm_cwd.relative_to(project_root)
                except ValueError:
                    rel = llm_cwd
                console.print(
                    f"[green]LLM resolved {basename} → cwd: {rel}[/green]"
                )
        else:
            detail = llm_err or err_output
            marker = _extract_provider_environment_marker(detail)
            errors.append(marker or f"{basename}: {detail}")

    all_valid = len(errors) == 0
    return all_valid, module_cwds, module_targets, errors, total_llm_cost


def _filter_already_synced(
    modules: List[str],
    module_cwds: Dict[str, Path],
    quiet: bool = False,
    module_targets: Optional[Dict[str, str]] = None,
) -> List[str]:
    """Filter out modules that are already fully synced (fingerprint matches).

    For each module, runs sync_determine_operation in log_mode (read-only) using
    the module's own resolved cwd `.pddrc` (prompts_dir/context) and the
    cwd-relative target (#1675), so a nested module's hashes are checked for the
    project that owns it — the same (cwd-relative) identity dry-run and the
    runner use, not the scheduler key. Modules whose operation is 'nothing' (all
    hashes match, workflow complete) are removed.

    Returns:
        List of module basenames (scheduler keys) that actually need syncing.
    """
    needs_sync: List[str] = []
    targets = module_targets or {}

    for basename in modules:
        cwd = module_cwds.get(basename)
        if cwd is None:
            # No resolved cwd — keep it in the list for the runner to handle
            needs_sync.append(basename)
            continue

        target = targets.get(basename, basename)
        try:
            context_name, prompts_dir, lang_to_path = _resolve_module_sync_context(
                target, cwd
            )
        except Exception:
            # Language discovery failed — keep module in the list (safe fallback)
            needs_sync.append(basename)
            continue

        if not lang_to_path:
            # No languages found — keep it for the runner to handle
            needs_sync.append(basename)
            continue

        # Check fingerprint for each language; if ANY needs work, keep the module
        all_nothing = True
        for lang in lang_to_path:
            try:
                decision = _sync_determine_operation_readonly(
                    basename=target,
                    language=lang,
                    target_coverage=90.0,
                    log_mode=True,
                    prompts_dir=str(prompts_dir),
                    context_override=context_name,
                )
                if decision.operation not in _GLOBAL_SYNC_NOOP_OPERATIONS:
                    all_nothing = False
                    break
            except Exception:
                # Fingerprint check failed — keep module (safe fallback)
                all_nothing = False
                break

        if all_nothing:
            if not quiet:
                console.print(f"  [green]\u2713[/green] {basename} — already synced, skipping")
        else:
            needs_sync.append(basename)

    return needs_sync


def _freeze_issue_sync_plan(
    project_root: Path,
    modules: List[str],
    module_cwds: Dict[str, Path],
    module_targets: Dict[str, str],
    dep_graph: Dict[str, List[str]],
    *,
    context_override: Optional[str] = None,
    provenance_source: str = "issue_selection",
) -> SyncPlan:
    """Freeze the write-free issue-sync scope before a child runner starts.

    This adapter deliberately consumes the same resolved cwd/target pair that
    dry-run validation produced.  It is kept narrow so legacy runners continue
    to receive their existing scheduler keys while Cloud evidence gets only the
    contract's canonical, path-qualified module IDs.
    """
    ids_by_scheduler_key: Dict[str, str] = {}
    candidates: List[SyncPlanCandidate] = []
    for key in modules:
        cwd = module_cwds.get(key)
        if cwd is None:
            raise SyncPlanError(f"unresolved sync target {key!r}")
        unit = resolve_sync_unit(
            key,
            module_targets.get(key, key),
            cwd,
            requested_context=context_override,
        )
        module_id = canonical_module_id(project_root, unit)
        ids_by_scheduler_key[key] = module_id
        try:
            _, _, language_paths = _resolve_module_sync_context(
                unit.target_basename, unit.cwd
            )
            prompt_paths = tuple(
                sorted(Path(path) for path in language_paths.values())
            )
        except Exception:
            prompt_paths = ()
        candidates.append(
            SyncPlanCandidate(
                module_id=module_id,
                unit=unit,
                prompt_paths=prompt_paths,
                details=SyncPlanDetails(
                    changed_reason="selected for issue sync",
                    expected_operation="generate",
                    confidence="high" if prompt_paths else "low",
                    provenance=(PlanProvenance(provenance_source, key),),
                ),
            )
        )

    candidates_with_deps: List[SyncPlanCandidate] = []
    for candidate in candidates:
        scheduler_key = next(
            key for key, module_id in ids_by_scheduler_key.items()
            if module_id == candidate.module_id
        )
        dependencies = tuple(
            sorted(
                ids_by_scheduler_key[dependency]
                for dependency in dep_graph.get(scheduler_key, [])
                if dependency in ids_by_scheduler_key
            )
        )
        candidates_with_deps.append(
            SyncPlanCandidate(
                module_id=candidate.module_id,
                unit=candidate.unit,
                prompt_paths=candidate.prompt_paths,
                output_paths=candidate.output_paths,
                details=candidate.details,
                dependencies=dependencies,
            )
        )
    return build_sync_plan(
        project_root,
        candidates_with_deps,
        [ids_by_scheduler_key[key] for key in modules],
    )


def _parse_llm_response(response: str) -> Tuple[List[str], bool, List[Dict[str, Any]]]:
    """
    Parse the LLM response for module identification and dependency validation.

    Returns:
        Tuple of (modules_to_sync, deps_valid, deps_corrections).
    """
    modules_to_sync: List[str] = []
    deps_valid = True
    deps_corrections: List[Dict[str, Any]] = []

    # Extract MODULES_TO_SYNC
    modules_match = re.search(r"MODULES_TO_SYNC:\s*\[([^\]]*)\]", response)
    if modules_match:
        raw = modules_match.group(1)
        # Parse quoted strings and deduplicate (preserve order)
        modules_to_sync = list(dict.fromkeys(
            m.strip().strip('"').strip("'") for m in raw.split(",") if m.strip().strip('"').strip("'")
        ))

    # Extract DEPS_VALID
    deps_match = re.search(r"DEPS_VALID:\s*(true|false)", response, re.IGNORECASE)
    if deps_match:
        deps_valid = deps_match.group(1).lower() == "true"

    # Extract DEPS_CORRECTIONS if present
    if not deps_valid:
        # Find the JSON array after DEPS_CORRECTIONS: by locating the opening [
        # and finding its matching ] using json.loads for reliable parsing
        corrections_start = response.find("DEPS_CORRECTIONS:")
        if corrections_start != -1:
            bracket_start = response.find("[", corrections_start)
            if bracket_start != -1:
                # Try progressively longer substrings to find valid JSON
                for end_idx in range(bracket_start + 1, len(response) + 1):
                    candidate = response[bracket_start:end_idx]
                    if candidate.count("]") > 0 and candidate.count("[") <= candidate.count("]"):
                        try:
                            deps_corrections = json.loads(candidate)
                            break
                        except json.JSONDecodeError:
                            continue

    return modules_to_sync, deps_valid, deps_corrections


def _apply_architecture_corrections(
    project_root: Path,
    corrections: List[Dict[str, Any]],
    architecture: Optional[List[Dict[str, Any]]] = None,
    quiet: bool = False,
) -> List[Dict[str, Any]]:
    """
    Apply LLM-suggested dependency corrections to the architecture.json file that
    *owns* each corrected ``filename``.

    Per issue #1060, combined architecture data is read-only analysis. Writes must
    go back to the single architecture.json that lists the corrected filename,
    never to the primary/root path with the combined list — that flattens nested
    arch entries into root and pollutes app architecture with bundled samples.

    Args:
        project_root: PDD project root used to discover architecture.json files.
        corrections: List of correction dicts with ``filename`` and ``dependencies``.
        architecture: Optional combined in-memory list; when provided, entries
            matching successfully written corrections are mutated in place so the
            downstream dependency-graph build sees the new dependencies without
            re-reading from disk.
        quiet: Suppress output.

    Returns:
        The (possibly mutated) combined ``architecture`` list, or ``[]`` if none
        was supplied.
    """
    if architecture is None:
        architecture = []

    successful_changes = 0
    for correction in corrections:
        filename = correction.get("filename", "")
        new_deps = correction.get("dependencies", [])
        if not filename:
            continue

        # Locate every architecture.json under project_root that declares this
        # filename. Use default discovery (skip bundled samples) so a root-level
        # sync run cannot write to bundled-sample arch files.
        #
        # Carry the *raw* loaded JSON alongside the extracted modules list so
        # write-back preserves the original on-disk shape (bare-list or
        # ``{prd_files, modules}`` dict). ``extract_modules`` returns the same
        # dict objects by reference (it does not deep-copy), so mutating
        # ``modules[idx]["dependencies"]`` also mutates the corresponding entry
        # in ``raw_data`` (whether ``raw_data`` is the bare list or the
        # dict wrapper). See ``pdd/architecture_registry.py::extract_modules``.
        owners: List[Tuple[Path, Any, List[Dict[str, Any]], int]] = []
        for arch_path in find_architecture_for_project(project_root):
            try:
                data = json.loads(arch_path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                continue
            modules = extract_modules(data)
            for idx, entry in enumerate(modules):
                if entry.get("filename") == filename:
                    owners.append((arch_path, data, modules, idx))
                    break  # one owner per file

        if not owners:
            if not quiet:
                console.print(
                    f"[yellow]Skipping correction: filename '{filename}' "
                    f"not found in any architecture.json[/yellow]"
                )
            continue

        if len(owners) > 1:
            paths = ", ".join(str(p) for p, _, _, _ in owners)
            if not quiet:
                console.print(
                    f"[yellow]Skipping ambiguous correction: filename "
                    f"'{filename}' appears in {len(owners)} architecture.json "
                    f"files at: {paths} — refusing to write[/yellow]"
                )
            continue

        arch_path, raw_data, modules, idx = owners[0]
        old_deps = modules[idx].get("dependencies", [])
        # Mutate the dict in place — because extract_modules returns the same
        # dict objects (not copies), this propagates into ``raw_data`` whether
        # the file was bare-list or ``{prd_files, modules}`` shaped.
        modules[idx]["dependencies"] = new_deps
        try:
            # Write the raw loaded structure back so the original shape (and
            # any sibling keys like ``prd_files``) is preserved on disk.
            atomic_write_json(arch_path, raw_data)
            successful_changes += 1
            if not quiet:
                console.print(
                    f"[yellow]Updated deps for {filename} in {arch_path}: "
                    f"{old_deps} -> {new_deps}[/yellow]"
                )
        except OSError as e:
            if not quiet:
                console.print(
                    f"[red]Failed to write {arch_path}: {e}[/red]"
                )
            continue

        # Keep the combined in-memory list aligned with the on-disk write so
        # the downstream graph build sees the new dependencies.
        for entry in architecture:
            if isinstance(entry, dict) and entry.get("filename") == filename:
                entry["dependencies"] = new_deps
                break

    if successful_changes and not quiet:
        console.print(
            f"[green]Applied {successful_changes} dependency correction(s) "
            f"across owning architecture.json files[/green]"
        )

    return architecture


# Issue #1664: keep the module-identification LLM prompt under the provider
# input limit. 1,048,576 is the documented provider input-char limit
# (issue #1664: max_chars: 1048576); the provider counts ≈ len(prompt) with
# negligible wrapper overhead, so no arbitrary margin is subtracted — a smaller
# cap would falsely trim/fail valid 1.0–1.048M-char prompts. Compact
# architecture + filter machine-noise comments, then a hard size guard that
# surfaces the REAL input_too_large failure instead of collapsing to "no
# modules to sync".
_IDENTIFY_MODULES_MAX_CHARS = 1_048_576

# The agentic_sync_identify_modules_LLM prompt uses architecture entries ONLY
# for origin-matching (Task 1) and dependency validation (Task 2); everything
# else (notably the ~5KB/entry `interface`) is dropped from the prompt copy.
_IDENTIFY_MODULES_ARCH_FIELDS = ("filename", "filepath", "origin", "dependencies")

# Structural anchors for machine-generated comments that add prompt size but no
# module-identification signal. Matched on the STRIPPED body via startswith.
# Conservative on purpose: NOT filtered by author or fuzzy keywords, because a
# bot comment can still carry useful FILES_MODIFIED / dev-unit output.
_LOW_SIGNAL_COMMENT_PREFIXES = (
    "🚀 **Job Queued!**",
    "## PDD Agentic Sync Progress",
    "## PDD Agentic Sync - Error",
    "<!-- PDD_WORKFLOW_STATE:",
)


def _provider_prompt_len(instruction: str) -> int:
    """Length of the exact prompt text that ``run_agentic_task`` sends."""
    return len(build_agentic_task_instruction(instruction))


def _compact_architecture_for_identification(
    architecture: Optional[List[Dict[str, Any]]],
) -> Optional[List[Dict[str, Any]]]:
    """Return an architecture copy carrying only identify-modules signal fields.

    Keeps only ``_IDENTIFY_MODULES_ARCH_FIELDS`` (filename/filepath/origin/
    dependencies) per entry and drops the heavy ``interface``/``description``/
    ``reason`` text that dominates prompt size (issue #1664). Order is
    preserved, non-dict entries are skipped, and the input is never mutated.
    Falsy input (None/empty) is returned as-is.
    """
    if not architecture:
        return architecture
    compact: List[Dict[str, Any]] = []
    for entry in architecture:
        if not isinstance(entry, dict):
            continue
        slim = {k: entry[k] for k in _IDENTIFY_MODULES_ARCH_FIELDS if k in entry}
        if slim:
            compact.append(slim)
    return compact


def _is_low_signal_comment(body: str) -> bool:
    """True if a comment body is empty or a known machine-noise template.

    Matches ``_LOW_SIGNAL_COMMENT_PREFIXES`` on the stripped body so a leading
    blank line cannot hide the anchor (issue #1664).
    """
    stripped = (body or "").strip()
    if not stripped:
        return True
    return any(stripped.startswith(prefix) for prefix in _LOW_SIGNAL_COMMENT_PREFIXES)


def _filter_low_signal_comments(
    comments: Optional[List[Dict[str, Any]]],
) -> Optional[List[Dict[str, Any]]]:
    """Drop machine-noise comments while keeping human/bot signal (issue #1664).

    Falsy or non-list input is returned as-is (never iterate a dict's keys).
    Non-dict entries are kept untouched.
    """
    if not comments or not isinstance(comments, list):
        return comments
    return [
        c
        for c in comments
        if not (isinstance(c, dict) and _is_low_signal_comment(c.get("body", "")))
    ]


def _build_identify_issue_content(
    title: str,
    body: str,
    comments: Optional[List[Dict[str, Any]]],
) -> str:
    """Build the identify-modules issue text from a title/body/comment set.

    Extracted so the same string can be rebuilt with different comment sets by
    the size guard (issue #1664). Does NOT escape format braces — callers do.
    """
    content = f"Title: {title}\n\nDescription:\n{body}\n"
    if comments and isinstance(comments, list):
        content += "\nComments:\n"
        for comment in comments:
            if isinstance(comment, dict):
                c_user = comment.get("user", {}).get("login", "unknown")
                c_body = comment.get("body", "")
                content += f"\n--- Comment by {c_user} ---\n{c_body}\n"
    return content


def _truncate_head_tail(text: str, max_len: int) -> str:
    """Truncate ``text`` to ``<= max_len`` chars, keeping the head and tail.

    Short text is returned unchanged. Otherwise a centred marker reports how
    many chars were dropped; the head+marker+tail total never exceeds
    ``max_len`` (issue #1664).
    """
    if len(text) <= max_len:
        return text
    # Reserve room for the marker, then split the remaining budget head/tail.
    # The marker length depends on the dropped count, so size it first using a
    # conservative estimate and recompute the kept window from the final marker.
    overhead = len("\n...[truncated 0000000000 chars]...\n")
    keep = max(0, max_len - overhead)
    head_len = keep // 2
    tail_len = keep - head_len
    dropped = len(text) - (head_len + tail_len)
    marker = f"\n...[truncated {dropped} chars]...\n"
    result = text[:head_len] + marker + (text[-tail_len:] if tail_len else "")
    # Marker width can grow the result past max_len for large dropped counts;
    # trim the head to guarantee the contract holds.
    if len(result) > max_len:
        excess = len(result) - max_len
        head_len = max(0, head_len - excess)
        result = text[:head_len] + marker + (text[-tail_len:] if tail_len else "")
    return result


def run_agentic_sync(
    issue_url: str,
    *,
    verbose: bool = False,
    quiet: bool = False,
    budget: Optional[float] = None,
    skip_verify: bool = False,
    skip_tests: bool = False,
    dry_run: bool = False,
    agentic_mode: bool = True,
    no_steer: bool = True,
    max_attempts: Optional[int] = None,
    timeout_adder: float = 0.0,
    use_github_state: bool = True,
    one_session: bool = False,
    reasoning_time: Optional[float] = None,
    durable: bool = False,
    durable_branch: Optional[str] = None,
    no_resume: bool = False,
    durable_max_parallel: Optional[int] = None,
    strength: Optional[float] = None,
    temperature: Optional[float] = None,
    context_override: Optional[str] = None,
    compressed_context: bool = False,
    local: bool = False,
) -> Tuple[bool, str, float, str]:
    """
    Run agentic sync workflow: identify modules from a GitHub issue and sync in parallel.

    Args:
        issue_url: GitHub issue URL.
        verbose: Enable detailed logging.
        quiet: Suppress standard output.
        budget: Maximum total cost across module identification and child syncs.
        skip_verify: Skip verification step.
        skip_tests: Skip test generation.
        dry_run: Analyze issue sync targets without launching write-mode child syncs.
        agentic_mode: Use agentic mode for individual syncs.
        no_steer: Disable interactive steering.
        max_attempts: Max fix attempts per module.
        timeout_adder: Additional seconds added on top of the per-module
            wall-clock cap. Stacks with ``PDD_MODULE_TIMEOUT_SECONDS``
            (default 2700s) and is forwarded to the runner via
            ``sync_options['timeout_adder']``. Negative or non-numeric
            values are clamped to 0 by the runner so an over-eager flag
            never *shrinks* the cap.
        use_github_state: Enable GitHub comment updates.
        durable: Use isolated worktrees and durable checkpoint commits.
        durable_branch: Optional durable checkpoint branch name.
        no_resume: Ignore existing durable checkpoint trailers.
        durable_max_parallel: Optional durable-mode concurrency cap.

    Returns:
        Tuple of (success, message, total_cost, model_used).
    """
    provider_failure_sink = _consume_provider_failure_sink()
    _clear_nested_pddrc_cache()
    # 1. Check gh CLI
    if not _check_gh_cli():
        return False, "GitHub CLI (gh) not found. Install from https://cli.github.com/", 0.0, ""

    # 2. Parse URL
    parsed = _parse_issue_url(issue_url)
    if not parsed:
        return False, f"Invalid GitHub issue URL: {issue_url}", 0.0, ""

    owner, repo, issue_number = parsed

    if not quiet:
        console.print(f"[bold]Fetching issue #{issue_number} from {owner}/{repo}...[/bold]")

    # 3. Fetch issue content
    success, issue_json = _run_gh_command(["api", f"repos/{owner}/{repo}/issues/{issue_number}"])
    if not success:
        return False, f"Failed to fetch issue: {issue_json}", 0.0, ""

    try:
        issue_data = json.loads(issue_json)
    except json.JSONDecodeError:
        return False, "Failed to parse issue JSON", 0.0, ""

    title = issue_data.get("title", "")
    body = issue_data.get("body", "") or ""
    comments_url = issue_data.get("comments_url", "")

    # 4. Fetch comments
    comments_data: List[Dict[str, Any]] = []
    if comments_url:
        ok, comments_json = _run_gh_command(["api", comments_url, "--paginate"])
        if ok:
            try:
                comments_data = json.loads(comments_json)
            except json.JSONDecodeError:
                if verbose:
                    console.print("[yellow]Warning: Failed to parse comments JSON[/yellow]")

    # 5. Build issue content. Drop machine-noise comments (issue #1664) before
    # building the string so they never count toward the identify-modules
    # prompt size budget; signal-bearing comments (FILES_MODIFIED, etc.) stay.
    filtered_comments = _filter_low_signal_comments(comments_data)
    issue_content = _escape_format_braces(
        _build_identify_issue_content(title, body, filtered_comments)
    )

    # 6. Find project root and load architecture.json
    project_root = _find_project_root(Path.cwd())
    architecture, arch_path = _load_architecture_json(project_root, issue_number=issue_number)

    if architecture is None:
        if not quiet:
            console.print("[yellow]No architecture.json found, falling back to include-based dependency graph[/yellow]")

    # 7. Try git diff-based module detection first (deterministic, free)
    branch_modules = _detect_modules_from_branch_diff(project_root)
    llm_cost = 0.0
    provider = ""
    deps_valid = True
    deps_corrections: List[Dict[str, Any]] = []
    changed_modules_env_used = False
    changed_modules_env_modules: List[str] = []

    if branch_modules:
        if not quiet:
            console.print(f"[green]Detected modules from branch diff: {branch_modules}[/green]")
        modules_to_sync = branch_modules
    elif _branch_diff_is_runtime_llm_only(project_root):
        # Hard boundary (Req 9 / issue #1396): the branch diff contains only
        # runtime *_LLM.prompt template changes. Those templates are consumed
        # directly by their owning code module via load_prompt_template(...)
        # and have no language-suffixed sync companion, so there is nothing to
        # sync. Return a deterministic no-op success without spending an LLM
        # call on the identify-modules step.
        msg = "All modules are already synced — nothing to do."
        if not quiet:
            console.print(
                "[green]Branch diff contains only runtime *_LLM.prompt templates; "
                "skipping LLM identification.[/green]"
            )
            console.print(f"[green]{msg}[/green]")
        return True, msg, llm_cost, provider
    else:
        changed_modules_env_modules = _parse_changed_modules_env(
            os.environ.get("PDD_CHANGED_MODULES", "")
        )
        if changed_modules_env_modules:
            changed_modules_env_used = True
            modules_to_sync = changed_modules_env_modules
            if not quiet:
                console.print(
                    "[green]Using PDD_CHANGED_MODULES for module identification: "
                    f"{modules_to_sync}[/green]"
                )
        else:
            # 7b. Fall back to LLM-based module identification
            prompt_template = load_prompt_template("agentic_sync_identify_modules_LLM")
            if not prompt_template:
                return False, "Failed to load agentic_sync_identify_modules_LLM prompt template", 0.0, ""

            # Issue #1664: compact the architecture for the PROMPT COPY ONLY. The
            # full ``architecture`` object is left untouched for downstream use
            # (dependency corrections, graph build); only this prompt rendering
            # drops the ~5KB/entry interface text that blows the input limit.
            compact_arch = _compact_architecture_for_identification(architecture)
            arch_json_str = (
                json.dumps(compact_arch, indent=2)
                if compact_arch
                else "No architecture.json available."
            )
            # Escape braces in dynamic content to prevent .format() from interpreting
            # code references like {uid} as template placeholders
            safe_arch_json = arch_json_str.replace("{", "{{").replace("}", "}}")

            def _render(issue_text: str) -> str:
                return prompt_template.format(
                    issue_content=issue_text,
                    architecture_json=safe_arch_json,
                    issue_number=issue_number,
                )

            # Size guard (issue #1664): the rendered prompt must stay under the
            # provider input limit. Trim levers in order of least signal lost:
            # 1) drop comments entirely, then 2) truncate the issue body. If even a
            # body-less prompt is over budget the architecture itself is too large
            # to fit, so surface a REAL input_too_large failure rather than letting
            # an over-limit call collapse to "no modules to sync".
            prompt = _render(issue_content)
            if _provider_prompt_len(prompt) > _IDENTIFY_MODULES_MAX_CHARS:
                prompt = _render(
                    _escape_format_braces(_build_identify_issue_content(title, body, None))
                )
            if _provider_prompt_len(prompt) > _IDENTIFY_MODULES_MAX_CHARS:
                base_len = _provider_prompt_len(
                    _render(
                        _escape_format_braces(_build_identify_issue_content(title, "", None))
                    )
                )
                body_budget = _IDENTIFY_MODULES_MAX_CHARS - base_len
                if body_budget > 0:
                    # The body is brace-escaped (each `{`/`}` doubled) before
                    # rendering, so the worst case is len(escaped(t)) == 2*len(t).
                    # Truncate the RAW body to half the budget so the escaped body
                    # still fits within body_budget even when it is all braces.
                    prompt = _render(
                        _escape_format_braces(
                            _build_identify_issue_content(
                                title, _truncate_head_tail(body, max(0, body_budget // 2)), None
                            )
                        )
                    )
            provider_prompt_len = _provider_prompt_len(prompt)
            if provider_prompt_len > _IDENTIFY_MODULES_MAX_CHARS:
                msg = (
                    "LLM failed to identify modules: input_too_large: identify-modules "
                    f"provider prompt is {provider_prompt_len} chars, over the "
                    f"{_IDENTIFY_MODULES_MAX_CHARS}-char budget even after compaction; "
                    "reduce architecture.json scope or split the sync."
                )
                if use_github_state:
                    _post_error_comment(owner, repo, issue_number, msg)
                return False, msg, 0.0, ""

            if not quiet:
                console.print("[bold]Identifying modules to sync via LLM...[/bold]")

            # 8. Call LLM
            llm_result = run_agentic_task(
                instruction=prompt,
                cwd=project_root,
                verbose=verbose,
                quiet=quiet,
                label="agentic_sync_identify_modules",
                timeout=IDENTIFY_MODULES_TIMEOUT_SECONDS,  # Issue #1714: fail fast on stalls
                stall_timeout=IDENTIFY_MODULES_STALL_SECONDS,  # Issue #1714: no-progress abort
                reasoning_time=reasoning_time,
                background_safe=True,
            )
            llm_success, llm_output, llm_cost, provider = llm_result

            if not llm_success:
                msg = f"LLM failed to identify modules: {llm_output}"
                if use_github_state:
                    _post_error_comment(owner, repo, issue_number, msg)
                _publish_provider_failure_sink(
                    provider_failure_sink,
                    getattr(llm_result, "provider_environment_failure", None),
                )
                return False, msg, llm_cost, provider

            # 9. Parse LLM response
            modules_to_sync, deps_valid, deps_corrections = _parse_llm_response(llm_output)

            if not modules_to_sync:
                # Treat an empty LLM selection as a successful no-op only when the
                # branch diff is verifiably runtime-template-only. The deterministic
                # short-circuit in step 7 normally handles that case before the LLM
                # is called, so reaching this branch implies either a non-prompt
                # diff, a mixed diff, or LLM/parsing failure. A blanket success
                # here would silently pass real issues without syncing anything
                # (issue #1396 review feedback).
                if _branch_diff_is_runtime_llm_only(project_root):
                    msg = "All modules are already synced — nothing to do."
                    if not quiet:
                        console.print(f"[green]{msg}[/green]")
                    return True, msg, llm_cost, provider
                msg = "LLM identified no modules to sync"
                if use_github_state:
                    _post_error_comment(owner, repo, issue_number, msg)
                return False, msg, llm_cost, provider

    # 9.4 Augment architecture with entries from the PR branch (new modules created by pdd-change)
    architecture = _augment_architecture_from_pr_branch(architecture, project_root, issue_number)

    # LLMs sometimes return architecture-style names with language suffixes
    # (e.g. "crm_models_Python"). Keep exact architecture basenames first so
    # modules whose real basename ends with a known language word
    # (e.g. "operation_log") are not shortened to "operation". This must run
    # after PR-branch architecture augmentation so new modules are protected too.
    modules_to_sync = _normalize_modules_for_sync(modules_to_sync, architecture)

    # Hard boundary (Req 9): drop any runtime *_LLM.prompt basename before it can
    # reach _filter_invalid_basenames or dry-run. These templates are consumed
    # directly by their owning code module and have no language-suffixed sync
    # companion, so pdd sync would always fail on them.
    pre_filter_modules = list(modules_to_sync)
    modules_to_sync = [m for m in pre_filter_modules if not _is_runtime_llm_template(m)]
    dropped_llm_templates = [m for m in pre_filter_modules if _is_runtime_llm_template(m)]
    if dropped_llm_templates and not quiet:
        for dropped in dropped_llm_templates:
            console.print(
                f"[yellow]Dropping runtime LLM template basename (not syncable): {dropped}[/yellow]"
            )
    if not modules_to_sync:
        # Issues that touch only runtime *_LLM.prompt templates are a successful
        # no-op — those templates are already consumed directly by their owning
        # code modules and there is nothing to regenerate.
        if changed_modules_env_used:
            msg = (
                "PDD_CHANGED_MODULES contained unresolved module targets: "
                f"{dropped_llm_templates or changed_modules_env_modules}"
            )
            if use_github_state:
                _post_error_comment(owner, repo, issue_number, msg)
            return False, msg, llm_cost, provider
        msg = "All modules are already synced — nothing to do."
        if not quiet:
            console.print(f"[green]{msg}[/green]")
        return True, msg, llm_cost, provider

    # 9.5 Filter out basenames not in architecture.json (catches LLM hallucinations)
    modules_to_sync, invalid_basenames = _filter_invalid_basenames(modules_to_sync, architecture)
    if invalid_basenames:
        if not quiet:
            console.print(f"[yellow]Warning: Skipping {len(invalid_basenames)} basenames not found in architecture.json: {invalid_basenames}[/yellow]")

    # 9.5b Drop ambiguous bare basenames (issue #1677) so a short leaf name like
    # `page` is never dispatched into a child sync job that would silently pick the
    # wrong module. Path-qualified names from the branch diff already survive.
    modules_to_sync, ambiguous_basenames = _drop_ambiguous_basenames(modules_to_sync, project_root)
    if ambiguous_basenames and not quiet:
        for name, choices in ambiguous_basenames.items():
            choice_list = ", ".join(choices)
            console.print(
                f"[yellow]Skipping ambiguous module '{name}': it maps to multiple "
                f"architecture entries ({choice_list}). Use a path-qualified name.[/yellow]"
            )

    if changed_modules_env_used:
        unresolved = dropped_llm_templates + invalid_basenames + list(ambiguous_basenames.keys())
        if unresolved:
            msg = f"PDD_CHANGED_MODULES contained unresolved module targets: {unresolved}"
            if use_github_state:
                _post_error_comment(owner, repo, issue_number, msg)
            return False, msg, llm_cost, provider

    if not modules_to_sync:
        if ambiguous_basenames:
            details = "; ".join(
                f"'{name}' -> {', '.join(choices)}"
                for name, choices in ambiguous_basenames.items()
            )
            msg = (
                "No unambiguous modules to sync (issue #1677). Ambiguous short module "
                f"name(s): {details}. Re-run with a path-qualified module name (one of "
                "the paths listed) so PDD writes to the intended file."
            )
        else:
            msg = f"No valid modules to sync (all basenames were invalid: {invalid_basenames})"
        if use_github_state:
            _post_error_comment(owner, repo, issue_number, msg)
        return False, msg, llm_cost, provider

    if not quiet:
        if changed_modules_env_used:
            console.print(
                "[green]Resolved PDD_CHANGED_MODULES module selection: "
                f"{modules_to_sync}[/green]"
            )
        console.print(f"[green]Modules to sync: {modules_to_sync}[/green]")

    # 10. Build dependency graph (#1675): modules_to_sync are full
    # repo-root-relative keys, but nested architecture entries are keyed relative
    # to their own architecture.json, so match each key by its owning-project-
    # relative target and remap edges back to full keys. Identity for bare/root
    # keys.
    if architecture is not None:
        dep_graph, dep_warnings = _build_targeted_dep_graph(
            architecture, modules_to_sync, project_root, str(arch_path)
        )
        if dep_warnings and not quiet:
            for w in dep_warnings:
                console.print(f"[yellow]Warning: {w}[/yellow]")
        if not quiet and verbose:
            for w in collect_architecture_include_validation_warnings(project_root):
                console.print(f"[yellow]Warning: {w}[/yellow]")
            for w in warnings_for_arch_vs_include_sync_order(
                dep_graph_from_architecture=dep_graph,
                modules_to_sync=modules_to_sync,
                project_root=project_root,
            ):
                console.print(f"[yellow]Warning: {w}[/yellow]")
    else:
        # Fallback: scan prompt files for <include> tags
        prompts_dir = project_root / "prompts"
        full_graph = build_dependency_graph(prompts_dir)
        dep_graph = {m: [d for d in full_graph.get(m, []) if d in modules_to_sync] for m in modules_to_sync}

    if not quiet:
        console.print(f"[blue]Dependency graph: {dep_graph}[/blue]")

    # 11.5 Dry-run validation (hybrid: programmatic + LLM fallback)
    if not quiet:
        console.print("[bold]Running dry-run validation for each module...[/bold]")

    trusted_validation_failures: List[Tuple[str, str]] = []
    all_valid, module_cwds, module_targets, dry_run_errors, dry_run_cost = (
        _run_dry_run_validation(
            modules=modules_to_sync,
            project_root=project_root,
            quiet=quiet,
            verbose=verbose,
            reasoning_time=reasoning_time,
            local=local,
            trusted_failures=trusted_validation_failures,
        )
    )
    llm_cost += dry_run_cost

    if not all_valid:
        error_detail = "\n".join(dry_run_errors)
        provider_marker = _extract_provider_environment_marker(error_detail)
        msg = provider_marker or f"Dry-run validation failed:\n{error_detail}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        if use_github_state:
            _post_error_comment(owner, repo, issue_number, msg)
        if trusted_validation_failures:
            _publish_provider_failure_sink(
                provider_failure_sink, trusted_validation_failures[0]
            )
        return False, msg, llm_cost, provider

    if not quiet:
        for bn, cwd in module_cwds.items():
            if cwd == project_root:
                rel = Path(".")
            else:
                try:
                    rel = cwd.relative_to(project_root)
                except ValueError:
                    rel = cwd
            console.print(f"  [green]\u2713[/green] {bn} \u2192 cwd: {rel}")
        console.print("[green]All modules passed dry-run validation[/green]")

    # 11.75 Filter out already-synced modules (fingerprint check)
    if not quiet:
        console.print("[bold]Checking fingerprints for already-synced modules...[/bold]")

    modules_to_sync = _filter_already_synced(
        modules_to_sync, module_cwds, quiet=quiet, module_targets=module_targets
    )
    if not modules_to_sync:
        msg = "All modules are already synced — nothing to do."
        if not quiet:
            console.print(f"[green]{msg}[/green]")
        return True, msg, llm_cost, provider

    # Freeze one complete, serializable scope before any child sync/generation
    # can start.  A bad cwd, ambiguous identity, or digest mismatch therefore
    # fails atomically while this process is still read-only.
    try:
        frozen_sync_plan = _freeze_issue_sync_plan(
            project_root,
            modules_to_sync,
            module_cwds,
            module_targets,
            dep_graph,
            context_override=context_override,
            provenance_source=(
                "PDD_CHANGED_MODULES" if changed_modules_env_used else "issue_selection"
            ),
        )
    except SyncPlanError as exc:
        msg = f"SyncPlan validation failed before writes: {exc}"
        if use_github_state:
            _post_error_comment(owner, repo, issue_number, msg)
        return False, msg, llm_cost, provider

    if dry_run:
        module_list = ", ".join(modules_to_sync)
        msg = f"Dry run complete: {len(modules_to_sync)} module(s) would sync: {module_list}"
        if not quiet:
            console.print(f"[green]{msg}[/green]")
        return True, msg, llm_cost, provider

    # The historic dependency-correction side effect is deliberately deferred
    # until after scope freezing.  A failed plan must leave architecture state
    # untouched; child generation always receives a plan that was validated
    # before any architecture write.
    if not deps_valid and deps_corrections and architecture is not None:
        if not quiet:
            console.print("[yellow]LLM flagged dependency corrections, updating architecture.json...[/yellow]")
        architecture = _apply_architecture_corrections(
            project_root, deps_corrections, architecture, quiet
        )

    # 12. Run parallel sync
    sync_options = {
        "total_budget": budget,
        "skip_verify": skip_verify,
        "skip_tests": skip_tests,
        "agentic": agentic_mode,
        "no_steer": no_steer,
        "max_attempts": max_attempts,
        "one_session": one_session,
        "timeout_adder": timeout_adder,
        "strength": strength,
        "temperature": temperature,
        "context": context_override,
        "compressed_context": compressed_context,
        # Cloud and a failed-module-only fallback consume the exact same frozen
        # candidate set.  The runner treats these values as evidence only; it
        # cannot broaden or replace the plan.
        "sync_plan": frozen_sync_plan.to_dict(),
        "sync_plan_serialized": frozen_sync_plan.serialized(),
        "sync_plan_digest": frozen_sync_plan.sync_plan_digest,
        "selection_digest": frozen_sync_plan.selection_digest,
        # Forward --local so child syncs skip PDD-cloud dispatch on argv, not
        # just via the inherited PDD_FORCE_LOCAL env (run_global_sync already
        # forwards this; the issue-URL path previously dropped it).
        "local": local,
    }

    github_info = {
        "owner": owner,
        "repo": repo,
        "issue_number": issue_number,
        "cwd": project_root,
    } if use_github_state else None

    # Resolve each module into a canonical ResolvedSyncUnit (cwd / .pddrc /
    # context / target / paths) — the SAME (cwd, target) dry-run/contract/
    # fingerprint validated — so every stage uses one identity and a nested or
    # path-qualified child runs `pdd --context <ctx> sync <target>` from its
    # owning project (#1675). The module_contexts dict is derived from the units
    # for backward-compatible callers/runners that have not adopted units.
    module_units = {
        bn: resolve_sync_unit(
            bn,
            module_targets.get(bn, bn),
            module_cwds[bn],
            requested_context=context_override,
        )
        for bn in modules_to_sync
        if bn in module_cwds
    }
    module_contexts = {bn: unit.context for bn, unit in module_units.items()}

    if durable:
        runner = DurableSyncRunner(
            basenames=modules_to_sync,
            dep_graph=dep_graph,
            sync_options=sync_options,
            github_info=github_info,
            issue_number=issue_number,
            project_root=project_root,
            durable_branch=durable_branch,
            no_resume=no_resume,
            durable_max_parallel=durable_max_parallel,
            quiet=quiet,
            verbose=verbose,
            issue_url=issue_url,
            module_cwds=module_cwds,
            module_targets=module_targets,
            module_contexts=module_contexts,
            module_units=module_units,
            initial_cost=llm_cost,
        )
    else:
        runner = AsyncSyncRunner(
            basenames=modules_to_sync,
            dep_graph=dep_graph,
            sync_options=sync_options,
            github_info=github_info,
            quiet=quiet,
            verbose=verbose,
            issue_url=issue_url,
            module_cwds=module_cwds,
            module_targets=module_targets,
            module_contexts=module_contexts,
            module_units=module_units,
            initial_cost=llm_cost,
        )

    runner_success, runner_msg, total_cost = runner.run()

    if runner_success:
        return True, runner_msg, total_cost, provider
    else:
        return False, runner_msg, total_cost, provider


def _post_error_comment(owner: str, repo: str, issue_number: int, message: str) -> None:
    """Post an error comment on the GitHub issue."""
    trusted_payload = message.removeprefix("LLM failed to identify modules: ")
    marker = _extract_provider_environment_marker(trusted_payload)
    if marker and marker == trusted_payload:
        clean_message = (
            marker
            + "\n\nProvider setup needs attention. Fix provider installation/auth/update "
            "state, switch provider, or use non-interactive configuration, then retry."
        )
    else:
        clean_message = _sanitize_agentic_sync_error(message)
    body = (
        "## PDD Agentic Sync - Error\n\n"
        f"```\n{clean_message[:1000]}\n```\n"
    )
    body = _sanitize_comment_body(body)
    _run_gh_command([
        "api", f"repos/{owner}/{repo}/issues/{issue_number}/comments",
        "-X", "POST", "-f", f"body={body}",
    ])


_ANSI_CSI_RE = re.compile(r"\x1b(?:\[[0-?]*[ -/]*[@-~]|\][^\x07]*(?:\x07|\x1b\\))")
_ORPHAN_OSC_RE = re.compile(r"\x1b\][^\n]*")
_CARET_CSI_RE = re.compile(r"(?:\^\[|\\e|\\033)\[[0-?]*[ -/]*[@-~]")
_TERMINAL_GLYPH_RE = re.compile(
    r"[\u2800-\u28ff\u2500-\u257f\u2700-\u27bf\u23f5\u2191]"
)
_TERMINAL_NOISE_LINE_RE = re.compile(
    r"(?:auto[- ]?update|update available|permission required|press enter|"
    r"trust this workspace|bypass permissions|shift\+tab|esc to interrupt|"
    r"read and execute instructions|helper|keyboard shortcut|footer|cursor)",
    re.IGNORECASE,
)


def _sanitize_agentic_sync_error(message: str) -> str:
    """Render provider failures as readable, non-interactive public text."""
    text = _ANSI_CSI_RE.sub("", message or "")
    text = _ORPHAN_OSC_RE.sub("", text)
    text = _CARET_CSI_RE.sub("", text)
    clean_lines: List[str] = []
    for line in text.splitlines():
        line = _TERMINAL_GLYPH_RE.sub("", line)
        line = "".join(ch for ch in line if ch in "\t" or ord(ch) >= 32)
        if _TERMINAL_NOISE_LINE_RE.search(line):
            continue
        line = line.strip()
        if line:
            clean_lines.append(line)
    return _sanitize_comment_body("\n".join(clean_lines))


_PROVIDER_ENVIRONMENT_MARKER_RE = re.compile(
    r'PDD_PROVIDER_ENVIRONMENT_FAILURE_V1:'
    r'\{"provider":"(?:claude|anthropic|codex|openai|gemini|google|agy|opencode|unknown)",'
    r'"reason":"(?:interactive_ui|trust_prompt|permission_prompt|update_prompt|authentication|update_required|non_interactive_required|runtime_unavailable)"\}'
)


def _extract_provider_environment_marker(text: str) -> Optional[str]:
    """Return one exact full-line trusted marker, rejecting embedded prose."""
    matches = {
        line
        for line in (text or "").splitlines()
        if _PROVIDER_ENVIRONMENT_MARKER_RE.fullmatch(line)
    }
    return next(iter(matches)) if len(matches) == 1 else None
