"""
Agentic sync: LLM-driven module identification and parallel sync orchestration.

Entry point for `pdd sync <github_issue_url>`. Fetches issue content, uses an LLM
to determine which modules need syncing and validate architecture.json dependencies,
then dispatches to the async sync runner for parallel execution.
"""
from __future__ import annotations

import json
import logging
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, NamedTuple, Optional, Tuple

from rich.console import Console

from .agentic_change import _check_gh_cli, _escape_format_braces, _parse_issue_url, _run_gh_command
from .agentic_common import run_agentic_task
from .agentic_sync_runner import (
    AsyncSyncRunner,
    _basename_from_architecture_filename,
    _find_pdd_executable,
    build_dep_graph_from_architecture_data,
)
from .durable_sync_runner import DurableSyncRunner
from .architecture_include_validation import collect_architecture_include_validation_warnings
from .sync_graph_order_consistency import warnings_for_arch_vs_include_sync_order
from .architecture_registry import extract_modules, find_project_root as _find_project_root
from .construct_paths import (
    _detect_context_from_basename,
    _extract_prefix_from_prompts_dir,
    _find_pddrc_file,
    _load_pddrc_config,
)
from .json_atomic import atomic_write_json
from .load_prompt_template import load_prompt_template
from .sync_determine_operation import sync_determine_operation
from .sync_main import _detect_languages_with_context
from .sync_order import build_dependency_graph, extract_module_from_include, topological_sort

console = Console()

_GLOBAL_SYNC_NOOP_OPERATIONS = {"nothing", "all_synced"}
_GLOBAL_SYNC_TIER1_OPERATIONS = {"generate", "auto-deps"}
_SYNC_DETERMINE_LOGGER_NAME = "pdd.sync_determine_operation"


def _is_github_issue_url(s: str) -> bool:
    """Check if a string looks like a GitHub issue URL."""
    return bool(re.search(r"github\.com/.+/issues/\d+", s))


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

        # 4. Extract basenames
        basenames: List[str] = []
        for pf in prompt_files:
            # Strip leading path up to and including "prompts/"
            idx = pf.find("prompts/")
            if idx == -1:
                continue
            relative = pf[idx + len("prompts/"):]
            # Extract basename: strip language suffix from filename,
            # preserving subdirectory prefix (e.g. "commands/fix_python.prompt" -> "commands/fix")
            rel_path = Path(relative)
            filename_basename = extract_module_from_include(rel_path.name)
            if not filename_basename:
                continue
            # Re-attach subdirectory prefix if present
            if rel_path.parent != Path("."):
                basename = str(rel_path.parent / filename_basename)
            else:
                basename = filename_basename
            if basename not in basenames:
                basenames.append(basename)

        return basenames
    except (subprocess.CalledProcessError, OSError):
        return []


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

    branch_ref = f"origin/change/issue-{issue_number}"

    for arch_path in arch_files:
        try:
            rel_path = arch_path.relative_to(project_root)
        except ValueError:
            continue

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
    if architecture is None:
        return modules, []

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
        # Try standard extraction (handles _python.prompt, _typescript.prompt, etc.)
        basename = extract_module_from_include(filename)
        if basename:
            basename_counts[basename] += 1
        else:
            # Fallback for non-prompt filenames (e.g. "GitHubAppCTA.tsx" from
            # frontend/architecture.json) and LLM prompts (_LLM.prompt).
            # Strip known code extensions first, then .prompt and _LLM suffixes.
            stem = filename
            for ext in (".tsx", ".ts", ".jsx", ".js", ".py", ".prompt"):
                if stem.endswith(ext):
                    stem = stem[: -len(ext)]
                    break
            for suffix in ("_LLM",):
                if stem.endswith(suffix):
                    stem = stem[: -len(suffix)]
                    break
            if stem:
                basename_counts[stem] += 1

        # Also extract basename from filepath (e.g. "src/app/dashboard/page.tsx"
        # -> "page"). The filename field may use a different convention
        # (e.g. "dashboardPage.tsx") that doesn't match the prompt basename.
        filepath = entry.get("filepath", "")
        if filepath:
            fp_stem = Path(filepath).stem  # "page" from "page.tsx"
            if fp_stem and fp_stem not in basename_counts:
                basename_counts[fp_stem] += 1

    known_basenames = set(basename_counts.keys())

    valid = []
    invalid = []
    for m in modules:
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
    estimated_cost: float
    module_operations: Dict[str, List[str]]
    skipped_modules: List[str]
    all_modules: List[str]


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
        context_name = _detect_context_from_basename(basename, config)
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
    modules: List[str],
    project_root: Path,
    *,
    quiet: bool = False,
    budget: Optional[float] = None,
    skip_tests: bool = False,
    skip_verify: bool = False,
    target_coverage: Optional[float] = None,
) -> GlobalSyncAnalysis:
    """Tier 1 global sync analysis: fingerprint-scan all architecture modules."""
    modules_to_sync: List[str] = []
    module_cwds: Dict[str, Path] = {}
    module_operations: Dict[str, List[str]] = {}
    skipped_modules: List[str] = []
    estimated_cost = 0.0
    effective_budget = budget if budget is not None else 10.0
    effective_coverage = target_coverage if target_coverage is not None else 90.0

    for basename in modules:
        cwd = _resolve_module_cwd(basename, project_root)
        module_cwds[basename] = cwd

        try:
            context_name, prompts_dir, lang_to_path = _resolve_module_sync_context(
                basename, cwd
            )
        except Exception as exc:
            modules_to_sync.append(basename)
            module_operations[basename] = [
                f"analysis-error: {exc}; queued for sync as safe fallback"
            ]
            continue

        if not lang_to_path:
            skipped_modules.append(f"{basename}: no syncable prompt file found")
            continue

        operations: List[str] = []
        needs_sync = False
        for language in lang_to_path:
            try:
                decision = _run_readonly_sync_determine_in_cwd(
                    cwd,
                    basename=basename,
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
                    f"{language}: analysis-error ({exc}); queued for sync"
                )
                continue

            operations.append(f"{language}: {decision.operation} - {decision.reason}")
            if decision.operation in _GLOBAL_SYNC_TIER1_OPERATIONS:
                needs_sync = True
                estimated_cost += float(decision.estimated_cost or 0.0)
            elif decision.operation not in _GLOBAL_SYNC_NOOP_OPERATIONS:
                skipped_modules.append(
                    f"{basename}: {language} requires {decision.operation}; "
                    "outside Tier 1 prompt-staleness scope"
                )

        if needs_sync:
            modules_to_sync.append(basename)
            module_operations[basename] = operations

    if not quiet:
        skipped_count = len(modules) - len(modules_to_sync)
        console.print(
            f"[bold]Global sync analysis:[/bold] {len(modules_to_sync)} stale "
            f"module(s), {skipped_count} already synced or skipped."
        )

    return GlobalSyncAnalysis(
        modules_to_sync=modules_to_sync,
        module_cwds=module_cwds,
        estimated_cost=estimated_cost,
        module_operations=module_operations,
        skipped_modules=skipped_modules,
        all_modules=modules,
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


def _print_global_sync_plan(
    analysis: GlobalSyncAnalysis,
    ordered_modules: List[str],
    warnings: List[str],
    budget: Optional[float] = None,
) -> None:
    """Render a concise global sync dry-run plan."""
    console.print("[bold]Global sync dry run:[/bold]")
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
) -> Tuple[bool, str, float, str]:
    """Run project-wide Tier 1 global sync from architecture.json."""
    project_root = _find_project_root(Path.cwd())
    architecture, arch_path = _load_architecture_json(project_root)
    if architecture is None:
        return (
            False,
            f"No architecture.json found under {project_root}.",
            0.0,
            "global-sync",
        )

    all_modules = _architecture_module_basenames(architecture)
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
    )

    dep_result = build_dep_graph_from_architecture_data(
        architecture,
        analysis.modules_to_sync,
        source_name=f"combined architecture data under {project_root}",
    )
    ordered_modules = _dependency_ordered_modules(
        analysis.modules_to_sync, dep_result.graph
    )

    if dry_run:
        if not quiet:
            _print_global_sync_plan(analysis, ordered_modules, dep_result.warnings, budget)
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

    for warning in dep_result.warnings:
        if not quiet:
            console.print(f"[yellow]Warning: {warning}[/yellow]")

    runner = AsyncSyncRunner(
        basenames=ordered_modules,
        dep_graph=dep_result.graph,
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
        },
        github_info=None,
        quiet=quiet,
        verbose=verbose,
        issue_url=None,
        module_cwds=analysis.module_cwds,
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


def _resolve_module_cwd(basename: str, project_root: Path) -> Path:
    """Determine the correct working directory for a module based on .pddrc discovery.

    Logic:
    1. Scan subdirectories (recursive, max depth 2) for nested .pddrc files
       whose context patterns match the basename. Deepest match wins
       (nearest-config-wins resolution).
       Skip catch-all matches (e.g. paths: ['**']) from subdirectories —
       they match everything and should not claim ownership of unrelated modules.
    2. Fall back to project_root (which may have its own root .pddrc).
    """
    # 1. Scan subdirectories for .pddrc files (max depth 2)
    best_match: Optional[Path] = None
    best_depth = -1

    for depth in range(1, 3):
        pattern = "/".join(["*"] * depth) + "/.pddrc"
        for pddrc_path in project_root.glob(pattern):
            try:
                config = _load_pddrc_config(pddrc_path)
                detected = _detect_context_from_basename(basename, config)
                if detected and detected != "default":
                    # Skip catch-all patterns from subdirectories — they match
                    # everything and would incorrectly claim unrelated modules
                    if _is_catchall_match(basename, config):
                        continue
                    candidate_dir = pddrc_path.parent
                    candidate_depth = len(candidate_dir.relative_to(project_root).parts)
                    if candidate_depth > best_depth:
                        best_match = candidate_dir
                        best_depth = candidate_depth
            except (ValueError, OSError):
                continue

    if best_match is not None:
        return best_match

    # 2. Fall back to project root
    return project_root


def _run_single_dry_run(
    basename: str, cwd: Path, quiet: bool = False
) -> Tuple[bool, str]:
    """Run pdd sync <basename> --dry-run from the given cwd.

    Returns:
        Tuple of (success, stderr_output).
    """
    pdd_exe = _find_pdd_executable()
    if pdd_exe:
        cmd = [pdd_exe]
    else:
        cmd = [sys.executable, "-m", "pdd"]

    cmd.extend(["--force", "sync", basename, "--dry-run", "--agentic", "--no-steer"])

    try:
        result = subprocess.run(
            cmd,
            cwd=str(cwd),
            capture_output=True,
            text=True,
            timeout=60,
            env={**os.environ, "PDD_FORCE": "1", "CI": "1"},
        )
        if result.returncode == 0:
            return True, ""
        return False, result.stderr or result.stdout or f"Exit code {result.returncode}"
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

    llm_success, llm_output, llm_cost, _ = run_agentic_task(
        instruction=prompt,
        cwd=project_root,
        verbose=verbose,
        quiet=quiet,
        label="agentic_sync_fix_dry_run",
        reasoning_time=reasoning_time,
    )

    if not llm_success:
        return False, None, llm_cost, f"LLM failed to suggest fix: {llm_output}"

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
    try:
        result = subprocess.run(
            augmented_cmd,
            shell=True,
            cwd=str(project_root),
            capture_output=True,
            text=True,
            timeout=60,
            env={**os.environ, "PDD_FORCE": "1", "CI": "1"},
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
        return (
            False,
            None,
            llm_cost,
            f"LLM suggested command failed: {err_output[:500]}",
        )


def _run_dry_run_validation(
    modules: List[str],
    project_root: Path,
    quiet: bool = False,
    verbose: bool = False,
    reasoning_time: Optional[float] = None,
) -> Tuple[bool, Dict[str, Path], List[str], float]:
    """Run dry-run validation for each module with LLM fallback.

    Returns:
        Tuple of (all_valid, module_to_cwd_map, error_messages, total_llm_cost).
    """
    module_cwds: Dict[str, Path] = {}
    errors: List[str] = []
    total_llm_cost = 0.0

    for basename in modules:
        # 1. Resolve cwd programmatically
        cwd = _resolve_module_cwd(basename, project_root)

        # 2. Run dry-run
        ok, err_output = _run_single_dry_run(basename, cwd, quiet=quiet)

        if ok:
            module_cwds[basename] = cwd
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
        )
        total_llm_cost += llm_cost

        if llm_ok and llm_cwd is not None:
            module_cwds[basename] = llm_cwd
            if not quiet:
                try:
                    rel = Path(".") if llm_cwd == project_root else llm_cwd.relative_to(project_root)
                except ValueError:
                    rel = llm_cwd
                console.print(
                    f"[green]LLM resolved {basename} → cwd: {rel}[/green]"
                )
        else:
            errors.append(f"{basename}: {llm_err or err_output}")

    all_valid = len(errors) == 0
    return all_valid, module_cwds, errors, total_llm_cost


def _filter_already_synced(
    modules: List[str],
    module_cwds: Dict[str, Path],
    quiet: bool = False,
) -> List[str]:
    """Filter out modules that are already fully synced (fingerprint matches).

    For each module, runs sync_determine_operation in log_mode (read-only)
    to check if the operation is 'nothing' (all hashes match, workflow complete).
    Modules returning 'nothing' are removed from the sync list.

    Returns:
        List of module basenames that actually need syncing.
    """
    needs_sync: List[str] = []

    for basename in modules:
        cwd = module_cwds.get(basename)
        if cwd is None:
            # No resolved cwd — keep it in the list for the runner to handle
            needs_sync.append(basename)
            continue

        try:
            context_name, prompts_dir, lang_to_path = _resolve_module_sync_context(
                basename, cwd
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
                    basename=basename,
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
    arch_path: Path,
    architecture: List[Dict[str, Any]],
    corrections: List[Dict[str, Any]],
    quiet: bool = False,
) -> List[Dict[str, Any]]:
    """
    Apply LLM-suggested dependency corrections to architecture.json.

    Args:
        arch_path: Path to architecture.json.
        architecture: Current architecture data.
        corrections: List of correction dicts with 'filename' and 'dependencies'.
        quiet: Suppress output.

    Returns:
        Updated architecture data.
    """
    # Build lookup by filename
    filename_to_idx: Dict[str, int] = {}
    for idx, entry in enumerate(architecture):
        filename_to_idx[entry.get("filename", "")] = idx

    changes_made = 0
    for correction in corrections:
        filename = correction.get("filename", "")
        new_deps = correction.get("dependencies", [])
        if filename in filename_to_idx:
            idx = filename_to_idx[filename]
            old_deps = architecture[idx].get("dependencies", [])
            architecture[idx]["dependencies"] = new_deps
            changes_made += 1
            if not quiet:
                console.print(
                    f"[yellow]Updated deps for {filename}: "
                    f"{old_deps} -> {new_deps}[/yellow]"
                )

    if changes_made > 0:
        try:
            atomic_write_json(arch_path, architecture)
            if not quiet:
                console.print(
                    f"[green]Wrote {changes_made} dependency correction(s) "
                    f"to {arch_path}[/green]"
                )
        except OSError as e:
            if not quiet:
                console.print(f"[red]Failed to write architecture.json: {e}[/red]")

    return architecture


def run_agentic_sync(
    issue_url: str,
    *,
    verbose: bool = False,
    quiet: bool = False,
    budget: Optional[float] = None,
    skip_verify: bool = False,
    skip_tests: bool = False,
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

    # 5. Build issue content
    issue_content = f"Title: {title}\n\nDescription:\n{body}\n"
    if comments_data and isinstance(comments_data, list):
        issue_content += "\nComments:\n"
        for comment in comments_data:
            if isinstance(comment, dict):
                c_user = comment.get("user", {}).get("login", "unknown")
                c_body = comment.get("body", "")
                issue_content += f"\n--- Comment by {c_user} ---\n{c_body}\n"

    issue_content = _escape_format_braces(issue_content)

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

    if branch_modules:
        if not quiet:
            console.print(f"[green]Detected modules from branch diff: {branch_modules}[/green]")
        modules_to_sync = branch_modules
    else:
        # 7b. Fall back to LLM-based module identification
        prompt_template = load_prompt_template("agentic_sync_identify_modules_LLM")
        if not prompt_template:
            return False, "Failed to load agentic_sync_identify_modules_LLM prompt template", 0.0, ""

        arch_json_str = json.dumps(architecture, indent=2) if architecture else "No architecture.json available."
        # Escape braces in dynamic content to prevent .format() from interpreting
        # code references like {uid} as template placeholders
        safe_arch_json = arch_json_str.replace("{", "{{").replace("}", "}}")
        prompt = prompt_template.format(
            issue_content=issue_content,
            architecture_json=safe_arch_json,
            issue_number=issue_number,
        )

        if not quiet:
            console.print("[bold]Identifying modules to sync via LLM...[/bold]")

        # 8. Call LLM
        llm_success, llm_output, llm_cost, provider = run_agentic_task(
            instruction=prompt,
            cwd=project_root,
            verbose=verbose,
            quiet=quiet,
            label="agentic_sync_identify_modules",
            reasoning_time=reasoning_time,
        )

        if not llm_success:
            msg = f"LLM failed to identify modules: {llm_output}"
            if use_github_state:
                _post_error_comment(owner, repo, issue_number, msg)
            return False, msg, llm_cost, provider

        # 9. Parse LLM response
        modules_to_sync, deps_valid, deps_corrections = _parse_llm_response(llm_output)

        if not modules_to_sync:
            return False, "LLM identified no modules to sync", llm_cost, provider

    # LLM returns basenames from architecture.json filenames (e.g., "crm_models_Python").
    # pdd sync expects basenames without the language suffix (e.g., "crm_models").
    # Strip language suffixes using the same logic as the step 10 dry-run guide.
    # Deduplicate after stripping: LLM may return both "recruiting_config_Python" and
    # "recruiting_config" which both map to "recruiting_config" after suffix removal.
    stripped_modules = []
    for m in modules_to_sync:
        stripped = extract_module_from_include(m + ".prompt")
        stripped_modules.append(stripped if stripped else m)
    modules_to_sync = list(dict.fromkeys(stripped_modules))

    # 9.4 Augment architecture with entries from the PR branch (new modules created by pdd-change)
    architecture = _augment_architecture_from_pr_branch(architecture, project_root, issue_number)

    # 9.5 Filter out basenames not in architecture.json (catches LLM hallucinations)
    modules_to_sync, invalid_basenames = _filter_invalid_basenames(modules_to_sync, architecture)
    if invalid_basenames:
        if not quiet:
            console.print(f"[yellow]Warning: Skipping {len(invalid_basenames)} basenames not found in architecture.json: {invalid_basenames}[/yellow]")
    if not modules_to_sync:
        msg = f"No valid modules to sync (all basenames were invalid: {invalid_basenames})"
        if use_github_state:
            _post_error_comment(owner, repo, issue_number, msg)
        return False, msg, llm_cost, provider

    if not quiet:
        console.print(f"[green]Modules to sync: {modules_to_sync}[/green]")

    # 10. Apply dependency corrections if needed
    if not deps_valid and deps_corrections and architecture is not None:
        if not quiet:
            console.print("[yellow]LLM flagged dependency corrections, updating architecture.json...[/yellow]")
        architecture = _apply_architecture_corrections(arch_path, architecture, deps_corrections, quiet)

    # 11. Build dependency graph
    if architecture is not None:
        dep_graph_result = build_dep_graph_from_architecture_data(
            architecture,
            modules_to_sync,
            source_name=str(arch_path),
        )
        dep_graph = dep_graph_result.graph
        if dep_graph_result.warnings and not quiet:
            for w in dep_graph_result.warnings:
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

    all_valid, module_cwds, dry_run_errors, dry_run_cost = _run_dry_run_validation(
        modules=modules_to_sync,
        project_root=project_root,
        quiet=quiet,
        verbose=verbose,
        reasoning_time=reasoning_time,
    )
    llm_cost += dry_run_cost

    if not all_valid:
        error_detail = "\n".join(dry_run_errors)
        msg = f"Dry-run validation failed:\n{error_detail}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        if use_github_state:
            _post_error_comment(owner, repo, issue_number, msg)
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

    modules_to_sync = _filter_already_synced(modules_to_sync, module_cwds, quiet=quiet)
    if not modules_to_sync:
        msg = "All modules are already synced — nothing to do."
        if not quiet:
            console.print(f"[green]{msg}[/green]")
        return True, msg, llm_cost, provider

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
    }

    github_info = {
        "owner": owner,
        "repo": repo,
        "issue_number": issue_number,
        "cwd": project_root,
    } if use_github_state else None

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
            initial_cost=llm_cost,
        )

    runner_success, runner_msg, total_cost = runner.run()

    if runner_success:
        return True, runner_msg, total_cost, provider
    else:
        return False, runner_msg, total_cost, provider


def _post_error_comment(owner: str, repo: str, issue_number: int, message: str) -> None:
    """Post an error comment on the GitHub issue."""
    body = (
        "## PDD Agentic Sync - Error\n\n"
        f"```\n{message[:1000]}\n```\n"
    )
    _run_gh_command([
        "api", f"repos/{owner}/{repo}/issues/{issue_number}/comments",
        "-X", "POST", "-f", f"body={body}",
    ])
