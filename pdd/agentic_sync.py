"""
Agentic sync: LLM-driven module identification and parallel sync orchestration.

Entry point for `pdd sync <github_issue_url>`. Fetches issue content, uses an LLM
to determine which modules need syncing and validate architecture.json dependencies,
then dispatches to the async sync runner for parallel execution.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from rich.console import Console

from .agentic_change import _check_gh_cli, _escape_format_braces, _parse_issue_url, _run_gh_command
from .agentic_common import run_agentic_task
from .agentic_sync_runner import AsyncSyncRunner, _find_pdd_executable, build_dep_graph_from_architecture
from .construct_paths import _detect_context_from_basename, _load_pddrc_config
from .load_prompt_template import load_prompt_template
from .sync_order import build_dependency_graph, extract_module_from_include, topological_sort

console = Console()


def _is_github_issue_url(s: str) -> bool:
    """Check if a string looks like a GitHub issue URL."""
    return bool(re.search(r"github\.com/.+/issues/\d+", s))


def _find_project_root(start: Path) -> Path:
    """Walk up from start to find project root (directory containing .pddrc or .git)."""
    current = start.resolve()
    for _ in range(20):
        if (current / ".pddrc").exists() or (current / ".git").exists():
            return current
        parent = current.parent
        if parent == current:
            break
        current = parent
    return start.resolve()


def _load_architecture_json(project_root: Path) -> Tuple[Optional[List[Dict[str, Any]]], Path]:
    """
    Load architecture.json from the project root.

    Returns:
        Tuple of (parsed data or None, path to architecture.json).
    """
    arch_path = project_root / "architecture.json"
    if not arch_path.exists():
        return None, arch_path
    try:
        with open(arch_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            return data, arch_path
        return None, arch_path
    except (json.JSONDecodeError, OSError):
        return None, arch_path


def _resolve_module_cwd(basename: str, project_root: Path) -> Path:
    """Determine the correct working directory for a module based on .pddrc discovery.

    Logic:
    1. Try project root first — load its .pddrc, check if a non-default context matches.
    2. If matched, return project_root.
    3. If not, scan subdirectories (recursive, max depth 2) for .pddrc files.
       For each, load and check if a context matches. Deepest match wins.
    4. Fall back to project_root.
    """
    # 1. Check project root .pddrc
    root_pddrc = project_root / ".pddrc"
    if root_pddrc.exists():
        try:
            config = _load_pddrc_config(root_pddrc)
            detected = _detect_context_from_basename(basename, config)
            if detected and detected != "default":
                return project_root
        except (ValueError, OSError):
            pass

    # 2. Scan subdirectories for .pddrc files (max depth 2)
    best_match: Optional[Path] = None
    best_depth = -1

    for depth in range(1, 3):
        pattern = "/".join(["*"] * depth) + "/.pddrc"
        for pddrc_path in project_root.glob(pattern):
            try:
                config = _load_pddrc_config(pddrc_path)
                detected = _detect_context_from_basename(basename, config)
                if detected and detected != "default":
                    candidate_dir = pddrc_path.parent
                    candidate_depth = len(candidate_dir.relative_to(project_root).parts)
                    if candidate_depth > best_depth:
                        best_match = candidate_dir
                        best_depth = candidate_depth
            except (ValueError, OSError):
                continue

    if best_match is not None:
        return best_match

    # 3. Fall back to project root
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
    )

    if not llm_success:
        return False, None, llm_cost, f"LLM failed to suggest fix: {llm_output}"

    # Parse SYNC_CWD from response
    match = re.search(r"SYNC_CWD:\s*(.+)", llm_output)
    if not match:
        return False, None, llm_cost, "LLM response did not contain SYNC_CWD marker"

    suggested_rel = match.group(1).strip()
    project_root_resolved = project_root.resolve()
    suggested_cwd = (project_root_resolved / suggested_rel).resolve()

    # Guard against symlink-based directory traversal outside project root
    try:
        suggested_cwd.relative_to(project_root_resolved)
    except ValueError:
        return (
            False,
            None,
            llm_cost,
            f"LLM suggested directory outside project root: {suggested_rel}",
        )

    if not suggested_cwd.is_dir():
        return False, None, llm_cost, f"LLM suggested non-existent directory: {suggested_rel}"

    # Re-validate with dry-run from suggested cwd
    revalidate_ok, revalidate_err = _run_single_dry_run(basename, suggested_cwd, quiet=quiet)
    if revalidate_ok:
        return True, suggested_cwd, llm_cost, ""
    else:
        return (
            False,
            None,
            llm_cost,
            f"LLM suggested cwd '{suggested_rel}' but dry-run still failed: {revalidate_err[:500]}",
        )


def _run_dry_run_validation(
    modules: List[str],
    project_root: Path,
    quiet: bool = False,
    verbose: bool = False,
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
        # Parse quoted strings
        modules_to_sync = [m.strip().strip('"').strip("'") for m in raw.split(",") if m.strip().strip('"').strip("'")]

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
            with open(arch_path, "w", encoding="utf-8") as f:
                json.dump(architecture, f, indent=2, ensure_ascii=False)
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
) -> Tuple[bool, str, float, str]:
    """
    Run agentic sync workflow: identify modules from a GitHub issue and sync in parallel.

    Args:
        issue_url: GitHub issue URL.
        verbose: Enable detailed logging.
        quiet: Suppress standard output.
        budget: Max cost per module sync.
        skip_verify: Skip verification step.
        skip_tests: Skip test generation.
        agentic_mode: Use agentic mode for individual syncs.
        no_steer: Disable interactive steering.
        max_attempts: Max fix attempts per module.
        timeout_adder: Additional timeout per step.
        use_github_state: Enable GitHub comment updates.

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
    architecture, arch_path = _load_architecture_json(project_root)

    if architecture is None:
        if not quiet:
            console.print("[yellow]No architecture.json found, falling back to include-based dependency graph[/yellow]")

    # 7. Build LLM prompt for module identification
    prompt_template = load_prompt_template("agentic_sync_identify_modules_LLM")
    if not prompt_template:
        return False, "Failed to load agentic_sync_identify_modules_LLM prompt template", 0.0, ""

    arch_json_str = json.dumps(architecture, indent=2) if architecture else "No architecture.json available."
    prompt = prompt_template.format(
        issue_content=issue_content,
        architecture_json=arch_json_str,
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
    stripped_modules = []
    for m in modules_to_sync:
        stripped = extract_module_from_include(m + ".prompt")
        stripped_modules.append(stripped if stripped else m)
    modules_to_sync = stripped_modules

    if not quiet:
        console.print(f"[green]Modules to sync: {modules_to_sync}[/green]")

    # 10. Apply dependency corrections if needed
    if not deps_valid and deps_corrections and architecture is not None:
        if not quiet:
            console.print("[yellow]LLM flagged dependency corrections, updating architecture.json...[/yellow]")
        architecture = _apply_architecture_corrections(arch_path, architecture, deps_corrections, quiet)

    # 11. Build dependency graph
    if architecture is not None:
        dep_graph = build_dep_graph_from_architecture(arch_path, modules_to_sync)
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

    # 12. Run parallel sync
    sync_options = {
        "budget": budget,
        "skip_verify": skip_verify,
        "skip_tests": skip_tests,
        "agentic": agentic_mode,
        "no_steer": no_steer,
        "max_attempts": max_attempts,
    }

    github_info = {
        "owner": owner,
        "repo": repo,
        "issue_number": issue_number,
        "cwd": project_root,
    } if use_github_state else None

    runner = AsyncSyncRunner(
        basenames=modules_to_sync,
        dep_graph=dep_graph,
        sync_options=sync_options,
        github_info=github_info,
        quiet=quiet,
        verbose=verbose,
        issue_url=issue_url,
        module_cwds=module_cwds,
    )

    runner_success, runner_msg, runner_cost = runner.run()
    total_cost = llm_cost + runner_cost

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
