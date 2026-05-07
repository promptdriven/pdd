"""
CLI entry point for the agentic architecture workflow.
Detects GitHub issue URLs, fetches issue content and comments via `gh api`,
ensures repository context is available, then invokes the orchestrator.
"""

from __future__ import annotations

import json
import re
import shutil
import subprocess
from pathlib import Path
from typing import List, Optional, Tuple

from rich.console import Console

# Internal imports
from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .agentic_architecture_orchestrator import run_agentic_architecture_orchestrator
from .architecture_registry import extract_modules, find_git_toplevel, find_project_root
from .incremental_prd_architecture import INCREMENTAL_STATUS_MARKER

# Backwards-compatible alias for any code that imported the leading-underscore name.
_INCREMENTAL_STATUS_MARKER = INCREMENTAL_STATUS_MARKER

_SAFE_PATH_SEGMENT = r"[A-Za-z0-9_](?:[A-Za-z0-9._-]*[A-Za-z0-9_])?"
_TARGET_DIR_PATTERN = re.compile(rf"{_SAFE_PATH_SEGMENT}(/{_SAFE_PATH_SEGMENT})*")
_UNQUOTED_TARGET_RE = re.compile(
    rf"\bin\s+({_TARGET_DIR_PATTERN.pattern})(?=$|[\s`\"'),.:!?])",
    re.IGNORECASE,
)

console = Console()


def _is_github_issue_url(url: str) -> bool:
    """
    Detect if the string is a valid GitHub issue URL.
    
    Args:
        url: The URL string to check.
        
    Returns:
        True if the URL matches the GitHub issue pattern, False otherwise.
    """
    return _parse_github_url(url) is not None


def _parse_github_url(url: str) -> Optional[Tuple[str, str, int]]:
    """
    Extract owner, repo, and issue number from a GitHub URL.
    
    Supports:
      - https://github.com/{owner}/{repo}/issues/{number}
      - https://www.github.com/{owner}/{repo}/issues/{number}
      - github.com/{owner}/{repo}/issues/{number}
      
    Args:
        url: The URL string to parse.
        
    Returns:
        Tuple of (owner, repo, issue_number) if successful, None otherwise.
    """
    pattern = r"(?:https?://)?(?:www\.)?github\.com/([^/]+)/([^/]+)/issues/(\d+)"
    match = re.search(pattern, url)
    if match:
        owner, repo, number = match.groups()
        return owner, repo, int(number)
    return None


def _check_gh_cli() -> bool:
    """Check if gh CLI tool is available on the PATH."""
    return shutil.which("gh") is not None


def _run_gh_command(args: List[str]) -> Tuple[bool, str]:
    """
    Run a gh command and return (success, stdout/stderr).
    
    Args:
        args: List of arguments to pass to the gh command.
        
    Returns:
        Tuple of (success boolean, output string).
    """
    try:
        result = subprocess.run(
            ["gh"] + args,
            capture_output=True,
            text=True,
            check=True
        )
        return True, result.stdout
    except subprocess.CalledProcessError as e:
        return False, e.stderr or str(e)
    except FileNotFoundError:
        return False, "gh CLI not found"


def _ensure_repo_context(
    owner: str,
    repo: str,
    current_cwd: Path,
    quiet: bool,
    *,
    project_root: Optional[Path] = None,
) -> Tuple[Path, Optional[str]]:
    """
    Ensure the repository is available locally.

    Logic:
    1. If current_cwd is inside the target repo (checked via remote), use it.
    2. If current_cwd is a git repo but the remote does not match owner/repo,
       warn and proceed — except when ``project_root`` is a strict descendant
       of the enclosing git toplevel (a self-contained pdd project nested
       inside an unrelated outer git repo), in which case the warning is
       suppressed because the outer remote is irrelevant.
    3. If current_cwd is NOT a git repo:
       a. Check if subdirectory {repo} exists and is a git repo -> use it.
       b. Clone {owner}/{repo} -> use it.

    Args:
        owner: Repository owner.
        repo: Repository name.
        current_cwd: Current working directory.
        quiet: Whether to suppress non-error output.
        project_root: Optional resolved PDD project root. When the project root
            is a strict descendant of the enclosing git toplevel, the
            remote-vs-issue mismatch warning is suppressed (the cwd is a
            self-contained pdd project nested inside an unrelated outer git
            repo, so the remote of that outer repo is irrelevant).

    Returns:
        Tuple of (path to repo root, error message if any).
    """

    def get_remote_url(path: Path) -> Optional[str]:
        try:
            res = subprocess.run(
                ["git", "config", "--get", "remote.origin.url"],
                cwd=path, capture_output=True, text=True
            )
            if res.returncode == 0:
                return res.stdout.strip()
        except Exception:
            pass
        return None

    # Case 1 & 2: Already in a git repo
    remote = get_remote_url(current_cwd)
    if remote:
        # Simple check if owner/repo is in the remote URL
        # Remotes can be git@github.com:owner/repo.git or https://github.com/owner/repo.git
        if f"{owner}/{repo}" in remote or f"{owner}/{repo}.git" in remote:
            return current_cwd, None

        # Mismatch. Suppress the warning when the resolved PDD project root is
        # a strict descendant of the enclosing git toplevel — the cwd is a
        # self-contained pdd project nested inside an unrelated outer git repo,
        # so the outer remote is expected to differ from the issue's owner/repo
        # and the warning is a false positive.
        suppress_warning = False
        if project_root is not None:
            try:
                git_top = find_git_toplevel(current_cwd)
                if git_top is not None:
                    pr_resolved = project_root.resolve()
                    git_top_resolved = git_top.resolve()
                    if pr_resolved != git_top_resolved:
                        pr_resolved.relative_to(git_top_resolved)
                        suppress_warning = True
            except (ValueError, OSError):
                suppress_warning = False

        if not quiet and not suppress_warning:
            console.print(f"[yellow]Warning: Current directory is a git repo but remote '{remote}' does not match '{owner}/{repo}'. Proceeding in current directory.[/yellow]")
        return current_cwd, None

    # Case 3: Not in a git repo
    target_dir = current_cwd / repo
    
    # 3a: Subdirectory exists
    if target_dir.exists() and target_dir.is_dir():
        if (target_dir / ".git").exists():
            if not quiet:
                console.print(f"[blue]Found existing repository at {target_dir}[/blue]")
            return target_dir, None
        else:
            return current_cwd, f"Directory '{repo}' exists but is not a git repository."

    # 3b: Clone
    if not quiet:
        console.print(f"[blue]Cloning {owner}/{repo} into {target_dir}...[/blue]")
    
    try:
        subprocess.run(
            ["gh", "repo", "clone", f"{owner}/{repo}"],
            cwd=current_cwd,
            check=True,
            capture_output=True,
            text=True
        )
        return target_dir, None
    except subprocess.CalledProcessError as e:
        err_msg = e.stderr if e.stderr else str(e)
        return current_cwd, f"Failed to clone repository: {err_msg}"


def _parse_related_issues(issue_body: str) -> List[int]:
    """Extract related sub-issue numbers from issue body."""
    pattern = r'###\s*Related sub-issues:\s*\n((?:\s*-\s*#\d+.*\n?)*)'
    match = re.search(pattern, issue_body, re.IGNORECASE)
    if not match:
        return []
    refs = re.findall(r'#(\d+)', match.group(1))
    return [int(n) for n in refs]


def _read_sibling_context_yamls(sibling_dir: Path) -> dict:
    """Read context YAML files from a sibling project's prompts/_context/ directory."""
    context_dir = sibling_dir / "prompts" / "_context"
    result = {}
    if not context_dir.is_dir():
        return result
    for yaml_name in ("data_dictionary.yaml", "api_contracts.yaml"):
        yaml_path = context_dir / yaml_name
        if yaml_path.exists():
            try:
                content = yaml_path.read_text(encoding="utf-8")
                if content.strip():
                    result[yaml_name] = content
            except IOError:
                continue
    return result


def _fetch_sibling_architectures(cwd: Path, current_target_dir: Optional[str]) -> str:
    """Scan repo for existing architecture.json files from sibling sub-projects."""
    siblings = {}
    sibling_contexts: dict = {}
    try:
        children = list(cwd.iterdir())
    except (OSError, IOError):
        return ""
    for child in children:
        if not child.is_dir() or child.name.startswith('.') or child.name in ('node_modules', '__pycache__'):
            continue
        if current_target_dir and child.name == current_target_dir:
            continue
        arch_file = child / "architecture.json"
        if arch_file.exists():
            try:
                arch_data = json.loads(arch_file.read_text(encoding="utf-8"))
                modules = extract_modules(arch_data)
                if modules:
                    siblings[child.name] = modules
                    sibling_contexts[child.name] = _read_sibling_context_yamls(child)
            except (json.JSONDecodeError, IOError):
                continue
    # Also check root architecture.json if we're generating into a subdir
    if current_target_dir:
        root_arch = cwd / "architecture.json"
        if root_arch.exists():
            try:
                arch_data = json.loads(root_arch.read_text(encoding="utf-8"))
                modules = extract_modules(arch_data)
                if modules:
                    siblings["."] = modules
                    sibling_contexts["."] = _read_sibling_context_yamls(cwd)
            except (json.JSONDecodeError, IOError):
                pass
    if not siblings:
        return ""
    # Format as markdown summary table
    lines = [
        "## Existing Architecture from Related Sub-Issues",
        "",
        "The following sub-projects have already been generated. "
        "You MUST read their architecture.json files and make proper updates rather than overwriting. "
        "Do NOT duplicate modules that already exist.",
        "",
    ]
    for dir_name, modules in siblings.items():
        lines.append(f"### `{dir_name}/` ({len(modules)} modules)")
        lines.append("| Filename | Filepath | Description | Interface Type | Origin Issue |")
        lines.append("|----------|----------|-------------|----------------|--------------|")
        for mod in modules:
            fn = mod.get("filename", "?")
            fp = mod.get("filepath", "?")
            desc = mod.get("reason", mod.get("description", ""))[:80]
            itype = mod.get("interface", {}).get("type", "?") if isinstance(mod.get("interface"), dict) else "?"
            origin = mod.get("origin", {})
            origin_issue = f"#{origin.get('issue_number', '?')}" if isinstance(origin, dict) and origin.get("issue_number") else "-"
            lines.append(f"| {fn} | {fp} | {desc} | {itype} | {origin_issue} |")
        lines.append("")

        # Include full interface details for cross-project dependency resolution
        interfaces_with_detail = [m for m in modules if isinstance(m.get("interface"), dict)
                                  and m["interface"].get("type") != "?" and len(m["interface"]) > 1]
        if interfaces_with_detail:
            lines.append(f"#### `{dir_name}/` Interface Details")
            lines.append("")
            for mod in interfaces_with_detail:
                fn = mod.get("filename", "?")
                iface = mod["interface"]
                lines.append(f"**{fn}** (`{iface.get('type', '?')}`):")
                lines.append(f"```json\n{json.dumps(iface, indent=2)}\n```")
                lines.append("")

        # Include sibling context YAML files (data dictionary, API contracts)
        ctx = sibling_contexts.get(dir_name, {})
        if ctx:
            lines.append(f"#### `{dir_name}/` Shared Context Documents")
            lines.append("")
            for yaml_name, yaml_content in ctx.items():
                lines.append(f"**`{dir_name}/prompts/_context/{yaml_name}`:**")
                lines.append(f"```yaml\n{yaml_content}\n```")
                lines.append("")

    return "\n".join(lines)


def _read_existing_pddrc(cwd: Path) -> str:
    """Read root .pddrc if it exists, return its content for merge context."""
    pddrc_file = cwd / ".pddrc"
    if pddrc_file.exists():
        try:
            return pddrc_file.read_text(encoding="utf-8")
        except IOError:
            return ""
    return ""


def _read_existing_architecture(cwd: Path, target_dir: Optional[str]) -> str:
    """Read existing architecture.json at the target location."""
    base = cwd / target_dir if target_dir else cwd
    arch_file = base / "architecture.json"
    if arch_file.exists():
        try:
            return arch_file.read_text(encoding="utf-8")
        except IOError:
            return ""
    return ""


def _is_safe_target_dir(target_dir: str) -> bool:
    """Return True for shell-safe repo-relative target dirs."""
    if not isinstance(target_dir, str):
        return False
    value = target_dir.strip().rstrip("/")
    if not value or value == ".":
        return True
    path = Path(value)
    return not (
        path.is_absolute()
        or "\\" in value
        or ".." in path.parts
    ) and bool(_TARGET_DIR_PATTERN.fullmatch(value))


def _resolve_target_dir(repo_path: Path, target_dir: Optional[str]) -> Tuple[Path, Optional[str], Optional[str]]:
    """Validate and resolve a target_dir under repo_path.

    Returns (base_dir, normalized_target_dir, error). The normalized target is
    safe to pass to downstream orchestrators; base_dir is guaranteed to resolve
    inside repo_path.
    """
    repo_root = repo_path.resolve()
    if target_dir is None:
        return repo_root, None, None

    normalized = target_dir.strip().rstrip("/")
    if normalized in ("", "."):
        return repo_root, None, None
    if not _is_safe_target_dir(normalized):
        return repo_root, None, f"Invalid target directory: {target_dir!r}"

    base_dir = (repo_root / normalized).resolve()
    try:
        base_dir.relative_to(repo_root)
    except ValueError:
        return repo_root, None, f"Invalid target directory: {target_dir!r}"
    return base_dir, normalized, None


def _extract_target_dir(issue_body: str) -> Optional[str]:
    """
    Parse target directory from issue body.

    Matches patterns like:
      - in `src/my_app/`         (backtick-quoted with trailing slash)
      - in `src/my_app`          (backtick-quoted)
      - in "src/my_app"          (double-quoted)
      - in src/my_app/           (unquoted with trailing slash)

    Uses tight patterns to avoid matching natural English like "in Python",
    "in the", "in a new directory", etc.
    """
    # Pattern 1: backtick or double-quote wrapped. Capture broadly enough to
    # detect explicit unsafe paths like `../outside` and fail instead of falling
    # back to the repo root.
    quoted = re.compile(r'\bin\s+[`"]([^`"]+)[`"]', re.IGNORECASE)
    match = quoted.search(issue_body)
    if match:
        candidate = match.group(1).strip().rstrip("/")
        if candidate in ("", "."):
            return None
        if not _is_safe_target_dir(candidate):
            raise ValueError(f"Invalid target directory: {candidate!r}")
        return candidate

    match = _UNQUOTED_TARGET_RE.search(issue_body)
    if match:
        candidate = match.group(1).strip().rstrip("/")
        if not ("/" in candidate or "_" in candidate or "." in candidate):
            return None
        if not _is_safe_target_dir(candidate):
            raise ValueError(f"Invalid target directory: {candidate!r}")
        return candidate
    return None


def run_agentic_architecture(
    issue_url: str,
    *,
    verbose: bool = False,
    quiet: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True,
    skip_prompts: bool = False,
    target_dir: Optional[str] = None,
    force_single: bool = False,
    project_root: Optional[str] = None,
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Entry point for the agentic architecture workflow.

    1. Validates the GitHub issue URL.
    2. Fetches issue details and comments using `gh` CLI.
    3. Ensures the repository is available locally (clones if necessary).
    4. Invokes the architecture orchestrator.

    Args:
        issue_url: Full URL to the GitHub issue.
        verbose: Enable verbose logging.
        quiet: Suppress non-error output.
        timeout_adder: Additional seconds to add to step timeouts.
        use_github_state: Whether to persist state to GitHub comments.
        skip_prompts: If True, skip Step 9 (prompt generation). Default False (prompts ARE generated).
        target_dir: Optional subdirectory for new project. If None, parsed from issue body.
        force_single: If True, skip complexity check and force single-project generation.
        project_root: Optional explicit override for the resolved PDD project root.
            When None, walks up from cwd through tier A/B/C markers (`.pddrc`/`.pdd/`,
            `sources/` + PRD/spec markdown, `.git`). When supplied, the path is used
            verbatim, bypassing marker discovery.

    Returns:
        Tuple containing:
        - success (bool): Whether the workflow completed successfully.
        - message (str): Final status message or error description.
        - total_cost (float): Total estimated cost of LLM calls.
        - model_used (str): The model used for the last step.
        - output_files (List[str]): List of files generated/modified.
    """
    cwd = Path.cwd()

    # Resolve PDD project root. Explicit --project-root wins; otherwise walk up
    # from cwd looking for PDD-explicit / PDD-conventional / git markers so a
    # self-contained pdd project nested inside an unrelated outer git repo is
    # detected as its own root.
    if project_root is not None:
        candidate = Path(project_root).expanduser()
        if not candidate.exists():
            return False, f"project_root does not exist: {candidate}", 0.0, "", []
        if not candidate.is_dir():
            return False, f"project_root is not a directory: {candidate}", 0.0, "", []
        resolved_project_root = candidate.resolve()
    else:
        resolved_project_root = find_project_root(cwd)

    # 1. Check gh CLI
    if not _check_gh_cli():
        return False, "gh CLI not found. Please install GitHub CLI.", 0.0, "", []

    # 2. Parse URL
    parsed = _parse_github_url(issue_url)
    if not parsed:
        return False, f"Invalid GitHub URL: {issue_url}", 0.0, "", []

    owner, repo, issue_number = parsed

    if not quiet:
        console.print(f"[bold blue]Fetching issue #{issue_number} from {owner}/{repo}...[/bold blue]")

    # 3. Fetch Issue Data
    # gh api repos/{owner}/{repo}/issues/{number}
    success, output = _run_gh_command(["api", f"repos/{owner}/{repo}/issues/{issue_number}"])
    if not success:
        return False, f"Issue not found: {output}", 0.0, "", []
    
    try:
        issue_data = json.loads(output)
    except json.JSONDecodeError:
        return False, "Failed to parse GitHub API response", 0.0, "", []

    issue_title = issue_data.get("title", "")
    issue_body = issue_data.get("body", "") or ""
    issue_author = issue_data.get("user", {}).get("login", "unknown")
    comments_url = issue_data.get("comments_url", "")

    # 4. Fetch Comments. Reuse the shared filter so pdd's own
    # PDD-INCREMENTAL-STATUS comments are excluded from PRD content on the
    # full-agentic path too — otherwise a later non-incremental regenerate
    # would feed prior status output back in as part of the PRD.
    comments_text = _fetch_issue_comments_text(comments_url, verbose=verbose) if comments_url else ""

    full_issue_content = f"{issue_body}{comments_text}"

    # 5. Ensure Repo Context. Use the resolved project root as the working
    # directory for repo discovery so a self-contained pdd project nested
    # inside an unrelated outer git repo isn't routed through the outer
    # repo's remote.
    repo_path, error = _ensure_repo_context(
        owner, repo, resolved_project_root, quiet, project_root=resolved_project_root
    )
    if error:
        return False, error, 0.0, "", []

    # Parse target_dir from issue body if not provided via CLI
    if target_dir is None:
        try:
            target_dir = _extract_target_dir(issue_body)
        except ValueError as exc:
            return False, str(exc), 0.0, "", []
        if target_dir and not quiet:
            console.print(f"[blue]Detected subproject directory: {target_dir}[/blue]")
    base_dir, target_dir, error = _resolve_target_dir(repo_path, target_dir)
    if error:
        return False, error, 0.0, "", []

    # 6. Discover sibling architectures and related context
    related_issues = _parse_related_issues(issue_body)
    sibling_arch_context = _fetch_sibling_architectures(repo_path, target_dir)
    existing_pddrc_context = _read_existing_pddrc(repo_path)
    existing_arch_context = _read_existing_architecture(repo_path, target_dir)

    # 7. Invoke Orchestrator
    return run_agentic_architecture_orchestrator(
        issue_url=issue_url,
        issue_content=full_issue_content,
        repo_owner=owner,
        repo_name=repo,
        issue_number=issue_number,
        issue_author=issue_author,
        issue_title=issue_title,
        cwd=repo_path,
        verbose=verbose,
        quiet=quiet,
        timeout_adder=timeout_adder,
        use_github_state=use_github_state,
        skip_prompts=skip_prompts,
        target_dir=target_dir,
        force_single=force_single,
        sibling_architectures=sibling_arch_context,
        existing_pddrc=existing_pddrc_context,
        existing_architecture=existing_arch_context,
        related_issues=related_issues,
    )


def run_incremental_architecture(
    prd_source: str,
    *,
    dry_run: bool = False,
    verbose: bool = False,
    quiet: bool = False,
    use_github_state: bool = True,
    target_dir: Optional[str] = None,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time: float = DEFAULT_TIME,
    project_root: Optional[str] = None,
) -> Tuple[bool, str, float, str, List[str]]:
    """Run guarded incremental PRD -> architecture propagation.

    Args:
        prd_source: Path to a local PRD-like file or a GitHub issue URL.
        dry_run: When True, analyze and report what would change without writing.
        verbose: Enable verbose logging.
        quiet: Suppress non-error output.
        use_github_state: Persist progress as GitHub issue comments (when applicable).
        target_dir: Optional subdirectory under the resolved project root.
        strength, temperature, time: Forwarded model knobs.
        project_root: Optional explicit override for the resolved PDD project root.
            When None, walks up from cwd through tier A/B/C markers; when supplied,
            the path is used verbatim, bypassing marker discovery.
    """
    cwd = Path.cwd()

    # Resolve PDD project root via explicit override or marker walk.
    if project_root is not None:
        candidate = Path(project_root).expanduser()
        if not candidate.exists():
            return False, f"project_root does not exist: {candidate}", 0.0, "", []
        if not candidate.is_dir():
            return False, f"project_root is not a directory: {candidate}", 0.0, "", []
        resolved_project_root = candidate.resolve()
    else:
        resolved_project_root = find_project_root(cwd)

    issue_content: Optional[str] = None
    repo_path = resolved_project_root
    owner = repo = ""
    issue_number: Optional[int] = None

    if _is_github_issue_url(prd_source):
        if not _check_gh_cli():
            return False, "gh CLI not found. Please install GitHub CLI.", 0.0, "", []

        parsed = _parse_github_url(prd_source)
        if not parsed:
            return False, f"Invalid GitHub URL: {prd_source}", 0.0, "", []
        owner, repo, issue_number = parsed

        if not quiet:
            console.print(
                "[bold blue]Fetching issue "
                f"#{issue_number} from {owner}/{repo} "
                "for incremental update...[/bold blue]"
            )

        success, output = _run_gh_command(
            ["api", f"repos/{owner}/{repo}/issues/{issue_number}"]
        )
        if not success:
            return False, f"Issue not found: {output}", 0.0, "", []
        try:
            issue_data = json.loads(output)
        except json.JSONDecodeError:
            return False, "Failed to parse GitHub API response", 0.0, "", []

        issue_title = issue_data.get("title", "") or ""
        issue_body = issue_data.get("body", "") or ""
        comments_url = issue_data.get("comments_url", "") or ""
        comments_text = _fetch_issue_comments_text(comments_url, verbose=verbose)
        issue_content = f"# {issue_title}\n\n{issue_body}{comments_text}".strip()

        repo_path, error = _ensure_repo_context(
            owner, repo, resolved_project_root, quiet, project_root=resolved_project_root
        )
        if error:
            return False, error, 0.0, "", []

        if target_dir is None:
            try:
                target_dir = _extract_target_dir(issue_body)
            except ValueError as exc:
                return False, str(exc), 0.0, "", []
            if target_dir and not quiet:
                console.print(f"[blue]Detected subproject directory: {target_dir}[/blue]")
    else:
        prd_path = Path(prd_source)
        if not prd_path.is_absolute():
            # When the caller supplied an explicit project_root, resolve the
            # relative PRD path against that root rather than cwd — matches the
            # documented `pdd generate --project-root <p> --incremental
            # --experimental-prd <relative-prd>` workflow and is consistent
            # with run_incremental_prd_propagation's own resolution policy.
            prd_path = (resolved_project_root if project_root is not None else cwd) / prd_path
        if not prd_path.is_file():
            return False, f"PRD file not found: {prd_path}", 0.0, "", []

    base_dir, target_dir, error = _resolve_target_dir(repo_path, target_dir)
    if error:
        return False, error, 0.0, "", []
    architecture_path = base_dir / "architecture.json"
    prompts_dir = base_dir / "prompts"
    state_root = base_dir if issue_content is not None else repo_path

    try:
        from .incremental_prd_architecture import run_incremental_prd_propagation

        result = run_incremental_prd_propagation(
            prd_source=prd_source,
            architecture_path=architecture_path,
            prompts_dir=prompts_dir,
            project_root=state_root,
            issue_content=issue_content,
            dry_run=dry_run,
            verbose=verbose,
            quiet=quiet,
            strength=strength,
            temperature=temperature,
            time=time,
        )
    except Exception as exc:
        result = (False, f"Incremental architecture error: {exc}", 0.0, "", [])

    if issue_content is not None:
        result = _prefix_target_changed_files(result, target_dir)
    if result[0] and target_dir and not dry_run and result[4]:
        result = _append_target_sync_hint(result, target_dir)

    if (
        use_github_state
        and issue_number is not None
        and owner
        and repo
        and not dry_run
    ):
        _post_incremental_status_comment(owner, repo, issue_number, result, quiet=quiet)

    return result


def _prefix_target_changed_files(
    result: Tuple[bool, str, float, str, List[str]],
    target_dir: Optional[str],
) -> Tuple[bool, str, float, str, List[str]]:
    """Convert subproject-relative issue results to repo-relative paths."""
    if not target_dir:
        return result
    success, message, cost, model, changed_files = result
    prefix = target_dir.strip().rstrip("/")
    if not prefix:
        return result

    prefixed: List[str] = []
    for path in changed_files:
        if (
            not path
            or path.startswith("/")
            or path == prefix
            or path.startswith(f"{prefix}/")
        ):
            prefixed.append(path)
        else:
            prefixed.append(f"{prefix}/{path}")
    return success, message, cost, model, prefixed


def _append_target_sync_hint(
    result: Tuple[bool, str, float, str, List[str]],
    target_dir: str,
) -> Tuple[bool, str, float, str, List[str]]:
    """Add the subproject sync working-directory hint for target-dir writes."""
    success, message, cost, model, changed_files = result
    hint = (
        f"\nNext: run `cd {target_dir} && pdd sync` for follow-up sync validation "
        "because generated prompt includes are target-directory relative."
    )
    if "pdd sync" not in message:
        message = f"{message.rstrip()}{hint}"
    return success, message, cost, model, changed_files


def _fetch_issue_comments_text(comments_url: str, *, verbose: bool) -> str:
    if not comments_url:
        return ""
    success, output = _run_gh_command(["api", comments_url, "--paginate"])
    if not success:
        return ""
    try:
        comments = json.loads(output)
    except json.JSONDecodeError:
        if verbose:
            console.print("[yellow]Warning: Failed to parse comments JSON[/yellow]")
        return ""
    if not isinstance(comments, list) or not comments:
        return ""

    formatted_comments = []
    for comment in comments:
        body = comment.get("body", "") or ""
        if not body:
            continue
        if _INCREMENTAL_STATUS_MARKER in body:
            # Skip pdd's own incremental status comments so they don't feed back
            # into the next run as a PRD change.
            continue
        user = comment.get("user", {}).get("login", "unknown")
        formatted_comments.append(f"User: {user}\n{body}")
    if not formatted_comments:
        return ""
    return "\n\n--- Comments ---\n" + "\n\n".join(formatted_comments)


def _post_incremental_status_comment(
    owner: str,
    repo: str,
    issue_number: int,
    result: Tuple[bool, str, float, str, List[str]],
    *,
    quiet: bool,
) -> None:
    success, message, cost, model, changed_files = result
    status = "successful" if success else "failed"
    files = (
        "\n".join(f"- `{_sanitize_status_message(path)}`" for path in changed_files)
        or "- No files changed"
    )
    safe_message = _sanitize_status_message(message)
    body = (
        f"{_INCREMENTAL_STATUS_MARKER}\n"
        f"pdd incremental architecture update {status}.\n\n"
        f"Result: {safe_message}\n\n"
        f"Model: {model or 'n/a'}\n"
        f"Estimated cost: ${cost:.4f}\n\n"
        f"Changed files:\n{files}"
    )
    ok, output = _run_gh_command(
        [
            "api",
            f"repos/{owner}/{repo}/issues/{issue_number}/comments",
            "-f",
            f"body={body}",
        ]
    )
    if not ok and not quiet:
        console.print(
            "[yellow]Warning: failed to post incremental status comment: "
            f"{output}[/yellow]"
        )


def _sanitize_status_message(message: str) -> str:
    """Remove local absolute paths before posting public GitHub status comments."""
    if not message:
        return message

    # Redact common POSIX absolute paths while leaving URLs and command names intact.
    sanitized = re.sub(
        r"(?<![\w:])/(?:Users|home|root|workspace|workspaces|mnt|private|tmp|var|Volumes)/[^\s`'\"),]+",
        "<local-path>",
        message,
    )
    # Redact Windows absolute paths for users running the workflow from Windows.
    sanitized = re.sub(
        r"\b[A-Za-z]:\\[^\s`'\"),]+",
        "<local-path>",
        sanitized,
    )
    return sanitized
