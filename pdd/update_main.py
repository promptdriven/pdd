from __future__ import annotations

import os
import re
import json
import hashlib
import fnmatch
import subprocess
from pathlib import Path
from typing import Optional, Tuple, Dict, List, Set, Any

import click
from rich.console import Console
from rich.theme import Theme
from rich.table import Table
from rich.progress import (
    Progress,
    SpinnerColumn,
    BarColumn,
    TextColumn,
    TimeRemainingColumn,
    TaskProgressColumn,
)

from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .construct_paths import construct_paths
from .update_prompt import update_prompt
from .git_update import git_update
from .get_language import get_language
from .operation_log import (
    infer_module_identity,
    save_fingerprint,
)


# ---------------------------------------------------------------------------
# Module-level Rich Console with custom theme.
# ---------------------------------------------------------------------------
_THEME = Theme(
    {
        "info": "cyan",
        "warning": "yellow",
        "error": "bold red",
        "success": "green",
        "path": "dim blue",
    }
)
console = Console(theme=_THEME)
# Stderr-bound console for failure lines (issue #1005 acceptance criterion).
_err_console = Console(stderr=True, theme=_THEME)


# ---------------------------------------------------------------------------
# Repo-mode exclusion sets.
# ---------------------------------------------------------------------------
_SKIP_EXTENSIONS: Set[str] = {
    ".json", ".jsonl", ".yaml", ".yml", ".md", ".toml", ".ini", ".css",
    ".html", ".lock", ".svg", ".png", ".jpg", ".gif", ".ico", ".woff",
    ".woff2", ".ttf", ".eot", ".map", ".csv", ".txt",
}
_SKIP_FILENAMES: Set[str] = {
    "package-lock.json", "yarn.lock", "pnpm-lock.yaml",
    "jest.config.js", "tailwind.config.js", "postcss.config.js",
    "next.config.js", "vite.config.js", "rollup.config.js",
    "babel.config.js", "webpack.config.js",
    "mockServiceWorker.js", "next-env.d.ts",
    "setup.py", "conftest.py",
}
_SKIP_BASENAME_SUFFIXES: Tuple[str, ...] = (
    ".config", ".setup", ".stories", ".story",
    ".test", ".spec", ".e2e.test", ".e2e.spec", ".d",
)
_WALK_IGNORE_DIRS: Set[str] = {
    ".git", ".idea", ".vscode", "__pycache__", "node_modules",
    ".venv", "venv", "dist", "build", ".next", ".nuxt", ".output",
    ".cache", ".turbo", ".parcel-cache", "coverage", ".pdd",
}


# ---------------------------------------------------------------------------
# Sanitization helper for prompt outputs.
# ---------------------------------------------------------------------------
def _sanitize_for_write(content: str, destination_path: Path) -> str:
    """
    Run sanitize_prompt_output before writing prompt content to disk.

    Wrapped in try/except so that a missing/optional validator never blocks
    the legacy update path; we just write the raw content if sanitization
    is unavailable.
    """
    try:
        from .validate_prompt_includes import sanitize_prompt_output

        sanitized, _removed = sanitize_prompt_output(content, destination_path)
        return sanitized
    except Exception:
        return content


# ---------------------------------------------------------------------------
# .pddrc template-path helpers.
# ---------------------------------------------------------------------------
def _extract_template_vars(concrete_path: str, template: str) -> Optional[Dict[str, str]]:
    """
    Reverse-match a path against a template like
    ``"src/{category}/{name}/{name}.py"`` to extract variable bindings.

    Repeated variables generate regex backreferences, so the same `{name}`
    must match the same captured value.
    """
    var_pattern = re.compile(r"\{([a-zA-Z_][a-zA-Z0-9_]*)\}")
    seen: Dict[str, int] = {}
    regex_parts: List[str] = []
    last_end = 0
    var_order: List[str] = []
    for m in var_pattern.finditer(template):
        regex_parts.append(re.escape(template[last_end:m.start()]))
        var_name = m.group(1)
        if var_name in seen:
            regex_parts.append(f"\\{seen[var_name]}")
        else:
            group_index = len(seen) + 1
            seen[var_name] = group_index
            regex_parts.append(f"(?P<{var_name}>[^/]+)")
            var_order.append(var_name)
        last_end = m.end()
    regex_parts.append(re.escape(template[last_end:]))
    regex = "^" + "".join(regex_parts) + "$"
    match = re.match(regex, concrete_path)
    if not match:
        return None
    return {name: match.group(name) for name in var_order}


def _resolve_prompt_from_pddrc(
    code_file_path: Path,
    repo_root: Path,
    language: str,
) -> Optional[str]:
    """
    Resolve a prompt path by consulting `.pddrc` matching contexts.

    Returns the expanded prompt path (string) or None if no matching
    context produces a prompt template we can resolve.
    """
    try:
        from .pddrc_loader import load_pddrc, find_matching_context
        from .template_expander import expand_template
    except Exception:
        return None

    search_dirs: List[Path] = []
    parent = code_file_path.parent.resolve()
    while True:
        search_dirs.append(parent)
        if parent == parent.parent:
            break
        parent = parent.parent
    if repo_root.resolve() not in search_dirs:
        search_dirs.append(repo_root.resolve())

    pddrc_data = None
    for d in search_dirs:
        candidate = d / ".pddrc"
        if candidate.exists():
            try:
                pddrc_data = load_pddrc(candidate)
                break
            except Exception:
                continue
    if pddrc_data is None:
        return None

    try:
        rel_code_path = str(code_file_path.resolve().relative_to(repo_root.resolve()))
    except ValueError:
        rel_code_path = str(code_file_path)

    try:
        ctx = find_matching_context(pddrc_data, rel_code_path)
    except Exception:
        ctx = None
    if not ctx:
        return None

    outputs = (ctx or {}).get("outputs") or {}
    prompt_cfg = outputs.get("prompt") or {}
    template = prompt_cfg.get("path")
    if not template:
        return None

    # Try to extract vars from a configured code-output template if present.
    code_template = (outputs.get("code") or {}).get("path")
    variables: Dict[str, str] = {"language": language}
    basename = code_file_path.stem
    variables.setdefault("name", basename)
    variables.setdefault("module", basename)
    if code_template:
        extracted = _extract_template_vars(rel_code_path, code_template)
        if extracted:
            variables.update(extracted)

    try:
        expanded = expand_template(template, variables)
    except Exception:
        return None

    if not os.path.isabs(expanded):
        expanded = str((repo_root / expanded).resolve())
    return expanded


def _resolve_existing_prompt_path_case_insensitive(prompt_path: Path) -> Path:
    """
    Preserve the on-disk casing of an existing prompt file, if any.

    On case-sensitive filesystems, callers may construct prompt paths that
    differ only in case from an already-present file. We don't want to
    create a second sibling file — return the existing path verbatim.
    """
    parent = prompt_path.parent
    if not parent.exists():
        return prompt_path
    target_lower = prompt_path.name.lower()
    try:
        for entry in parent.iterdir():
            if entry.is_file() and entry.name.lower() == target_lower:
                return entry
    except OSError:
        pass
    return prompt_path


# ---------------------------------------------------------------------------
# .pddrc helpers for repo scanning.
# ---------------------------------------------------------------------------
def _find_nearest_pddrc_for_file(file_path: Path, repo_root: Path) -> Optional[Path]:
    """Walk upward from file_path's parent to repo_root looking for `.pddrc`."""
    parent = file_path.parent.resolve()
    root = repo_root.resolve()
    while True:
        candidate = parent / ".pddrc"
        if candidate.exists():
            return candidate
        if parent == root or parent == parent.parent:
            return None
        parent = parent.parent


def resolve_prompt_code_pair(
    code_file_path: Path,
    quiet: bool,
    output_dir: Optional[str] = None,
) -> Tuple[Path, Path]:
    """
    Derive the prompt file path for a given code file.

    1. If no `output_dir` override, try `.pddrc` template resolution.
    2. Otherwise fall back to a `prompts/` sibling layout, preserving any
       sub-directory structure relative to repo root.

    Always preserves on-disk case for an existing prompt file and creates
    missing directories / empty prompt files so downstream code can read
    and overwrite them.
    """
    code_path = code_file_path.resolve()
    language = get_language(str(code_path)) or "python"

    # Find a repo root (git or fallback to walking up).
    repo_root: Path
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=str(code_path.parent),
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode == 0 and result.stdout.strip():
            repo_root = Path(result.stdout.strip()).resolve()
        else:
            repo_root = Path.cwd().resolve()
    except Exception:
        repo_root = Path.cwd().resolve()

    prompt_path: Optional[Path] = None
    if not output_dir:
        resolved = _resolve_prompt_from_pddrc(code_path, repo_root, language)
        if resolved:
            prompt_path = Path(resolved)

    if prompt_path is None:
        # Fallback: prompts/<rel_dir>/<basename>_<lang>.prompt
        try:
            rel = code_path.relative_to(repo_root)
        except ValueError:
            rel = Path(code_path.name)
        # Strip generate_output_path prefix if it matches the first segment.
        rel_parts = list(rel.parts[:-1])
        # Best-effort strip of common code-output dirs.
        for prefix in ("src", "pdd", "lib"):
            if rel_parts and rel_parts[0] == prefix:
                rel_parts = rel_parts[1:]
                break
        sub_dir = Path(*rel_parts) if rel_parts else Path()
        base_dir = Path(output_dir) if output_dir else (repo_root / "prompts")
        prompt_dir = base_dir / sub_dir
        prompt_name = f"{code_path.stem}_{language}.prompt"
        prompt_path = prompt_dir / prompt_name

    # Preserve existing-on-disk casing.
    prompt_path = _resolve_existing_prompt_path_case_insensitive(prompt_path)

    prompt_path.parent.mkdir(parents=True, exist_ok=True)
    if not prompt_path.exists():
        prompt_path.write_text("", encoding="utf-8")
        if not quiet:
            console.print(f"[info]Created empty prompt file:[/info] [path]{prompt_path}[/path]")

    return prompt_path, code_path


# ---------------------------------------------------------------------------
# .pddignore handling.
# ---------------------------------------------------------------------------
def _load_pddignore(scan_root: Path) -> Tuple[List[str], Optional[Path]]:
    """
    Walk upward from `scan_root` to find `.pddignore`.

    Stops at the git root if reached. Returns a list of patterns and the
    directory containing the file (used as the anchor for relative-path
    matches). When no `.pddignore` is found, returns ([], None).
    """
    current = scan_root.resolve()
    git_root: Optional[Path] = None
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=str(current),
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode == 0 and result.stdout.strip():
            git_root = Path(result.stdout.strip()).resolve()
    except Exception:
        git_root = None

    while True:
        candidate = current / ".pddignore"
        if candidate.exists():
            try:
                lines = candidate.read_text(encoding="utf-8").splitlines()
            except Exception:
                return [], None
            patterns = [
                ln.strip()
                for ln in lines
                if ln.strip() and not ln.strip().startswith("#")
            ]
            return patterns, current
        if git_root is not None and current == git_root:
            return [], None
        if current == current.parent:
            return [], None
        current = current.parent


def _is_pddignored(filepath: Path, pddignore_root: Optional[Path], patterns: List[str]) -> bool:
    """
    Match `filepath` against `.pddignore` patterns.

    Supports:
      - directory-prefix patterns (ending in `/`)
      - relative-path glob patterns
      - bare basename glob patterns
    """
    if not patterns or pddignore_root is None:
        return False
    try:
        rel = filepath.resolve().relative_to(pddignore_root.resolve())
    except ValueError:
        return False
    rel_str = str(rel).replace(os.sep, "/")
    base = filepath.name
    for pat in patterns:
        if pat.endswith("/"):
            prefix = pat.rstrip("/")
            if rel_str == prefix or rel_str.startswith(prefix + "/"):
                return True
        elif "/" in pat:
            if fnmatch.fnmatch(rel_str, pat):
                return True
        else:
            if fnmatch.fnmatch(base, pat):
                return True
    return False


def _has_skip_suffix(filepath: Path) -> bool:
    """Return True if the file stem ends with one of the skip suffixes."""
    stem = filepath.stem.lower()
    name_lower = filepath.name.lower()
    for suf in _SKIP_BASENAME_SUFFIXES:
        # Suffixes like ".d" need stem-end matching against a leading dot.
        if stem.endswith(suf) or name_lower.endswith(suf):
            return True
    return False


def _has_meaningful_code(filepath: Path) -> bool:
    """Return True iff the file has at least one non-blank, non-comment line."""
    try:
        with open(filepath, "r", encoding="utf-8", errors="ignore") as f:
            for line in f:
                stripped = line.strip()
                if not stripped:
                    continue
                if stripped.startswith(("#", "//", "/*", "*", "--", ";")):
                    continue
                return True
    except OSError:
        return False
    return False


def find_and_resolve_all_pairs(
    repo_root: Path,
    quiet: bool,
    extensions: Optional[Tuple[str, ...]] = None,
    output_dir: Optional[str] = None,
) -> List[Tuple[Path, Path]]:
    """
    Walk the repo, apply multi-layer exclusion, and resolve each remaining
    code file to a (prompt_path, code_path) pair.
    """
    repo_root = repo_root.resolve()
    candidate_files: List[Path] = []

    # Prefer git ls-files to respect .gitignore.
    used_git = False
    try:
        result = subprocess.run(
            ["git", "ls-files", "--cached", "--others", "--exclude-standard"],
            cwd=str(repo_root),
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode == 0:
            used_git = True
            for line in result.stdout.splitlines():
                line = line.strip()
                if not line:
                    continue
                p = (repo_root / line).resolve()
                if p.is_file():
                    candidate_files.append(p)
    except Exception:
        used_git = False

    if not used_git:
        for root, dirs, files in os.walk(repo_root):
            dirs[:] = [d for d in dirs if d not in _WALK_IGNORE_DIRS]
            for f in files:
                candidate_files.append(Path(root) / f)

    pddignore_patterns, pddignore_root = _load_pddignore(repo_root)
    extensions_norm: Optional[Set[str]] = None
    if extensions:
        extensions_norm = {
            ("." + e.lstrip(".")).lower() for e in extensions if e
        }

    pairs: List[Tuple[Path, Path]] = []
    seen: Set[Path] = set()

    for fp in candidate_files:
        if fp in seen:
            continue
        seen.add(fp)
        name = fp.name
        ext = fp.suffix.lower()
        # Hard skips first.
        if ext == ".prompt":
            continue
        if ext in _SKIP_EXTENSIONS:
            continue
        if name in _SKIP_FILENAMES:
            continue
        if name.startswith("test_"):
            continue
        if fp.stem.endswith("_example"):
            continue
        if _has_skip_suffix(fp):
            continue
        if _is_pddignored(fp, pddignore_root, pddignore_patterns):
            continue
        if extensions_norm is not None and ext not in extensions_norm:
            continue
        if get_language(str(fp)) is None:
            continue
        if not _has_meaningful_code(fp):
            continue
        try:
            prompt_path, code_path = resolve_prompt_code_pair(fp, quiet=True, output_dir=output_dir)
        except Exception as exc:
            if not quiet:
                console.print(
                    f"[warning]Skipping {fp}: failed to resolve prompt ({exc})[/warning]"
                )
            continue
        pairs.append((prompt_path, code_path))
    return pairs


# ---------------------------------------------------------------------------
# Git-changed-files helpers.
# ---------------------------------------------------------------------------
def get_git_changed_files(repo_root: Path, base_branch: str = "main") -> Set[str]:
    """
    Combine merge-base diff, uncommitted changes, and untracked files into
    a set of absolute path strings.
    """
    changed: Set[str] = set()
    cwd = str(repo_root)
    cmds: List[List[str]] = [
        ["git", "diff", "--name-only", f"{base_branch}...HEAD"],
        ["git", "diff", "--name-only", "HEAD"],
        ["git", "diff", "--name-only", "--cached"],
        ["git", "ls-files", "--others", "--exclude-standard"],
    ]
    for cmd in cmds:
        try:
            res = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False)
            if res.returncode != 0:
                continue
            for line in res.stdout.splitlines():
                line = line.strip()
                if not line:
                    continue
                changed.add(str((repo_root / line).resolve()))
        except Exception:
            continue
    return changed


def derive_basename_and_language(
    code_file_path: Path, repo_root: Path
) -> Tuple[str, str]:
    """
    Use the relative path from repo_root (without extension) as the basename
    so same-named files in different directories don't collide in `.pdd/meta`.
    """
    code_file_path = code_file_path.resolve()
    repo_root = repo_root.resolve()
    try:
        rel = code_file_path.relative_to(repo_root)
    except ValueError:
        rel = Path(code_file_path.name)
    rel_no_ext = rel.with_suffix("")
    basename = "_".join(rel_no_ext.parts) if rel_no_ext.parts else code_file_path.stem
    language = get_language(str(code_file_path)) or "python"
    return basename, language


def _check_include_deps_changed(fingerprint: Any) -> Tuple[bool, str]:
    """
    Compare each include dependency's stored hash against the file's
    current SHA256 hash on disk.
    """
    deps = getattr(fingerprint, "include_deps", None)
    if not deps:
        return False, ""
    if isinstance(deps, dict):
        items = deps.items()
    else:
        try:
            items = list(deps)
        except Exception:
            return False, ""
    for item in items:
        try:
            if isinstance(item, tuple) and len(item) == 2:
                path, stored_hash = item
            elif isinstance(item, dict):
                path, stored_hash = item.get("path"), item.get("hash")
            else:
                continue
            if not path or not stored_hash:
                continue
            p = Path(path)
            if not p.exists():
                return True, f"include dep missing: {path}"
            current = hashlib.sha256(p.read_bytes()).hexdigest()
            if current != stored_hash:
                return True, f"include dep changed: {path}"
        except Exception:
            continue
    return False, ""


def is_code_changed(
    code_file_path: Path,
    repo_root: Path,
    git_changed_files: Set[str],
    prompt_file_path: Optional[Path] = None,
) -> Tuple[bool, str]:
    """
    Decide whether a code file has effectively changed since its last
    PDD operation.

    Strategy:
      1. Try to load a fingerprint via infer_module_identity (using prompt
         path) or via derive_basename_and_language (using code path).
      2. If a fingerprint exists, compare the code hash; if it matches,
         also compare include-dependency hashes.
      3. If no fingerprint exists, fall back to the git-changed set.
    """
    code_abs = str(code_file_path.resolve())

    fingerprint = None
    basename: Optional[str] = None
    language: Optional[str] = None

    if prompt_file_path is not None:
        try:
            basename, language = infer_module_identity(str(prompt_file_path))
        except Exception:
            basename, language = None, None

    if basename is None or language is None:
        basename, language = derive_basename_and_language(code_file_path, repo_root)

    fp_path = repo_root / ".pdd" / "meta" / f"{basename}_{language}.json"
    if fp_path.exists():
        try:
            data = json.loads(fp_path.read_text(encoding="utf-8"))
            stored_code_hash = data.get("code_hash")
            current_hash = hashlib.sha256(code_file_path.read_bytes()).hexdigest()
            if stored_code_hash and current_hash != stored_code_hash:
                return True, "code hash differs from fingerprint"

            class _FP:
                pass

            fp_obj = _FP()
            fp_obj.include_deps = data.get("include_deps")
            inc_changed, inc_reason = _check_include_deps_changed(fp_obj)
            if inc_changed:
                return True, inc_reason
            return False, "fingerprint matches"
        except Exception:
            pass

    if code_abs in git_changed_files:
        return True, "git reports change"
    return False, "no change detected"


# ---------------------------------------------------------------------------
# Single-file metadata sync helper (issue #1005).
# ---------------------------------------------------------------------------
def _run_single_file_metadata_sync(
    prompt_path: Path,
    code_path: Path,
    dry_run: bool = False,
) -> bool:
    """
    Wrap `pdd.metadata_sync.run_metadata_sync` for the single-file and
    regeneration success paths.

    Returns True on `MetadataSyncResult.ok` (including dry-runs/skipped
    stages), and False on orchestrator exceptions or any stage whose
    status is "failed". Failure lines are written to stderr per the
    issue #1005 acceptance criterion so that "no silent stale-metadata
    path remains" is directly testable by capturing stderr.
    """
    try:
        from .metadata_sync import run_metadata_sync
    except Exception as exc:
        _err_console.print(
            f"[error]metadata sync unavailable:[/error] {exc}"
        )
        return False
    try:
        result = run_metadata_sync(prompt_path, code_path, dry_run=dry_run)
    except Exception as exc:
        _err_console.print(
            f"[error]metadata sync raised:[/error] {exc}"
        )
        return False

    failed_any = False
    for stage_name, stage in (result.stages or {}).items():
        status = getattr(stage, "status", None)
        if status == "failed":
            reason = getattr(stage, "reason", "") or ""
            _err_console.print(
                f"[error]metadata sync failed[/error] stage={stage_name} reason={reason}"
            )
            failed_any = True

    if failed_any or not getattr(result, "ok", False):
        return False
    if not dry_run:
        console.print("[success]metadata: synced[/success]")
    else:
        console.print("[info]metadata: dry-run (no writes)[/info]")
    return True


# ---------------------------------------------------------------------------
# Per-pair update wrapper (repo mode).
# ---------------------------------------------------------------------------
def update_file_pair(
    prompt_file: Path,
    code_file: Path,
    ctx: Any,
    repo: bool,
    simple: bool,
) -> Dict[str, Any]:
    """
    Update a single (prompt, code) pair.

    Tries the agentic path first (when not `simple` and agents are
    available); falls back to legacy git_update / update_prompt.
    """
    obj = ctx.obj or {}
    verbose = obj.get("verbose", False)
    quiet = obj.get("quiet", False)
    strength = obj.get("strength", DEFAULT_STRENGTH)
    temperature = obj.get("temperature", 0.0)
    time_param = obj.get("time", DEFAULT_TIME)

    result: Dict[str, Any] = {
        "prompt_file": str(prompt_file),
        "status": "pending",
        "cost": 0.0,
        "model": "",
        "error": "",
    }

    # Determine if file is empty / untracked (regeneration sentinel).
    try:
        is_empty = (not prompt_file.exists()) or prompt_file.stat().st_size == 0
    except OSError:
        is_empty = True

    # 1. Try agentic.
    if not simple:
        try:
            from .agentic_update import run_agentic_update

            success, message, cost, model, _changed = run_agentic_update(
                prompt_file=str(prompt_file),
                code_file=str(code_file),
                quiet=quiet,
            )
            if success:
                result.update(
                    {"status": "updated (agentic)", "cost": float(cost or 0.0), "model": model or ""}
                )
                return result
            if verbose and not quiet:
                console.print(
                    f"[warning]Agentic update unavailable for {prompt_file.name}: {message}[/warning]"
                )
        except ImportError:
            pass
        except Exception as exc:
            if verbose and not quiet:
                console.print(f"[warning]Agentic update error: {exc}[/warning]")

    # 2. Legacy fallback.
    try:
        if is_empty:
            # Treat as regeneration: run update_prompt with a generation sentinel.
            try:
                modified_code = code_file.read_text(encoding="utf-8")
            except Exception as exc:
                result.update({"status": "error", "error": f"cannot read code: {exc}"})
                return result
            modified_prompt, total_cost, model_name = update_prompt(
                input_prompt="",
                input_code="",
                modified_code=modified_code,
                strength=strength,
                temperature=temperature,
                verbose=verbose,
                time=time_param,
            )
            if modified_prompt:
                sanitized = _sanitize_for_write(modified_prompt, prompt_file)
                prompt_file.write_text(sanitized, encoding="utf-8")
                result.update(
                    {"status": "regenerated", "cost": float(total_cost or 0.0), "model": model_name or ""}
                )
            else:
                result.update({"status": "error", "error": "empty prompt returned"})
            return result

        try:
            input_prompt = prompt_file.read_text(encoding="utf-8")
        except Exception as exc:
            result.update({"status": "error", "error": f"cannot read prompt: {exc}"})
            return result

        gu_result = git_update(
            input_prompt=input_prompt,
            modified_code_file=str(code_file),
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            simple=True,  # we already tried agentic above
            quiet=quiet,
            prompt_file=str(prompt_file),
            time=time_param,
        )
        if not gu_result:
            result.update({"status": "error", "error": "git_update returned no result"})
            return result
        modified_prompt, total_cost, model_name = gu_result
        if modified_prompt and modified_prompt.strip():
            sanitized = _sanitize_for_write(modified_prompt, prompt_file)
            prompt_file.write_text(sanitized, encoding="utf-8")
            result.update(
                {"status": "updated", "cost": float(total_cost or 0.0), "model": model_name or ""}
            )
        else:
            result.update({"status": "error", "error": "empty prompt returned"})
    except Exception as exc:
        result.update({"status": "error", "error": str(exc)})
    return result


# ---------------------------------------------------------------------------
# PRD discovery helper.
# ---------------------------------------------------------------------------
def _find_prd_file(project_root: Path) -> Optional[Path]:
    """Find a PRD file by convention (PRD.md, prd.md, *_prd.md, *_PRD.md)."""
    project_root = project_root.resolve()
    for name in ("PRD.md", "prd.md"):
        p = project_root / name
        if p.exists():
            return p
    for pattern in ("*_prd.md", "*_PRD.md"):
        matches = list(project_root.glob(pattern))
        if matches:
            return matches[0]
    return None


# ---------------------------------------------------------------------------
# Repo mode entry.
# ---------------------------------------------------------------------------
def _meta_status_string(meta_result: Any) -> str:
    """Render a one-cell metadata status for the summary table."""
    if meta_result is None:
        return "skipped"
    stages = getattr(meta_result, "stages", {}) or {}
    failed = [n for n, s in stages.items() if getattr(s, "status", None) == "failed"]
    if failed:
        return f"failed:{failed[0]}"
    skipped_only = [n for n, s in stages.items() if getattr(s, "status", None) == "skipped"]
    if skipped_only and len(skipped_only) == len(stages):
        return "skipped"
    if getattr(meta_result, "dry_run", False):
        return "dry-run"
    partial = [n for n, s in stages.items() if getattr(s, "status", None) not in ("ok", "dry_run")]
    if partial and len(partial) < len(stages):
        return f"partial:{partial[0]}"
    return "synced"


def _run_repo_mode(
    ctx: Any,
    directory: Optional[str],
    extensions: Optional[Tuple[str, ...]],
    base_branch: str,
    simple: bool,
    output_dir: Optional[str],
    sync_metadata: bool,
    dry_run: bool,
    budget: Optional[float] = None,
) -> Optional[Tuple[str, float, str]]:
    obj = ctx.obj or {}
    quiet = obj.get("quiet", False)

    # Determine repo root.
    cwd = Path.cwd()
    try:
        res = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            check=False,
        )
        if res.returncode != 0 or not res.stdout.strip():
            if not quiet:
                console.print("[warning]Not in a git repository — repo mode requires git.[/warning]")
            return None
        repo_root = Path(res.stdout.strip()).resolve()
    except Exception as exc:
        if not quiet:
            console.print(f"[error]Failed to detect git repo:[/error] {exc}")
        return None

    scan_root = Path(directory).resolve() if directory else repo_root

    if not quiet:
        console.print(f"[info]Scanning for code/prompt pairs under[/info] [path]{scan_root}[/path]")

    pairs = find_and_resolve_all_pairs(
        repo_root=scan_root,
        quiet=quiet,
        extensions=extensions,
        output_dir=output_dir,
    )
    if not pairs:
        if not quiet:
            console.print("[warning]No scannable code files found.[/warning]")
        return None

    # Auto-create .pddrc if needed.
    try:
        from .pddrc_initializer import ensure_pddrc_for_scan

        ensure_pddrc_for_scan(scan_root, pairs, quiet=quiet)
    except Exception:
        pass

    git_changed = get_git_changed_files(repo_root, base_branch=base_branch)
    changed_pairs: List[Tuple[Path, Path]] = []
    for prompt_file, code_file in pairs:
        try:
            empty_prompt = prompt_file.exists() and prompt_file.stat().st_size == 0
        except OSError:
            empty_prompt = False
        is_changed, _reason = is_code_changed(
            code_file, repo_root, git_changed, prompt_file_path=prompt_file
        )
        if is_changed or empty_prompt:
            changed_pairs.append((prompt_file, code_file))

    if not changed_pairs:
        if not quiet:
            console.print("[success]Everything is in sync — no updates needed.[/success]")
        return None

    if dry_run:
        if not quiet:
            console.print(
                f"[info]Dry run: {len(changed_pairs)} pair(s) would be updated "
                f"(no LLM calls, no prompt writes, no architecture/PRD sync).[/info]"
            )
            for prompt_file, code_file in changed_pairs:
                console.print(f"  [path]{code_file}[/path] -> [path]{prompt_file}[/path]")
        return (
            f"Dry run: {len(changed_pairs)} prompt(s) would be updated (no changes made).",
            0.0,
            "N/A",
        )

    if not quiet:
        console.print(
            f"[info]Updating {len(changed_pairs)} pair(s)…[/info]"
        )

    results: List[Dict[str, Any]] = []
    meta_results: Dict[str, Any] = {}  # prompt_file -> MetadataSyncResult or None
    arch_updates_count = 0
    total_cost = 0.0
    models_used: Set[str] = set()

    progress_columns = (
        SpinnerColumn(),
        TextColumn("[progress.description]{task.description}"),
        BarColumn(),
        TaskProgressColumn(),
        TextColumn("•"),
        TimeRemainingColumn(),
        TextColumn("• ${task.fields[cost]:.4f}"),
    )
    with Progress(*progress_columns, console=console, disable=quiet) as progress:
        task = progress.add_task(
            "Updating pairs", total=len(changed_pairs), cost=0.0
        )
        for prompt_file, code_file in changed_pairs:
            if budget is not None and total_cost >= budget:
                if not quiet:
                    console.print(
                        f"[info]Budget cap reached (${budget:.2f}); "
                        f"stopping with {len(results)} pair(s) processed.[/info]"
                    )
                break
            res = update_file_pair(prompt_file, code_file, ctx, repo=True, simple=simple)
            results.append(res)
            total_cost += float(res.get("cost") or 0.0)
            if res.get("model"):
                models_used.add(res["model"])

            # Metadata finalization.
            if res.get("status", "").startswith(("updated", "regenerated")):
                if sync_metadata:
                    try:
                        from .metadata_sync import run_metadata_sync

                        meta = run_metadata_sync(prompt_file, code_file, dry_run=dry_run)
                        meta_results[str(prompt_file)] = meta
                        if not getattr(meta, "ok", False):
                            for stage_name, stage in (meta.stages or {}).items():
                                if getattr(stage, "status", None) == "failed":
                                    _err_console.print(
                                        f"[error]metadata sync failed[/error] "
                                        f"prompt={prompt_file} stage={stage_name} "
                                        f"reason={getattr(stage, 'reason', '') or ''}"
                                    )
                        # Track arch updates from orchestrator.
                        arch_stage = (meta.stages or {}).get("architecture")
                        if arch_stage and getattr(arch_stage, "status", None) in ("ok", "dry_run"):
                            detail = getattr(arch_stage, "detail", "") or ""
                            if "updated" in detail.lower() or getattr(arch_stage, "status", None) == "ok":
                                arch_updates_count += 1
                    except Exception as exc:
                        _err_console.print(
                            f"[error]metadata sync exception for {prompt_file}:[/error] {exc}"
                        )
                        meta_results[str(prompt_file)] = None
                else:
                    # Legacy: save fingerprint and run architecture sync inline.
                    meta_results[str(prompt_file)] = None
                    if not dry_run:
                        try:
                            basename, language = infer_module_identity(str(prompt_file))
                            save_fingerprint(
                                basename=basename,
                                language=language,
                                operation="update",
                                paths={"prompt": prompt_file, "code": code_file},
                                cost=float(res.get("cost") or 0.0),
                                model=res.get("model") or "",
                            )
                        except Exception as exc:
                            if not quiet:
                                console.print(
                                    f"[warning]fingerprint save failed for {prompt_file}: {exc}[/warning]"
                                )
                        # Architecture sync per pair.
                        try:
                            from .architecture_sync import (
                                find_architecture_for_project,
                                update_architecture_from_prompt,
                            )

                            arch_path = find_architecture_for_project(repo_root)
                            if arch_path and arch_path.exists():
                                arch_res = update_architecture_from_prompt(
                                    prompt_filename=prompt_file.name,
                                    prompts_dir=prompt_file.parent,
                                    architecture_path=arch_path,
                                    dry_run=dry_run,
                                )
                                if arch_res and arch_res.get("updated"):
                                    arch_updates_count += 1
                        except Exception:
                            pass
            progress.update(task, advance=1, cost=total_cost)

    # Render summary table.
    table = Table(title="Update Summary")
    table.add_column("prompt file", style="path")
    table.add_column("status")
    table.add_column("cost", justify="right")
    table.add_column("model")
    table.add_column("error")
    if sync_metadata:
        table.add_column("metadata")
    for r in results:
        cells = [
            str(r.get("prompt_file", "")),
            str(r.get("status", "")),
            f"${float(r.get('cost') or 0.0):.4f}",
            str(r.get("model", "")),
            str(r.get("error", "")),
        ]
        if sync_metadata:
            meta = meta_results.get(str(r.get("prompt_file", "")))
            cells.append(_meta_status_string(meta))
        table.add_row(*cells)
    if not quiet:
        console.print(table)

    # PRD sync (both branches): keyed off arch_updates_count.
    if arch_updates_count > 0:
        prd_path = _find_prd_file(repo_root)
        if prd_path:
            try:
                from .agentic_common import run_agentic_task

                instruction = (
                    f"Review the PRD at {prd_path} against the updated architecture and "
                    "produce an updated PRD. Wrap the new PRD content in "
                    "<updated-prd>...</updated-prd> tags."
                )
                llm_success, llm_output, llm_cost, _llm_model = run_agentic_task(
                    instruction, repo_root, verbose=False, max_retries=1
                )
                total_cost += float(llm_cost or 0.0)
                if llm_success and llm_output:
                    m = re.search(
                        r"<updated-prd>(.*?)</updated-prd>",
                        llm_output,
                        re.DOTALL,
                    )
                    if m and not dry_run:
                        prd_path.write_text(m.group(1).strip() + "\n", encoding="utf-8")
                        if not quiet:
                            console.print(
                                f"[success]PRD updated:[/success] [path]{prd_path}[/path]"
                            )
                elif not quiet:
                    console.print("[warning]PRD agent call failed; PRD unchanged.[/warning]")
            except Exception as exc:
                if not quiet:
                    console.print(f"[warning]PRD sync skipped:[/warning] {exc}")

    # Non-zero exit on per-pair metadata failure (sync_metadata only).
    if sync_metadata:
        any_failed = any(
            (m is None) or (not getattr(m, "ok", False))
            for m in meta_results.values()
        )
        # Only treat as failure if at least one pair was updated and its
        # metadata sync attempt did not succeed.
        attempted_meta = [m for m in meta_results.values() if m is not None]
        # If we have an explicit failure (None or not-ok) for any updated pair:
        any_explicit_failure = any(
            not getattr(m, "ok", False) for m in attempted_meta
        )
        if any_explicit_failure:
            raise click.exceptions.Exit(1)
        if any_failed and attempted_meta:
            raise click.exceptions.Exit(1)

    models_str = ",".join(sorted(models_used)) if models_used else "models"
    return ("Repository update complete.", total_cost, models_str)


# ---------------------------------------------------------------------------
# Single-file & regeneration paths.
# ---------------------------------------------------------------------------
def _run_single_file_mode(
    ctx: Any,
    input_prompt_file: Optional[str],
    modified_code_file: str,
    input_code_file: Optional[str],
    output: Optional[str],
    use_git: bool,
    simple: bool,
    strength: Optional[float],
    temperature: Optional[float],
    dry_run: bool,
) -> Optional[Tuple[str, float, str]]:
    obj = ctx.obj or {}
    verbose = obj.get("verbose", False)
    quiet = obj.get("quiet", False)
    time_param = obj.get("time", DEFAULT_TIME)
    force = obj.get("force", False)
    context_override = obj.get("context")
    confirm_callback = obj.get("confirm_callback")

    # Resolve strength/temperature.
    resolved_strength = strength if strength is not None else obj.get("strength", DEFAULT_STRENGTH)
    resolved_temperature = temperature if temperature is not None else obj.get("temperature", 0.0)
    obj["strength"] = resolved_strength
    obj["temperature"] = resolved_temperature

    # Regeneration mode: only modified_code_file provided.
    regeneration_mode = input_prompt_file is None

    if regeneration_mode:
        # Distinguish --output values that name a destination prompt file from
        # those that name an output directory. Treating an explicit file path
        # as a directory creates a phantom sub-prompt and then fails the
        # final write because the directory entry shadows the requested path.
        output_is_explicit_file = (
            output is not None
            and not os.path.isdir(output)
            and not output.endswith(("/", os.sep))
        )
        try:
            if output_is_explicit_file:
                explicit_path = Path(output).resolve()
                explicit_path.parent.mkdir(parents=True, exist_ok=True)
                if not explicit_path.exists():
                    explicit_path.write_text("", encoding="utf-8")
                prompt_path = explicit_path
                code_path = Path(modified_code_file).resolve()
            else:
                prompt_path, code_path = resolve_prompt_code_pair(
                    Path(modified_code_file), quiet=quiet, output_dir=output
                )
        except Exception as exc:
            if not quiet:
                console.print(f"[error]Failed to resolve prompt for code:[/error] {exc}")
            return None
        input_prompt_file = str(prompt_path)
    else:
        prompt_path = Path(input_prompt_file)
        code_path = Path(modified_code_file)

    output_path = Path(output) if output else prompt_path

    # Try agentic first when allowed.
    if not simple:
        try:
            from .agentic_update import run_agentic_update

            success, message, cost, model, _changed = run_agentic_update(
                prompt_file=str(prompt_path),
                code_file=str(code_path),
                quiet=quiet,
            )
            if success:
                # Agentic writes directly to file; read back the prompt.
                try:
                    new_prompt = prompt_path.read_text(encoding="utf-8")
                except Exception as exc:
                    if not quiet:
                        console.print(f"[error]Agentic update succeeded but file unreadable:[/error] {exc}")
                    return None
                # If a separate output path was requested, copy it there.
                if output and Path(output) != prompt_path:
                    sanitized = _sanitize_for_write(new_prompt, output_path)
                    Path(output).write_text(sanitized, encoding="utf-8")
                # Metadata finalization (always-on).
                ok = _run_single_file_metadata_sync(prompt_path, code_path, dry_run=dry_run)
                if not ok:
                    raise click.exceptions.Exit(1)
                return (new_prompt, float(cost or 0.0), model or "")
            if verbose and not quiet:
                console.print(f"[info]Falling back to legacy update: {message}[/info]")
        except click.exceptions.Exit:
            raise
        except ImportError:
            pass
        except Exception as exc:
            if verbose and not quiet:
                console.print(f"[warning]Agentic path error: {exc}[/warning]")

    # Legacy path.
    try:
        if regeneration_mode:
            try:
                modified_code = code_path.read_text(encoding="utf-8")
            except Exception as exc:
                if not quiet:
                    console.print(f"[error]Cannot read modified code:[/error] {exc}")
                return None
            modified_prompt, total_cost, model_name = update_prompt(
                input_prompt="",
                input_code="",
                modified_code=modified_code,
                strength=resolved_strength,
                temperature=resolved_temperature,
                verbose=verbose,
                time=time_param,
            )
        elif use_git:
            try:
                input_prompt = prompt_path.read_text(encoding="utf-8")
            except Exception as exc:
                if not quiet:
                    console.print(f"[error]Cannot read prompt:[/error] {exc}")
                return None
            gu = git_update(
                input_prompt=input_prompt,
                modified_code_file=str(code_path),
                strength=resolved_strength,
                temperature=resolved_temperature,
                verbose=verbose,
                simple=True,
                quiet=quiet,
                prompt_file=str(prompt_path),
                time=time_param,
            )
            if not gu:
                if not quiet:
                    console.print("[error]git_update returned no result.[/error]")
                return None
            modified_prompt, total_cost, model_name = gu
        else:
            # True update with explicit input_code_file.
            if not input_code_file:
                raise ValueError("input_code_file or use_git is required for true update mode.")
            try:
                input_prompt = prompt_path.read_text(encoding="utf-8")
                input_code = Path(input_code_file).read_text(encoding="utf-8")
                modified_code = code_path.read_text(encoding="utf-8")
            except Exception as exc:
                if not quiet:
                    console.print(f"[error]Cannot read inputs:[/error] {exc}")
                return None
            modified_prompt, total_cost, model_name = update_prompt(
                input_prompt=input_prompt,
                input_code=input_code,
                modified_code=modified_code,
                strength=resolved_strength,
                temperature=resolved_temperature,
                verbose=verbose,
                time=time_param,
            )
    except click.Abort:
        raise
    except ValueError as exc:
        if not quiet:
            console.print(f"[error]{exc}[/error]")
        return None
    except Exception as exc:
        if not quiet:
            console.print(f"[error]Update failed:[/error] {exc}")
        return None

    # Validate prompt non-empty (true-update).
    if modified_prompt is None or not modified_prompt.strip():
        if not quiet:
            console.print("[error]Update produced an empty prompt; aborting write.[/error]")
        return None

    # Sanitize and write.
    sanitized = _sanitize_for_write(modified_prompt, output_path)
    try:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        if not dry_run:
            output_path.write_text(sanitized, encoding="utf-8")
        if not quiet:
            console.print(f"[success]Wrote updated prompt:[/success] [path]{output_path}[/path]")
    except Exception as exc:
        if not quiet:
            console.print(f"[error]Failed to write output:[/error] {exc}")
        return None

    # Always-on metadata finalization for single-file/regeneration mode (#1005).
    ok = _run_single_file_metadata_sync(
        prompt_path=output_path if output else prompt_path,
        code_path=code_path,
        dry_run=dry_run,
    )
    if not ok:
        # Non-zero exit per #1005 acceptance criterion.
        raise click.exceptions.Exit(1)

    # Touch construct_paths for context propagation (best-effort).
    if context_override or confirm_callback or force:
        try:
            _ = construct_paths  # noqa: F841 — referenced for side-effectful imports
        except Exception:
            pass

    return (sanitized, float(total_cost or 0.0), model_name or "")


# ---------------------------------------------------------------------------
# Public entry point.
# ---------------------------------------------------------------------------
def update_main(
    ctx: Any,
    input_prompt_file: Optional[str],
    modified_code_file: Optional[str],
    input_code_file: Optional[str],
    output: Optional[str],
    use_git: bool = False,
    repo: bool = False,
    extensions: Optional[Tuple[str, ...]] = None,
    directory: Optional[str] = None,
    strength: Optional[float] = None,
    temperature: Optional[float] = None,
    simple: bool = False,
    base_branch: str = "main",
    budget: Optional[float] = None,
    dry_run: bool = False,
    sync_metadata: bool = False,
) -> Optional[Tuple[str, float, str]]:
    """
    CLI wrapper for `pdd update`.

    Modes:
      - Repo mode (`repo=True`): scan repo, detect changed pairs, update
        each, optionally run multi-stage metadata sync per pair, and run
        PRD sync once at the end.
      - Regeneration mode: only `modified_code_file` provided — derive the
        prompt path and treat as regeneration.
      - True update: `input_prompt_file` + `modified_code_file` plus either
        `use_git` or `input_code_file`.

    Returns (prompt, cost, model) on success, or None on early no-op /
    error. Raises `click.exceptions.Exit(1)` when single-file or
    repo-mode metadata finalization reports a stage failure (issue #1005,
    #871) — the success tuple is reserved for fully-clean finalization.
    """
    obj = ctx.obj or {}
    quiet = obj.get("quiet", False)

    # Mutually-exclusive validation.
    if use_git and input_code_file:
        raise ValueError("use_git and input_code_file are mutually exclusive.")

    try:
        if repo:
            return _run_repo_mode(
                ctx=ctx,
                directory=directory,
                extensions=extensions,
                base_branch=base_branch,
                simple=simple,
                output_dir=output,
                sync_metadata=sync_metadata,
                dry_run=dry_run,
                budget=budget,
            )

        if not modified_code_file:
            raise ValueError("modified_code_file is required outside of repo mode.")

        return _run_single_file_mode(
            ctx=ctx,
            input_prompt_file=input_prompt_file,
            modified_code_file=modified_code_file,
            input_code_file=input_code_file,
            output=output,
            use_git=use_git,
            simple=simple,
            strength=strength,
            temperature=temperature,
            dry_run=dry_run,
        )
    except click.Abort:
        raise
    except click.exceptions.Exit:
        raise
    except ValueError as exc:
        if not quiet:
            console.print(f"[error]{exc}[/error]")
        return None
    except Exception as exc:
        # Try to detect git-repo errors by name to keep heavy imports out.
        if exc.__class__.__name__ == "InvalidGitRepositoryError":
            if not quiet:
                console.print(f"[error]Invalid git repository:[/error] {exc}")
            return None
        if not quiet:
            console.print(f"[error]update_main failed:[/error] {exc}")
        return None