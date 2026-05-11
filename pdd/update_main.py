from __future__ import annotations

import os
import re
import sys
import json
import fnmatch
import hashlib
import subprocess
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

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
from .validate_prompt_includes import sanitize_prompt_output
from .operation_log import infer_module_identity, save_fingerprint

# Module-level Console with custom theme
_THEME = Theme({
    "info": "cyan",
    "warning": "yellow",
    "error": "bold red",
    "success": "green",
    "path": "dim blue",
})
console = Console(theme=_THEME)


# ---------------------------------------------------------------------------
# Constants for repo scanning
# ---------------------------------------------------------------------------
_SKIP_EXTENSIONS: Set[str] = {
    ".json", ".jsonl", ".yaml", ".yml", ".md", ".toml", ".ini", ".css",
    ".html", ".lock", ".svg", ".png", ".jpg", ".gif", ".ico", ".woff",
    ".woff2", ".ttf", ".eot", ".map", ".csv", ".txt",
}

_SKIP_FILENAMES: Set[str] = {
    "package-lock.json", "yarn.lock", "pnpm-lock.yaml", "poetry.lock",
    "jest.config.js", "jest.config.ts", "tailwind.config.js",
    "tailwind.config.ts", "postcss.config.js", "next.config.js",
    "next.config.ts", "vite.config.js", "vite.config.ts",
    "babel.config.js", "rollup.config.js", "webpack.config.js",
    "mockServiceWorker.js", "next-env.d.ts", "vitest.config.js",
    "vitest.config.ts", "setup.js", "setup.ts",
}

_SKIP_BASENAME_SUFFIXES: Tuple[str, ...] = (
    ".config", ".setup", ".stories", ".story",
    ".test", ".spec", ".e2e.test", ".e2e.spec", ".d",
)

_SKIP_DIRS: Set[str] = {
    ".git", ".idea", ".vscode", "__pycache__", "node_modules",
    ".venv", "venv", "dist", "build", ".next", ".nuxt", ".output",
    ".cache", ".turbo", ".parcel-cache", "coverage", ".pdd",
}


# ---------------------------------------------------------------------------
# Helper: extract template variables / pddrc handling
# ---------------------------------------------------------------------------
def _extract_template_vars(
    concrete_path: str, template: str
) -> Optional[Dict[str, str]]:
    """Reverse-match a path against a template like 'src/{category}/{name}.py'."""
    if not template:
        return None
    # Find variables in the template in order
    var_names = re.findall(r"\{([^}]+)\}", template)
    if not var_names:
        return {} if concrete_path == template else None

    # Build regex with backreferences for repeated vars
    pattern_parts: List[str] = []
    seen: Dict[str, int] = {}
    group_idx = 0
    for piece in re.split(r"(\{[^}]+\})", template):
        if piece.startswith("{") and piece.endswith("}"):
            var = piece[1:-1]
            if var in seen:
                pattern_parts.append(f"\\{seen[var]}")
            else:
                group_idx += 1
                seen[var] = group_idx
                pattern_parts.append(r"([^/]+)")
        else:
            pattern_parts.append(re.escape(piece))
    regex = "^" + "".join(pattern_parts) + "$"
    m = re.match(regex, concrete_path)
    if not m:
        return None
    result: Dict[str, str] = {}
    for var, idx in seen.items():
        result[var] = m.group(idx)
    return result


def _load_pddrc(start_dir: Path, repo_root: Path) -> Optional[Dict[str, Any]]:
    """Search upward for .pddrc starting at start_dir, stopping at repo_root."""
    try:
        import yaml  # type: ignore
    except ImportError:
        try:
            from ruamel.yaml import YAML  # type: ignore
            yaml = None  # type: ignore
        except ImportError:
            return None

    current = start_dir.resolve()
    repo_root = repo_root.resolve()
    while True:
        candidate = current / ".pddrc"
        if candidate.is_file():
            try:
                text = candidate.read_text(encoding="utf-8")
                if yaml is not None:
                    return yaml.safe_load(text)
                # ruamel fallback
                from ruamel.yaml import YAML  # type: ignore
                y = YAML(typ="safe")
                from io import StringIO
                return y.load(StringIO(text))
            except Exception:
                return None
        if current == repo_root or current == current.parent:
            break
        current = current.parent
    # Final check at repo_root if not visited
    candidate = repo_root / ".pddrc"
    if candidate.is_file():
        try:
            import yaml  # type: ignore
            return yaml.safe_load(candidate.read_text(encoding="utf-8"))
        except Exception:
            return None
    return None


def _find_matching_context(
    pddrc_data: Dict[str, Any], rel_code_path: str
) -> Optional[Dict[str, Any]]:
    """Find the first context whose paths pattern matches the relative code path."""
    if not pddrc_data or "contexts" not in pddrc_data:
        return None
    for ctx in pddrc_data.get("contexts", []):
        patterns = ctx.get("paths", [])
        if isinstance(patterns, str):
            patterns = [patterns]
        for pat in patterns:
            if fnmatch.fnmatch(rel_code_path, pat) or fnmatch.fnmatch(
                rel_code_path, pat.rstrip("/") + "/*"
            ):
                return ctx
        # Default context (no paths specified or "**")
        if not patterns or "**" in patterns:
            return ctx
    return None


def _expand_template(template: str, variables: Dict[str, str]) -> str:
    """Expand a template like '{name}_{language}.prompt' with variables."""
    try:
        return template.format(**variables)
    except (KeyError, IndexError):
        # Fallback: replace known vars manually
        out = template
        for k, v in variables.items():
            out = out.replace("{" + k + "}", v)
        return out


def _resolve_existing_prompt_path_case_insensitive(prompt_path: Path) -> Path:
    """Preserve on-disk casing of any case-insensitive filename match."""
    parent = prompt_path.parent
    if not parent.is_dir():
        return prompt_path
    target_lower = prompt_path.name.lower()
    try:
        for entry in parent.iterdir():
            if entry.name.lower() == target_lower:
                return entry
    except OSError:
        pass
    return prompt_path


# ---------------------------------------------------------------------------
# Language detection
# ---------------------------------------------------------------------------
_LANGUAGE_MAP: Dict[str, str] = {
    ".py": "python",
    ".js": "javascript",
    ".jsx": "javascript",
    ".ts": "typescript",
    ".tsx": "typescript",
    ".go": "go",
    ".rs": "rust",
    ".java": "java",
    ".kt": "kotlin",
    ".rb": "ruby",
    ".php": "php",
    ".c": "c",
    ".h": "c",
    ".cpp": "cpp",
    ".hpp": "cpp",
    ".cc": "cpp",
    ".cs": "csharp",
    ".swift": "swift",
    ".scala": "scala",
    ".sh": "bash",
    ".bash": "bash",
    ".zsh": "bash",
    ".lua": "lua",
    ".r": "r",
    ".jl": "julia",
}


def get_language(filepath: Path) -> Optional[str]:
    suffix = filepath.suffix.lower()
    return _LANGUAGE_MAP.get(suffix)


# ---------------------------------------------------------------------------
# .pddrc-based prompt resolution
# ---------------------------------------------------------------------------
def _find_nearest_pddrc_for_file(
    file_path: Path, repo_root: Path
) -> Tuple[Path, Optional[Dict[str, Any]]]:
    """Find the nearest .pddrc and return its directory (effective root) and data."""
    current = file_path.parent.resolve()
    repo_root = repo_root.resolve()
    while True:
        candidate = current / ".pddrc"
        if candidate.is_file():
            try:
                import yaml  # type: ignore
                data = yaml.safe_load(candidate.read_text(encoding="utf-8"))
                return current, data
            except Exception:
                return current, None
        if current == repo_root or current == current.parent:
            break
        current = current.parent
    return repo_root, None


def _resolve_prompt_from_pddrc(
    code_file_path: Path, repo_root: Path, language: str
) -> Optional[str]:
    """Resolve prompt path using .pddrc template, returning absolute path string."""
    eff_root, pddrc_data = _find_nearest_pddrc_for_file(code_file_path, repo_root)
    if not pddrc_data:
        return None
    try:
        rel_code = str(code_file_path.resolve().relative_to(eff_root))
    except ValueError:
        return None

    ctx = _find_matching_context(pddrc_data, rel_code)
    if not ctx:
        return None

    outputs = ctx.get("outputs", {}) or {}
    prompt_cfg = outputs.get("prompt", {}) or {}
    path_template = prompt_cfg.get("path") or prompt_cfg.get("template")
    if not path_template:
        return None

    # Try to extract variables by reverse-matching the code path against
    # the generate output template, or fall back to deriving from filename.
    code_template = (outputs.get("generate", {}) or {}).get("path", "")
    variables: Dict[str, str] = {
        "name": code_file_path.stem,
        "basename": code_file_path.stem,
        "language": language,
        "ext": code_file_path.suffix.lstrip("."),
    }
    extracted = _extract_template_vars(rel_code, code_template)
    if extracted:
        variables.update(extracted)

    expanded = _expand_template(path_template, variables)
    abs_prompt_path = (eff_root / expanded).resolve()
    return str(abs_prompt_path)


# ---------------------------------------------------------------------------
# Repo root detection
# ---------------------------------------------------------------------------
def _find_repo_root(start: Path) -> Path:
    """Walk upward to find a .git directory; fall back to start."""
    current = start.resolve()
    while True:
        if (current / ".git").exists():
            return current
        if current == current.parent:
            return start.resolve()
        current = current.parent


# ---------------------------------------------------------------------------
# resolve_prompt_code_pair
# ---------------------------------------------------------------------------
def resolve_prompt_code_pair(
    code_file_path: Path,
    quiet: bool,
    output_dir: Optional[str] = None,
) -> Tuple[Path, Path]:
    """Derive the prompt file path for a given code file."""
    code_file_path = code_file_path.resolve()
    language = get_language(code_file_path) or "unknown"
    repo_root = _find_repo_root(code_file_path.parent)

    prompt_path: Optional[Path] = None
    if not output_dir:
        resolved = _resolve_prompt_from_pddrc(code_file_path, repo_root, language)
        if resolved:
            prompt_path = Path(resolved)

    if prompt_path is None:
        # Fallback: prompts/ directory at the appropriate root, mirror the
        # subdirectory structure relative to the repo root, stripping common
        # generate output prefixes.
        eff_root, pddrc_data = _find_nearest_pddrc_for_file(
            code_file_path, repo_root
        )
        prompts_dir_name = "prompts"
        gen_out_prefix = ""
        if pddrc_data:
            try:
                rel_code = str(code_file_path.relative_to(eff_root))
                ctx = _find_matching_context(pddrc_data, rel_code) or {}
                outputs = ctx.get("outputs", {}) or {}
                prompts_dir_name = (
                    outputs.get("prompts_dir")
                    or (outputs.get("prompt", {}) or {}).get("dir")
                    or "prompts"
                )
                gen_out_prefix = outputs.get("generate_output_path", "") or ""
            except Exception:
                pass

        if output_dir:
            base_prompts_dir = Path(output_dir)
        else:
            base_prompts_dir = (eff_root / prompts_dir_name).resolve()

        try:
            rel = code_file_path.relative_to(eff_root)
        except ValueError:
            rel = Path(code_file_path.name)

        rel_str = str(rel)
        if gen_out_prefix and rel_str.startswith(gen_out_prefix.rstrip("/") + "/"):
            rel_str = rel_str[len(gen_out_prefix.rstrip("/")) + 1:]
            rel = Path(rel_str)

        # Build prompt filename: <stem>_<language>.prompt mirroring subdirs
        subdir = rel.parent
        stem = code_file_path.stem
        prompt_name = f"{stem}_{language}.prompt"
        if str(subdir) in ("", "."):
            prompt_path = base_prompts_dir / prompt_name
        else:
            prompt_path = base_prompts_dir / subdir / prompt_name

    # Preserve case-insensitive filename match
    prompt_path = _resolve_existing_prompt_path_case_insensitive(prompt_path)

    # Ensure parent directory exists & create empty prompt if missing
    try:
        prompt_path.parent.mkdir(parents=True, exist_ok=True)
        if not prompt_path.exists():
            prompt_path.touch()
    except OSError as exc:
        if not quiet:
            console.print(
                f"[warning]Could not create prompt path "
                f"{prompt_path}: {exc}[/warning]"
            )

    return prompt_path, code_file_path


# ---------------------------------------------------------------------------
# .pddignore handling
# ---------------------------------------------------------------------------
def _load_pddignore(scan_root: Path) -> Tuple[List[str], Optional[Path]]:
    """Walk upward from scan_root to find .pddignore (stop at git root)."""
    current = scan_root.resolve()
    git_root = _find_repo_root(current)
    while True:
        candidate = current / ".pddignore"
        if candidate.is_file():
            try:
                lines = candidate.read_text(encoding="utf-8").splitlines()
                patterns = [
                    line.strip() for line in lines
                    if line.strip() and not line.strip().startswith("#")
                ]
                return patterns, current
            except OSError:
                return [], None
        if current == git_root or current == current.parent:
            break
        current = current.parent
    return [], None


def _is_pddignored(
    filepath: Path, pddignore_root: Optional[Path], patterns: List[str]
) -> bool:
    if not patterns or pddignore_root is None:
        return False
    try:
        rel = str(filepath.resolve().relative_to(pddignore_root.resolve()))
    except ValueError:
        return False
    basename = filepath.name
    rel_posix = rel.replace(os.sep, "/")

    for pat in patterns:
        # Directory pattern (ends with /)
        if pat.endswith("/"):
            dir_pat = pat.rstrip("/")
            parts = rel_posix.split("/")
            if dir_pat in parts:
                return True
            if fnmatch.fnmatch(rel_posix, dir_pat + "/*"):
                return True
            continue
        # Relative path glob
        if "/" in pat:
            if fnmatch.fnmatch(rel_posix, pat):
                return True
        else:
            # Basename glob
            if fnmatch.fnmatch(basename, pat):
                return True
            # Also try matching as a path component
            if fnmatch.fnmatch(rel_posix, pat) or fnmatch.fnmatch(
                rel_posix, "*/" + pat
            ):
                return True
    return False


def _has_skip_suffix(filepath: Path) -> bool:
    stem = filepath.stem.lower()
    name_lower = filepath.name.lower()
    # Special handling for compound suffixes like .e2e.test
    for suf in _SKIP_BASENAME_SUFFIXES:
        if stem.endswith(suf) or name_lower.endswith(suf + filepath.suffix.lower()):
            return True
    return False


def _has_meaningful_code(filepath: Path) -> bool:
    """Return True if file has at least one non-blank, non-comment line."""
    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as f:
            for line in f:
                stripped = line.strip()
                if not stripped:
                    continue
                if stripped.startswith(("#", "//", "/*", "*", "<!--", "--")):
                    continue
                return True
    except OSError:
        return False
    return False


# ---------------------------------------------------------------------------
# Repo scanning
# ---------------------------------------------------------------------------
def _git_ls_files(repo_root: Path) -> Optional[List[str]]:
    try:
        result = subprocess.run(
            ["git", "-C", str(repo_root), "ls-files"],
            capture_output=True, text=True, check=True, timeout=60,
        )
        return [line for line in result.stdout.splitlines() if line]
    except (subprocess.CalledProcessError, FileNotFoundError,
            subprocess.TimeoutExpired):
        return None


def _walk_files(repo_root: Path) -> List[str]:
    out: List[str] = []
    for root, dirs, files in os.walk(repo_root):
        dirs[:] = [d for d in dirs if d not in _SKIP_DIRS]
        for f in files:
            full = Path(root) / f
            try:
                rel = str(full.relative_to(repo_root))
                out.append(rel)
            except ValueError:
                continue
    return out


def find_and_resolve_all_pairs(
    repo_root: Path,
    quiet: bool,
    extensions: Optional[List[str]] = None,
    output_dir: Optional[str] = None,
) -> List[Tuple[Path, Path]]:
    """Walk repo and resolve (prompt, code) pairs for eligible files."""
    repo_root = repo_root.resolve()
    files = _git_ls_files(repo_root)
    if files is None:
        files = _walk_files(repo_root)

    pddignore_patterns, pddignore_root = _load_pddignore(repo_root)

    # Normalize extensions
    ext_filter: Optional[Set[str]] = None
    if extensions:
        ext_filter = set()
        for e in extensions:
            ext_filter.add(e if e.startswith(".") else "." + e)

    pairs: List[Tuple[Path, Path]] = []
    seen_codes: Set[Path] = set()

    for rel in files:
        path = (repo_root / rel).resolve()
        if not path.is_file():
            continue
        suffix = path.suffix.lower()
        name = path.name

        # Multi-layer exclusion
        if suffix == ".prompt":
            continue
        if suffix in _SKIP_EXTENSIONS:
            continue
        if name in _SKIP_FILENAMES:
            continue
        if name.startswith("test_"):
            continue
        if path.stem.endswith("_example"):
            continue
        if _has_skip_suffix(path):
            continue
        if _is_pddignored(path, pddignore_root, pddignore_patterns):
            continue
        if get_language(path) is None:
            continue
        if ext_filter is not None and suffix not in ext_filter:
            continue
        if not _has_meaningful_code(path):
            continue
        if path in seen_codes:
            continue
        seen_codes.add(path)

        try:
            prompt_path, code_path = resolve_prompt_code_pair(
                path, quiet, output_dir
            )
            pairs.append((prompt_path, code_path))
        except Exception as exc:
            if not quiet:
                console.print(
                    f"[warning]Could not resolve pair for "
                    f"{path}: {exc}[/warning]"
                )
            continue

    return pairs


# ---------------------------------------------------------------------------
# Git changed files
# ---------------------------------------------------------------------------
def get_git_changed_files(repo_root: Path, base_branch: str = "main") -> Set[str]:
    """Combine merge-base diff, uncommitted changes, and untracked files."""
    changed: Set[str] = set()
    repo_root = repo_root.resolve()

    def _run(args: List[str]) -> Optional[str]:
        try:
            r = subprocess.run(
                ["git", "-C", str(repo_root)] + args,
                capture_output=True, text=True, timeout=60,
            )
            if r.returncode == 0:
                return r.stdout
        except (FileNotFoundError, subprocess.TimeoutExpired):
            return None
        return None

    # Merge-base diff
    merge_base_out = _run(["merge-base", "HEAD", base_branch])
    if merge_base_out:
        base_sha = merge_base_out.strip()
        diff = _run(["diff", "--name-only", base_sha, "HEAD"])
        if diff:
            for line in diff.splitlines():
                if line.strip():
                    changed.add(str((repo_root / line.strip()).resolve()))

    # Uncommitted changes
    diff_uncommitted = _run(["diff", "--name-only"])
    if diff_uncommitted:
        for line in diff_uncommitted.splitlines():
            if line.strip():
                changed.add(str((repo_root / line.strip()).resolve()))
    diff_staged = _run(["diff", "--name-only", "--staged"])
    if diff_staged:
        for line in diff_staged.splitlines():
            if line.strip():
                changed.add(str((repo_root / line.strip()).resolve()))

    # Untracked files
    untracked = _run(["ls-files", "--others", "--exclude-standard"])
    if untracked:
        for line in untracked.splitlines():
            if line.strip():
                changed.add(str((repo_root / line.strip()).resolve()))

    return changed


# ---------------------------------------------------------------------------
# Basename / language inference for fingerprints
# ---------------------------------------------------------------------------
def derive_basename_and_language(
    code_file_path: Path, repo_root: Path
) -> Tuple[str, str]:
    """Derive (basename, language) using rel-path-without-extension as basename."""
    code_file_path = code_file_path.resolve()
    repo_root = repo_root.resolve()
    language = get_language(code_file_path) or "unknown"
    try:
        rel = code_file_path.relative_to(repo_root)
    except ValueError:
        rel = Path(code_file_path.name)
    rel_no_ext = rel.with_suffix("")
    basename = str(rel_no_ext).replace(os.sep, "_").replace("/", "_")
    return basename, language


# ---------------------------------------------------------------------------
# Fingerprint / change detection
# ---------------------------------------------------------------------------
def _sha256_of(path: Path) -> Optional[str]:
    try:
        h = hashlib.sha256()
        with open(path, "rb") as f:
            for chunk in iter(lambda: f.read(8192), b""):
                h.update(chunk)
        return h.hexdigest()
    except OSError:
        return None

def _load_fingerprint(basename: str, language: str) -> Optional[Dict[str, Any]]:
    fp_path = Path(".pdd") / "meta" / f"{basename}_{language}.json"
    if not fp_path.is_file():
        return None
    try:
        return json.loads(fp_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None


def _check_include_deps_changed(
    fingerprint: Dict[str, Any]
) -> Tuple[bool, str]:
    deps = fingerprint.get("include_deps") or {}
    if not deps or not isinstance(deps, dict):
        return False, ""
    for dep_path, stored_hash in deps.items():
        p = Path(dep_path)
        current = _sha256_of(p)
        if current is None:
            return True, f"include dep missing: {dep_path}"
        if current != stored_hash:
            return True, f"include dep changed: {dep_path}"
    return False, ""


def is_code_changed(
    code_file_path: Path,
    repo_root: Path,
    git_changed_files: Set[str],
    prompt_file_path: Optional[Path] = None,
) -> Tuple[bool, str]:
    """Check if code is changed relative to fingerprint or git."""
    code_file_path = code_file_path.resolve()
    basename: Optional[str] = None
    language: Optional[str] = None

    if prompt_file_path is not None:
        try:
            basename, language = infer_module_identity(str(prompt_file_path))
        except Exception:
            basename = None
    if not basename or not language:
        basename, language = derive_basename_and_language(
            code_file_path, repo_root
        )

    fp = _load_fingerprint(basename, language)
    if fp is not None:
        stored_code_hash = fp.get("code_hash")
        current_hash = _sha256_of(code_file_path)
        if stored_code_hash and current_hash:
            if stored_code_hash != current_hash:
                return True, "code hash changed since last fingerprint"
            # Code unchanged; check include deps
            deps_changed, reason = _check_include_deps_changed(fp)
            if deps_changed:
                return True, reason
            return False, "fingerprint matches"
        # Missing hash data — fall through to git check

    # No fingerprint → fall back to git changed set
    if str(code_file_path) in git_changed_files:
        return True, "in git changed set"
    return False, "no fingerprint, not in git changed set"


# ---------------------------------------------------------------------------
# Sanitize-and-write helper
# ---------------------------------------------------------------------------
def _sanitize_and_write(content: str, destination: Path) -> str:
    """Sanitize prompt content and write to destination. Returns final content."""
    try:
        sanitized, _removed = sanitize_prompt_output(content, destination)
    except Exception:
        sanitized = content
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(sanitized, encoding="utf-8")
    return sanitized


# ---------------------------------------------------------------------------
# Save fingerprint helper (best-effort)
# ---------------------------------------------------------------------------
def _save_fingerprint_safe(
    prompt_file_path: Path,
    code_file_path: Path,
    cost: float,
    model: str,
    quiet: bool,
) -> None:
    try:
        basename, language = infer_module_identity(str(prompt_file_path))
        save_fingerprint(
            basename=basename,
            language=language,
            operation="update",
            paths={
                "prompt": prompt_file_path,
                "code": code_file_path,
            },
            cost=cost,
            model=model,
        )
    except Exception as exc:
        if not quiet:
            console.print(
                f"[warning]Could not save fingerprint for "
                f"{prompt_file_path}: {exc}[/warning]"
            )


# ---------------------------------------------------------------------------
# Agentic update wrapper
# ---------------------------------------------------------------------------
def _try_agentic_update(
    prompt_file: str,
    code_file: str,
    quiet: bool,
    verbose: bool,
) -> Optional[Tuple[str, float, str]]:
    """Try agentic update; return (prompt, cost, model) or None on failure."""
    try:
        from .agentic_update import run_agentic_update
    except ImportError:
        return None
    try:
        success, message, cost, model, _changed = run_agentic_update(
            prompt_file=prompt_file,
            code_file=code_file,
            quiet=quiet,
        )
        if success:
            try:
                content = Path(prompt_file).read_text(encoding="utf-8")
            except OSError:
                return None
            if not content.strip():
                return None
            return content, cost, model
        if verbose and not quiet:
            console.print(f"[warning]Agentic update failed: {message}[/warning]")
        return None
    except Exception as exc:
        if verbose and not quiet:
            console.print(
                f"[warning]Agentic update raised: {exc}[/warning]"
            )
        return None


# ---------------------------------------------------------------------------
# Single-pair update
# ---------------------------------------------------------------------------
def update_file_pair(
    prompt_file: Path,
    code_file: Path,
    ctx: Any,
    repo: bool,
    simple: bool,
) -> Dict[str, Any]:
    """Update a single (prompt, code) pair."""
    obj = (ctx.obj or {}) if ctx is not None else {}
    quiet = obj.get("quiet", False)
    verbose = obj.get("verbose", False)
    strength = obj.get("strength", DEFAULT_STRENGTH)
    temperature = obj.get("temperature", 0.0)
    time_param = obj.get("time", DEFAULT_TIME)

    result: Dict[str, Any] = {
        "prompt_file": str(prompt_file),
        "code_file": str(code_file),
        "status": "skipped",
        "cost": 0.0,
        "model": "",
        "error": "",
    }

    if not code_file.is_file():
        result["status"] = "error"
        result["error"] = f"Code file does not exist: {code_file}"
        return result

    # Try agentic first when allowed
    if not simple:
        agentic = _try_agentic_update(
            str(prompt_file), str(code_file), quiet, verbose
        )
        if agentic is not None:
            content, cost, model = agentic
            # Agentic writes directly; ensure sanitization
            try:
                _sanitize_and_write(content, prompt_file)
            except Exception:
                pass
            result["status"] = "updated (agentic)"
            result["cost"] = cost
            result["model"] = model
            _save_fingerprint_safe(prompt_file, code_file, cost, model, quiet)
            return result

    # Legacy fallback
    try:
        prompt_content = ""
        if prompt_file.is_file():
            prompt_content = prompt_file.read_text(encoding="utf-8")

        is_empty_or_new = not prompt_content.strip()

        if is_empty_or_new:
            # Use update_prompt with sentinel for generation
            updated, cost, model = update_prompt(
                input_prompt="<GENERATE_FROM_CODE>",
                input_code="",
                modified_code=code_file.read_text(encoding="utf-8"),
                strength=strength,
                temperature=temperature,
                verbose=verbose,
            )
        else:
            res = git_update(
                input_prompt=prompt_content,
                modified_code_file=str(code_file),
                strength=strength,
                temperature=temperature,
                verbose=verbose,
                simple=True,
                quiet=quiet,
                prompt_file=str(prompt_file),
            )
            if not res:
                result["status"] = "error"
                result["error"] = "git_update returned no result"
                return result
            updated, cost, model = res

        if not updated or not updated.strip():
            result["status"] = "error"
            result["error"] = "Empty prompt produced"
            return result

        _sanitize_and_write(updated, prompt_file)
        result["status"] = "updated (legacy)"
        result["cost"] = cost
        result["model"] = model
        _save_fingerprint_safe(prompt_file, code_file, cost, model, quiet)
        return result

    except Exception as exc:
        result["status"] = "error"
        result["error"] = str(exc)
        return result


# ---------------------------------------------------------------------------
# PRD discovery
# ---------------------------------------------------------------------------
def _find_prd_file(project_root: Path) -> Optional[Path]:
    candidates = ["PRD.md", "prd.md"]
    for c in candidates:
        p = project_root / c
        if p.is_file():
            return p
    for entry in project_root.glob("*_prd.md"):
        if entry.is_file():
            return entry
    for entry in project_root.glob("*_PRD.md"):
        if entry.is_file():
            return entry
    return None


# ---------------------------------------------------------------------------
# Repo-mode runner
# ---------------------------------------------------------------------------
def _repo_update(
    ctx: Any,
    extensions: Optional[List[str]],
    directory: Optional[str],
    output_dir: Optional[str],
    simple: bool,
    base_branch: str,
) -> Optional[Tuple[str, float, str]]:
    obj = ctx.obj or {} if ctx is not None else {}
    quiet = obj.get("quiet", False)

    scan_root = Path(directory).resolve() if directory else Path.cwd().resolve()
    repo_root = _find_repo_root(scan_root)

    if not quiet:
        console.print(
            f"[info]Scanning repository at[/info] [path]{scan_root}[/path]"
        )

    pairs = find_and_resolve_all_pairs(
        scan_root, quiet, extensions, output_dir
    )

    if not pairs:
        if not quiet:
            console.print("[warning]No eligible code files found.[/warning]")
        return None

    # Auto-create .pddrc if needed
    try:
        from .pddrc_initializer import ensure_pddrc_for_scan
        ensure_pddrc_for_scan(scan_root, pairs, quiet=quiet)
    except ImportError:
        pass
    except Exception as exc:
        if not quiet:
            console.print(
                f"[warning]ensure_pddrc_for_scan failed: {exc}[/warning]"
            )

    # Determine which pairs need updating
    git_changed = get_git_changed_files(repo_root, base_branch)
    pairs_to_update: List[Tuple[Path, Path]] = []
    for prompt_p, code_p in pairs:
        # Always include if prompt file is empty (0-byte)
        is_empty = (
            not prompt_p.is_file()
            or prompt_p.stat().st_size == 0
        )
        if is_empty:
            pairs_to_update.append((prompt_p, code_p))
            continue
        changed, _reason = is_code_changed(
            code_p, repo_root, git_changed, prompt_file_path=prompt_p
        )
        if changed:
            pairs_to_update.append((prompt_p, code_p))

    if not pairs_to_update:
        if not quiet:
            console.print(
                "[success]All prompts are up to date.[/success]"
            )
        return None

    if not quiet:
        console.print(
            f"[info]Updating {len(pairs_to_update)} prompt(s)...[/info]"
        )

    results: List[Dict[str, Any]] = []
    total_cost = 0.0

    progress_columns = [
        SpinnerColumn(),
        TextColumn("[progress.description]{task.description}"),
        BarColumn(),
        TaskProgressColumn(),
        TimeRemainingColumn(),
        TextColumn("[bold green]${task.fields[total_cost]:.4f}"),
    ]

    with Progress(*progress_columns, console=console, disable=quiet) as progress:
        task = progress.add_task(
            "Updating prompts",
            total=len(pairs_to_update),
            total_cost=0.0,
        )
        for prompt_p, code_p in pairs_to_update:
            res = update_file_pair(prompt_p, code_p, ctx, repo=True, simple=simple)
            total_cost += res.get("cost", 0.0)
            results.append(res)
            progress.update(task, advance=1, total_cost=total_cost)

    # Post-update architecture sync
    arch_updated_entries: List[str] = []
    arch_status = ""
    try:
        from .architecture_sync import (
            update_architecture_from_prompt,
        )
        try:
            from .architecture_sync import find_architecture_for_project
            arch_path = find_architecture_for_project(repo_root)
        except ImportError:
            arch_path = repo_root / "architecture.json"
            if not arch_path.is_file():
                arch_path = None

        if arch_path and arch_path.is_file():
            for r in results:
                if not r.get("status", "").startswith("updated"):
                    continue
                pp = Path(r["prompt_file"])
                try:
                    arch_res = update_architecture_from_prompt(
                        prompt_filename=pp.name,
                        prompts_dir=pp.parent,
                        architecture_path=arch_path,
                        dry_run=False,
                    )
                    if arch_res.get("success") and arch_res.get("updated"):
                        arch_updated_entries.append(pp.name)
                except Exception as exc:
                    if not quiet:
                        console.print(
                            f"[warning]Architecture sync failed for "
                            f"{pp.name}: {exc}[/warning]"
                        )
            arch_status = (
                f"{len(arch_updated_entries)} architecture entries updated"
                if arch_updated_entries else "architecture in sync"
            )
    except ImportError:
        pass
    except Exception as exc:
        if not quiet:
            console.print(
                f"[warning]Architecture sync error: {exc}[/warning]"
            )

    # Post-update PRD sync
    prd_status = ""
    if arch_updated_entries:
        prd_file = _find_prd_file(repo_root)
        if prd_file is not None:
            try:
                from .agentic_common import run_agentic_task
                prd_content = prd_file.read_text(encoding="utf-8")
                instr = (
                    "Review the following PRD against recent architecture "
                    f"updates: {', '.join(arch_updated_entries)}.\n"
                    "If updates are needed, return the full revised PRD "
                    "wrapped in <updated-prd>...</updated-prd> tags. "
                    "Otherwise reply with NO_CHANGES.\n\n"
                    f"PRD:\n{prd_content}"
                )
                success, output, cost, _provider = run_agentic_task(
                    instr, repo_root, verbose=False, max_retries=1,
                )
                total_cost += cost or 0.0
                if success and output:
                    m = re.search(
                        r"<updated-prd>(.*?)</updated-prd>",
                        output, re.DOTALL,
                    )
                    if m:
                        new_prd = m.group(1).strip()
                        if new_prd:
                            prd_file.write_text(new_prd, encoding="utf-8")
                            prd_status = f"PRD updated: {prd_file.name}"
                    else:
                        prd_status = "PRD: no changes needed"
            except ImportError:
                pass
            except Exception as exc:
                if not quiet:
                    console.print(
                        f"[warning]PRD sync error: {exc}[/warning]"
                    )

    # Summary table
    if not quiet:
        table = Table(title="Update Summary", show_lines=False)
        table.add_column("Prompt File", style="path")
        table.add_column("Status")
        table.add_column("Cost", justify="right")
        table.add_column("Model")
        table.add_column("Error", style="error")
        for r in results:
            table.add_row(
                Path(r["prompt_file"]).name,
                r.get("status", ""),
                f"${r.get('cost', 0.0):.4f}",
                r.get("model", ""),
                r.get("error", ""),
            )
        console.print(table)
        if arch_status:
            console.print(f"[info]Architecture:[/info] {arch_status}")
        if prd_status:
            console.print(f"[info]PRD:[/info] {prd_status}")
        console.print(
            f"[success]Total cost:[/success] ${total_cost:.4f}"
        )

    return ("Repository update complete.", total_cost, "models")


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------
def update_main(
    ctx: Any,
    input_prompt_file: Optional[str],
    modified_code_file: Optional[str],
    input_code_file: Optional[str],
    output: Optional[str],
    use_git: bool,
    repo: bool,
    extensions: Optional[List[str]],
    directory: Optional[str],
    strength: Optional[float],
    temperature: Optional[float],
    simple: bool = False,
    base_branch: str = "main",
) -> Optional[Tuple[str, float, str]]:
    """CLI wrapper for updating prompts based on modified code."""
    obj = (ctx.obj if ctx is not None and getattr(ctx, "obj", None) else {}) or {}
    verbose = obj.get("verbose", False)
    quiet = obj.get("quiet", False)
    time_param = obj.get("time", DEFAULT_TIME)
    force = obj.get("force", False)
    confirm_callback = obj.get("confirm_callback")
    context_override = obj.get("context")

    # Resolve strength/temperature
    resolved_strength = (
        strength if strength is not None
        else obj.get("strength", DEFAULT_STRENGTH)
    )
    resolved_temperature = (
        temperature if temperature is not None
        else obj.get("temperature", 0.0)
    )
    if isinstance(obj, dict):
        obj["strength"] = resolved_strength
        obj["temperature"] = resolved_temperature
        if ctx is not None:
            ctx.obj = obj

    try:
        # Validate mutual exclusion
        if use_git and input_code_file:
            raise ValueError(
                "--use-git and --input-code-file are mutually exclusive."
            )

        # Mode 3: Repo
        if repo:
            return _repo_update(
                ctx, extensions, directory, output,
                simple, base_branch,
            )

        # Mode 2: Regeneration (only modified_code_file provided)
        if (
            modified_code_file
            and not input_prompt_file
            and not use_git
            and not input_code_file
        ):
            code_path = Path(modified_code_file).resolve()
            if not code_path.is_file():
                raise ValueError(f"Code file not found: {modified_code_file}")
            prompt_path, _ = resolve_prompt_code_pair(code_path, quiet, output)

            target_prompt = Path(output).resolve() if output else prompt_path

            # Try agentic first
            if not simple:
                agentic = _try_agentic_update(
                    str(prompt_path), str(code_path), quiet, verbose
                )
                if agentic is not None:
                    content, cost, model = agentic
                    final = _sanitize_and_write(content, target_prompt)
                    _save_fingerprint_safe(
                        target_prompt, code_path, cost, model, quiet
                    )
                    if not quiet:
                        console.print(
                            f"[success]Prompt regenerated:[/success] "
                            f"[path]{target_prompt}[/path]"
                        )
                    return final, cost, model

            # Legacy regeneration: read existing prompt or empty, then update
            existing = ""
            if prompt_path.is_file():
                existing = prompt_path.read_text(encoding="utf-8")
            try:
                if not existing.strip():
                    updated, cost, model = update_prompt(
                        input_prompt="<GENERATE_FROM_CODE>",
                        input_code="",
                        modified_code=code_path.read_text(encoding="utf-8"),
                        strength=resolved_strength,
                        temperature=resolved_temperature,
                        verbose=verbose,
                    )
                else:
                    res = git_update(
                        input_prompt=existing,
                        modified_code_file=str(code_path),
                        strength=resolved_strength,
                        temperature=resolved_temperature,
                        verbose=verbose,
                        simple=True,
                        quiet=quiet,
                        prompt_file=str(prompt_path),
                    )
                    if not res:
                        raise ValueError("git_update returned no result")
                    updated, cost, model = res
            except Exception as exc:
                if not quiet:
                    console.print(
                        f"[error]Regeneration failed: {exc}[/error]"
                    )
                return None

            if not updated or not updated.strip():
                if not quiet:
                    console.print(
                        "[error]Generated prompt is empty.[/error]"
                    )
                return None

            final = _sanitize_and_write(updated, target_prompt)
            _save_fingerprint_safe(
                target_prompt, code_path, cost, model, quiet
            )
            if not quiet:
                console.print(
                    f"[success]Prompt regenerated:[/success] "
                    f"[path]{target_prompt}[/path]"
                )
            return final, cost, model

        # Mode 1: True update
        if not input_prompt_file or not modified_code_file:
            raise ValueError(
                "True update requires --input-prompt-file and "
                "--modified-code-file."
            )
        if not (use_git or input_code_file):
            raise ValueError(
                "True update requires either --use-git or --input-code-file."
            )

        prompt_path = Path(input_prompt_file).resolve()
        modified_path = Path(modified_code_file).resolve()
        if not prompt_path.is_file():
            raise ValueError(f"Prompt file not found: {input_prompt_file}")
        if not modified_path.is_file():
            raise ValueError(f"Modified code file not found: {modified_code_file}")

        target_prompt = Path(output).resolve() if output else prompt_path

        # Construct paths (best-effort, optional)
        try:
            input_files: Dict[str, str] = {
                "input_prompt_file": str(prompt_path),
                "modified_code_file": str(modified_path),
            }
            if input_code_file:
                input_files["input_code_file"] = str(
                    Path(input_code_file).resolve()
                )
            construct_paths(
                input_file_paths=input_files,
                force=force,
                quiet=quiet,
                command="update",
                command_options={"output": str(target_prompt)},
                context_override=context_override,
                confirm_callback=confirm_callback,
            )
        except Exception:
            # Non-fatal; continue
            pass

        # Try agentic first
        if not simple:
            agentic = _try_agentic_update(
                str(prompt_path), str(modified_path), quiet, verbose
            )
            if agentic is not None:
                content, cost, model = agentic
                if not content.strip():
                    if not quiet:
                        console.print(
                            "[error]Updated prompt is empty.[/error]"
                        )
                    return None
                final = _sanitize_and_write(content, target_prompt)
                _save_fingerprint_safe(
                    target_prompt, modified_path, cost, model, quiet
                )
                if not quiet:
                    console.print(
                        f"[success]Prompt updated (agentic):[/success] "
                        f"[path]{target_prompt}[/path]"
                    )
                return final, cost, model

        # Legacy true update path
        prompt_content = prompt_path.read_text(encoding="utf-8")
        if use_git:
            res = git_update(
                input_prompt=prompt_content,
                modified_code_file=str(modified_path),
                strength=resolved_strength,
                temperature=resolved_temperature,
                verbose=verbose,
                simple=True,
                quiet=quiet,
                prompt_file=str(prompt_path),
            )
            if not res:
                if not quiet:
                    console.print(
                        "[error]git_update produced no result.[/error]"
                    )
                return None
            updated, cost, model = res
        else:
            input_code_content = Path(input_code_file).read_text(
                encoding="utf-8"
            )
            modified_code_content = modified_path.read_text(encoding="utf-8")
            updated, cost, model = update_prompt(
                input_prompt=prompt_content,
                input_code=input_code_content,
                modified_code=modified_code_content,
                strength=resolved_strength,
                temperature=resolved_temperature,
                verbose=verbose,
            )

        if not updated or not updated.strip():
            if not quiet:
                console.print(
                    "[error]Updated prompt is empty; not writing.[/error]"
                )
            return None

        final = _sanitize_and_write(updated, target_prompt)
        _save_fingerprint_safe(
            target_prompt, modified_path, cost, model, quiet
        )
        if not quiet:
            console.print(
                f"[success]Prompt updated:[/success] "
                f"[path]{target_prompt}[/path]"
            )
        return final, cost, model

    except click.Abort:
        raise
    except ValueError as exc:
        if not quiet:
            console.print(f"[error]Error:[/error] {exc}")
        return None
    except Exception as exc:
        # Handle InvalidGitRepositoryError and other unexpected errors
        if not quiet:
            console.print(f"[error]Unexpected error:[/error] {exc}")
            if verbose:
                console.print_exception()
        return None