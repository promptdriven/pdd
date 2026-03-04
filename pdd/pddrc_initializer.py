from __future__ import annotations

import os
import re
from collections import Counter
from pathlib import Path
from typing import Dict, List, Optional

from rich.console import Console
from rich.syntax import Syntax

console = Console()

# Language detection markers
PYTHON_MARKERS = ("setup.py", "pyproject.toml", "setup.cfg", "Pipfile", "requirements.txt")
TYPESCRIPT_MARKERS = ("package.json",)
GO_MARKERS = ("go.mod",)
RUST_MARKERS = ("Cargo.toml",)

# Path defaults per language
LANGUAGE_DEFAULTS: dict[str, dict[str, str]] = {
    "python": {
        "generate_output_path": "pdd/",
        "test_output_path": "tests/",
        "example_output_path": "context/",
    },
    "typescript": {
        "generate_output_path": "src/",
        "test_output_path": "__tests__/",
        "example_output_path": "examples/",
    },
    "go": {
        "generate_output_path": ".",
        "test_output_path": ".",
        "example_output_path": "examples/",
    },
    "rust": {
        "generate_output_path": "src/",
        "test_output_path": "tests/",
        "example_output_path": "examples/",
    },
}

# Standard defaults
STANDARD_DEFAULTS: dict[str, float | int] = {
    "strength": 0.818,
    "temperature": 0.0,
    "target_coverage": 80.0,
    "budget": 10.0,
    "max_attempts": 3,
}

PDDRC_FILENAME = ".pddrc"


def _detect_language(cwd: Path) -> Optional[str]:
    """Detect project language based on marker files in the current directory.

    Returns the detected language string or ``None`` if the project type
    cannot be determined automatically.
    """
    # Check Python markers
    for marker in PYTHON_MARKERS:
        if (cwd / marker).exists():
            return "python"

    # Check TypeScript – look for typescript in package.json dependencies
    package_json_path = cwd / "package.json"
    if package_json_path.exists():
        try:
            import json

            with open(package_json_path, "r", encoding="utf-8") as fh:
                pkg = json.load(fh)
            all_deps: dict[str, str] = {}
            all_deps.update(pkg.get("dependencies", {}))
            all_deps.update(pkg.get("devDependencies", {}))
            if "typescript" in all_deps:
                return "typescript"
        except (json.JSONDecodeError, OSError):
            pass

    # Check Go markers
    for marker in GO_MARKERS:
        if (cwd / marker).exists():
            return "go"

    # Check Rust markers
    for marker in RUST_MARKERS:
        if (cwd / marker).exists():
            return "rust"

    return None


def _prompt_language() -> str:
    """Interactively ask the user to choose a project language."""
    console.print("\n[warning]Could not auto-detect project language.[/warning]")
    console.print("  [bold]1)[/bold] Python")
    console.print("  [bold]2)[/bold] TypeScript")
    console.print("  [bold]3)[/bold] Go")

    while True:
        choice = console.input("\nSelect language [1/2/3]: ").strip()
        if choice == "1":
            return "python"
        elif choice == "2":
            return "typescript"
        elif choice == "3":
            return "go"
        else:
            console.print("[error]Invalid choice. Please enter 1, 2, or 3.[/error]")


def _build_pddrc_content(language: str) -> str:
    """Build the YAML content for a ``.pddrc`` file.

    Parameters
    ----------
    language:
        One of ``"python"``, ``"typescript"``, or ``"go"``.

    Returns
    -------
    str
        The full YAML string ready to be written to disk.
    """
    paths = LANGUAGE_DEFAULTS.get(language, LANGUAGE_DEFAULTS["python"])

    lines: list[str] = [
        'version: "1.0"',
        "",
        "contexts:",
        "  default:",
        "    defaults:",
        f'      generate_output_path: "{paths["generate_output_path"]}"',
        f'      test_output_path: "{paths["test_output_path"]}"',
        f'      example_output_path: "{paths["example_output_path"]}"',
        f'      default_language: "{language}"',
    ]

    for key, value in STANDARD_DEFAULTS.items():
        # Format integers without trailing .0, floats with one decimal
        if isinstance(value, int):
            lines.append(f"      {key}: {value}")
        else:
            lines.append(f"      {key}: {value}")

    lines.append("")  # trailing newline
    return "\n".join(lines)


def offer_pddrc_init() -> bool:
    """Offer to create a ``.pddrc`` configuration file in the current directory.

    If a ``.pddrc`` already exists the user is informed and the function
    returns ``False``.  Otherwise a preview of sensible defaults is shown
    and the user is prompted to confirm creation.

    Returns
    -------
    bool
        ``True`` if the file was created, ``False`` otherwise.
    """
    cwd = Path.cwd()
    pddrc_path = cwd / PDDRC_FILENAME

    # ── Already exists ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    if pddrc_path.exists():
        console.print(
            f"[info]A {PDDRC_FILENAME} file already exists in {cwd}.[/info]"
        )
        return False

    # ── Detect / prompt language ━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    language = _detect_language(cwd)
    if language is None:
        language = _prompt_language()
    else:
        console.print(f"\n[success]Detected project language: {language}[/success]")

    # ── Build & preview ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    content = _build_pddrc_content(language)

    console.print(f"\n[info]Proposed {PDDRC_FILENAME} contents:[/info]\n")
    syntax = Syntax(content, "yaml", theme="monokai", line_numbers=False)
    console.print(syntax)

    # ── Prompt for confirmation (Enter = yes) ━━━━━━━━━━━━━━━━━━━━━
    answer = console.input(f"\nCreate {PDDRC_FILENAME}? [Y/n] ").strip().lower()
    if answer in ("", "y", "yes"):
        try:
            pddrc_path.write_text(content, encoding="utf-8")
            console.print(
                f"[success]Created {PDDRC_FILENAME} in {cwd}[/success]"
            )
            return True
        except OSError as exc:
            console.print(
                f"[error]Failed to write {PDDRC_FILENAME}: {exc}[/error]"
            )
            return False
    else:
        console.print("[info]Skipped .pddrc creation.[/info]")
        return False


# ---------------------------------------------------------------------------
# Auto-generation helpers for `pdd update --directory / --repo`
# ---------------------------------------------------------------------------


def _detect_language_from_extensions(code_files: List[str]) -> str:
    """Majority-vote language from file extensions.

    Uses ``get_language()`` to map each file's extension to a language name
    and returns the most common one (lowercase).  Falls back to ``"unknown"``
    if the list is empty or nothing can be detected.
    """
    from .get_language import get_language

    counts: Counter[str] = Counter()
    for fpath in code_files:
        ext = os.path.splitext(fpath)[1]
        lang = get_language(ext)
        if lang:
            counts[lang.lower()] += 1

    if not counts:
        return "unknown"
    return counts.most_common(1)[0][0]


def _sanitize_context_name(scan_rel: str, subdir: str) -> str:
    """Create a valid ``.pddrc`` context name from directory components.

    Joins *scan_rel* and *subdir* with ``-``, lowercases, and replaces any
    character that is not alphanumeric, hyphen, or underscore with ``-``.
    Consecutive hyphens are collapsed, and leading/trailing hyphens stripped.

    Examples::

        ("crates", "selune-compiler") → "crates-selune-compiler"
        ("src",    "utils")           → "src-utils"
        ("",       "backend")         → "backend"
    """
    parts = [p for p in (scan_rel, subdir) if p]
    raw = "-".join(parts).lower()
    sanitized = re.sub(r"[^a-z0-9_-]", "-", raw)
    sanitized = re.sub(r"-{2,}", "-", sanitized)
    return sanitized.strip("-") or "default-scan"


def infer_contexts_from_scan(
    scan_dir: str,
    repo_root: str,
    code_files: List[str],
) -> Dict[str, Dict]:
    """Group code files by top-level subdirectory and produce context dicts.

    Each group becomes a context entry suitable for a ``.pddrc`` file::

        {
            "crates-selune-compiler": {
                "paths": ["crates/selune-compiler/**"],
                "defaults": {
                    "prompts_dir": "prompts/crates/selune-compiler",
                    "generate_output_path": "crates/selune-compiler",
                    "default_language": "rust",
                    ...
                }
            }
        }

    If all files sit directly in *scan_dir* (no subdirectories), a single
    context is created for the entire directory.

    If *scan_dir* equals *repo_root* and there are no first-level subdirs
    with code files, returns an empty dict (defaults already work).
    """
    scan_abs = os.path.abspath(scan_dir)
    root_abs = os.path.abspath(repo_root)

    # Relative path from repo root to scan directory (e.g. "crates")
    if scan_abs == root_abs:
        scan_rel = ""
    else:
        scan_rel = os.path.relpath(scan_abs, root_abs)

    # Group files by first directory component under scan_dir
    groups: Dict[str, List[str]] = {}
    for fpath in code_files:
        fpath_abs = os.path.abspath(fpath)
        try:
            rel = os.path.relpath(fpath_abs, scan_abs)
        except ValueError:
            continue
        parts = rel.replace("\\", "/").split("/")
        if len(parts) > 1:
            # File is inside a subdirectory
            top_dir = parts[0]
        else:
            # File is directly in scan_dir
            top_dir = ""
        groups.setdefault(top_dir, []).append(fpath)

    # If scan_dir == repo_root and all files are in the root (flat), skip
    if scan_rel == "" and list(groups.keys()) == [""]:
        return {}

    contexts: Dict[str, Dict] = {}

    if list(groups.keys()) == [""]:
        # All files directly in scan_dir, create one context
        name = _sanitize_context_name("", scan_rel)
        lang = _detect_language_from_extensions(groups[""])
        rel_path = scan_rel.replace("\\", "/")
        contexts[name] = {
            "paths": [f"{rel_path}/**"],
            "defaults": _build_context_defaults(rel_path, lang),
        }
    else:
        for top_dir, files in sorted(groups.items()):
            if not top_dir:
                # Files directly in scan_dir without a subdirectory — skip
                # since they'll be covered by a more specific context or the
                # default context.
                continue
            name = _sanitize_context_name(scan_rel, top_dir)
            lang = _detect_language_from_extensions(files)
            if scan_rel:
                rel_path = f"{scan_rel}/{top_dir}".replace("\\", "/")
            else:
                rel_path = top_dir.replace("\\", "/")
            contexts[name] = {
                "paths": [f"{rel_path}/**"],
                "defaults": _build_context_defaults(rel_path, lang),
            }

    return contexts


def _build_context_defaults(rel_path: str, language: str) -> Dict:
    """Build the ``defaults`` dict for an auto-generated context."""
    # Ensure no trailing slash on generate_output_path — critical for
    # path-mirroring in resolve_prompt_code_pair (see plan for proof).
    gen_path = rel_path.rstrip("/")
    prompts_dir = f"prompts/{gen_path}" if gen_path else "prompts"

    defaults: Dict = {
        "prompts_dir": prompts_dir,
        "generate_output_path": gen_path,
        "default_language": language,
    }
    for key, value in STANDARD_DEFAULTS.items():
        defaults[key] = value
    return defaults


def _paths_already_covered(
    new_patterns: List[str],
    existing_patterns: List[str],
) -> bool:
    """Check if a new context's paths are already covered by existing patterns.

    A new pattern like ``"pdd/commands/**"`` is covered if any existing pattern
    would match the same directory tree — e.g. ``"pdd/**"`` or
    ``"pdd/commands/**"``.  Uses ``fnmatch`` for glob matching.
    """
    import fnmatch

    for new_pat in new_patterns:
        # Strip trailing "/**" to get the directory prefix to test
        test_dir = new_pat.removesuffix("/**")
        for existing in existing_patterns:
            # Direct pattern match: existing covers the new dir
            if fnmatch.fnmatch(test_dir, existing.removesuffix("/**")):
                return True
            # Existing glob covers files under new dir
            # e.g. existing="pdd/**" matches "pdd/commands/foo.py"
            if fnmatch.fnmatch(test_dir + "/test.py", existing):
                return True
    return False


def ensure_pddrc_for_scan(
    scan_dir: str,
    repo_root: str,
    code_files: List[str],
    quiet: bool = False,
) -> Optional[Path]:
    """Auto-generate or update ``.pddrc`` with contexts for the scanned directory.

    1. Reads the existing ``.pddrc`` (if any) via ``_find_pddrc_file()``.
    2. Infers needed contexts via ``infer_contexts_from_scan()``.
    3. Filters out contexts whose names already exist.
    4. Appends new context blocks (never overwrites existing ones).
    5. Prints what was created unless *quiet*.

    Returns the path to the ``.pddrc`` file, or ``None`` if no changes were made.
    """
    from .construct_paths import _find_pddrc_file

    needed = infer_contexts_from_scan(scan_dir, repo_root, code_files)
    if not needed:
        return None

    pddrc_path = _find_pddrc_file(Path(repo_root))
    existing_content = ""
    existing_context_names: set[str] = set()
    existing_path_patterns: List[str] = []

    if pddrc_path and pddrc_path.is_file():
        existing_content = pddrc_path.read_text(encoding="utf-8")
        try:
            import yaml

            existing_config = yaml.safe_load(existing_content)
            if isinstance(existing_config, dict):
                contexts_cfg = existing_config.get("contexts", {})
                existing_context_names = set(contexts_cfg.keys())
                # Collect all existing path patterns for overlap detection
                for _cname, cval in contexts_cfg.items():
                    if isinstance(cval, dict):
                        for p in cval.get("paths", []):
                            existing_path_patterns.append(p)
        except Exception:
            pass

    # Filter out contexts that are already covered — by name OR by path overlap.
    # A new context for "crates/foo/**" is covered if any existing pattern
    # already matches that directory (e.g. "crates/**", "pdd/**", "pdd/commands/**").
    new_contexts: Dict[str, Dict] = {}
    for name, ctx in needed.items():
        if name in existing_context_names:
            continue
        if _paths_already_covered(ctx.get("paths", []), existing_path_patterns):
            continue
        new_contexts[name] = ctx

    if not new_contexts:
        return None

    # Build output (best-effort — don't crash if repo_root is read-only)
    target = Path(repo_root) / PDDRC_FILENAME
    try:
        if existing_content:
            # Append new contexts to existing file
            lines = [existing_content.rstrip("\n")]
            lines.append("")  # blank separator
            for name, ctx in new_contexts.items():
                lines.extend(_format_context_block(name, ctx))
            lines.append("")
            target.write_text("\n".join(lines), encoding="utf-8")
        else:
            # Build from scratch
            lines = ['version: "1.0"', "", "contexts:"]
            for name, ctx in new_contexts.items():
                lines.extend(_format_context_block(name, ctx))
            lines.append("")
            target.write_text("\n".join(lines), encoding="utf-8")
    except OSError:
        return None

    if not quiet:
        names = ", ".join(sorted(new_contexts.keys()))
        console.print(
            f"[success]Auto-generated .pddrc with contexts: {names}[/success]"
        )

    return target


def _format_context_block(name: str, ctx: Dict) -> List[str]:
    """Format a single context block as YAML lines.

    Returns a list of indented strings (no trailing newline).
    """
    lines: List[str] = []
    lines.append(f"  {name}:")

    # paths
    paths = ctx.get("paths", [])
    if paths:
        lines.append("    paths:")
        for p in paths:
            lines.append(f'      - "{p}"')

    # defaults
    defaults = ctx.get("defaults", {})
    if defaults:
        lines.append("    defaults:")
        for key, value in defaults.items():
            if isinstance(value, str):
                lines.append(f'      {key}: "{value}"')
            elif isinstance(value, int):
                lines.append(f"      {key}: {value}")
            else:
                lines.append(f"      {key}: {value}")

    return lines