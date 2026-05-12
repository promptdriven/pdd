#!/usr/bin/env python3
"""Detect PDD module basenames affected by a git diff.

Ported from the inline bash+python block in .github/workflows/auto-heal-drift.yml
so it can run identically on GitHub Actions and Google Cloud Build.

Usage:
    python scripts/ci_detect_changed_modules.py --diff-base 'origin/main...HEAD'
    python scripts/ci_detect_changed_modules.py --diff-base 'HEAD~1'

Prints a single line with comma-separated module basenames, or an empty line
if no PDD-managed files changed. Exit code is always 0 unless git itself fails.
"""
from __future__ import annotations

import argparse
import ast
import os
import re
import subprocess
import sys
from pathlib import Path

PDD_PATH_PREFIXES = ("pdd/", "prompts/", "context/", "tests/")
# Package execution shims and CI helper scripts are not PDD dev units;
# auto-heal must not try to generate examples for them in headless CI.
EXCLUDED_MODULE_BASENAMES = {
    "__main__",
    "ci_detect_changed_modules",
    # Public release sync is an operational packaging helper, not a
    # prompt-managed PDD module.
    "copy_package_data_to_public",
    # The model catalog score refresh is intentionally agent-reviewed and
    # manifest-driven. Headless auto-heal should not regenerate this module:
    # it can enter interactive agent auth while trying to rewrite the full
    # generator, and the reviewed manifest/schema/tests are the audit surface.
    "generate_model_catalog",
}

# Prompt file names follow prompts/[subdir/...]/{basename}_{language}.prompt.
_PROMPT_FILENAME = re.compile(r"^(.*)_([^_]+)\.prompt$")
_INCLUDE_OPEN_TAG = re.compile(
    r"<(?P<tag>include(?:-many)?)(?P<attrs>[^>]*)>",
    re.DOTALL,
)
_SELECT_ATTR = re.compile(r"""\bselect\s*=\s*(['"])(.*?)\1""", re.DOTALL)
_PROMPT_DIRS = ("prompts/", "pdd/prompts/")
_INCLUDE_PATH_SUFFIXES = (
    ".bash",
    ".csv",
    ".html",
    ".java",
    ".js",
    ".json",
    ".md",
    ".prompt",
    ".py",
    ".rb",
    ".rs",
    ".rst",
    ".sh",
    ".toml",
    ".ts",
    ".tsx",
    ".txt",
    ".yaml",
    ".yml",
)


def _git_changed_files(diff_base: str) -> list[str]:
    """Return changed files restricted to PDD-managed prefixes."""
    cmd = ["git", "diff", "--name-only", diff_base, "--", *PDD_PATH_PREFIXES]
    result = subprocess.run(cmd, capture_output=True, text=True, check=True)
    return [line.strip() for line in result.stdout.splitlines() if line.strip()]


def _normalize_repo_path(path: str) -> str:
    """Normalize repo-relative paths for matching include references."""
    normalized = os.path.normpath(path.strip()).replace("\\", "/")
    if normalized == ".":
        return ""
    while normalized.startswith("./"):
        normalized = normalized[2:]
    return normalized


def _prompt_basename_from_path(path: str) -> str | None:
    """Return module basename from prompts/[subdir]/name_lang.prompt paths."""
    normalized = _normalize_repo_path(path)
    for prompt_dir in _PROMPT_DIRS:
        prefix = _normalize_repo_path(prompt_dir) + "/"
        if not normalized.startswith(prefix):
            continue
        relative = normalized[len(prefix):]
        match = _PROMPT_FILENAME.match(relative)
        if not match:
            return None
        return match.group(1)
    return None


def _context_basename_from_path(path: str) -> str | None:
    """Return module basename from context/[subdir]/name_example.ext paths."""
    normalized = _normalize_repo_path(path)
    for prefix in ("context/", "pdd/context/"):
        if not normalized.startswith(prefix):
            continue
        relative = normalized[len(prefix):]
        rel_path = Path(relative)
        stem = rel_path.stem
        if not stem.endswith("_example"):
            return None
        basename = stem[: -len("_example")]
        parent = rel_path.parent.as_posix()
        return f"{parent}/{basename}" if parent != "." else basename
    return None


def _test_basename_from_path(path: str) -> str | None:
    """Return module basename from tests/[subdir]/test_name.py paths."""
    normalized = _normalize_repo_path(path)
    prefix = "tests/"
    if not normalized.startswith(prefix) or not normalized.endswith(".py"):
        return None
    relative = normalized[len(prefix):]
    rel_path = Path(relative)
    if not rel_path.name.startswith("test_"):
        return None
    basename = rel_path.stem[len("test_") :]
    parent = rel_path.parent.as_posix()
    return f"{parent}/{basename}" if parent != "." else basename


def _basename_from_path(path: str) -> str | None:
    prompt_basename = _prompt_basename_from_path(path)
    if prompt_basename:
        return None if prompt_basename in EXCLUDED_MODULE_BASENAMES else prompt_basename

    normalized = _normalize_repo_path(path)
    if normalized.startswith("pdd/") and normalized.endswith(".py"):
        basename = normalized[len("pdd/") : -len(".py")]
        # Skip root package shims only; nested __init__.py files map to real
        # prompt basenames like commands/__init__ and server/routes/__init__.
        if basename == "__init__" or basename in EXCLUDED_MODULE_BASENAMES:
            return None
        return basename

    context_basename = _context_basename_from_path(path)
    if context_basename:
        return None if context_basename in EXCLUDED_MODULE_BASENAMES else context_basename

    test_basename = _test_basename_from_path(path)
    if test_basename:
        return None if test_basename in EXCLUDED_MODULE_BASENAMES else test_basename

    return None


def _extract_include_paths(content: str) -> list[str]:
    """Return normalized include targets from <include> and <include-many> tags."""
    return [path for path, _selected_defs in _extract_include_refs(content)]


def _extract_include_refs(content: str) -> list[tuple[str, set[str] | None]]:
    """Return include targets with optional function selectors.

    A ``None`` selector means "conservative match": either the include has no
    select attribute, or it uses a selector type this detector cannot map to
    Python function definitions.
    """
    refs: list[tuple[str, set[str] | None]] = []
    pos = 0
    while True:
        start = content.find("<include", pos)
        if start == -1:
            break
        match = _INCLUDE_OPEN_TAG.match(content, start)
        if not match:
            pos = start + 1
            continue

        close_tag = f"</{match.group('tag')}>"
        close_start = content.find(close_tag, match.end())
        if close_start == -1:
            pos = match.end()
            continue

        attrs = match.group("attrs") or ""
        body = content[match.end() : close_start]
        # Prompt prose sometimes mentions literal <include> tags before a real
        # include block. If a candidate body contains another include opener,
        # this was prose, so advance one byte and let the real tag match next.
        if "<include" in body:
            pos = start + 1
            continue

        selected_defs = _selected_defs_from_attrs(attrs)
        for part in re.split(r"[,\n]", body):
            normalized = _normalize_repo_path(part)
            if _looks_like_include_target(normalized):
                refs.append((normalized, selected_defs))
        pos = close_start + len(close_tag)
    return refs


def _looks_like_include_target(path: str) -> bool:
    """Return True for normalized include bodies that look like file paths."""
    if not path or "<" in path or ">" in path:
        return False
    if any(char.isspace() for char in path):
        return False
    return path.endswith(_INCLUDE_PATH_SUFFIXES)


def _selected_defs_from_attrs(attrs: str) -> set[str] | None:
    """Extract ``def:name`` selectors from include tag attributes."""
    match = _SELECT_ATTR.search(attrs)
    if not match:
        return None

    selected_defs: set[str] = set()
    for raw_selector in match.group(2).split(","):
        selector = raw_selector.strip()
        if not selector:
            continue
        if not selector.startswith("def:"):
            return None
        name = selector[len("def:") :].strip()
        if name:
            selected_defs.add(name)

    return selected_defs or None


def _diff_base_ref(diff_base: str) -> str:
    """Return the left-hand git ref from a diff expression."""
    if "..." in diff_base:
        return diff_base.split("...", 1)[0]
    if ".." in diff_base:
        return diff_base.split("..", 1)[0]
    return diff_base


def _function_dumps(source: str) -> dict[str, str]:
    """Return AST dumps for Python function definitions in source."""
    tree = ast.parse(source)
    functions: dict[str, str] = {}
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            functions[node.name] = ast.dump(node, include_attributes=False)
    return functions


def _changed_python_defs(path: str, diff_base: str | None) -> set[str] | None:
    """Return changed Python function names for path, or None if unknown."""
    if diff_base is None or not path.endswith(".py"):
        return None

    try:
        current_source = Path(path).read_text(encoding="utf-8")
        current_funcs = _function_dumps(current_source)
    except (OSError, SyntaxError):
        return None

    base_ref = _diff_base_ref(diff_base)
    try:
        result = subprocess.run(
            ["git", "show", f"{base_ref}:{path}"],
            capture_output=True,
            text=True,
            timeout=30,
        )
    except Exception:
        return None

    if result.returncode != 0:
        old_funcs: dict[str, str] = {}
    else:
        try:
            old_funcs = _function_dumps(result.stdout)
        except SyntaxError:
            return None

    changed_defs = {
        name
        for name, dumped in current_funcs.items()
        if old_funcs.get(name) != dumped
    }
    changed_defs.update(name for name in old_funcs if name not in current_funcs)
    return changed_defs


def _include_matches_changed(
    include_path: str,
    selected_defs: set[str] | None,
    changed_path: str,
    changed_basename: str,
    changed_defs_by_path: dict[str, set[str] | None],
) -> bool:
    """Return True if a prompt include should react to a changed file."""
    include_basename = os.path.basename(include_path)
    path_matches = (
        changed_path.endswith(include_path)
        or include_path.endswith(changed_basename)
        or include_basename == changed_basename
    )
    if not path_matches:
        return False

    if selected_defs is None:
        return True

    changed_defs = changed_defs_by_path.get(changed_path)
    if changed_defs is None:
        return True

    return bool(selected_defs & changed_defs)


def _reverse_dep_basenames(
    changed_files: list[str], diff_base: str | None = None
) -> set[str]:
    """Find prompts whose include tags reference any changed file.

    Catches the case where module B's example changes and module A includes it:
    A's basename must also be emitted so the healer re-generates A.
    """
    found: set[str] = set()
    if not changed_files:
        return found
    changed_lookup = {}
    for path in changed_files:
        normalized = _normalize_repo_path(path)
        if normalized:
            changed_lookup[normalized] = os.path.basename(normalized)
    changed_defs_by_path = {
        path: _changed_python_defs(path, diff_base) for path in changed_lookup
    }
    for pdir in _PROMPT_DIRS:
        prompt_root = Path(pdir)
        if not prompt_root.exists():
            continue
        for prompt_file in prompt_root.rglob("*.prompt"):
            try:
                content = prompt_file.read_text(encoding="utf-8")
            except OSError:
                continue
            prompt_basename = _prompt_basename_from_path(prompt_file.as_posix())
            if not prompt_basename:
                continue
            for include_path, selected_defs in _extract_include_refs(content):
                if any(
                    _include_matches_changed(
                        include_path,
                        selected_defs,
                        changed_path,
                        changed_basename,
                        changed_defs_by_path,
                    )
                    for changed_path, changed_basename in changed_lookup.items()
                ):
                    found.add(prompt_basename)
                    break
    return found


def detect(diff_base: str) -> list[str]:
    changed_files = _git_changed_files(diff_base)
    basenames: set[str] = set()
    for f in changed_files:
        name = _basename_from_path(f)
        if name:
            basenames.add(name)
    basenames |= _reverse_dep_basenames(changed_files, diff_base=diff_base)
    return sorted(basenames)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--diff-base",
        required=True,
        help="git diff reference (e.g. 'origin/main...HEAD' or 'HEAD~1')",
    )
    args = parser.parse_args()
    try:
        basenames = detect(args.diff_base)
    except subprocess.CalledProcessError as exc:
        print(f"git diff failed: {exc}", file=sys.stderr)
        return 2
    print(",".join(basenames))
    return 0


if __name__ == "__main__":
    sys.exit(main())
