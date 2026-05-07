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
_INCLUDE_BLOCK_TAG = re.compile(
    r"<include(?:-many)?[^>]*>(.*?)</include(?:-many)?>",
    re.DOTALL,
)
_PROMPT_DIRS = ("prompts/", "pdd/prompts/")


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
    includes: list[str] = []
    for block in _INCLUDE_BLOCK_TAG.findall(content):
        for part in block.split(","):
            normalized = _normalize_repo_path(part)
            if normalized:
                includes.append(normalized)
    return includes


def _reverse_dep_basenames(changed_files: list[str]) -> set[str]:
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
            for include_path in _extract_include_paths(content):
                include_basename = os.path.basename(include_path)
                if any(
                    changed_path.endswith(include_path)
                    or include_path.endswith(changed_basename)
                    or include_basename == changed_basename
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
    basenames |= _reverse_dep_basenames(changed_files)
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
