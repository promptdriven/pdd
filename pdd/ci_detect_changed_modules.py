#!/usr/bin/env python3
"""CI/CD utility to detect PDD module basenames affected by changes in a Git diff.

Usage:
    python scripts/ci_detect_changed_modules.py --diff-base origin/main...HEAD

This script identifies which PDD (Prompt-Driven Development) modules need to be
re-processed or "healed" based on modifications to their prompts, logic, context,
or tests. It supports workflows on both GitHub Actions and Google Cloud Build.

The script:
  1. Runs `git diff --name-only` with the provided diff-base argument.
  2. Maps changed file paths to module basenames using PDD conventions.
  3. Performs reverse dependency resolution by scanning all .prompt files for
     <include> and <include-many> tags that reference changed files.
  4. Outputs a single line of comma-separated, alphabetically sorted module basenames.

Exit codes:
  0 - Success (even if no modules detected; prints empty line)
  1 - Git command failure
"""

import argparse
import glob
import os
import re
import subprocess
import sys


def _normalize_path(path: str) -> str:
    """Normalize a repository path for consistent matching.

    Strips leading './', replaces backslashes with forward slashes,
    collapses multiple slashes, and strips leading/trailing whitespace.
    """
    path = path.strip()
    path = path.replace("\\", "/")
    # Collapse multiple slashes
    path = re.sub(r"/+", "/", path)
    # Strip leading ./
    while path.startswith("./"):
        path = path[2:]
    # Strip trailing slash
    path = path.rstrip("/")
    return path


def _basename_from_path(filepath: str) -> str | None:
    """Extract a module basename from a changed file path.

    Handles four categories:
      - prompts/[subdir/...]/{basename}_{language}.prompt -> {subdir/...}/{basename}
      - context/[subdir/...]/{basename}_example.{ext} -> {subdir/...}/{basename}
      - pdd/{path/to/module}.py -> {path/to/module} (excluding root __init__.py)
      - tests/[subdir/...]/test_{basename}.py -> {subdir/...}/{basename}

    Returns None if the path doesn't match any known pattern.
    """
    filepath = _normalize_path(filepath)

    # --- Prompts ---
    # prompts/[subdir/...]/{basename}_{language}.prompt
    prompt_match = re.match(r"^prompts/(.+)$", filepath)
    if prompt_match:
        rest = prompt_match.group(1)
        # Must end with .prompt
        if rest.endswith(".prompt"):
            # Remove .prompt extension
            without_ext = rest[: -len(".prompt")]
            # The filename part is the last component
            parts = without_ext.rsplit("/", 1)
            if len(parts) == 2:
                subdir, filename = parts
            else:
                subdir = ""
                filename = parts[0]

            # Strip the _{language} suffix from filename
            # The basename is everything before the last underscore
            lang_match = re.match(r"^(.+)_([^_]+)$", filename)
            if lang_match:
                basename = lang_match.group(1)
            else:
                # No language suffix found; use the whole filename as basename
                basename = filename

            if subdir:
                return f"{subdir}/{basename}"
            return basename
        return None

    # --- Context ---
    # context/[subdir/...]/{basename}_example.{ext}
    context_match = re.match(r"^context/(.+)$", filepath)
    if context_match:
        rest = context_match.group(1)
        # Must match {basename}_example.{ext}
        example_match = re.match(r"^(.+/)?(.*?)_example\.[^/]+$", rest)
        if example_match:
            subdir = example_match.group(1)
            basename = example_match.group(2)
            if subdir:
                # Remove trailing slash from subdir
                subdir = subdir.rstrip("/")
                return f"{subdir}/{basename}"
            return basename
        return None

    # --- Logic (pdd/) ---
    # pdd/{path/to/module}.py -> {path/to/module}, excluding root __init__.py
    pdd_match = re.match(r"^pdd/(.+)\.py$", filepath)
    if pdd_match:
        module_path = pdd_match.group(1)
        # Exclude root-level __init__.py (pdd/__init__.py)
        if module_path == "__init__":
            return None
        # But allow nested __init__.py files like pdd/sub/__init__.py -> sub/__init__
        return module_path

    # --- Tests ---
    # tests/[subdir/...]/test_{basename}.py -> {subdir/...}/{basename}
    tests_match = re.match(r"^tests/(.+)$", filepath)
    if tests_match:
        rest = tests_match.group(1)
        # Must match [subdir/...]test_{basename}.py
        test_match = re.match(r"^(.+/)?test_(.+)\.py$", rest)
        if test_match:
            subdir = test_match.group(1)
            basename = test_match.group(2)
            if subdir:
                subdir = subdir.rstrip("/")
                return f"{subdir}/{basename}"
            return basename
        return None

    return None


def _extract_include_paths(content: str) -> list[str]:
    """Extract file paths from <include> and <include-many> tags in prompt content.

    Parses both:
      <include>path/to/file</include>
      <include-many>path1, path2, glob/pattern</include-many>

    Returns a list of normalized path strings (glob patterns are included as-is).
    """
    paths = []

    # Match <include>...</include> tags (single path)
    for match in re.finditer(r"<include>(.*?)</include>", content, re.DOTALL):
        inner = match.group(1).strip()
        if inner:
            paths.append(_normalize_path(inner))

    # Match <include-many>...</include-many> tags (comma-separated paths/globs)
    for match in re.finditer(r"<include-many>(.*?)</include-many>", content, re.DOTALL):
        inner = match.group(1)
        # Split by comma and/or newline
        for item in re.split(r"[,\n]", inner):
            item = item.strip()
            if item:
                paths.append(_normalize_path(item))

    return paths


def _path_matches_include(changed_path: str, include_path: str) -> bool:
    """Check if a changed file path matches an include path reference.

    Uses three matching strategies:
      1. Full path match (exact)
      2. Path suffix match (include_path is a suffix of changed_path)
      3. Filename match (just the filename portions match)

    Also handles glob patterns in include_path by expanding them.
    """
    changed_norm = _normalize_path(changed_path)
    include_norm = _normalize_path(include_path)

    # Strategy 1: Full path match
    if changed_norm == include_norm:
        return True

    # Strategy 2: Path suffix match
    if changed_norm.endswith("/" + include_norm) or changed_norm == include_norm:
        return True

    # Strategy 3: Filename match
    changed_filename = changed_norm.rsplit("/", 1)[-1]
    include_filename = include_norm.rsplit("/", 1)[-1]

    # Don't match on glob pattern filenames (e.g., *.py)
    if "*" not in include_filename and "?" not in include_filename:
        if changed_filename == include_filename:
            return True

    # Handle glob patterns: check if the changed path matches the glob
    if any(c in include_norm for c in ("*", "?", "[")):
        # Use fnmatch-style matching
        import fnmatch

        if fnmatch.fnmatch(changed_norm, include_norm):
            return True

    return False


def _find_all_prompt_files() -> list[str]:
    """Find all .prompt files in the prompts/ directory recursively."""
    prompt_files = []
    prompts_dir = "prompts"
    if os.path.isdir(prompts_dir):
        for root, _dirs, files in os.walk(prompts_dir):
            for f in files:
                if f.endswith(".prompt"):
                    path = os.path.join(root, f)
                    prompt_files.append(_normalize_path(path))
    return prompt_files


def _resolve_reverse_dependencies(changed_files: list[str]) -> set[str]:
    """Scan all prompt files for include tags referencing changed files.

    For every prompt file in the repo, check if its <include> or <include-many>
    paths match any of the changed files. If so, extract the basename of that
    prompt file and add it to the result set.

    Returns a set of module basenames that are indirectly affected.
    """
    affected_basenames = set()
    prompt_files = _find_all_prompt_files()

    for prompt_path in prompt_files:
        try:
            with open(prompt_path, "r", encoding="utf-8", errors="replace") as f:
                content = f.read()
        except (OSError, IOError):
            continue

        include_paths = _extract_include_paths(content)
        if not include_paths:
            continue

        # Check if any changed file matches any include path in this prompt
        matched = False
        for changed_file in changed_files:
            for inc_path in include_paths:
                if _path_matches_include(changed_file, inc_path):
                    matched = True
                    break
            if matched:
                break

        if matched:
            basename = _basename_from_path(prompt_path)
            if basename is not None:
                affected_basenames.add(basename)

    return affected_basenames


def _get_changed_files(diff_base: str) -> list[str]:
    """Run git diff --name-only and return the list of changed file paths.

    Raises subprocess.CalledProcessError if the git command fails.
    """
    result = subprocess.run(
        ["git", "diff", "--name-only", diff_base],
        capture_output=True,
        text=True,
        check=True,
    )
    lines = result.stdout.strip().split("\n") if result.stdout.strip() else []
    return [_normalize_path(line) for line in lines if line.strip()]


def main() -> int:
    """Main entry point for the CI module detection script.

    Returns:
        0 on success, 1 if the git command fails.
    """
    parser = argparse.ArgumentParser(
        description="Detect PDD module basenames affected by changes in a Git diff."
    )
    parser.add_argument(
        "--diff-base",
        required=True,
        help="Git diff base reference, e.g. 'origin/main...HEAD' or a commit SHA.",
    )
    args = parser.parse_args()

    # Step 1: Get changed files from git
    try:
        changed_files = _get_changed_files(args.diff_base)
    except subprocess.CalledProcessError as e:
        print(f"Error: git diff command failed: {e}", file=sys.stderr)
        return 1
    except FileNotFoundError:
        print("Error: git executable not found", file=sys.stderr)
        return 1

    if not changed_files:
        print("")
        return 0

    # Step 2: Extract basenames from directly changed files
    basenames = set()
    for filepath in changed_files:
        basename = _basename_from_path(filepath)
        if basename is not None:
            basenames.add(basename)

    # Step 3: Resolve reverse dependencies (include tags in prompt files)
    reverse_deps = _resolve_reverse_dependencies(changed_files)
    basenames.update(reverse_deps)

    # Step 4: Sort and output
    sorted_basenames = sorted(basenames)
    print(",".join(sorted_basenames))

    return 0


if __name__ == "__main__":
    sys.exit(main())