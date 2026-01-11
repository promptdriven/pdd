"""
Utilities for validating and cleaning <include> tags in generated prompt content.

This module is intended to clean up references to non-existent files in
generated prompts (e.g., dependencies sections), particularly when using
generic/generate_prompt templates that may hallucinate <include> tags.

Primary functions:
    - validate_include_tag(file_path, base_dir)
    - validate_prompt_includes(content, base_dir=".", remove_invalid=False)
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Dict, List, Tuple


_INCLUDE_TAG_RE = re.compile(
    r"<include>(.*?)</include>",
    re.DOTALL | re.IGNORECASE,
)

# Simple XML-ish tag matcher: <tag>, </tag>, <tag ...>, <tag/>
_XML_TAG_RE = re.compile(
    r"<(?P<closing>/)?(?P<name>[A-Za-z_][\w\-.]*)[^>]*?>",
    re.DOTALL,
)


def validate_include_tag(file_path: str, base_dir: str) -> bool:
    """
    Validate that a file referenced by an <include> tag exists.

    Parameters
    ----------
    file_path:
        The file path string extracted from within an <include>...</include> tag.
    base_dir:
        The base directory against which to resolve relative paths.

    Returns
    -------
    exists:
        True if the file exists on disk, False otherwise.

    Notes
    -----
    - Absolute paths are checked as-is.
    - Relative paths are resolved against `base_dir`.
    """
    raw_path = file_path.strip()

    # Handle optional "Error processing include:" noise if present
    # e.g., "[Error processing include: context/foo.py]"
    # We only strip a common prefix; any remaining text is treated as part of the path.
    error_prefix = "Error processing include:"
    if raw_path.startswith(error_prefix):
        raw_path = raw_path[len(error_prefix) :].strip()

    p = Path(raw_path)
    if not p.is_absolute():
        p = Path(base_dir) / p

    return p.exists()


def _build_element_spans(content: str) -> List[Tuple[str, int, int]]:
    """
    Build a list of (tag_name, start_index, end_index) for XML-like elements
    in `content` using a simple stack-based matcher.

    This is used so we can remove the entire parent XML block that contains
    an <include> tag when an include is invalid.

    Parameters
    ----------
    content:
        The string to scan for XML-like tags.

    Returns
    -------
    elements:
        A list of tuples (tag_name, start, end) representing the span of each
        matched element, where `start` is the index of the opening '<' and
        `end` is the index just after the closing '>'.
    """
    stack: List[Tuple[str, int]] = []
    elements: List[Tuple[str, int, int]] = []

    for match in _XML_TAG_RE.finditer(content):
        name = match.group("name")
        is_closing = bool(match.group("closing"))
        start, end = match.span()

        # Self-closing tags like <tag ... /> are treated as standalone elements
        # Note: this is a heuristic; good enough for the dependency XML structure.
        if not is_closing and content[end - 2 : end] == "/>":
            elements.append((name, start, end))
            continue

        if not is_closing:
            # Opening tag
            stack.append((name, start))
        else:
            # Closing tag: find matching last open tag with same name
            for i in range(len(stack) - 1, -1, -1):
                open_name, open_start = stack[i]
                if open_name == name:
                    # Matched pair: record element
                    elements.append((name, open_start, end))
                    # Remove matched open and everything after it from stack
                    del stack[i:]
                    break

    return elements


def _find_parent_element_span(
    elements: List[Tuple[str, int, int]],
    child_start: int,
    child_end: int,
) -> Tuple[int, int] | None:
    """
    Given a list of element spans and a child span, find the smallest element
    that strictly contains the child.

    Parameters
    ----------
    elements:
        List of (tag_name, start, end) tuples.
    child_start:
        Start index of the child span.
    child_end:
        End index of the child span.

    Returns
    -------
    parent_span:
        (start, end) of the parent element, or None if no parent is found.
    """
    parent: Tuple[int, int] | None = None
    parent_size = None

    for name, start, end in elements:
        if start <= child_start and child_end <= end:
            # Exclude the element if it is exactly the child span (e.g., <include> itself)
            if start == child_start and end == child_end:
                continue
            size = end - start
            if parent is None or size < parent_size:  # type: ignore[operator]
                parent = (start, end)
                parent_size = size

    return parent


def validate_prompt_includes(
    content: str,
    base_dir: str | Path = ".",
    remove_invalid: bool = False,
) -> Tuple[str, List[str]]:
    """
    Validate and clean <include> tags in a generated prompt.

    Parameters
    ----------
    content:
        The generated prompt content that may contain <include>...</include> tags.
    base_dir:
        Base directory to resolve relative include paths against.
        Defaults to current working directory (".").
    remove_invalid:
        - If True, remove the entire XML block containing an invalid <include>,
          e.g., <dependency_name> ... </dependency_name>.
        - If False, replace the <include> tag with a comment:
          <!-- Missing: path/to/file.py -->

    Returns
    -------
    validated_content:
        The prompt content with invalid <include> tags handled according to
        `remove_invalid`.
    invalid_includes:
        A list of file path strings that were found to be invalid (non-existent).

    Behavior
    --------
    - Uses a regex to find all <include>...</include> patterns.
    - For each include, resolves the file path relative to `base_dir` and checks
      if it exists.
    - Tracks invalid paths and either:
        * removes the containing XML block (when `remove_invalid=True`), or
        * replaces the <include> tag itself with an XML comment describing
          the missing dependency (when `remove_invalid=False`).
    - Handles:
        * Nested tags (e.g., <dependency><include>...</include></dependency>)
        * Multiple includes on the same line
        * Paths with spaces or special characters (non-greedy matching)
    """
    base_dir_path = Path(base_dir)
    elements = _build_element_spans(content)

    invalid_includes: List[str] = []
    exists_cache: Dict[Path, bool] = {}
    edits: List[Tuple[int, int, str]] = []
    removed_blocks: set[Tuple[int, int]] = set()

    for m in _INCLUDE_TAG_RE.finditer(content):
        inc_start, inc_end = m.span()
        raw_path = m.group(1).strip()

        # Normalize possible "Error processing include:" prefix but preserve
        # the original raw_path for reporting.
        path_for_fs = raw_path
        error_prefix = "Error processing include:"
        if path_for_fs.startswith(error_prefix):
            path_for_fs = path_for_fs[len(error_prefix) :].strip()

        p = Path(path_for_fs)
        if not p.is_absolute():
            p = base_dir_path / p

        if p in exists_cache:
            exists = exists_cache[p]
        else:
            exists = p.exists()
            exists_cache[p] = exists

        if exists:
            continue

        # Track invalid include using the raw string from the tag
        invalid_includes.append(raw_path)

        if remove_invalid:
            # Remove the entire parent XML block that contains this <include>
            parent_span = _find_parent_element_span(elements, inc_start, inc_end)
            if parent_span is None:
                # No parent element found; just remove the <include> tag itself
                block_start, block_end = inc_start, inc_end
            else:
                block_start, block_end = parent_span

            if (block_start, block_end) in removed_blocks:
                # Already scheduled for removal
                continue

            removed_blocks.add((block_start, block_end))
            edits.append((block_start, block_end, ""))

        else:
            # Replace only the <include> tag with a comment about the missing file
            replacement = f"<!-- Missing: {raw_path} -->"
            edits.append((inc_start, inc_end, replacement))

    # Apply edits from end to start so indices remain valid
    if edits:
        edits.sort(key=lambda e: e[0], reverse=True)
        chars = list(content)
        for start, end, replacement in edits:
            chars[start:end] = list(replacement)
        content = "".join(chars)

    return content, invalid_includes
