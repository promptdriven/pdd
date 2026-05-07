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
from typing import Dict, List, Match, Tuple


_INCLUDE_TAG_RE = re.compile(
    r"<include(?P<attrs>\s+[^>]*?)?>(?P<content>.*?)</include>|"
    r"<include(?P<attrs_self>\s+[^>]*?)\s*/>",
    re.DOTALL | re.IGNORECASE,
)

# Simple XML-ish tag matcher: <tag>, </tag>, <tag ...>, <tag/>
_XML_TAG_RE = re.compile(
    r"<(?P<closing>/)?(?P<name>[A-Za-z_][\w\-.]*)[^>]*?>",
    re.DOTALL,
)

_OPTIONAL_SHARED_CONTEXT_BLOCKS = {
    "prompts/_context/data_dictionary.yaml": "context_data_dictionary",
    "prompts/_context/api_contracts.yaml": "context_api_contracts",
    "prompts/_context/integration_points.yaml": "context_integration_points",
}


def _resolve_include_against_base_dir(rel_or_abs: str, base_dir: Path) -> Path:
    """
    Resolve a path from an ``<include>`` tag for existence checks.

    Absolute paths are normalized with :meth:`Path.resolve`. Relative paths are
    resolved by walking upward from ``base_dir`` (inclusive), joining the
    relative path at each ancestor, and returning the first candidate that exists.
    If none exist, returns ``(base_dir / rel).resolve()`` as the canonical
    missing path (Issue #225: must not depend on process ``cwd`` alone).
    """
    raw = (rel_or_abs or "").strip()
    p = Path(raw)
    if p.is_absolute():
        return p.resolve()
    rel = p
    base = base_dir.resolve()
    cur: Path = base
    for _ in range(128):
        candidate = (cur / rel).resolve()
        if candidate.exists():
            return candidate
        parent = cur.parent
        if parent == cur:
            break
        cur = parent
    return (base / rel).resolve()


def _parse_attrs(attr_str: str) -> Dict[str, str]:
    """Parse XML-ish include attributes used by preprocess.py."""
    attrs: Dict[str, str] = {}
    if not attr_str:
        return attrs
    for match in re.finditer(r'(\w+)\s*=\s*["\']([^"\']*)["\']', attr_str):
        attrs[match.group(1)] = match.group(2)
    if "optional" not in attrs and re.search(
        r"(?<![A-Za-z0-9_])optional(?![A-Za-z0-9_])",
        attr_str,
    ):
        attrs["optional"] = "true"
    return attrs


def _optional_attr_is_truthy(attrs: Dict[str, str]) -> bool:
    optional_val = attrs.get("optional")
    if optional_val is None:
        return False
    return str(optional_val).strip().lower() not in {"", "0", "false", "no", "off"}


def _include_match_path_and_attrs(match: Match[str]) -> Tuple[str, Dict[str, str]]:
    attrs_str = match.group("attrs") or match.group("attrs_self") or ""
    attrs = _parse_attrs(attrs_str)
    content = match.group("content") if match.group("content") is not None else ""
    raw_path = (attrs.get("path") or content.strip()).strip()
    return raw_path, attrs


def _selector_error_for_include(path: Path, attrs: Dict[str, str]) -> str | None:
    selectors_str = attrs.get("select")
    lines_str = attrs.get("lines")
    mode = attrs.get("mode", "full")
    if not selectors_str and not lines_str and mode == "full":
        return None

    selectors: List[str] = []
    if selectors_str:
        selectors.extend(selector.strip() for selector in selectors_str.split(","))
    if lines_str:
        selectors.append(f"lines:{lines_str}")
    selectors = [selector for selector in selectors if selector]

    try:
        from pdd.content_selector import ContentSelector

        ContentSelector().select(
            content=path.read_text(encoding="utf-8"),
            selectors=selectors,
            file_path=str(path),
            mode=mode,
        )
    except Exception as exc:  # noqa: BLE001 - validation reports any selector failure
        return str(exc)
    return None


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
    - Relative paths are resolved against ``base_dir`` (walking up to ancestors)
      until a matching file is found; see :func:`_resolve_include_against_base_dir`.
    """
    raw_path = file_path.strip()

    # Handle optional "Error processing include:" noise if present
    # e.g., "[Error processing include: context/foo.py]"
    # We only strip a common prefix; any remaining text is treated as part of the path.
    error_prefix = "Error processing include:"
    if raw_path.startswith(error_prefix):
        raw_path = raw_path[len(error_prefix) :].strip()

    p = _resolve_include_against_base_dir(raw_path, Path(base_dir))
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

    for _name, start, end in elements:
        if start <= child_start and child_end <= end:
            # Exclude the element if it is exactly the child span (e.g., <include> itself)
            if start == child_start and end == child_end:
                continue
            size = end - start
            if parent is None or size < parent_size:  # type: ignore[operator]
                parent = (start, end)
                parent_size = size

    return parent


def _find_parent_element(
    elements: List[Tuple[str, int, int]],
    child_start: int,
    child_end: int,
) -> Tuple[str, int, int] | None:
    """Return the smallest XML-like parent element that contains a child span."""
    parent: Tuple[str, int, int] | None = None
    parent_size = None

    for name, start, end in elements:
        if start <= child_start and child_end <= end:
            if start == child_start and end == child_end:
                continue
            size = end - start
            if parent is None or size < parent_size:  # type: ignore[operator]
                parent = (name, start, end)
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
    - For each include, resolves the file path against ``base_dir`` (not process ``cwd``
      alone) and checks if it exists.
    - Tracks invalid paths and either:
        * removes the containing XML block (when `remove_invalid=True`), or
        * replaces the <include> tag itself with an XML comment describing
          the missing dependency (when `remove_invalid=False`).
    - Handles:
        * Nested tags (e.g., <dependency><include>...</include></dependency>)
        * Multiple includes on the same line
        * Paths with spaces or special characters (non-greedy matching)
    """
    elements = _build_element_spans(content)
    base_path = Path(base_dir).resolve()

    invalid_includes: List[str] = []
    exists_cache: Dict[Path, bool] = {}
    edits: List[Tuple[int, int, str]] = []
    removed_blocks: set[Tuple[int, int]] = set()

    for m in _INCLUDE_TAG_RE.finditer(content):
        inc_start, inc_end = m.span()
        raw_path, attrs = _include_match_path_and_attrs(m)
        if not raw_path:
            continue

        # Normalize possible "Error processing include:" prefix but preserve
        # the original raw_path for reporting.
        path_for_fs = raw_path
        error_prefix = "Error processing include:"
        if path_for_fs.startswith(error_prefix):
            path_for_fs = path_for_fs[len(error_prefix) :].strip()

        p = _resolve_include_against_base_dir(path_for_fs, base_path)

        if p in exists_cache:
            exists = exists_cache[p]
        else:
            exists = p.exists()
            exists_cache[p] = exists

        if exists:
            selector_error = _selector_error_for_include(p, attrs)
            if selector_error is None:
                continue

            invalid_label = (
                f"{raw_path} select=\"{attrs.get('select', '')}\": {selector_error}"
            )
            invalid_includes.append(invalid_label)

            if remove_invalid:
                parent_span = _find_parent_element_span(elements, inc_start, inc_end)
                if parent_span is None:
                    block_start, block_end = inc_start, inc_end
                else:
                    block_start, block_end = parent_span
                if (block_start, block_end) in removed_blocks:
                    continue
                removed_blocks.add((block_start, block_end))
                edits.append((block_start, block_end, ""))
            else:
                replacement = f"<!-- Invalid selector for {raw_path}: {selector_error} -->"
                edits.append((inc_start, inc_end, replacement))
            continue

        parent_element = _find_parent_element(elements, inc_start, inc_end)
        expected_parent = _OPTIONAL_SHARED_CONTEXT_BLOCKS.get(path_for_fs)
        if (
            expected_parent is not None
            and parent_element is not None
            and parent_element[0] == expected_parent
        ):
            block_start, block_end = parent_element[1], parent_element[2]
            if (block_start, block_end) not in removed_blocks:
                removed_blocks.add((block_start, block_end))
                edits.append((block_start, block_end, ""))
            continue

        if _optional_attr_is_truthy(attrs):
            edits.append((inc_start, inc_end, ""))
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


def sanitize_prompt_output(
    content: str,
    output_path: str | Path,
) -> Tuple[str, List[str]]:
    """
    Validate generated prompt content before writing it to ``output_path``.

    Non-prompt outputs are returned unchanged. Prompt outputs are validated
    relative to the output file's parent directory, matching the post-generation
    cleanup used by ``pdd generate``.
    """
    path = Path(output_path)
    if path.suffix != ".prompt":
        return content, []
    return validate_prompt_includes(
        content,
        base_dir=path.parent,
        remove_invalid=False,
    )
