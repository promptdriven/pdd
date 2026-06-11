"""
Content selector module for precise extraction of file content.

Provides extraction based on line ranges, AST structures (Python),
Markdown sections, regex patterns, and JSON/YAML path traversal.
Used by the PDD preprocessor for selective includes.
"""

from __future__ import annotations

import ast
import json
import os
import re
import textwrap
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

from ._selector_parse import parse_selectors_string
from .api_contract_slicer import ApiContractSlicer, ContractSlicerError
from .cli_theme import get_console
from .compression_reporting import (
    CompressionFallbackError,
    record_compression_applied,
    record_compression_fallback,
)
from .pytest_slicer import PytestSlicer, SlicerError

# Conditional YAML support
try:
    import yaml

    _HAS_YAML = True
except ImportError:  # pragma: no cover
    _HAS_YAML = False

# Rich console for error reporting, themed by the central PDD color system
# (pdd/cli_theme.py) so commands, tags, and states render consistently.
console = get_console()


# ---------------------------------------------------------------------------
# Exceptions
# ---------------------------------------------------------------------------

class SelectorError(Exception):
    """Raised when a selector is malformed or cannot be resolved."""


# ---------------------------------------------------------------------------
# Internal data helpers
# ---------------------------------------------------------------------------

@dataclass
class _Span:
    """A half-open range of 0-based line indices [start, end)."""
    start: int
    end: int


def _lines_of(content: str) -> list[str]:
    return content.splitlines(keepends=False) if hasattr(str, "splitlines") else content.split("\n")


def _splitlines(content: str) -> list[str]:
    """Split content into lines *without* trailing newline artifacts."""
    return content.splitlines()


def _extract_spans(lines: list[str], spans: list[_Span]) -> str:
    """Merge possibly-overlapping spans and return the selected text."""
    if not spans:
        return ""
    # Sort and merge
    spans = sorted(spans, key=lambda s: (s.start, s.end))
    merged: list[_Span] = [spans[0]]
    for sp in spans[1:]:
        prev = merged[-1]
        if sp.start <= prev.end:
            prev.end = max(prev.end, sp.end)
        else:
            merged.append(sp)
    selected: list[str] = []
    for sp in merged:
        selected.extend(lines[sp.start : sp.end])
    return "\n".join(selected)


# ---------------------------------------------------------------------------
# Selector parsers
# ---------------------------------------------------------------------------

_SELECTOR_RE = re.compile(
    r"^(?P<kind>lines|def|class|section|pattern|path|pytest|contract):(?P<value>.+)$"
)


@dataclass
class _ParsedSelector:
    kind: str
    value: str


def _parse_selectors(selectors: list[str]) -> list[_ParsedSelector]:
    """Parse a list of selector strings into structured objects."""
    parsed: list[_ParsedSelector] = []
    for raw in selectors:
        raw = raw.strip()
        if not raw:
            continue
        m = _SELECTOR_RE.match(raw)
        if not m:
            raise SelectorError(
                f"Malformed selector: '{raw}'. "
                "Expected format: lines:N-M | def:name | class:Name[.method] "
                "| section:Heading | pattern:/regex/ | path:key.path "
                "| pytest:test_name | contract:symbol"
            )
        parsed.append(_ParsedSelector(kind=m.group("kind"), value=m.group("value")))
    return parsed


# ---------------------------------------------------------------------------
# Line selector
# ---------------------------------------------------------------------------

def _resolve_lines(content_lines: list[str], value: str) -> list[_Span]:
    """Resolve a ``lines:`` selector value into spans.

    Supported forms (1-based):
      ``N``        – single line
      ``N-M``      – inclusive range
      ``N-``       – from N to end
      ``-M``       – from start to M
    """
    total = len(content_lines)
    spans: list[_Span] = []
    for part in value.split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            # Could be N-M, N-, -M
            idx = part.index("-")
            left = part[:idx].strip()
            right = part[idx + 1 :].strip()
            if left == "" and right == "":
                raise SelectorError(f"Invalid line range: '{part}'")
            start_0 = (int(left) - 1) if left else 0
            end_0 = int(right) if right else total  # end is exclusive
            if start_0 < 0:
                start_0 = 0
            if end_0 > total:
                end_0 = total
            if start_0 >= end_0:
                raise SelectorError(
                    f"Empty or inverted line range: '{part}' (resolved {start_0+1}-{end_0})"
                )
            spans.append(_Span(start_0, end_0))
        else:
            n = int(part)
            if n < 1 or n > total:
                raise SelectorError(
                    f"Line {n} out of range (file has {total} lines)"
                )
            spans.append(_Span(n - 1, n))
    return spans


# ---------------------------------------------------------------------------
# AST helpers (Python)
# ---------------------------------------------------------------------------

def _node_start_line(node: ast.AST) -> int:
    """Return the 0-based start line of a node, including decorators."""
    if hasattr(node, "decorator_list") and node.decorator_list:
        return node.decorator_list[0].lineno - 1
    return node.lineno - 1


def _node_end_line(node: ast.AST) -> int:
    """Return the 0-based exclusive end line of a node."""
    return node.end_lineno  # end_lineno is 1-based inclusive → use as exclusive 0-based


def _find_ast_node(
    tree: ast.Module,
    kind: str,
    value: str,
) -> list[_Span]:
    """Find spans for ``def:name`` or ``class:Name[.method]`` selectors."""
    spans: list[_Span] = []

    if kind == "def":
        # Top-level or nested function
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if node.name == value:
                    spans.append(_Span(_node_start_line(node), _node_end_line(node)))
        if not spans:
            raise SelectorError(f"Function '{value}' not found in source")

    elif kind == "class":
        if "." in value:
            cls_name, method_name = value.split(".", 1)
        else:
            cls_name = value
            method_name = None

        for node in ast.walk(tree):
            if isinstance(node, ast.ClassDef) and node.name == cls_name:
                if method_name is None:
                    spans.append(_Span(_node_start_line(node), _node_end_line(node)))
                else:
                    found_method = False
                    for child in node.body:
                        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                            if child.name == method_name:
                                spans.append(
                                    _Span(_node_start_line(child), _node_end_line(child))
                                )
                                found_method = True
                    if not found_method:
                        raise SelectorError(
                            f"Method '{method_name}' not found in class '{cls_name}'"
                        )
        if not spans:
            target = f"Class '{cls_name}'" if method_name is None else f"Class '{cls_name}' (for method '{method_name}')"
            raise SelectorError(f"{target} not found in source")

    return spans


# ---------------------------------------------------------------------------
# Interface mode (Python)
# ---------------------------------------------------------------------------

def _interface_for_node(node: ast.AST, source_lines: list[str]) -> list[str]:
    """Produce interface-mode output for a single class or function node."""
    lines: list[str] = []

    if isinstance(node, ast.ClassDef):
        # Decorators
        for dec in node.decorator_list:
            lines.extend(source_lines[dec.lineno - 1 : dec.end_lineno])
        # Class definition line(s)
        class_start = node.lineno - 1
        # Find the colon that ends the class header
        class_header_end = class_start
        for i in range(class_start, node.end_lineno):
            if ":" in source_lines[i]:
                class_header_end = i
                break
        lines.extend(source_lines[class_start : class_header_end + 1])

        # Docstring
        ds = _extract_docstring_lines(node, source_lines)
        if ds:
            lines.extend(ds)

        # Methods (excluding private except __init__)
        for child in node.body:
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if child.name.startswith("_") and child.name != "__init__":
                    continue
                lines.extend(_interface_for_func(child, source_lines))
            elif isinstance(child, ast.AnnAssign):
                # Class-level annotated assignments (type hints)
                lines.extend(source_lines[child.lineno - 1 : child.end_lineno])

    elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        lines.extend(_interface_for_func(node, source_lines))

    return lines


def _interface_for_func(
    node: ast.FunctionDef | ast.AsyncFunctionDef,
    source_lines: list[str],
) -> list[str]:
    """Return interface lines for a single function/method."""
    lines: list[str] = []
    # Decorators
    for dec in node.decorator_list:
        lines.extend(source_lines[dec.lineno - 1 : dec.end_lineno])

    # Signature – may span multiple lines
    sig_start = node.lineno - 1
    # Find the colon ending the signature
    sig_end = sig_start
    paren_depth = 0
    for i in range(sig_start, node.end_lineno):
        line = source_lines[i]
        for ch in line:
            if ch == "(":
                paren_depth += 1
            elif ch == ")":
                paren_depth -= 1
        if paren_depth <= 0 and ":" in line:
            sig_end = i
            break
    lines.extend(source_lines[sig_start : sig_end + 1])

    # Docstring
    ds = _extract_docstring_lines(node, source_lines)
    if ds:
        lines.extend(ds)

    # Determine indentation for the ellipsis
    body_indent = _body_indent(node, source_lines)
    lines.append(f"{body_indent}...")

    return lines


def _extract_docstring_lines(
    node: ast.AST, source_lines: list[str]
) -> list[str] | None:
    """If the first statement is a string constant (docstring), return its source lines."""
    body = getattr(node, "body", None)
    if not body:
        return None
    first = body[0]
    if isinstance(first, ast.Expr) and isinstance(first.value, (ast.Constant,)):
        if isinstance(first.value.value, str):
            return source_lines[first.value.lineno - 1 : first.value.end_lineno]
    return None


def _body_indent(node: ast.AST, source_lines: list[str]) -> str:
    """Determine the indentation of the body of a function/class."""
    body = getattr(node, "body", None)
    if body:
        first_body_line = source_lines[body[0].lineno - 1]
        return first_body_line[: len(first_body_line) - len(first_body_line.lstrip())]
    # Fallback: indent from the node line + 4 spaces
    node_line = source_lines[node.lineno - 1]
    base = node_line[: len(node_line) - len(node_line.lstrip())]
    return base + "    "


def _full_interface(content: str, source_lines: list[str]) -> str:
    """Produce interface-mode output for an entire Python file."""
    tree = ast.parse(content)
    result_lines: list[str] = []

    for node in tree.body:
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            result_lines.extend(source_lines[node.lineno - 1 : node.end_lineno])
        elif isinstance(node, ast.Assign):
            # Module-level constants
            result_lines.extend(source_lines[node.lineno - 1 : node.end_lineno])
        elif isinstance(node, ast.AnnAssign):
            result_lines.extend(source_lines[node.lineno - 1 : node.end_lineno])
        elif isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            if node.name.startswith("_") and node.name != "__init__":
                continue
            iface = _interface_for_node(node, source_lines)
            if result_lines and result_lines[-1].strip() != "":
                result_lines.append("")
            result_lines.extend(iface)
        elif isinstance(node, ast.Expr) and isinstance(
            getattr(node, "value", None), ast.Constant
        ):
            # Module-level docstring
            if isinstance(node.value.value, str):
                result_lines.extend(source_lines[node.lineno - 1 : node.end_lineno])

    return "\n".join(result_lines)


# ---------------------------------------------------------------------------
# Compression mode (Python only)
# ---------------------------------------------------------------------------

_COMPRESSED_MAX_CHARS = 120_000  # ~30k tokens at 4 chars/token
_PATCH_TARGET_RE = re.compile(r"""patch\s*\(\s*['"]([^'"]+)['"]""")


def _is_test_file_path(file_path: str | None) -> bool:
    if not file_path:
        return False
    name = Path(file_path).name
    return name.startswith("test_") or name.endswith("_test.py")


class _DocstringStripper(ast.NodeTransformer):
    """Remove module/class/function docstrings while preserving executable nodes."""

    @staticmethod
    def _strip_leading_docstring(body: list[ast.stmt]) -> list[ast.stmt]:
        if (
            body
            and isinstance(body[0], ast.Expr)
            and isinstance(getattr(body[0].value, "value", None), str)
        ):
            return body[1:]
        return body

    @staticmethod
    def _ensure_executable_body(body: list[ast.stmt]) -> list[ast.stmt]:
        """Docstring-only bodies must become valid Python (``pass``)."""
        if not body:
            return [ast.Pass()]
        return body

    def visit_FunctionDef(self, node: ast.FunctionDef) -> ast.FunctionDef:
        node = self.generic_visit(node)
        node.body = self._ensure_executable_body(
            self._strip_leading_docstring(node.body)
        )
        return node

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> ast.AsyncFunctionDef:
        node = self.generic_visit(node)
        node.body = self._ensure_executable_body(
            self._strip_leading_docstring(node.body)
        )
        return node

    def visit_ClassDef(self, node: ast.ClassDef) -> ast.ClassDef:
        node = self.generic_visit(node)
        node.body = self._ensure_executable_body(
            self._strip_leading_docstring(node.body)
        )
        return node

    def visit_Module(self, node: ast.Module) -> ast.Module:
        node = self.generic_visit(node)
        node.body = self._strip_leading_docstring(node.body)
        return node


def _strip_standalone_comment_lines(text: str) -> str:
    """Drop comment-only lines; keep end-of-line comments on code lines."""
    kept: list[str] = []
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("#") and not line.lstrip().startswith("# type:"):
            continue
        kept.append(line)
    return "\n".join(kept)


def _full_compressed(content: str, *, file_path: str | None) -> str:
    """Deterministic few-shot compression: strip docstrings and comment-only lines."""
    tree = ast.parse(content)
    tree = _DocstringStripper().visit(tree)
    ast.fix_missing_locations(tree)
    compressed = ast.unparse(tree)
    compressed = _strip_standalone_comment_lines(compressed)
    ast.parse(compressed)
    return compressed


def _compressed_from_spans(
    content: str,
    source_lines: list[str],
    spans: list[_Span],
    *,
    file_path: str | None,
) -> str:
    """Apply compression to span-selected Python source."""
    raw = _extract_spans(source_lines, spans)
    return _full_compressed(raw, file_path=file_path)


def _sibling_test_paths(module_path: Path) -> list[Path]:
    """Candidate sibling test files for a Python module (issue #876)."""
    stem = module_path.stem
    candidates = [
        module_path.parent / f"test_{stem}.py",
        module_path.parent / f"{stem}_test.py",
        module_path.parent / "tests" / f"test_{stem}.py",
    ]
    if module_path.parent.name != "tests":
        candidates.append(module_path.parent.parent / "tests" / f"test_{stem}.py")
    return [path for path in candidates if path.is_file()]


def discover_sibling_patch_targets(file_path: str | Path) -> set[str]:
    """Names patched on this module in sibling tests (e.g. ``fetch_data``)."""
    path = Path(file_path)
    if _is_test_file_path(str(path)):
        return set()
    module_name = path.stem
    targets: set[str] = set()
    for test_path in _sibling_test_paths(path):
        try:
            text = test_path.read_text(encoding="utf-8")
        except OSError:
            continue
        for match in _PATCH_TARGET_RE.finditer(text):
            target = match.group(1)
            symbol = _patch_symbol_for_module(target, module_name)
            if symbol:
                targets.add(symbol)
    return targets


def _patch_symbol_for_module(target: str, module_stem: str) -> Optional[str]:
    """Return the patched symbol when *target* refers to module *module_stem*."""
    if target == module_stem:
        return None
    parts = target.split(".")
    if not parts:
        return None
    if parts[0] == module_stem and len(parts) > 1:
        return parts[1].split(".")[0]
    for idx in range(len(parts) - 1):
        if parts[idx] == module_stem:
            return parts[idx + 1].split(".")[0]
    return None


def _extract_named_definitions(content: str, names: set[str]) -> list[str]:
    """Return full source spans for top-level functions named in *names*."""
    if not names:
        return []
    tree = ast.parse(content)
    lines = _splitlines(content)
    chunks: list[str] = []
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name in names:
            chunks.append("\n".join(lines[node.lineno - 1 : node.end_lineno]))
    return chunks


def augment_interface_with_patch_targets(
    interface_text: str,
    full_content: str,
    targets: set[str],
) -> str:
    """Re-append full definitions for sibling ``patch()`` targets missing from interface."""
    if not targets:
        return interface_text
    extras: list[str] = []
    for chunk in _extract_named_definitions(full_content, targets):
        if chunk and chunk not in interface_text:
            extras.append(chunk)
    if not extras:
        return interface_text
    return interface_text.rstrip() + "\n\n" + "\n\n".join(extras) + "\n"

# ---------------------------------------------------------------------------
# Markdown section selector
# ---------------------------------------------------------------------------

_MD_HEADING_RE = re.compile(r"^(#{1,6})\s+(.+)$")


def _resolve_section(content_lines: list[str], heading_text: str) -> list[_Span]:
    """Find a Markdown section by heading text.

    Returns all content under the heading until the next heading of the
    same or higher (fewer ``#``) level.
    """
    spans: list[_Span] = []
    i = 0
    while i < len(content_lines):
        m = _MD_HEADING_RE.match(content_lines[i])
        if m and m.group(2).strip() == heading_text.strip():
            level = len(m.group(1))
            start = i
            j = i + 1
            while j < len(content_lines):
                m2 = _MD_HEADING_RE.match(content_lines[j])
                if m2 and len(m2.group(1)) <= level:
                    break
                j += 1
            spans.append(_Span(start, j))
            i = j
        else:
            i += 1
    if not spans:
        raise SelectorError(f"Markdown section '{heading_text}' not found")
    return spans


# ---------------------------------------------------------------------------
# Regex pattern selector
# ---------------------------------------------------------------------------

_REGEX_TIMEOUT_SECONDS = 5


def _resolve_pattern(content_lines: list[str], value: str) -> list[_Span]:
    """Select lines matching ``pattern:/regex/``."""
    # Strip surrounding slashes if present
    pattern = value.strip()
    if pattern.startswith("/") and pattern.endswith("/") and len(pattern) >= 2:
        pattern = pattern[1:-1]
    if not pattern:
        raise SelectorError("Empty regex pattern")
    try:
        compiled = re.compile(pattern)
    except re.error as exc:
        raise SelectorError(f"Invalid regex pattern '{pattern}': {exc}") from exc

    import signal

    def _timeout_handler(signum, frame):
        raise SelectorError(
            f"Regex pattern '{pattern}' timed out after {_REGEX_TIMEOUT_SECONDS}s "
            "(possible catastrophic backtracking)"
        )

    # Set a timeout to guard against catastrophic backtracking (ReDoS)
    old_handler = signal.signal(signal.SIGALRM, _timeout_handler)
    signal.alarm(_REGEX_TIMEOUT_SECONDS)
    try:
        spans: list[_Span] = []
        for i, line in enumerate(content_lines):
            if compiled.search(line):
                spans.append(_Span(i, i + 1))
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old_handler)

    if not spans:
        raise SelectorError(f"No lines matched pattern '{pattern}'")
    return spans


# ---------------------------------------------------------------------------
# JSON/YAML path selector
# ---------------------------------------------------------------------------

_PATH_SEGMENT_RE = re.compile(r"([^\.\[\]]+)|\[(\d+)\]")


def _parse_path_segments(path: str) -> list[str | int]:
    """Parse a dot/bracket path expression into a list of segments.

    Examples::

        "key"                → ["key"]
        "key.nested.child"   → ["key", "nested", "child"]
        "key[0]"             → ["key", 0]
        "key[0].name"        → ["key", 0, "name"]
        "[0]"                → [0]
    """
    segments: list[str | int] = []
    pos = 0
    while pos < len(path):
        if path[pos] == ".":
            pos += 1
            continue
        if path[pos] == "[":
            # Array index
            end = path.index("]", pos)
            idx_str = path[pos + 1 : end]
            try:
                segments.append(int(idx_str))
            except ValueError:
                raise SelectorError(
                    f"Invalid array index in path: '{path}' (got '{idx_str}')"
                )
            pos = end + 1
        else:
            # Key segment — read until next '.' or '['
            end = pos
            while end < len(path) and path[end] not in (".", "["):
                end += 1
            segments.append(path[pos:end])
            pos = end
    if not segments:
        raise SelectorError(f"Empty path expression: '{path}'")
    return segments


def _traverse_path(data: object, segments: list[str | int], full_path: str) -> object:
    """Navigate into *data* following *segments*, raising on missing keys."""
    current = data
    traversed: list[str] = []
    for seg in segments:
        if isinstance(seg, int):
            if not isinstance(current, list):
                raise SelectorError(
                    f"Expected array at '{'.'.join(traversed)}' in path '{full_path}', "
                    f"got {type(current).__name__}"
                )
            if seg < 0 or seg >= len(current):
                raise SelectorError(
                    f"Array index {seg} out of range (length {len(current)}) "
                    f"at '{'.'.join(traversed)}' in path '{full_path}'"
                )
            current = current[seg]
            traversed.append(f"[{seg}]")
        else:
            if not isinstance(current, dict):
                raise SelectorError(
                    f"Expected object at '{'.'.join(traversed)}' in path '{full_path}', "
                    f"got {type(current).__name__}"
                )
            if seg not in current:
                raise SelectorError(
                    f"Key '{seg}' not found at '{'.'.join(traversed) or 'root'}' "
                    f"in path '{full_path}'"
                )
            current = current[seg]
            traversed.append(seg)
    return current


def _resolve_path(content: str, value: str, file_path: str | None) -> str:
    """Resolve a ``path:`` selector for JSON/YAML content.

    Parses the content, traverses to the requested path, and re-serializes
    the extracted value in the same format (pretty-printed).
    """
    is_json_file = _is_json(file_path)
    is_yaml_file = _is_yaml(file_path)

    # Parse the content
    if is_json_file:
        try:
            data = json.loads(content)
        except json.JSONDecodeError as exc:
            raise SelectorError(f"Failed to parse JSON: {exc}") from exc
    elif is_yaml_file:
        if not _HAS_YAML:
            raise SelectorError(
                "PyYAML is required for YAML path selectors but is not installed. "
                "Install it with: pip install pyyaml"
            )
        try:
            data = yaml.safe_load(content)
        except yaml.YAMLError as exc:
            raise SelectorError(f"Failed to parse YAML: {exc}") from exc
    else:
        raise SelectorError(
            f"Path selector requires a JSON or YAML file, got '{file_path}'"
        )

    # Parse and traverse the path
    segments = _parse_path_segments(value)
    result = _traverse_path(data, segments, value)

    # Re-serialize in the source format
    if is_json_file:
        return json.dumps(result, indent=2, ensure_ascii=False)
    else:
        # YAML output
        return yaml.dump(result, default_flow_style=False, allow_unicode=True).rstrip("\n")


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def apply_compressed_include_with_fallback(
    content: str,
    *,
    file_path: str,
    selectors: list[str] | str | None = None,
    expand_dependencies: bool = False,
) -> str:
    """Apply compressed-mode include transform with interface/truncation fallback."""
    if not _is_python(file_path):
        return content
    if isinstance(selectors, str):
        sel_list = parse_selectors_string(selectors)
    elif selectors:
        sel_list = [s.strip() for s in selectors if s.strip()]
    else:
        sel_list = []
    selector = ContentSelector()
    raw = content
    compressed = selector.select(
        raw,
        sel_list,
        file_path=file_path,
        mode="compressed",
        expand_dependencies=expand_dependencies,
    )
    if len(compressed) <= _COMPRESSED_MAX_CHARS:
        return compressed
    iface = selector.select(
        raw,
        sel_list,
        file_path=file_path,
        mode="interface",
        expand_dependencies=expand_dependencies,
    )
    patch_targets = discover_sibling_patch_targets(file_path)
    restored = augment_interface_with_patch_targets(iface, raw, patch_targets)
    if len(restored) <= _COMPRESSED_MAX_CHARS:
        return restored
    return raw[:_COMPRESSED_MAX_CHARS]


class ContentSelector:
    """Precise content extraction from file content."""

    @staticmethod
    def select(
        content: str,
        selectors: list[str] | str,
        file_path: str | None = None,
        mode: str = "full",
        expand_dependencies: bool = False,
    ) -> str:
        """Select portions of *content* according to *selectors*.

        Parameters
        ----------
        content:
            The full text content to select from.
        selectors:
            A list of selector strings **or** a single comma-separated string.
            Each selector has the form ``kind:value`` where *kind* is one of
            ``lines``, ``def``, ``class``, ``section``, ``pattern``, ``path``,
            ``pytest``, ``contract``.
        file_path:
            Optional file path used to infer the file type (e.g. ``.py``,
            ``.md``, ``.json``, ``.yaml``).  When ``None``, AST-based
            selectors will attempt to parse as Python.
        mode:
            ``"full"`` (default) returns the selected content verbatim.
            ``"interface"`` (Python only) returns signatures, docstrings,
            and type hints with bodies replaced by ``...``.
            ``"compressed"`` (Python only) strips docstrings and comment-only
            lines while preserving executable logic.
        expand_dependencies:
            When ``True`` (Python only), expand the selection to include
            local symbol dependencies and unittest/mock patch targets.

        Returns
        -------
        str
            The selected (and possibly transformed) content.
        """
        # Normalise selectors to a list (preserve commas inside kind:value)
        if isinstance(selectors, str):
            selectors = parse_selectors_string(selectors)
        else:
            selectors = [s.strip() for s in selectors if s.strip()]

        if not selectors and mode == "interface":
            # No selectors but interface mode → produce interface for whole file
            source_lines = _splitlines(content)
            try:
                return _full_interface(content, source_lines)
            except SyntaxError as exc:
                _report_error(f"Failed to parse Python source: {exc}", file_path)
                raise SelectorError(f"Python parse error: {exc}") from exc

        if not selectors and mode == "contracts":
            return _contracts_mode(content)

        if not selectors and mode == "test_interface":
            return _test_interface_mode(content, file_path)

        if not selectors and mode == "compressed":
            if not _is_python(file_path):
                return content
            try:
                return _full_compressed(content, file_path=file_path)
            except SyntaxError as exc:
                _report_error(f"Failed to parse Python source: {exc}", file_path)
                raise SelectorError(f"Python parse error: {exc}") from exc

        if not selectors:
            return content

        parsed = _parse_selectors(selectors)

        # If all selectors were empty/whitespace strings, parsed will be empty.
        # In that case, treat as "no selectors" and return full content.
        if not parsed:
            return content

        source_lines = _splitlines(content)

        # Determine file type
        is_python = _is_python(file_path)
        is_markdown = _is_markdown(file_path)
        is_json_or_yaml = _is_json(file_path) or _is_yaml(file_path)

        # We may need the AST for Python selectors
        tree: ast.Module | None = None
        needs_ast = any(p.kind in ("def", "class") for p in parsed)
        if needs_ast:
            if not is_python and file_path is not None:
                _report_error(
                    f"AST selectors (def/class) require a Python file, got '{file_path}'",
                    file_path,
                )
                raise SelectorError(
                    f"AST selectors require a .py file, got '{file_path}'"
                )
            try:
                tree = ast.parse(content)
            except SyntaxError as exc:
                _report_error(f"Failed to parse Python source: {exc}", file_path)
                raise SelectorError(f"Python parse error: {exc}") from exc

        needs_md = any(p.kind == "section" for p in parsed)
        if needs_md and not is_markdown and file_path is not None:
            _report_error(
                f"Section selector requires a Markdown file, got '{file_path}'",
                file_path,
            )
            raise SelectorError(
                f"Section selector requires a .md file, got '{file_path}'"
            )

        needs_slicer = any(p.kind in ("pytest", "contract") for p in parsed)
        if needs_slicer and not is_python and file_path is not None:
            _report_error(
                f"pytest/contract selectors require a Python file, got '{file_path}'",
                file_path,
            )
            raise SelectorError(
                f"pytest/contract selectors require a .py file, got '{file_path}'"
            )

        needs_path = any(p.kind == "path" for p in parsed)
        if needs_path and not is_json_or_yaml:
            _report_error(
                f"Path selector requires a JSON or YAML file, got '{file_path}'",
                file_path,
            )
            raise SelectorError(
                f"Path selector requires a .json/.yaml/.yml file, got '{file_path}'"
            )

        # Collect spans (for span-based selectors) and path results separately
        all_spans: list[_Span] = []
        path_results: list[str] = []

        for sel in parsed:
            try:
                if sel.kind == "lines":
                    all_spans.extend(_resolve_lines(source_lines, sel.value))
                elif sel.kind in ("def", "class"):
                    assert tree is not None
                    all_spans.extend(_find_ast_node(tree, sel.kind, sel.value))
                elif sel.kind == "section":
                    all_spans.extend(_resolve_section(source_lines, sel.value))
                elif sel.kind == "pattern":
                    all_spans.extend(_resolve_pattern(source_lines, sel.value))
                elif sel.kind == "path":
                    path_results.append(_resolve_path(content, sel.value, file_path))
                elif sel.kind == "pytest":
                    test_names = [t.strip() for t in sel.value.split(",") if t.strip()]
                    try:
                        slicer = PytestSlicer(content, file_path=file_path)
                        sliced_content, _ = slicer.slice(test_names)
                    except SlicerError as exc:
                        sliced_content = _handle_selector_slice_failure(
                            exc,
                            slice_kind="pytest",
                            file_path=file_path,
                            content=content,
                        )
                    if sliced_content != content and file_path:
                        record_compression_applied(file_path, f"pytest:{sel.value}")
                    path_results.append(sliced_content)
                elif sel.kind == "contract":
                    symbols = [t.strip() for t in sel.value.split(",") if t.strip()]
                    try:
                        slicer = ApiContractSlicer(content, file_path=file_path)
                        sliced_content, _ = slicer.slice(symbols)
                    except ContractSlicerError as exc:
                        sliced_content = _handle_selector_slice_failure(
                            exc,
                            slice_kind="contract",
                            file_path=file_path,
                            content=content,
                        )
                    if sliced_content != content and file_path:
                        record_compression_applied(file_path, f"contract:{sel.value}")
                    path_results.append(sliced_content)
                else:
                    raise SelectorError(f"Unknown selector kind: '{sel.kind}'")
            except (SelectorError, CompressionFallbackError):
                raise
            except Exception as exc:
                _report_error(
                    f"Error processing selector '{sel.kind}:{sel.value}': {exc}",
                    file_path,
                )
                raise SelectorError(
                    f"Error processing selector '{sel.kind}:{sel.value}': {exc}"
                ) from exc

        if expand_dependencies and is_python and tree is not None and all_spans:
            all_spans = _expand_dependency_spans(tree, all_spans, file_path)

        # Build final result
        parts: list[str] = []

        # Span-based content
        if all_spans:
            # Interface/compressed mode post-processing for AST selectors
            if mode == "interface" and is_python and tree is not None:
                parts.append(_interface_from_spans(content, source_lines, tree, all_spans))
            elif mode == "compressed" and is_python:
                parts.append(
                    _compressed_from_spans(
                        content, source_lines, all_spans, file_path=file_path
                    )
                )
            else:
                parts.append(_extract_spans(source_lines, all_spans))

        # Path-based content
        if path_results and mode == "compressed" and is_python:
            compressed_paths: list[str] = []
            for chunk in path_results:
                try:
                    compressed_paths.append(
                        _full_compressed(chunk, file_path=file_path)
                    )
                except SyntaxError:
                    compressed_paths.append(chunk)
            path_results = compressed_paths
        parts.extend(path_results)

        if not parts:
            return ""

        return "\n".join(parts)


# ---------------------------------------------------------------------------
# Dependency expansion (Python)
# ---------------------------------------------------------------------------

def _span_overlaps_node(span: _Span, node: ast.AST) -> bool:
    node_start = _node_start_line(node)
    node_end = _node_end_line(node)
    return span.start < node_end and span.end > node_start


def _top_level_symbol_map(tree: ast.Module) -> dict[str, ast.AST]:
    mapping: dict[str, ast.AST] = {}
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            mapping[node.name] = node
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    mapping[target.id] = node
        elif (
            isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name)
            and node.value is not None
        ):
            mapping[node.target.id] = node
    return mapping


def _referenced_local_names(node: ast.AST, top_level: set[str]) -> set[str]:
    found: set[str] = set()
    for child in ast.walk(node):
        if isinstance(child, ast.Name) and isinstance(child.ctx, ast.Load):
            if child.id in top_level:
                found.add(child.id)
    return found


def _ast_node_for_symbol(
    tree: ast.Module,
    symbol: str,
    top_map: dict[str, ast.AST],
) -> ast.AST | None:
    if "." not in symbol:
        return top_map.get(symbol)
    cls_name, remainder = symbol.split(".", 1)
    cls_node = top_map.get(cls_name)
    if not isinstance(cls_node, ast.ClassDef):
        return None
    if "." not in remainder:
        for child in cls_node.body:
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)) and child.name == remainder:
                return child
        return None
    inner_cls, method_name = remainder.split(".", 1)
    for child in cls_node.body:
        if isinstance(child, ast.ClassDef) and child.name == inner_cls:
            for method in child.body:
                if isinstance(method, (ast.FunctionDef, ast.AsyncFunctionDef)) and method.name == method_name:
                    return method
    return None


def _used_names_for_needed(
    tree: ast.Module,
    needed: set[str],
    top_map: dict[str, ast.AST],
) -> set[str]:
    used: set[str] = set()
    for name in needed:
        node = _ast_node_for_symbol(tree, name, top_map)
        if node is None:
            continue
        for child in ast.walk(node):
            if isinstance(child, ast.Name) and isinstance(child.ctx, ast.Load):
                used.add(child.id)
    return used


def _import_spans_for_used_names(tree: ast.Module, used_names: set[str]) -> list[_Span]:
    if not used_names:
        return []
    spans: list[_Span] = []
    for node in tree.body:
        if isinstance(node, ast.Import):
            if any((alias.asname or alias.name.split(".")[0]) in used_names for alias in node.names):
                spans.append(_Span(_node_start_line(node), _node_end_line(node)))
        elif isinstance(node, ast.ImportFrom):
            if any((alias.asname or alias.name) in used_names for alias in node.names):
                spans.append(_Span(_node_start_line(node), _node_end_line(node)))
    return spans


def _span_for_symbol(tree: ast.Module, symbol: str, top_map: dict[str, ast.AST]) -> _Span | None:
    node = _ast_node_for_symbol(tree, symbol, top_map)
    if node is None:
        return None
    return _Span(_node_start_line(node), _node_end_line(node))


def _expand_dependency_spans(
    tree: ast.Module,
    spans: list[_Span],
    file_path: str | None,
) -> list[_Span]:
    top_map = _top_level_symbol_map(tree)
    top_names = set(top_map.keys())

    seed_names: set[str] = set()
    for node in tree.body:
        if not isinstance(
            node,
            (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Assign, ast.AnnAssign),
        ):
            continue
        if any(_span_overlaps_node(span, node) for span in spans):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                seed_names.add(node.name)
            elif isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        seed_names.add(target.id)
            elif isinstance(node.target, ast.Name):
                seed_names.add(node.target.id)

    from pdd.split_validation import collect_patch_symbols_for_module  # pylint: disable=import-outside-toplevel

    if file_path:
        seed_names.update(collect_patch_symbols_for_module(file_path))

    needed: set[str] = set()
    pending = list(seed_names)
    while pending:
        name = pending.pop()
        if name in needed:
            continue
        needed.add(name)
        root = name.split(".", 1)[0]
        node = top_map.get(root)
        if node is None:
            continue
        for dep in _referenced_local_names(node, top_names):
            if dep not in needed:
                pending.append(dep)

    expanded = list(spans)
    for name in needed:
        symbol_span = _span_for_symbol(tree, name, top_map)
        if symbol_span is not None:
            expanded.append(symbol_span)
    expanded.extend(_import_spans_for_used_names(tree, _used_names_for_needed(tree, needed, top_map)))
    return expanded


# ---------------------------------------------------------------------------
# Interface mode with specific spans
# ---------------------------------------------------------------------------

def _interface_from_spans(
    content: str,
    source_lines: list[str],
    tree: ast.Module,
    spans: list[_Span],
) -> str:
    """Produce interface output only for AST nodes overlapping *spans*."""
    # Merge spans
    spans = sorted(spans, key=lambda s: (s.start, s.end))
    merged: list[_Span] = [_Span(spans[0].start, spans[0].end)]
    for sp in spans[1:]:
        prev = merged[-1]
        if sp.start <= prev.end:
            prev.end = max(prev.end, sp.end)
        else:
            merged.append(sp)

    def _is_contained(node_span: _Span) -> bool:
        for sp in merged:
            if node_span.start >= sp.start and node_span.end <= sp.end:
                return True
        return False

    def _overlaps(node_span: _Span) -> bool:
        for sp in merged:
            if node_span.start < sp.end and node_span.end > sp.start:
                return True
        return False

    result_lines: list[str] = []

    def _visit(node: ast.AST) -> None:
        if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            ns = _Span(_node_start_line(node), _node_end_line(node))
            if _is_contained(ns):
                iface = _interface_for_node(node, source_lines)
                if result_lines and result_lines[-1].strip() != "":
                    result_lines.append("")
                result_lines.extend(iface)
                return
            elif not _overlaps(ns):
                return
        for child in ast.iter_child_nodes(node):
            _visit(child)

    _visit(tree)

    return "\n".join(result_lines) if result_lines else _extract_spans(source_lines, merged)


# ---------------------------------------------------------------------------
# Utilities
# ---------------------------------------------------------------------------

def _is_python(file_path: str | None) -> bool:
    if file_path is None:
        return True  # assume Python when unknown
    return file_path.rstrip().lower().endswith(".py")


def _is_markdown(file_path: str | None) -> bool:
    if file_path is None:
        return False
    lower = file_path.rstrip().lower()
    return lower.endswith(".md") or lower.endswith(".markdown")


def _is_json(file_path: str | None) -> bool:
    if file_path is None:
        return False
    return file_path.rstrip().lower().endswith(".json")


def _is_yaml(file_path: str | None) -> bool:
    if file_path is None:
        return False
    lower = file_path.rstrip().lower()
    return lower.endswith(".yaml") or lower.endswith(".yml")


def _report_error(message: str, file_path: str | None = None) -> None:
    """Print a formatted error to the rich console."""
    location = f" in [path]{file_path}[/path]" if file_path else ""
    console.print(f"[error]ContentSelector error{location}:[/error] {message}")
# ---------------------------------------------------------------------------
# Contract and Test Interface Modes
# ---------------------------------------------------------------------------

_PDD_META_TAGS = ("pdd-reason", "pdd-interface", "pdd-dependency")
_LOGICAL_SECTION_TAGS = (
    "responsibility",
    "non_responsibilities",
    "vocabulary",
    "contract_rules",
    "capabilities",
    "waivers",
    "coverage",
)


def _failing_test_ids_for_file(
    failing_test_ids: list[str],
    file_path: str | None,
) -> list[str]:
    """Keep only pytest node IDs that belong to the file being sliced."""
    if not file_path:
        return failing_test_ids

    target = Path(file_path).as_posix()
    target_name = Path(target).name
    filtered: list[str] = []
    for ftid in failing_test_ids:
        file_part = ftid.split("::", 1)[0]
        node_path = Path(file_part).as_posix()
        if (
            node_path == target
            or node_path.endswith(f"/{target}")
            or (Path(node_path).name == target_name and target.endswith(node_path))
        ):
            filtered.append(ftid)
    return filtered


def _node_id_to_slicer_name(ftid: str) -> str | None:
    """Map a pytest node id to a ``PytestSlicer`` symbol name."""
    parts = [part for part in ftid.split("::") if part]
    if not parts:
        return None
    if parts[0].endswith(".py") or "/" in parts[0]:
        parts = parts[1:]
    if not parts:
        return None
    if len(parts) == 1:
        return parts[0]
    return f"{parts[0]}.{parts[1]}"


def _compression_fallback_policy() -> str:
    return (os.environ.get("PDD_COMPRESSION_FALLBACK", "full") or "full").lower()


def _handle_selector_slice_failure(
    exc: Exception,
    *,
    slice_kind: str,
    file_path: str | None,
    content: str,
) -> str:
    """Apply ``PDD_COMPRESSION_FALLBACK`` when pytest/contract slicing fails."""
    label = file_path or "<file>"
    message = f"{slice_kind} slice failed for {label}: {exc}"
    if _compression_fallback_policy() == "error":
        record_compression_fallback(message)
        raise CompressionFallbackError(message) from exc
    record_compression_fallback(message)
    return content


def _handle_test_slice_failure(exc: SlicerError, *, file_path: str | None, content: str) -> str:
    """Apply ``PDD_COMPRESSION_FALLBACK`` when pytest test_interface slicing fails."""
    return _handle_selector_slice_failure(
        exc, slice_kind="pytest", file_path=file_path, content=content
    )


def slice_test_interface_context(content: str, file_path: str | None = None) -> str:
    """Slice test source to failing tests and dependency-aware helpers via ``PytestSlicer``."""
    failing_tests_env = os.environ.get("PDD_FAILING_TESTS", "")
    failing_test_ids = [item.strip() for item in failing_tests_env.split(",") if item.strip()]
    failing_test_ids = _failing_test_ids_for_file(failing_test_ids, file_path)
    if not failing_test_ids:
        return content

    test_names: list[str] = []
    seen: set[str] = set()
    for ftid in failing_test_ids:
        name = _node_id_to_slicer_name(ftid)
        if name and name not in seen:
            test_names.append(name)
            seen.add(name)

    if not test_names:
        return content

    try:
        slicer = PytestSlicer(content, file_path=file_path)
        sliced_content, _ = slicer.slice(test_names)
    except SlicerError as exc:
        return _handle_test_slice_failure(exc, file_path=file_path, content=content)
    return sliced_content


def _contracts_mode(content: str) -> str:
    """Extract contract-related elements from prompt or documentation files."""
    output_parts: list[str] = []

    for tag in _PDD_META_TAGS:
        output_parts.extend(
            re.findall(rf"<{tag}>.*?</{tag}>", content, re.DOTALL)
        )

    for tag in _LOGICAL_SECTION_TAGS:
        output_parts.extend(
            re.findall(rf"<{tag}>.*?</{tag}>", content, re.DOTALL)
        )

    rule_lines: list[str] = []
    for line in content.splitlines():
        stripped = line.strip()
        if re.match(r"^R\d+ -", stripped):
            rule_lines.append(line)
        elif re.match(r"^- (MAY|MUST|MUST NOT)\b", stripped):
            rule_lines.append(line)

    if rule_lines:
        output_parts.append("\n".join(rule_lines))

    if not output_parts:
        return content

    return "\n".join(output_parts)


def _test_interface_mode(content: str, file_path: str | None) -> str:
    """Extract only failing tests and necessary fixtures using ``PytestSlicer``."""
    failing_tests_env = os.environ.get("PDD_FAILING_TESTS", "")
    if not failing_tests_env.strip():
        label = file_path or "<test>"
        record_compression_fallback(
            f"test_interface compression skipped for {label}: PDD_FAILING_TESTS unset; "
            "using full test content"
        )
        return content
    return slice_test_interface_context(content, file_path)
