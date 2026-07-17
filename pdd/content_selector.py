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
import subprocess
import textwrap
import time
from contextlib import contextmanager
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Mapping, Optional

from filelock import FileLock

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


# JS/TS jest/vitest/Next.js co-located test conventions (issue #1903).
_JS_TS_EXTENSIONS = (".ts", ".tsx", ".js", ".jsx", ".mjs", ".cjs")
_JS_TS_TEST_SUFFIXES = (".test", ".spec")
_JS_TS_TEST_SUBDIRS = ("__test__", "__tests__", "tests")
# Python modules whose sibling tests `_sibling_test_paths` (always `.py`) can
# legitimately match (issue #1903). Any other suffix is unsupported and yields no
# candidates — a safe no-op — so e.g. `src/foo.go` never adopts a same-stem
# `tests/test_foo.py` and retargets Go generation into a Python file.
_PYTHON_EXTENSIONS = (".py", ".pyi")


def _collocated_js_ts_candidates(module_path: Path) -> list[Path]:
    """Candidate co-located test files for a JS/TS module (issue #1903).

    Covers ``{stem}.test.<ext>`` / ``{stem}.spec.<ext>`` beside the module and
    under ``__test__/``, ``__tests__/`` and ``tests/`` — the conventions jest,
    vitest and Next.js collect. Existence is filtered by the caller.
    """
    stem = module_path.stem
    parent = module_path.parent
    candidates: list[Path] = []
    for ext in _JS_TS_EXTENSIONS:
        for suffix in _JS_TS_TEST_SUFFIXES:
            filename = f"{stem}{suffix}{ext}"
            candidates.append(parent / filename)
            for subdir in _JS_TS_TEST_SUBDIRS:
                candidates.append(parent / subdir / filename)
    return candidates


def _contained_in_root(candidate_resolved: Path, root_resolved: Path) -> bool:
    """CWE-022 containment barrier: *candidate_resolved* is *root* or inside it.

    Both arguments MUST already be ``.resolve()``d (symlinks and ``..``
    normalized). Adoption candidates are derived from a caller-supplied
    code-file path — issue-influenced in the hosted/agentic flow — and must
    never escape the working tree: a traversal like ``../../victim`` would
    otherwise become a generated-test WRITE target (py/path-injection,
    PR #1914 CodeQL alerts #339-#342).
    """
    candidate_s, root_s = str(candidate_resolved), str(root_resolved)
    return candidate_s == root_s or candidate_s.startswith(
        root_s.rstrip(os.sep) + os.sep
    )


def _validated_project_path(
    untrusted_path: str | Path,
    *,
    root: Path | None = None,
) -> Optional[Path]:
    """Return a canonical in-project path built from sanitized components.

    ``code_file`` can originate in an issue-driven/cloud request, so it must
    not flow directly into any filesystem operation. First reduce an absolute
    path to a path relative to the trusted working-tree root (or reject it),
    then sanitize every component with :func:`os.path.basename` before joining
    it back to that root. Only after that lexical barrier do we resolve
    symlinks and enforce canonical containment. This ordering is important:
    checking containment *after* calling ``resolve`` on the raw caller value is
    too late for CWE-022 and is reported by CodeQL's ``py/path-injection``
    query.

    The helper is total. Traversal, an outside absolute path, a symlink escape,
    or any malformed value returns ``None``.
    """
    try:
        root_resolved = (root or Path.cwd()).resolve()
        raw = Path(untrusted_path)
        if raw.is_absolute():
            try:
                relative = raw.relative_to(root_resolved)
            except ValueError:
                return None
        else:
            relative = raw

        if not relative.parts:
            return None

        safe_parts: list[str] = []
        for part in relative.parts:
            # basename is the path-component sanitization barrier. Equality
            # ensures separators/traversal were not silently stripped.
            safe_part = os.path.basename(part)
            if safe_part != part or safe_part in {'', os.curdir, os.pardir}:
                return None
            safe_parts.append(safe_part)

        candidate = root_resolved.joinpath(*safe_parts)
        resolved = candidate.resolve()
        if not _contained_in_root(resolved, root_resolved):
            return None
        return resolved
    except (OSError, RuntimeError, TypeError, ValueError):
        return None


def find_collocated_test(code_file: str | Path) -> Optional[Path]:
    """Return the single existing co-located test for *code_file*, else ``None``.

    Pure runner-awareness detector (issue #1903). Covers Python sibling
    conventions (reusing :func:`_sibling_test_paths`) and JS/TS jest/vitest/
    Next.js conventions (``{stem}.test.<ext>`` / ``{stem}.spec.<ext>`` beside
    the module and under ``__test__/``, ``__tests__/``, ``tests/``). Any other
    language is unsupported and returns ``None`` (no candidates) so a non-Python,
    non-JS/TS module is never retargeted onto a same-stem ``.py`` sibling.

    Only EXISTING files are considered, the module itself is excluded, and
    candidates are de-duped by resolved path. Candidates outside the current
    working tree are rejected (containment, CWE-022): adoption only ever
    targets tests inside the project the CLI is operating on, so a
    traversal-shaped *code_file* degrades to no-adoption rather than escaping
    the repo. The match is returned only when exactly one distinct test file
    exists (0 matches OR >1 match -> ``None``) so an ambiguous project is
    never silently retargeted. Never raises: any error yields ``None``.
    """
    matches = _collocated_test_matches(code_file)
    return matches[0] if len(matches) == 1 else None


def _collocated_test_matches(code_file: str | Path) -> list[Path]:
    """All distinct EXISTING co-located tests for *code_file* (validated, in-root).

    The shared match set behind :func:`find_collocated_test`. Cardinality
    matters to callers: ZERO matches is greenfield-eligible, but an AMBIGUOUS
    (>1) project must NOT be treated as greenfield (that would fork a third
    test) — see :func:`resolve_test_output_path`. Never raises: any error yields
    ``[]``.
    """
    try:
        root_resolved = Path.cwd().resolve()
        module_path = _validated_project_path(code_file, root=root_resolved)
        if module_path is None:
            return []
        suffix = module_path.suffix.lower()
        if suffix in _JS_TS_EXTENSIONS:
            raw_candidates = _collocated_js_ts_candidates(module_path)
        elif suffix in _PYTHON_EXTENSIONS:
            raw_candidates = _sibling_test_paths(module_path)
        else:
            return []

        seen: set[Path] = set()
        matches: list[Path] = []
        for candidate in raw_candidates:
            resolved = _validated_project_path(candidate, root=root_resolved)
            if resolved is None or not resolved.is_file():
                continue
            if resolved == module_path or resolved in seen:
                continue
            seen.add(resolved)
            matches.append(resolved)
        return matches
    except Exception:  # pylint: disable=broad-except
        return []


# JS/TS test-runner config markers for greenfield discovery (issue #1903 §A).
# A project that configures jest/vitest collects tests co-located with the
# module: jest's default ``testMatch`` matches any ``*.test.<ext>`` /
# ``*.spec.<ext>`` regardless of directory, so an ``__test__/{stem}.test.tsx``
# beside the module is collected. When PDD would otherwise write the FIRST test
# for a brand-new module to a runner-blind ``tests/`` shadow, detect that the
# project uses such a runner and write the first test where the runner will
# actually collect it — never a root ``tests/`` orphan.
_JS_TS_RUNNER_CONFIG_STEMS = ("jest.config", "vitest.config")
_JS_TS_RUNNER_CONFIG_EXTS = ("", ".js", ".ts", ".mjs", ".cjs", ".mts", ".cts", ".json")


def _package_json_declares_js_runner(package_json: Path) -> bool:
    """Return True when *package_json* references jest/vitest.

    Checks an inline ``"jest"``/``"vitest"`` config block, a declared
    dependency on jest/vitest, or a ``test`` script that invokes one. Total —
    any read/parse error yields ``False``.
    """
    try:
        data = json.loads(package_json.read_text(encoding="utf-8", errors="ignore"))
    except (OSError, ValueError):
        return False
    if not isinstance(data, Mapping):
        return False
    # Inline runner config block (``"jest": {...}`` / ``"vitest": {...}``).
    for key in ("jest", "vitest"):
        if data.get(key) is not None:
            return True
    # Declared dependency on a runner (incl. scoped ``@scope/jest`` wrappers).
    for dep_key in (
        "dependencies",
        "devDependencies",
        "peerDependencies",
        "optionalDependencies",
    ):
        deps = data.get(dep_key)
        if isinstance(deps, Mapping):
            for name in deps:
                if isinstance(name, str) and (
                    name in ("jest", "vitest")
                    or name.endswith("/jest")
                    or name.endswith("/vitest")
                ):
                    return True
    # A ``test`` / ``test:*`` script that INVOKES a runner as a command token —
    # only these script keys, and only a real ``jest``/``vitest`` command token
    # (not any substring, so ``"build": "echo no-jest"`` does not false-positive;
    # issue #1903 review round 5).
    scripts = data.get("scripts")
    if isinstance(scripts, Mapping):
        for key, cmd in scripts.items():
            if not (isinstance(key, str) and (key == "test" or key.startswith("test:"))):
                continue
            if not isinstance(cmd, str):
                continue
            if re.search(r"(?:^|[\s;&|/])(?:jest|vitest)(?:$|[\s;&|@'\"])", cmd):
                return True
    return False


def _project_uses_js_test_runner(module_path: Path, root_resolved: Path) -> bool:
    """True when a jest/vitest runner is configured at or above *module_path*.

    Walks from the module's directory up to (and including) *root_resolved*,
    looking for a jest/vitest config file or a ``package.json`` that declares
    one. Never walks above the trusted root. Total — any error yields ``False``.
    """
    try:
        current = module_path.parent.resolve()
    except (OSError, RuntimeError):
        return False
    root_s = str(root_resolved)
    while True:
        for stem in _JS_TS_RUNNER_CONFIG_STEMS:
            for ext in _JS_TS_RUNNER_CONFIG_EXTS:
                if (current / f"{stem}{ext}").is_file():
                    return True
        pkg = current / "package.json"
        if pkg.is_file() and _package_json_declares_js_runner(pkg):
            return True
        if str(current) == root_s or not _contained_in_root(current, root_resolved):
            break
        parent = current.parent
        if parent == current:
            break
        current = parent
    return False


def _as_str_list(value: Any) -> list[str]:
    """Coerce a jest config value (str | list | None) to a list of strings."""
    if isinstance(value, str):
        return [value]
    if isinstance(value, (list, tuple)):
        return [v for v in value if isinstance(v, str)]
    return []


def _jest_config_from_package_json(package_json: Path) -> Optional[Mapping[str, Any]]:
    """Return the inline ``jest``/``vitest`` config block from a package.json."""
    try:
        data = json.loads(package_json.read_text(encoding="utf-8", errors="ignore"))
    except (OSError, ValueError):
        return None
    if not isinstance(data, Mapping):
        return None
    for key in ("jest", "vitest"):
        block = data.get(key)
        if isinstance(block, Mapping):
            return block
    return None


# Test-discovery keys whose presence in an unparseable JS/TS config means we
# cannot assume default discovery (issue #1903 §A). Covers BOTH the jest dialect
# (testMatch/testRegex/testPathIgnorePatterns/roots/rootDir) and the vitest
# dialect (test.include/exclude, projects, workspace) — matched as whole words
# so generic tokens (e.g. ``__dirname``, ``rootReducer``) do not false-trigger.
_JS_RUNNER_DISCOVERY_KEYS = (
    "testMatch",
    "testRegex",
    "testPathIgnorePatterns",
    "roots",
    "rootDir",
    "root",
    "dir",
    "include",
    "exclude",
    "projects",
    "workspace",
)
_JS_RUNNER_DISCOVERY_RE = re.compile(
    r"\b(?:" + "|".join(_JS_RUNNER_DISCOVERY_KEYS) + r")\b"
)
# Composition/delegation a static text scan cannot resolve: a config that
# imports/requires/spreads/extends a base, applies a preset, is a function, or
# whose export is a CALL expression (``module.exports = buildConfig()``,
# ``export default defineConfig(...)``, ``createJestConfig(...)``) could set
# discovery elsewhere. Any of these makes the config unresolvable -> refuse
# (issue #1903 review rounds 2-3, delegating/wrapper jest.config.js).
_JS_RUNNER_UNRESOLVABLE_RE = re.compile(
    r"\brequire\s*\(|\bimport\b|\bpreset\b|\bextends\b|\.\.\."
    r"|=>|\bfunction\b"
    r"|=\s*[A-Za-z_$][\w$.]*\s*\("          # export is a call: = buildConfig(
    r"|\.\w+\s*\("                          # ANY method call: ['a','b'].join(
    r"|\[[^\]\n]*\]\s*:"                    # computed property key: {[..]: ..}
    r"|`"                                   # template literal (dynamic strings)
    r"|module\.exports\s*=\s*[A-Za-z_$]"    # export is an identifier: = config
    r"|export\s+default\s+[A-Za-z_$]"       # export default ident / defineConfig
)
_JS_RUNNER_CONFIG_FILE_STEMS = ("jest.config", "vitest.config", "vite.config")


def _strip_js_comments_and_strings(text: str) -> str:
    """Best-effort: blank out JS comments and string/template literals.

    So a discovery keyword or extra ``;`` inside a comment or string cannot
    change the structural (whitelist) analysis. Replaces the CONTENTS of each
    ``//``, ``/* */``, ``'…'``, ``"…"``, `` `…` `` with spaces (preserving
    length/newlines is unnecessary). A single pass; never raises.
    """
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        two = text[i : i + 2]
        if two == "//":
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if two == "/*":
            j = text.find("*/", i + 2)
            i = n if j < 0 else j + 2
            continue
        if c in "'\"`":
            quote = c
            i += 1
            while i < n:
                if text[i] == "\\":
                    i += 2
                    continue
                if text[i] == quote:
                    i += 1
                    break
                i += 1
            out.append('""')  # placeholder token for a string value
            continue
        out.append(c)
        i += 1
    return "".join(out)


def _js_config_is_trivial_default_literal(text: str) -> bool:
    """True ONLY when *text* is provably a SINGLE plain-object-literal export.

    Whitelist (not blacklist): the config must be exactly ``module.exports = {…}``
    or ``export default {…}`` — one statement, balanced braces, nothing else
    before or after (only optional ``;``/whitespace) — and the object body must
    reference no discovery key and no dynamic/composition construct. This refuses
    evasions a blacklist misses, e.g. a second statement mutating the export
    (``module.exports = {}; module.exports['test'+'Match'] = […]``). Total.
    """
    code = _strip_js_comments_and_strings(text).strip()
    for prefix in ("module.exports", "export default"):
        if not code.startswith(prefix):
            continue
        rest = code[len(prefix):].lstrip()
        if prefix == "module.exports":
            if not rest.startswith("="):
                return False
            rest = rest[1:].lstrip()
        if not rest.startswith("{"):
            return False
        # Match the object literal via brace counting.
        depth, end = 0, -1
        for idx, ch in enumerate(rest):
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    end = idx
                    break
        if end < 0:
            return False  # unbalanced
        body = rest[: end + 1]
        trailing = rest[end + 1 :].strip().strip(";").strip()
        if trailing:
            return False  # extra statements/assignments after the literal
        # The object body must be a plain literal with no discovery/dynamic bits.
        if _JS_RUNNER_DISCOVERY_RE.search(body) or _JS_RUNNER_UNRESOLVABLE_RE.search(body):
            return False
        return True
    return False


def _js_config_text_has_custom_discovery(config_file: Path) -> bool:
    """True when a JS/TS config CANNOT be proven a trivial default literal.

    We cannot execute a ``jest.config.js`` / ``vitest.config.ts`` in Python, so
    (issue #1903 review round 7) we use a POSITIVE whitelist: trust DEFAULT
    discovery ONLY when the config text is a single plain-object-literal export
    with no discovery keys and no dynamic/composition constructs
    (:func:`_js_config_is_trivial_default_literal`). ANY other shape — extra
    statements, dynamic key construction, imports/require/spread/preset/function,
    or an unreadable file — returns True so the caller conservatively refuses to
    claim a co-located path is collected rather than risk a false-green.
    """
    try:
        text = config_file.read_text(encoding="utf-8", errors="ignore")
    except (OSError, ValueError):
        return True  # unreadable opaque config -> cannot prove default -> refuse
    # Check discovery keys against the ORIGINAL text (round 8): string-stripping
    # would erase a QUOTED property key like ``"testMatch"``, so a discovery key
    # anywhere in the raw text — quoted or not — forces refusal (a discovery word
    # inside a string VALUE only over-refuses, which is safe).
    if _JS_RUNNER_DISCOVERY_RE.search(text):
        return True
    return not _js_config_is_trivial_default_literal(text)


class _StaticJsLiteralParser:
    """Parse only closed, side-effect-free JS literals used by runner configs."""

    def __init__(self, text: str) -> None:
        self.tokens = self._tokenize(text)
        self.index = 0
        self.bindings: dict[str, tuple[Any, set[str]]] = {}

    @staticmethod
    def _tokenize(text: str) -> list[tuple[str, str]]:
        tokens: list[tuple[str, str]] = []
        index = 0
        while index < len(text):
            char = text[index]
            if char.isspace():
                index += 1
                continue
            if text.startswith("//", index):
                newline = text.find("\n", index + 2)
                index = len(text) if newline < 0 else newline + 1
                continue
            if text.startswith("/*", index):
                end = text.find("*/", index + 2)
                if end < 0:
                    raise ValueError("unterminated comment")
                index = end + 2
                continue
            if char in "'\"":
                start = index
                quote = char
                index += 1
                escaped = False
                while index < len(text):
                    current = text[index]
                    index += 1
                    if escaped:
                        escaped = False
                    elif current == "\\":
                        escaped = True
                    elif current == quote:
                        break
                else:
                    raise ValueError("unterminated string")
                raw = text[start:index]
                try:
                    value = ast.literal_eval(raw)
                except (SyntaxError, ValueError) as exc:
                    raise ValueError("unsupported string") from exc
                if not isinstance(value, str):
                    raise ValueError("non-string literal")
                tokens.append(("string", value))
                continue
            match = re.match(r"[A-Za-z_$][A-Za-z0-9_$]*", text[index:])
            if match:
                value = match.group(0)
                tokens.append(("ident", value))
                index += len(value)
                continue
            match = re.match(r"-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?", text[index:])
            if match:
                value = match.group(0)
                tokens.append(("number", value))
                index += len(value)
                continue
            if char not in "{}[]():,;.=+":
                raise ValueError("dynamic token")
            tokens.append((char, char))
            index += 1
        return tokens

    def _peek(self, kind: str, value: Optional[str] = None) -> bool:
        if self.index >= len(self.tokens):
            return False
        token_kind, token_value = self.tokens[self.index]
        return token_kind == kind and (value is None or token_value == value)

    def _take(self, kind: str, value: Optional[str] = None) -> str:
        if not self._peek(kind, value):
            raise ValueError("unexpected token")
        token_value = self.tokens[self.index][1]
        self.index += 1
        return token_value

    def _expression(self) -> tuple[Any, set[str]]:
        value, references = self._primary()
        while self._peek("+"):
            self._take("+")
            right, right_references = self._primary()
            if not isinstance(value, str) or not isinstance(right, str):
                raise ValueError("non-string concatenation")
            value += right
            references.update(right_references)
        if self._peek("."):
            self._take(".")
            self._take("ident", "join")
            self._take("(")
            separator = self._take("string")
            self._take(")")
            if not isinstance(value, list) or not all(
                isinstance(item, str) for item in value
            ):
                raise ValueError("non-literal join")
            value = separator.join(value)
        return value, references

    def _primary(self) -> tuple[Any, set[str]]:
        if self._peek("string"):
            return self._take("string"), set()
        if self._peek("number"):
            return json.loads(self._take("number")), set()
        if self._peek("ident"):
            name = self._take("ident")
            if name in {"true", "false", "null"}:
                return {"true": True, "false": False, "null": None}[name], set()
            if name not in self.bindings:
                raise ValueError("unbound identifier")
            return self.bindings[name][0], {name}
        if self._peek("["):
            return self._array()
        if self._peek("{"):
            return self._object()
        raise ValueError("non-literal expression")

    def _array(self) -> tuple[list[Any], set[str]]:
        self._take("[")
        values: list[Any] = []
        references: set[str] = set()
        while not self._peek("]"):
            value, item_references = self._expression()
            values.append(value)
            references.update(item_references)
            if not self._peek(","):
                break
            self._take(",")
            if self._peek("]"):
                break
        self._take("]")
        return values, references

    def _object(self) -> tuple[dict[str, Any], set[str]]:
        self._take("{")
        values: dict[str, Any] = {}
        references: set[str] = set()
        while not self._peek("}"):
            if self._peek("["):
                self._take("[")
                key, key_references = self._expression()
                self._take("]")
                if not isinstance(key, str):
                    raise ValueError("non-string key")
                references.update(key_references)
            elif self._peek("string"):
                key = self._take("string")
            else:
                key = self._take("ident")
            self._take(":")
            value, value_references = self._expression()
            if key in values:
                raise ValueError("duplicate key")
            values[key] = value
            references.update(value_references)
            if not self._peek(","):
                break
            self._take(",")
            if self._peek("}"):
                break
        self._take("}")
        return values, references

    def parse_export(self) -> dict[str, Any]:
        """Return the sole exported object, rejecting unused/unrelated bindings."""
        while self._peek("ident", "const"):
            self._take("ident", "const")
            name = self._take("ident")
            self._take("=")
            value, references = self._expression()
            if name in self.bindings:
                raise ValueError("duplicate binding")
            self.bindings[name] = (value, references)
            if self._peek(";"):
                self._take(";")

        if self._peek("ident", "module"):
            self._take("ident", "module")
            self._take(".")
            self._take("ident", "exports")
            self._take("=")
        else:
            self._take("ident", "export")
            self._take("ident", "default")
        exported, direct_references = self._expression()
        if self._peek(";"):
            self._take(";")
        if self.index != len(self.tokens) or not isinstance(exported, dict):
            raise ValueError("not one exported object")

        used = set(direct_references)
        pending = list(direct_references)
        while pending:
            name = pending.pop()
            for dependency in self.bindings[name][1]:
                if dependency not in used:
                    used.add(dependency)
                    pending.append(dependency)
        if used != set(self.bindings):
            raise ValueError("unrelated binding")
        return exported


def _parse_static_js_runner_config(config_file: Path) -> Optional[Mapping[str, Any]]:
    """Parse only discovery fields in the actual exported static config object."""
    try:
        text = config_file.read_text(encoding="utf-8", errors="ignore")
        exported = _StaticJsLiteralParser(text).parse_export()
    except (OSError, ValueError):
        return None

    discovery_names = {
        "testMatch",
        "testRegex",
        "roots",
        "rootDir",
        "testPathIgnorePatterns",
        "include",
        "exclude",
    }

    def has_nested_discovery(value: Any) -> bool:
        if isinstance(value, Mapping):
            return any(
                key in discovery_names or has_nested_discovery(item)
                for key, item in value.items()
            )
        if isinstance(value, list):
            return any(has_nested_discovery(item) for item in value)
        return False

    parsed: dict[str, Any] = {}
    for key in ("testMatch", "testRegex", "roots", "testPathIgnorePatterns"):
        if key in exported:
            value = exported[key]
            if not isinstance(value, (str, list)) or (
                isinstance(value, list)
                and not all(isinstance(item, str) for item in value)
            ):
                return None
            parsed[key] = value
    if "rootDir" in exported:
        if not isinstance(exported["rootDir"], str):
            return None
        parsed["rootDir"] = exported["rootDir"]

    vitest = exported.get("test")
    if vitest is not None:
        if not isinstance(vitest, Mapping):
            return None
        if set(vitest) - {"include", "exclude"}:
            return None
        for source_key, target_key in (
            ("include", "testMatch"),
            ("exclude", "testPathIgnorePatterns"),
        ):
            if source_key not in vitest:
                continue
            value = vitest[source_key]
            if not isinstance(value, (str, list)) or (
                isinstance(value, list)
                and not all(isinstance(item, str) for item in value)
            ):
                return None
            parsed[target_key] = value

    # Presets/projects and discovery keys hidden below an unrelated option can
    # change collection without the top-level fields parsed above. Other
    # side-effect-free scalar options (for example testEnvironment) are safe.
    for key, value in exported.items():
        if key == "test" or key in discovery_names:
            continue
        if key in {"preset", "projects", "workspace"} or has_nested_discovery(value):
            return None
    return parsed


def _collect_js_runner_config(
    module_path: Path, root_resolved: Path
) -> tuple[Mapping[str, Any], Optional[Path], bool]:
    """Return the nearest jest/vitest config, its directory, and an opaque flag.

    Walks from the module's directory up to (and including) *root_resolved*,
    reading ``jest.config.json`` / ``.jestrc`` / ``.jestrc.json`` and the
    ``package.json`` ``"jest"``/``"vitest"`` block (nearest wins). A JS/TS config
    file (``jest.config.js``/``.ts``, ``vitest.config.*``) is parsed only when it
    is a complete side-effect-free literal program whose sole export can be
    proven structurally. The third return value (``opaque_custom``) is ``True``
    for every unsupported/dynamic shape, signalling the caller to refuse to
    claim a path is collected. Returns ``({}, None, False)`` when no config is
    found. Total.
    """
    try:
        current = module_path.parent.resolve()
    except (OSError, RuntimeError):
        return {}, None, False
    root_s = str(root_resolved)
    while True:
        # Gather EVERY runner-config source AT THIS LEVEL. When more than one
        # exists (e.g. an inline package.json jest block AND a vitest.config.ts),
        # the ACTIVE runner is ambiguous — a different source could set different
        # discovery — so fail closed (opaque) rather than let one hide another
        # (issue #1903 review round 7).
        json_config: Optional[Mapping[str, Any]] = None
        for fname in ("jest.config.json", ".jestrc", ".jestrc.json"):
            candidate = current / fname
            if candidate.is_file():
                try:
                    data = json.loads(
                        candidate.read_text(encoding="utf-8", errors="ignore")
                    )
                    if isinstance(data, Mapping):
                        json_config = data
                        break
                except (OSError, ValueError):
                    pass
        pkg = current / "package.json"
        pkg_block = _jest_config_from_package_json(pkg) if pkg.is_file() else None
        # Collect EVERY JS/TS config file at this level (round 8) — e.g. both a
        # ``jest.config.js`` AND a ``vitest.config.ts`` — so two distinct runner
        # config files count as two sources rather than the loop silently keeping
        # only the first and missing the ambiguity.
        js_config_files: list[Path] = []
        for stem in _JS_RUNNER_CONFIG_FILE_STEMS:
            for ext in (".js", ".ts", ".mjs", ".cjs", ".mts", ".cts"):
                jsfile = current / f"{stem}{ext}"
                if jsfile.is_file():
                    js_config_files.append(jsfile)

        source_count = (
            (1 if json_config is not None else 0)
            + (1 if pkg_block is not None else 0)
            + len(js_config_files)
        )
        if source_count > 1:
            return {}, current, True  # ambiguous active runner -> refuse
        if json_config is not None:
            return json_config, current, False
        if pkg_block is not None:
            return pkg_block, current, False
        if js_config_files:
            parsed = _parse_static_js_runner_config(js_config_files[0])
            if parsed is not None:
                return parsed, current, False
            return {}, current, True

        if str(current) == root_s or not _contained_in_root(current, root_resolved):
            break
        parent = current.parent
        if parent == current:
            break
        current = parent
    return {}, None, False


def _micromatch_to_regex(glob: str) -> Optional[str]:
    """Translate a jest/micromatch ``testMatch`` glob to an anchored regex.

    Single pass. Handles the constructs jest's default and typical custom
    ``testMatch`` use: ``**``/``**/`` globstar, ``*``, ``?``, extglobs
    ``?(...)`` ``*(...)`` ``+(...)`` ``@(...)`` (with their quantifiers applied
    to the group), brace alternation ``{a,b}``, ``|`` alternation inside groups,
    and character classes ``[...]``. Returns ``None`` for negation ``!(...)`` (we
    refuse to guess). ``<rootDir>`` must already be substituted by the caller.
    """
    out = ["^"]
    # Parallel stacks per open group: the trailing regex quantifier ("", "?",
    # "*", "+") and the group KIND. Kind matters because alternation differs by
    # construct: BRACES ``{a,b}`` alternate on COMMA (pipe is literal), while
    # EXTGLOBS ``@(a|b)`` / plain parens alternate on PIPE (comma is literal) —
    # issue #1903 review round 5.
    group_quant: list[str] = []
    group_kind: list[str] = []  # "brace" | "extglob" | "paren"
    i, n = 0, len(glob)
    while i < n:
        c = glob[i]
        if c == "!" and glob[i + 1 : i + 2] == "(":
            return None  # negation — refuse to guess
        if c in "?*+@" and glob[i + 1 : i + 2] == "(":
            group_quant.append({"?": "?", "*": "*", "+": "+", "@": ""}[c])
            group_kind.append("extglob")
            out.append("(?:")
            i += 2
            continue
        if c == "*":
            # ``**`` is a GLOBSTAR (crosses ``/``) ONLY when it is a whole path
            # segment — preceded by ``/`` or start AND followed by ``/`` or end
            # (round 9). micromatch treats ``**`` embedded in a segment (``qa**/``,
            # ``**bar``, ``foo**``) as a plain single-segment ``*``, so translating
            # every ``**`` to ``.*`` over-matches paths jest rejects (an uncollected
            # green). ``[^/]*`` keeps embedded stars segment-local.
            is_double = glob[i : i + 2] == "**"
            at_seg_start = i == 0 or glob[i - 1] == "/"
            after_double = glob[i + 2 : i + 3]
            if is_double and at_seg_start and after_double == "/":
                out.append("(?:.*/)?")
                i += 3
            elif is_double and at_seg_start and after_double == "":
                out.append(".*")  # trailing whole-segment ``**`` -> match subtree
                i += 2
            elif is_double:
                out.append("[^/]*")  # embedded ``**`` == single-segment ``*``
                i += 2
            else:
                out.append("[^/]*")
                i += 1
            continue
        if c == "?":
            out.append("[^/]")
            i += 1
            continue
        if c == "(":
            group_quant.append("")
            group_kind.append("paren")
            out.append("(?:")
            i += 1
            continue
        if c == ")":
            out.append(")")
            out.append(group_quant.pop() if group_quant else "")
            if group_kind:
                group_kind.pop()
            i += 1
            continue
        if c == "|":
            # Alternation only inside an extglob/paren group; elsewhere literal.
            inside = group_kind and group_kind[-1] in ("extglob", "paren")
            out.append("|" if inside else r"\|")
            i += 1
            continue
        if c == "{":
            group_quant.append("")
            group_kind.append("brace")
            out.append("(?:")
            i += 1
            continue
        if c == "}":
            out.append(")")
            out.append(group_quant.pop() if group_quant else "")
            if group_kind:
                group_kind.pop()
            i += 1
            continue
        if c == ",":
            # Alternation only inside a brace group; elsewhere literal.
            inside_brace = group_kind and group_kind[-1] == "brace"
            out.append("|" if inside_brace else ",")
            i += 1
            continue
        if c == "[":
            # micromatch/bash character class. A leading ``!`` (or ``^``) means
            # NEGATION — translate to Python's ``[^...]`` (``[!_]`` = "not _", NOT
            # "``!`` or ``_``"). ``]`` as the FIRST class member is a literal.
            start = i + 1
            neg = start < n and glob[start] in "!^"
            scan = start + 1 if neg else start
            if scan < n and glob[scan] == "]":  # literal ] as first member
                scan += 1
            j = glob.find("]", scan)
            if j == -1:  # malformed / unterminated -> literal '['
                out.append(r"\[")
                i += 1
                continue
            inner = glob[(start + 1 if neg else start):j]
            out.append("[^" + inner + "]" if neg else "[" + inner + "]")
            i = j + 1
            continue
        out.append(re.escape(c))
        i += 1
    out.append("$")
    return "".join(out)


try:  # `regex` (already a pdd dependency) supports a per-match wall-clock timeout
    import regex as _redos_regex  # type: ignore
    _HAVE_REDOS_REGEX = True
except ImportError:  # pragma: no cover - stdlib fallback (no timeout, caps only)
    _redos_regex = re  # type: ignore
    _HAVE_REDOS_REGEX = False

# Repo-controlled ``testMatch``/``testRegex``/``testPathIgnorePatterns`` are
# hosted/issue-influenced. Matching them with backtracking regex is a ReDoS
# vector (issue #1903 review round 4), so every such match runs with a strict
# wall-clock timeout and generous length caps, and FAILS CLOSED (``None``).
_REGEX_MATCH_TIMEOUT_S = 0.05
_REGEX_MAX_PATTERN_LEN = 4096
_REGEX_MAX_TEXT_LEN = 2048
# Aggregate-work caps for greenfield discovery (issue #1903 review rounds 5-6): a
# hostile config with very many patterns/roots/candidates must not stall sync.
# Bounded by BOTH element caps AND a single wall-clock budget for the whole
# discovery call (worst case ~ caps * per-match timeout is further capped here).
_MAX_RUNNER_PATTERNS = 32
_MAX_GREENFIELD_CANDIDATES = 24
_DISCOVERY_TOTAL_BUDGET_S = 1.0


def _safe_regex_search(pattern: Optional[str], text: str) -> Optional[bool]:
    """Timeout-bounded, fail-closed ``search`` for a repo-controlled pattern.

    Returns ``True``/``False`` on a decisive match, or ``None`` (fail closed) on
    a timeout (catastrophic backtracking), a compile error, or over-long input —
    so a malicious/pathological runner pattern can never stall sync.
    """
    if pattern is None or text is None:
        return None
    if len(pattern) > _REGEX_MAX_PATTERN_LEN or len(text) > _REGEX_MAX_TEXT_LEN:
        return None
    if not _HAVE_REDOS_REGEX:
        # No wall-clock-timeout engine available. A SHORT catastrophic pattern
        # (e.g. ``(a+)+$``) well under the length caps can still backtrack
        # exponentially in text length, so the caps alone do NOT bound stdlib
        # ``re``. Repo-controlled patterns are hosted/issue-influenced, so fail
        # closed rather than evaluate an untrusted regex without a timeout
        # (ReDoS; Codex review, PR #1998). ``regex`` is declared directly in
        # pyproject so this fallback is not reached in a normal install.
        return None
    try:
        return _redos_regex.search(
            pattern, text, timeout=_REGEX_MATCH_TIMEOUT_S
        ) is not None
    except (re.error, ValueError, RecursionError, TimeoutError):
        return None
    except Exception:  # pylint: disable=broad-except  (regex.TimeoutError etc.)
        return None


def _glob_matches(glob: str, posix_path: str) -> Optional[bool]:
    """Best-effort: does *posix_path* match jest ``testMatch`` *glob*?

    Returns ``True``/``False`` when the glob is translatable and matched within
    the ReDoS timeout, or ``None`` when it is not (negation, compile failure, or
    a timeout) so the caller stays conservative rather than guessing.
    """
    # Reject an oversized RAW glob BEFORE translation (round 8): a multi-megabyte
    # repo-controlled pattern would otherwise be fully scanned/expanded by
    # ``_micromatch_to_regex`` outside the regex timeout and aggregate deadline.
    if glob is None or len(glob) > _REGEX_MAX_PATTERN_LEN:
        return None
    return _safe_regex_search(_micromatch_to_regex(glob), posix_path)


def _sub_root_dir(value: str, root_dir: Path) -> str:
    """Substitute jest's ``<rootDir>`` token with the effective root directory."""
    return value.replace("<rootDir>", str(root_dir))


def _resolve_config_roots(
    config: Mapping[str, Any], config_dir: Path
) -> tuple[list[Path], Path]:
    """Resolve jest's effective ``rootDir`` and ``roots`` (absolute paths).

    *config_dir* is the ``<rootDir>`` base. Returns ``(roots, root_dir)``;
    ``roots`` defaults to ``[root_dir]`` when none are configured.
    """
    root_dir = config_dir
    root_dir_value = config.get("rootDir")
    if isinstance(root_dir_value, str) and root_dir_value:
        try:
            root_dir = (config_dir / root_dir_value).resolve()
        except (OSError, RuntimeError, ValueError):
            root_dir = config_dir
    roots: list[Path] = []
    for r in _as_str_list(config.get("roots")):
        try:
            # jest resolves a non-absolute ``roots`` entry against the EFFECTIVE
            # rootDir (path.resolve(rootDir, entry)), NOT the config directory
            # (issue #1903 review round 5). ``<rootDir>`` substitution yields an
            # absolute path that is used as-is.
            sub = _sub_root_dir(r, root_dir)
            p = Path(sub)
            roots.append((p if p.is_absolute() else (root_dir / sub)).resolve())
        except (OSError, RuntimeError, ValueError):
            continue
    return (roots or [root_dir]), root_dir


_GLOB_WILDCARD_CHARS = frozenset("*?[]{}()+@!")


def _testmatch_literal_dir(glob: str, root_dir: Path) -> Optional[Path]:
    """Literal directory prefix of a ``testMatch`` glob before its first wildcard.

    ``<rootDir>/test/**/*.test.ts`` -> ``<root>/test``. Returns ``None`` when the
    pattern has no fixed directory anchor. Used to derive a collected write
    location for a centralized (non-co-located) test layout (issue #1903 §A).
    """
    if glob is None or len(glob) > _REGEX_MAX_PATTERN_LEN:
        return None  # round 8: bound preprocessing of an oversized raw pattern
    sub = _sub_root_dir(glob, root_dir)
    idx = next((i for i, c in enumerate(sub) if c in _GLOB_WILDCARD_CHARS), len(sub))
    slash = sub.rfind("/", 0, idx)
    if slash <= 0:
        return None
    dir_str = sub[:slash]
    try:
        directory = Path(dir_str)
        if not directory.is_absolute():
            directory = root_dir / dir_str
        return directory.resolve()
    except (OSError, RuntimeError, ValueError):
        return None


def _module_rel_dir(
    module_path: Path, root_dir: Path, config_dir: Path
) -> Optional[Path]:
    """The module's directory relative to the effective rootDir (or config dir).

    Preserved under a centralized test anchor so a same-stem module in a
    different source directory does not collide onto one shared test path.
    Returns ``None`` when the module sits directly at the base (no relative
    component) or cannot be related to either base.
    """
    parent = module_path.parent
    for base in (root_dir, config_dir):
        try:
            rel = parent.relative_to(base)
        except (ValueError, TypeError):
            continue
        return None if str(rel) in ("", ".") else rel
    return None


def _greenfield_candidate_paths(
    module_path: Path, config: Mapping[str, Any], config_dir: Optional[Path]
) -> list[Path]:
    """Ordered first-test candidates, biased by config conventions.

    Co-located placements beside the module come first (the preferred layout).
    When the config declares ``roots``/``rootDir`` or a ``testMatch`` with a
    fixed directory prefix (a CENTRALIZED layout), also derive candidates UNDER
    those collected directories so a project whose runner does not collect
    co-located tests still gets a runner-collected path instead of a runner-blind
    ``tests/`` shadow (issue #1903 §A). ``_candidate_is_collected`` decides which
    survive; ordering only sets preference.
    """
    stem = module_path.stem
    ext = module_path.suffix
    # Bound the hint scan (round 8): only a fixed number of patterns, each a
    # bounded prefix, so a hostile multi-megabyte ``testMatch`` cannot turn this
    # substring probe into unbounded preprocessing work.
    _hint_pats = (
        _as_str_list(config.get("testMatch")) + _as_str_list(config.get("testRegex"))
    )[:_MAX_RUNNER_PATTERNS]
    hint = " ".join(p[:_REGEX_MAX_PATTERN_LEN] for p in _hint_pats).lower()

    if "spec" in hint and "test" not in hint:
        infixes = [".spec", ".test"]
    else:
        infixes = [".test", ".spec"]

    if "__tests__" in hint and "__test__" not in hint:
        subdirs = ["__tests__", "__test__", ""]
    else:
        subdirs = ["__test__", "__tests__", ""]

    def _variants(base: Path) -> list[Path]:
        out: list[Path] = []
        for infix in infixes:
            for sub in subdirs:
                anchored = base / sub if sub else base
                out.append(anchored / f"{stem}{infix}{ext}")
        return out

    candidates: list[Path] = list(_variants(module_path.parent))

    if config_dir is not None:
        roots, root_dir = _resolve_config_roots(config, config_dir)
        # Mirror the module's directory (relative to the effective rootDir) under
        # each centralized anchor so DISTINCT modules that share a stem
        # (``src/a/util.ts`` vs ``src/b/util.ts``) map to DISTINCT collected test
        # paths — never onto one shared file that a second sync would overwrite
        # (issue #1903 "never fork, never overwrite").
        rel_dir = _module_rel_dir(module_path, root_dir, config_dir)
        anchor_dirs: list[Path] = []
        for glob in _as_str_list(config.get("testMatch")):
            literal = _testmatch_literal_dir(glob, root_dir)
            if literal is not None:
                anchor_dirs.append(literal)
        if config.get("roots"):
            anchor_dirs.extend(roots)
        # An explicit rootDir centralizes collection under it — a module OUTSIDE
        # rootDir has no collected co-located path, so derive one under rootDir.
        if isinstance(config.get("rootDir"), str) and config.get("rootDir"):
            anchor_dirs.append(root_dir)
        seen = {str(c) for c in candidates}
        for anchor in anchor_dirs:
            base = anchor / rel_dir if rel_dir is not None else anchor
            for cand in _variants(base):
                key = str(cand)
                if key not in seen:
                    candidates.append(cand)
                    seen.add(key)
    return candidates


def _candidate_is_collected(
    candidate: Path,
    config: Mapping[str, Any],
    config_dir: Optional[Path],
    deadline: Optional[float] = None,
) -> Optional[bool]:
    """Would the runner collect a test written at *candidate*?

    Enforces the config knobs issue #1903 §A names — ``roots``/``rootDir``
    (containment), ``testPathIgnorePatterns`` (exclusion), and
    ``testMatch``/``testRegex`` (collection patterns). Returns ``True`` when
    collected, ``False`` when provably NOT collected (so the caller falls back to
    the derived path rather than emit an uncollected test), or ``None`` when the
    config gives no verdict (no relevant keys, or unparseable patterns) so the
    caller keeps the default-convention behavior. When *deadline* (a
    ``time.monotonic`` value) is passed and already exceeded, fails CLOSED
    (``False``) so aggregate regex work stays bounded (issue #1903 review r6).
    """
    if config_dir is None:
        return None
    if deadline is not None and time.monotonic() > deadline:
        return False
    posix = candidate.as_posix()
    resolved_roots, root_dir = _resolve_config_roots(config, config_dir)

    # roots / rootDir containment.
    if config.get("roots") or (
        isinstance(config.get("rootDir"), str) and config.get("rootDir")
    ):
        if not any(_contained_in_root(candidate, root) for root in resolved_roots):
            return False

    # testPathIgnorePatterns exclusion (repo-controlled regex over the path,
    # ReDoS-bounded). A match excludes; an UNEVALUABLE ignore pattern could also
    # exclude, so fail closed to "not collected" either way.
    for pat in _as_str_list(config.get("testPathIgnorePatterns")):
        if _safe_regex_search(_sub_root_dir(pat, root_dir), posix) is not False:
            return False

    # testMatch / testRegex collection patterns.
    match_globs = _as_str_list(config.get("testMatch"))
    test_regexes = _as_str_list(config.get("testRegex"))
    has_explicit = (
        config.get("testMatch") is not None or config.get("testRegex") is not None
    )
    if not has_explicit:
        # DEFAULT discovery: no explicit collection constraint -> no verdict; the
        # caller applies the dialect-aware default-extension gate and default
        # convention.
        return None
    # jest rejects configuring BOTH testMatch and testRegex -> fail closed.
    if match_globs and test_regexes:
        return False
    # An EXPLICIT but empty collection set (``testMatch: []`` / ``testRegex: []``)
    # matches NOTHING in jest -> not collected here (issue #1903 review round 5).
    if not match_globs and not test_regexes:
        return False

    # EXPLICIT patterns are present (default discovery already returned above).
    # From here NEVER return ``None`` (which would mark the candidate a
    # default-convention fallback): an explicit-rule miss or an unevaluable rule
    # must FAIL CLOSED to ``False`` so the caller refuses rather than emit an
    # uncollected path (issue #1903 review round 3).
    #
    # jest/micromatch apply ``testMatch`` SEQUENTIALLY: a positive glob includes,
    # a leading-``!`` glob EXCLUDES, and a LATER match overrides an earlier one
    # (negative-then-positive re-includes, positive-then-negative excludes).
    included: Optional[bool] = None
    for glob in match_globs:
        if deadline is not None and time.monotonic() > deadline:
            return False  # aggregate budget exhausted mid-candidate -> fail closed
        g = _sub_root_dir(glob, root_dir)
        negated = g.startswith("!")
        matched = _glob_matches(g[1:] if negated else g, posix)
        if matched is None:
            return False  # cannot evaluate a rule whose position matters -> closed
        if matched:
            included = not negated
    for rgx in test_regexes:
        if deadline is not None and time.monotonic() > deadline:
            return False
        res = _safe_regex_search(_sub_root_dir(rgx, root_dir), posix)
        if res is None:
            return False  # unevaluable / timed-out regex -> fail closed
        if res:
            included = True
    return bool(included)  # True = collected; explicit miss / excluded -> False


def _project_uses_vitest(module_path: Path, root_resolved: Path) -> bool:
    """True when the detected runner is vitest (vs jest).

    Walks module dir -> root looking for a ``vitest.config.*``/``vite.config.*``
    file or a ``package.json`` that declares a ``vitest`` dependency / inline
    ``vitest`` config block. Used only to widen the DEFAULT-discovery extension
    set (vitest's default ``include`` collects ``.mjs``/``.cjs``; jest's does
    not). Total — any error yields ``False`` (treat as jest, the stricter set).
    """
    try:
        current = module_path.parent.resolve()
    except (OSError, RuntimeError):
        return False
    root_s = str(root_resolved)
    while True:
        for stem in ("vitest.config", "vite.config"):
            for ext in (".js", ".ts", ".mjs", ".cjs", ".mts", ".cts"):
                if (current / f"{stem}{ext}").is_file():
                    return True
        pkg = current / "package.json"
        if pkg.is_file():
            try:
                data = json.loads(pkg.read_text(encoding="utf-8", errors="ignore"))
            except (OSError, ValueError):
                data = None
            if isinstance(data, Mapping):
                if isinstance(data.get("vitest"), Mapping):
                    return True
                for dep_key in ("dependencies", "devDependencies",
                                "peerDependencies", "optionalDependencies"):
                    deps = data.get(dep_key)
                    if isinstance(deps, Mapping) and "vitest" in deps:
                        return True
        if str(current) == root_s or not _contained_in_root(current, root_resolved):
            break
        parent = current.parent
        if parent == current:
            break
        current = parent
    return False


def _semver_clause_min_major(clause: str) -> Optional[int]:
    """The guaranteed-minimum major of ONE AND-clause (space-separated
    comparators), or ``None`` when the clause has NO lower bound (only ``<``/
    ``<=``/``*``). Round 10: conservative — an upper-bound-only or wildcard clause
    admits arbitrarily low majors."""
    tokens = clause.split()
    if "-" in tokens:  # hyphen range "A - B": the lower bound is A
        idx = tokens.index("-")
        if idx > 0:
            m = re.search(r"(\d+)", tokens[idx - 1])
            return int(m.group(1)) if m else None
        return None
    lower: Optional[int] = None
    for tok in tokens:
        t = tok.strip()
        if not t or t in ("*", "x", "X", "latest"):
            continue
        if t.startswith("<"):
            continue  # upper bound, not a lower bound
        mm = re.match(r"^(?:\^|~|>=|>|=|v)?\s*(\d+)", t)
        if mm:
            maj = int(mm.group(1))
            lower = maj if lower is None else max(lower, maj)
    return lower


def _semver_range_min_major(range_str: str) -> int:
    """The guaranteed-minimum MAJOR across a full npm range (``||`` union), i.e.
    the lowest major any satisfying install could have (round 10). ``0`` when the
    range cannot guarantee a floor (``"<30"``, ``"*"``, ``"latest"``, ``""``, or a
    ``||`` alternative with no lower bound), so the caller enables version-gated
    defaults ONLY when the WHOLE range is provably >= the required major."""
    if not range_str or not range_str.strip():
        return 0
    mins: list[int] = []
    for alt in range_str.split("||"):
        cm = _semver_clause_min_major(alt)
        if cm is None:
            return 0  # an alternative admits arbitrarily low majors -> no floor
        mins.append(cm)
    return min(mins) if mins else 0


def _detected_jest_major(module_path: Path, root_resolved: Path) -> Optional[int]:
    """The GUARANTEED-MINIMUM declared jest major from the nearest package.json,
    or ``None`` when no jest dependency is declared. Parses the full npm range
    conservatively (round 10): ``"<30"`` -> 0, ``"^30 || ^29"`` -> 29, ``"^30"``
    -> 30 — so a caller enabling jest-30-only discovery never certifies an
    uncollected test on a range that could install jest <=29. Total."""
    try:
        current = module_path.parent.resolve()
    except (OSError, RuntimeError):
        return None
    root_s = str(root_resolved)
    while True:
        pkg = current / "package.json"
        if pkg.is_file():
            try:
                data = json.loads(pkg.read_text(encoding="utf-8", errors="ignore"))
            except (OSError, ValueError):
                data = None
            if isinstance(data, Mapping):
                for dep_key in ("dependencies", "devDependencies",
                                "peerDependencies", "optionalDependencies"):
                    deps = data.get(dep_key)
                    if isinstance(deps, Mapping) and isinstance(deps.get("jest"), str):
                        return _semver_range_min_major(deps["jest"])
        if str(current) == root_s or not _contained_in_root(current, root_resolved):
            break
        parent = current.parent
        if parent == current:
            break
        current = parent
    return None


_DEFAULT_RUNNER_IGNORED_SEGMENTS = frozenset({"node_modules"})


def _has_default_ignored_segment(candidate: Path, root_resolved: Path) -> bool:
    """True when *candidate* lies under a directory BOTH jest and vitest exclude
    from default discovery (``node_modules``) — round 10. Checked on the path
    RELATIVE to the project root so a root that legitimately sits under such a
    name does not force-refuse everything."""
    try:
        rel = candidate.resolve().relative_to(root_resolved)
    except (ValueError, OSError, RuntimeError):
        return False
    return any(seg in _DEFAULT_RUNNER_IGNORED_SEGMENTS for seg in rel.parts)


def find_runner_collected_test_path(code_file: str | Path) -> Optional[Path]:
    """Greenfield runner-aware first-test path for a NEW JS/TS module (#1903 §A).

    When no co-located test yet exists (:func:`find_collocated_test` returns
    ``None``) but the project configures a jest/vitest runner, return the
    co-located path the runner will actually collect so the FIRST generated test
    lands where ``npm test`` looks instead of a runner-blind root ``tests/``
    shadow (the primary false-green in issue #1903). The write location honors
    JSON-readable config: ``testMatch``/``testRegex`` pick the ``.test``/``.spec``
    + ``__test__``/``__tests__`` convention, and ``roots``/``rootDir``/
    ``testPathIgnorePatterns`` are enforced so a custom layout never yields an
    UNCOLLECTED test — if no candidate would be collected, return ``None`` (the
    sink records needs-review and selects no test). For a CENTRALIZED layout (``roots``/``rootDir`` or
    a ``testMatch`` with a fixed directory prefix) a collected path UNDER the
    configured directory is derived instead of a co-located one, so the test
    still lands where the runner looks. When the runner is configured only by a
    JS file (``jest.config.js``, unparseable in Python): if that file's text
    references NO discovery key the jest-default convention
    ``__test__/{stem}.test.{ext}`` is used (jest's default ``testMatch`` collects
    it); if it DOES customize discovery (``testMatch``/``roots``/... we cannot
    parse) we conservatively return ``None`` rather than claim an unproven path is
    collected. Python keeps its pytest-idiomatic ``tests/`` default (unchanged).
    Any other language, or no detectable runner, yields ``None``.

    The module path is caller/issue-influenced, so it flows through
    :func:`_validated_project_path` (CWE-022) before any filesystem use and the
    returned write-target is re-asserted in-root. Never raises: any error path
    returns ``None`` (no greenfield write authority).
    """
    try:
        root_resolved = Path.cwd().resolve()
        module_path = _validated_project_path(code_file, root=root_resolved)
        if module_path is None:
            return None
        if module_path.suffix.lower() not in _JS_TS_EXTENSIONS:
            return None
        if not _project_uses_js_test_runner(module_path, root_resolved):
            return None

        config, config_dir, opaque_custom = _collect_js_runner_config(
            module_path, root_resolved
        )
        # An unparseable JS/TS config that customizes discovery: we cannot prove
        # where tests are collected, so refuse to select a write target rather
        # than guess the default.
        if opaque_custom:
            return None
        # A parseable config that composes discovery in ways we do not resolve
        # (jest ``projects`` multi-project, or a vitest ``test``/``include``/
        # ``exclude`` block) — refuse rather than risk certifying an uncollected
        # path.
        if isinstance(config, Mapping) and any(
            config.get(k) is not None
            for k in ("projects", "workspace", "include", "exclude")
        ):
            return None
        # Bound AGGREGATE discovery work (issue #1903 review round 5): candidates
        # x repo-controlled patterns, each with a ReDoS timeout, is O(P^2); a
        # hostile config with a huge pattern/root count could still stall an
        # issue-driven sync for minutes. Refuse when the declared pattern/root
        # count is implausibly large rather than spend the budget.
        if isinstance(config, Mapping):
            declared_patterns = sum(
                len(_as_str_list(config.get(k)))
                for k in ("testMatch", "testRegex", "testPathIgnorePatterns", "roots")
            )
            if declared_patterns > _MAX_RUNNER_PATTERNS:
                return None
        # DEFAULT-convention safety: when the config declares no explicit
        # ``testMatch``/``testRegex`` (so placement relies on the runner's
        # default discovery), only a module whose extension the DEFAULT collects
        # is eligible. jest's default collects js/jsx/ts/tsx; vitest's default
        # ``include`` ALSO collects mjs/cjs — so widen the set for a vitest
        # project (issue #1903 review round 3).
        has_explicit_match = isinstance(config, Mapping) and (
            config.get("testMatch") is not None or config.get("testRegex") is not None
        )
        default_exts = (".js", ".jsx", ".ts", ".tsx")
        # vitest's default ``include`` collects mjs/cjs; jest's default collects
        # them only from v30+ (v30 added `[mc]` to the default testMatch). Widen
        # the default set accordingly; an UNKNOWN jest version stays strict
        # (refuse mjs/cjs) since jest <=29 would not collect them (#1903 review).
        # Widen to mjs/cjs ONLY when the ACTIVE runner unambiguously collects
        # them: jest>=30 (any project), OR vitest with NO jest present. A project
        # with jest<=29 AND a vitest dependency is AMBIGUOUS (a jest run would not
        # collect .mjs) -> fail closed, refuse (issue #1903 review round 6).
        jest_major = _detected_jest_major(module_path, root_resolved)
        allow_mc = (jest_major is not None and jest_major >= 30) or (
            jest_major is None and _project_uses_vitest(module_path, root_resolved)
        )
        if allow_mc:
            default_exts = default_exts + (".mjs", ".cjs")
        if not has_explicit_match and module_path.suffix.lower() not in default_exts:
            return None
        candidates = _greenfield_candidate_paths(module_path, config, config_dir)[
            :_MAX_GREENFIELD_CANDIDATES
        ]

        # Single wall-clock budget for the whole discovery call so an adversarial
        # config of many near-timeout patterns cannot accumulate minutes of work
        # (issue #1903 review round 6). On exhaustion, fail closed.
        deadline = time.monotonic() + _DISCOVERY_TOTAL_BUDGET_S
        fallback_default: Optional[Path] = None
        for candidate in candidates:
            resolved = _validated_project_path(candidate, root=root_resolved)
            if resolved is None or not _contained_in_root(resolved, root_resolved):
                continue
            if resolved == module_path:
                continue
            # Default runner ignore (round 10): both jest (default
            # ``testPathIgnorePatterns: ["/node_modules/"]``) and vitest (default
            # ``exclude`` includes ``**/node_modules/**``) never collect a test
            # under ``node_modules`` — so a co-located candidate there would be a
            # false-green even when the filename convention matches.
            if _has_default_ignored_segment(resolved, root_resolved):
                continue
            if time.monotonic() > deadline:
                return fallback_default  # budget exhausted -> stop, best-so-far
            verdict = _candidate_is_collected(resolved, config, config_dir, deadline)
            if verdict is True:
                return resolved
            if verdict is False:
                continue
            # verdict is None (no config verdict): remember the first valid
            # default-convention candidate but keep looking for a proven match.
            if fallback_default is None:
                fallback_default = resolved
        return fallback_default
    except Exception:  # pylint: disable=broad-except
        return None


def _existing_collocated_is_collected(
    module_path: Path, sibling: Path, root_resolved: Path
) -> Optional[bool]:
    """Would the configured runner COLLECT an EXISTING co-located *sibling*?

    Adoption (issue #1903 §B) must not blindly retarget onto a co-located file the
    project's runner does not actually collect — e.g. a stale
    ``src/__test__/page.test.ts`` under a Jest ``testMatch: ["qa/**/*.spec.ts"]``
    — which would just preserve the false-green on an EXCLUDED file (review round
    9). Returns ``True`` (collected), ``False`` (a configured runner PROVABLY
    excludes it), or ``None`` (no evaluable JS/TS runner config — Python, no
    runner, or an opaque/composed config we cannot resolve). A configured runner
    plus ``None`` is not adoption authority; the caller suppresses test output
    unless a bounded placement decision proves a collected path. Never raises.
    """
    try:
        if module_path.suffix.lower() not in _JS_TS_EXTENSIONS:
            return None
        if not _project_uses_js_test_runner(module_path, root_resolved):
            return None
        config, config_dir, opaque_custom = _collect_js_runner_config(
            module_path, root_resolved
        )
        if opaque_custom or not isinstance(config, Mapping):
            return None  # cannot parse -> cannot prove exclusion -> adopt
        if any(
            config.get(k) is not None
            for k in ("projects", "workspace", "include", "exclude")
        ):
            return None  # composed discovery we do not resolve -> adopt
        deadline = time.monotonic() + _DISCOVERY_TOTAL_BUDGET_S
        verdict = _candidate_is_collected(sibling, config, config_dir, deadline)
        if verdict is not None:
            return verdict

        # With no explicit collection matcher, ``None`` means the ordinary
        # runner defaults apply. Preserve an existing human-authored sibling
        # whenever it is one of our bounded default-convention candidates.
        # (Comparing only with ``find_runner_collected_test_path`` is too narrow:
        # that helper returns the FIRST candidate, while a collected sibling may
        # legitimately use another default layout such as ``page.test.tsx``.)
        if config.get("testMatch") is not None or config.get("testRegex") is not None:
            return None
        default_exts = (".js", ".jsx", ".ts", ".tsx")
        jest_major = _detected_jest_major(module_path, root_resolved)
        if (jest_major is not None and jest_major >= 30) or (
            jest_major is None and _project_uses_vitest(module_path, root_resolved)
        ):
            default_exts += (".mjs", ".cjs")
        if module_path.suffix.lower() not in default_exts:
            return False
        if _has_default_ignored_segment(sibling, root_resolved):
            return False
        sibling_resolved = _validated_project_path(sibling, root=root_resolved)
        if sibling_resolved is None:
            return False
        candidates = _greenfield_candidate_paths(module_path, config, config_dir)[
            :_MAX_GREENFIELD_CANDIDATES
        ]
        return any(
            _validated_project_path(candidate, root=root_resolved) == sibling_resolved
            for candidate in candidates
        )
    except Exception:  # pylint: disable=broad-except
        return None


PDD_TEST_OUTPUT_NEEDS_REVIEW_MARKER = "PDD_TEST_OUTPUT_NEEDS_REVIEW"


def _configured_js_runner_is_unresolved(code_file: str | Path) -> bool:
    """True when a detected JS/TS runner has no provable collected test path."""
    try:
        root_resolved = Path.cwd().resolve()
        module_path = _validated_project_path(code_file, root=root_resolved)
        return bool(
            module_path is not None
            and module_path.suffix.lower() in _JS_TS_EXTENSIONS
            and _project_uses_js_test_runner(module_path, root_resolved)
            and find_runner_collected_test_path(module_path) is None
        )
    except Exception:  # pylint: disable=broad-except
        return False


def unresolved_test_output_review_note(code_file: str | Path) -> str:
    """Return the stable operator-facing note for a suppressed test output."""
    return (
        f"test generation needs review for `{Path(code_file).name}`: a configured "
        "JavaScript/TypeScript runner was detected, but its effective collection "
        "path could not be proven safely; no unverified test path was selected or "
        "written"
    )


def resolve_test_output_path(
    code_file: str | Path,
    derived_test_path: str | Path,
    *,
    user_pinned: bool,
) -> Optional[Path]:
    """Adopt an existing co-located test as the canonical test path (issue #1903).

    PDD derives its test-output path from ``.pddrc`` / defaults, blind to the
    project's real test runner, so on a jest/Next.js project it maintains a
    ``tests/`` shadow while the co-located test the runner collects goes stale
    (a false-green). When a single unambiguous co-located test exists, return
    it so generate/change/sync target the real file instead. When NO co-located
    test exists yet but the project configures a jest/vitest runner (greenfield,
    issue #1903 §A), return the co-located path the runner will collect
    (``{module_dir}/__test__/{stem}.test.{ext}``) so the FIRST test lands where
    the runner looks — never a root ``tests/`` orphan.

    Args:
        code_file: The module under test.
        derived_test_path: The test path PDD derived from config/defaults.
        user_pinned: ``True`` when the user explicitly pinned the path (CLI
            ``--output`` or an explicit ``.pddrc test_output_path``); such
            paths are returned unchanged.

    Returns:
        The adopted/proven runner-collected test, the explicit/ordinary derived
        path, or ``None`` when a configured JS/TS runner is detected but no path
        can be proven collected. ``None`` is a structured non-write decision:
        callers continue while flagging the module for review. Never raises.
    """
    derived = Path(derived_test_path)
    if user_pinned:
        return derived
    try:
        matches = _collocated_test_matches(code_file)
        if len(matches) != 1:
            # ZERO existing co-located tests -> greenfield-eligible. AMBIGUOUS
            # (>1) is NOT greenfield: writing a first test there would fork a
            # THIRD file next to the existing ones. Only true greenfield (zero)
            # consults runner discovery; an unresolved configured runner becomes
            # a non-write decision (issue #1903 review round 3 — adoption never
            # fires when >1 exists).
            if matches:  # >1 existing co-located tests -> do not fork
                return None if _configured_js_runner_is_unresolved(code_file) else derived
            # Greenfield (issue #1903 §A): no existing co-located test. If the
            # project configures a JS/TS runner, write the FIRST test where the
            # runner actually collects it rather than the runner-blind derived
            # ``tests/`` shadow. No runner detected (or Python) -> derived.
            greenfield = find_runner_collected_test_path(code_file)
            if greenfield is None:
                return None if _configured_js_runner_is_unresolved(code_file) else derived
            root_resolved = Path.cwd().resolve()
            derived_resolved = _validated_project_path(derived, root=root_resolved)
            if derived_resolved is not None and greenfield == derived_resolved:
                return derived
            return greenfield
        # Exactly one existing co-located test -> adopt it.
        sibling = matches[0]
        root_resolved = Path.cwd().resolve()
        sibling_resolved = _validated_project_path(sibling, root=root_resolved)
        if sibling_resolved is None:
            return derived
        # Defense in depth (CWE-022): find_collocated_test already rejects
        # candidates outside the working tree, but re-assert containment at
        # the adoption sink — the returned path becomes a generated-test
        # WRITE target downstream.
        if not _contained_in_root(sibling_resolved, root_resolved):
            return derived
        derived_resolved = _validated_project_path(derived, root=root_resolved)
        if derived_resolved is not None and sibling_resolved == derived_resolved:
            return derived
        # Round 9: only adopt a sibling the runner ACTUALLY collects. When a
        # configured JS/TS runner PROVABLY excludes it (custom testMatch/roots the
        # sibling does not match), adopting it would perpetuate the false-green on
        # an excluded file. Redirect to the runner-collected location instead
        # (greenfield discovery); if none can be proven, suppress test output
        # rather than certify the excluded file or create a runner-blind shadow.
        module_path = _validated_project_path(code_file, root=root_resolved)
        collection_status = (
            _existing_collocated_is_collected(
                module_path, sibling_resolved, root_resolved
            )
            if module_path is not None
            else None
        )
        if module_path is not None and _project_uses_js_test_runner(
            module_path, root_resolved
        ):
            greenfield = find_runner_collected_test_path(code_file)
            if collection_status is True or greenfield == sibling_resolved:
                return sibling_resolved
            if greenfield is not None and greenfield != sibling_resolved:
                if derived_resolved is not None and greenfield == derived_resolved:
                    return derived
                return greenfield
            return None
        return sibling_resolved
    except Exception:  # pylint: disable=broad-except
        return None if _configured_js_runner_is_unresolved(code_file) else derived


def was_test_adopted(
    code_file: str | Path,
    resolved_test_path: str | Path,
    derived_test_path: str | Path,
    *,
    user_pinned: bool,
) -> bool:
    """True when *resolved_test_path* is an EXISTING co-located test PDD ADOPTED.

    This is the structured provenance the issue #1903 §B.4 never-block requires:
    it must fire ONLY for a co-located test PDD adopted from a HUMAN's existing
    file — NOT a user-pinned path and NOT a greenfield test PDD is creating for
    the first time. It is True only when ALL hold: the location was NOT
    ``user_pinned``; a single existing co-located sibling was found at resolution
    time (``find_collocated_test`` is not ``None`` — greenfield finds none yet);
    and the resolved path actually differs from the derived default (adoption
    genuinely happened, not a fall-through to the runner-blind shadow).

    MUST be evaluated at PATH-RESOLUTION time (before generation overwrites the
    file), because after generation the greenfield-created and human-adopted
    cases both exist on disk and become indistinguishable by presence. Total —
    any error yields ``False`` (conservative: no never-block).
    """
    try:
        if user_pinned:
            return False
        sibling = find_collocated_test(code_file)
        if sibling is None:
            return False
        if Path(resolved_test_path) == Path(derived_test_path):
            return False
        # Round 9: adoption means the resolved path IS that existing human
        # sibling — NOT a greenfield/runner-collected redirect AWAY from a sibling
        # the runner excludes (``resolve_test_output_path`` now redirects such
        # excluded siblings). A redirect target is a fresh PDD-created file, not a
        # human test, so it must never reach the never-block.
        root_resolved = Path.cwd().resolve()
        resolved_here = _validated_project_path(resolved_test_path, root=root_resolved)
        sibling_here = _validated_project_path(sibling, root=root_resolved)
        if (
            resolved_here is None
            or sibling_here is None
            or resolved_here != sibling_here
        ):
            return False
        # Ownership provenance (issue #1903 review round 7): a test PDD itself
        # GREENFIELD-created on a prior run must NOT be reclassified as
        # human-adopted just because it now exists as a single co-located sibling.
        if is_pdd_created_test(resolved_test_path):
            return False
        return True
    except Exception:  # pylint: disable=broad-except
        return False


# Manifest of tests PDD GREENFIELD-created itself (issue #1903 review round 7),
# so a later run never mistakes a PDD-owned co-located test for a human-adopted
# one when deciding the churn never-block. Repo-relative POSIX paths. Lives under
# ``.pdd/meta/`` — PDD's TRACKED sync-metadata directory (committed alongside the
# per-module fingerprints) — NOT the top-level ``.pdd/`` which projects routinely
# gitignore. This durability matters: a fresh checkout or the durable runner's
# fresh module worktree must still see PDD's ownership, else a PDD-created test
# is re-read as human-adopted and can improperly reach the never-block (round 8).
_PDD_CREATED_TESTS_MANIFEST = Path(".pdd") / "meta" / "pdd_created_tests.json"
# Legacy location (round 7) read as a fallback so ownership recorded before the
# move is not lost on the first post-upgrade run.
_PDD_CREATED_TESTS_MANIFEST_LEGACY = Path(".pdd") / "pdd_created_tests.json"


@contextmanager
def _interprocess_lock(lock_path: Path):
    """Hold an EXCLUSIVE cross-platform lock over *lock_path*.

    ``filelock`` is an existing project dependency and provides the native
    POSIX/Windows implementation.  Unlike the old fcntl-only branch, Windows
    writers now serialize the ownership-manifest read-modify-write operation.
    The lock file intentionally remains on disk after release and is ignored by
    Git; lock ownership itself is released by the context manager.
    """
    with FileLock(str(lock_path)):
        yield


def _pdd_created_tests_manifest_path() -> Path:
    return Path.cwd() / _PDD_CREATED_TESTS_MANIFEST


def _load_pdd_created_tests() -> Optional[set[str]]:
    """Load monotonic ownership from protected base plus the worktree.

    Invalid present evidence is fail-closed (``None``). A protected manifest
    cannot be weakened by candidate deletion or truncation because its entries
    are always unioned with the writable candidate copy.
    """
    result: set = set()
    protected_ref = os.environ.get("PDD_PROTECTED_BASE_REF", "").strip()
    if protected_ref:
        for rel in (_PDD_CREATED_TESTS_MANIFEST, _PDD_CREATED_TESTS_MANIFEST_LEGACY):
            try:
                loaded = subprocess.run(
                    ["git", "show", f"{protected_ref}:{rel.as_posix()}"],
                    cwd=Path.cwd(),
                    capture_output=True,
                    text=True,
                    timeout=10,
                    check=False,
                )
            except (OSError, subprocess.SubprocessError):
                return None
            if loaded.returncode != 0:
                continue
            try:
                data = json.loads(loaded.stdout)
            except ValueError:
                return None
            if not isinstance(data, list) or not all(isinstance(item, str) for item in data):
                return None
            result.update(data)
    for rel in (_PDD_CREATED_TESTS_MANIFEST, _PDD_CREATED_TESTS_MANIFEST_LEGACY):
        path = Path.cwd() / rel
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except FileNotFoundError:
            continue
        except (OSError, ValueError):
            return None
        if not isinstance(data, list) or not all(isinstance(item, str) for item in data):
            return None
        result.update(data)
    return result


def _test_repo_relative(test_path: str | Path) -> Optional[str]:
    """Repo-relative POSIX form of *test_path* (in-root), or ``None``."""
    try:
        root = Path.cwd().resolve()
        p = Path(test_path)
        resolved = (p if p.is_absolute() else (root / p)).resolve()
        return resolved.relative_to(root).as_posix()
    except (OSError, RuntimeError, ValueError):
        return None


def record_pdd_created_test(test_path: str | Path) -> None:
    """Record that PDD GREENFIELD-created the test at *test_path* (#1903 §A/§B.4).

    Callers invoke this ONLY when PDD writes a brand-new greenfield test (no
    pre-existing human file), so :func:`was_test_adopted` can later exclude it
    from the human-adopted never-block.

    Parallel agentic-sync CHILD PROCESSES can record concurrently, so the whole
    read-modify-write runs under an interprocess EXCLUSIVE file lock and commits
    via a temp file + atomic ``os.replace`` (round 9): an unlocked RMW would let
    two children read the same set and clobber each other's additions, dropping an
    ownership record so a later run misreads a PDD-owned test as human-adopted.
    Evidence/path persistence failures raise so publication cannot continue
    after silently losing ownership provenance.
    """
    rel = _test_repo_relative(test_path)
    if rel is None:
        raise RuntimeError("PDD test ownership path is outside the project")
    manifest = _pdd_created_tests_manifest_path()
    try:
        manifest.parent.mkdir(parents=True, exist_ok=True)
    except OSError as exc:
        raise RuntimeError("PDD test ownership directory is unavailable") from exc
    lock_path = manifest.with_suffix(manifest.suffix + ".lock")
    try:
        with _interprocess_lock(lock_path):
            existing = _load_pdd_created_tests()  # merges protected/legacy under lock
            if existing is None:
                raise RuntimeError("PDD test ownership evidence is unreadable")
            if rel in existing:
                return
            existing.add(rel)
            payload = json.dumps(sorted(existing), indent=2) + "\n"
            tmp = manifest.with_suffix(manifest.suffix + f".tmp.{os.getpid()}")
            try:
                tmp.write_text(payload, encoding="utf-8")
                os.replace(tmp, manifest)  # atomic within the same directory
            finally:
                try:
                    if tmp.exists():
                        tmp.unlink()
                except OSError:
                    pass
    except (OSError, ValueError) as exc:
        raise RuntimeError("PDD test ownership could not be persisted") from exc


def is_pdd_created_test(test_path: str | Path) -> bool:
    """True when *test_path* is recorded as a PDD greenfield-created test. Total."""
    rel = _test_repo_relative(test_path)
    if rel is None:
        return True
    owned = _load_pdd_created_tests()
    return owned is None or rel in owned


def _pins_test_output_location(config: Mapping[str, Any]) -> bool:
    """Return True when *config* explicitly pins the test-output location (#1903).

    Recognizes both the flat ``test_output_path`` key and the Issue #237
    template form ``outputs.test.path``. It MUST be fed a RAW ``.pddrc`` context
    ``defaults`` block (where these keys appear only when explicitly configured),
    NEVER the ``resolved_config`` that ``construct_paths`` returns: that config
    has a generated-default ``test_output_path`` injected back into it, so it is
    ALWAYS present and would read as pinned even for a default derivation. Use
    :func:`configured_test_output_pinned` to obtain the right raw defaults for a
    file. Never raises.
    """
    try:
        # Presence (not truthiness): an explicitly configured `test_output_path: ""`
        # (root-level test output) or `outputs.test.path: ""` is still an explicit
        # user pin. Only a genuinely ABSENT key (or an explicit null) means
        # "default derivation" and is eligible for co-located adoption (#1903).
        if config.get("test_output_path") is not None:
            return True
        outputs = config.get("outputs")
        if isinstance(outputs, Mapping):
            test_cfg = outputs.get("test")
            if isinstance(test_cfg, Mapping) and test_cfg.get("path") is not None:
                return True
        return False
    except Exception:  # pylint: disable=broad-except
        return False


def configured_test_output_pinned(
    target_file: str | Path,
    *,
    context_override: Optional[str] = None,
    search_from: Optional[str | Path] = None,
) -> bool:
    """True when the test-output location is user-pinned for *target_file* (#1903).

    Reads the explicit-vs-default provenance from the SAME authoritative source
    the path derivation is configured by — the RAW ``.pddrc`` context ``defaults``
    (``test_output_path`` / ``outputs.test.path``) and the ``PDD_TEST_OUTPUT_PATH``
    env var — and NEVER from ``construct_paths``' ``resolved_config`` (which injects
    a generated-default ``test_output_path`` and so always reads as pinned).

    The context is resolved the way ``construct_paths`` resolves it: an explicit
    *context_override* wins; otherwise the context that owns *target_file* is
    detected from its path (matching ``.pddrc`` ``prompts_dir`` / ``paths``), and
    when nothing matches the ``default`` context's defaults apply. This keeps the
    pin signal aligned with the derived path even when the owning context is
    selected by a ``prompts_dir`` prefix rather than the bare basename/CWD.

    Args:
        target_file: The file whose owning context is inspected — the prompt file
            for sync/change derivation, or the code file for ``pdd test``.
        context_override: An explicit context name, when the caller already
            resolved one (bypasses path-based detection).
        search_from: Directory to locate the nearest ``.pddrc`` from (defaults to
            *target_file*'s parent). Sync passes its ``prompts_root`` anchor so a
            nested subproject finds its own ``.pddrc``.

    Returns:
        True when the location is explicitly pinned, else False. Never raises.
    """
    try:
        # Presence (not truthiness): an explicitly exported `PDD_TEST_OUTPUT_PATH=`
        # (even empty — a root-level pin) is an explicit user choice, consistent with
        # the `.pddrc test_output_path: ""` handling in `_pins_test_output_location`.
        # Only a genuinely UNSET env var (None) is default-eligible (#1903).
        if os.environ.get("PDD_TEST_OUTPUT_PATH") is not None:
            return True
        # Lazy import: mirrors the repo's other construct_paths lookups from here
        # and avoids any import cycle at module load.
        from .construct_paths import (  # pylint: disable=import-outside-toplevel
            _find_pddrc_file,
            _load_pddrc_config,
            detect_context_for_file,
        )
        start = Path(search_from) if search_from else Path(target_file).parent
        pddrc_path = _find_pddrc_file(start)
        if not pddrc_path:
            return False
        config = _load_pddrc_config(pddrc_path)
        contexts = config.get("contexts", {})
        context_name = context_override
        if not context_name:
            context_name, _ = detect_context_for_file(
                str(target_file), repo_root=str(pddrc_path.parent)
            )
        # `.pddrc`'s `default` context is the fallback when no context matches
        # (construct_paths applies it too), so a project that keeps all config in
        # `default` is still recognized as pinned.
        if not context_name and "default" in contexts:
            context_name = "default"
        defaults = contexts.get(context_name or "", {}).get("defaults", {})
        return _pins_test_output_location(defaults)
    except Exception:  # pylint: disable=broad-except
        return False


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
