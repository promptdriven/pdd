"""Detect hardcoded-list-vs-canonical-source drift in Python files.

Issue ``promptdriven/pdd_cloud#1405`` Fix B.  Three of the seven test
isolation bugs that surfaced after autonomous solve of
``promptdriven/pdd#798`` (OpenCode CLI backend, ``promptdriven/pdd#858``)
shared the same structural shape:

* A test or helper file declared a hardcoded tuple/list of N domain
  string literals (provider env vars, file markers, supported
  languages, ...).
* The same package owned a canonical source — a function or
  module-level constant — returning the authoritative M-item list of
  the same domain.
* ``set(static_list) ⊂ set(canonical())`` with ``M > N``.  The drift
  surfaces only when the runtime carries one of the missing entries
  (e.g., a developer machine that has ``XAI_API_KEY`` set, while the
  ``pdd`` worker container does not).

`pdd checkup --review-loop` had no signal for this pattern: the
reviewer LLM had to enumerate both lists from the diff and compute the
difference itself, which is unreliable.  This module provides a
deterministic AST-based scan that emits ``StaticListDriftFinding``
records the reviewer prompt embeds as candidate findings.  The
reviewer LLM remains the source of truth — it can verify, accept,
reject, or escalate each candidate — but it now has concrete file:line
evidence to attach to the finding.

The scan is intentionally narrow:

* Only pure-literal lists/tuples qualify as "static" (every element is
  a ``str`` constant).  A list with any non-literal element
  (``Name``, ``Call``, ``Attribute``, ``BinOp``, ...) is skipped
  because we cannot AST-compare it without runtime evaluation.
* Only functions whose body is a single ``return`` of a pure-literal
  list/tuple, or module-level constants assigned to a pure-literal
  list/tuple, qualify as canonical sources.
* Drift is only flagged when the static list is a *strict subset* of
  the canonical list (``set(static) ⊊ set(canonical)``) and the
  static list has at least 2 entries (1-item static lists produce
  too many spurious matches in real codebases).

Files that fail to parse (syntax errors, missing files) are skipped
silently — the scanner is best-effort and never raises on input.

Public surface
--------------

``StaticListDriftFinding`` — dataclass with ``static_list_name``,
``static_path``, ``static_line``, ``static_size``,
``canonical_source_name``, ``canonical_path``, ``canonical_line``,
``canonical_size``, ``missing_items``, ``summary``.

``detect_static_list_drift(paths)`` — accepts an iterable of file
paths (``str`` or ``pathlib.Path``); returns a ``list`` of findings.
Order is stable: sorted by static-file path, then static-line.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, List, Optional, Sequence, Tuple, Union


PathLike = Union[str, Path]

# Smaller static lists than this are excluded; in practice 1-item static
# lists like ``SUPPORTED = ["python"]`` produce many false positives that
# are not the drift class we care about.  Two items is the minimum
# evidence we need to claim "the author meant a list, not a singleton".
_MIN_STATIC_LIST_SIZE = 2


# ---------------------------------------------------------------------------
# Public dataclass
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class StaticListDriftFinding:
    """One detected hardcoded-list-vs-canonical drift instance."""

    static_list_name: str
    static_path: Path
    static_line: int
    static_size: int
    canonical_source_name: str
    canonical_path: Path
    canonical_line: int
    canonical_size: int
    # Items present in the canonical source but missing from the static list.
    # Sorted for stable output.
    missing_items: Tuple[str, ...] = field(default_factory=tuple)

    @property
    def summary(self) -> str:
        """One-line human/LLM-readable summary the reviewer prompt can quote."""
        return (
            f"Static list `{self.static_list_name}` "
            f"({self.static_size} items) at "
            f"{self.static_path}:{self.static_line} drifts from canonical "
            f"`{self.canonical_source_name}` "
            f"({self.canonical_size} items) at "
            f"{self.canonical_path}:{self.canonical_line}."
        )


# ---------------------------------------------------------------------------
# Internal record types
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _LiteralList:
    """A pure-literal list/tuple: ``Name = [literal, ...]`` or
    ``def f(): return [literal, ...]``.
    """

    name: str
    path: Path
    line: int
    items: Tuple[str, ...]

    @property
    def item_set(self) -> frozenset:
        return frozenset(self.items)


# ---------------------------------------------------------------------------
# AST extraction
# ---------------------------------------------------------------------------


def _extract_string_literal_sequence(node: ast.AST) -> Optional[Tuple[str, ...]]:
    """Return the string-literal items of *node* iff *every* element is a
    ``Constant`` of type ``str``; else ``None``.

    Accepts:
    * ``ast.List`` and ``ast.Tuple`` -- the bare literal forms.
    * ``ast.Set`` -- the bare ``{"a", "b"}`` set literal.
    * ``ast.Call`` wrapping ``set`` or ``frozenset`` with a single literal
      argument: ``set([...])``, ``frozenset({...})``, etc.  This is the
      production pattern at ``pdd/agentic_common.py:1053``
      (``_OPENCODE_PROVIDER_CREDENTIAL_FIELDS = frozenset({...})``).

    Guards against half-literal lists like ``[FALLBACK, "FOO"]`` (where
    ``FALLBACK`` is a ``Name``), which are not AST-comparable without
    runtime evaluation.
    """
    # Unwrap ``set(...)`` / ``frozenset(...)`` calls with a single literal
    # argument so the canonical-source matcher can pair against them.
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
        if node.func.id in {"set", "frozenset"} and len(node.args) == 1 and not node.keywords:
            node = node.args[0]
    if not isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return None
    items: List[str] = []
    for elt in node.elts:
        if not isinstance(elt, ast.Constant) or not isinstance(elt.value, str):
            return None
        items.append(elt.value)
    return tuple(items)


def _module_assign_target_name(target: ast.AST) -> Optional[str]:
    """Return the target name iff *target* is a single ``Name`` node, else ``None``.

    Skips tuple-targets (``A, B = (...)``) and attribute targets
    (``self.x = ...``) because they would produce many spurious matches.
    """
    if isinstance(target, ast.Name):
        return target.id
    return None


def _module_level_literal_list_or_constant(
    stmt: ast.stmt,
    path: Path,
) -> Optional[_LiteralList]:
    """Recognize ``Name = [literal, ...]`` or ``Name: T = [literal, ...]`` at
    module level.  Return the captured ``_LiteralList`` or ``None``.
    """
    if isinstance(stmt, ast.Assign):
        if len(stmt.targets) != 1:
            return None
        name = _module_assign_target_name(stmt.targets[0])
        if name is None:
            return None
        items = _extract_string_literal_sequence(stmt.value)
        if items is None:
            return None
        return _LiteralList(name=name, path=path, line=stmt.lineno, items=items)
    if isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
        name = _module_assign_target_name(stmt.target)
        if name is None:
            return None
        items = _extract_string_literal_sequence(stmt.value)
        if items is None:
            return None
        return _LiteralList(name=name, path=path, line=stmt.lineno, items=items)
    return None


def _function_with_literal_return(
    stmt: ast.stmt,
    path: Path,
) -> Optional[_LiteralList]:
    """Recognize ``def f(...): return [literal, ...]`` (single return statement).

    Functions with multiple return paths, or whose return value is not a
    pure literal list/tuple, are not recognized as canonical sources.
    """
    if not isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return None

    # Walk the body to find a single ``return`` of a literal list/tuple.
    # We only accept functions whose *only* substantive statement is the
    # return.  Docstrings (``Expr(Constant(str))``) are skipped.
    return_value: Optional[ast.AST] = None
    for body_stmt in stmt.body:
        # Skip docstrings.
        if (
            isinstance(body_stmt, ast.Expr)
            and isinstance(body_stmt.value, ast.Constant)
            and isinstance(body_stmt.value.value, str)
        ):
            continue
        if isinstance(body_stmt, ast.Return) and body_stmt.value is not None:
            if return_value is not None:
                # Multiple return statements; bail out.
                return None
            return_value = body_stmt.value
        else:
            # Any other statement disqualifies the function as a
            # "trivial canonical source": we can't statically resolve
            # what the return will be.
            return None

    if return_value is None:
        return None
    items = _extract_string_literal_sequence(return_value)
    if items is None:
        return None
    return _LiteralList(
        name=stmt.name,
        path=path,
        line=stmt.lineno,
        items=items,
    )


def _scan_module(path: Path) -> Tuple[List[_LiteralList], List[_LiteralList]]:
    """Return ``(static_lists, canonical_sources)`` extracted from *path*.

    Walks the full AST -- not just ``tree.body`` -- so inline literals in
    function/method/class bodies are also captured.  The real #858 bug
    used ``for k in (...)`` inline tuples inside test function bodies,
    not module-level constants; restricting to ``tree.body`` silently
    skipped those.

    Files that cannot be opened or parsed yield ``([], [])``.
    """
    try:
        source = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return [], []
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return [], []

    static_lists: List[_LiteralList] = []
    canonical_sources: List[_LiteralList] = []

    # First pass: top-level constructs (module-level constants, top-level
    # function definitions).  Keeps backwards-compatible behavior for
    # callers that read the (well-tested) module-level path.
    for stmt in tree.body:
        as_constant = _module_level_literal_list_or_constant(stmt, path)
        if as_constant is not None:
            static_lists.append(as_constant)
            canonical_sources.append(as_constant)
            continue

        as_function = _function_with_literal_return(stmt, path)
        if as_function is not None:
            canonical_sources.append(as_function)

    # Second pass: walk the entire tree to pick up literal sequences in
    # function/method/class/conditional bodies.  These are recorded as
    # *static lists only* -- never as canonical sources -- because
    # function-local literals (fixture data, scratch buffers) regularly
    # share names like ``candidates`` or ``lines`` across unrelated
    # tests and would produce noise pairs.  A canonical source must be
    # a module-level constant or a top-level function with a single
    # literal return (already captured in the first pass).
    seen: set = {(lit.name, lit.line) for lit in static_lists}

    def _add_function_body_static(name: str, line: int, items: Tuple[str, ...]) -> None:
        if (name, line) in seen:
            return
        seen.add((name, line))
        static_lists.append(
            _LiteralList(name=name, path=path, line=line, items=items)
        )

    # ``ast.walk`` yields every node including ``tree.body`` items.  We
    # only want descendants -- module-level was handled above.  Use a
    # parent map to skip top-level statements.
    top_level_ids = {id(stmt) for stmt in tree.body}

    for node in ast.walk(tree):
        if id(node) in top_level_ids:
            continue
        # Inline assignments: ``name = [literal, ...]`` inside function,
        # class, with-, try-, etc. bodies.
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            name = _module_assign_target_name(node.targets[0])
            if name is None:
                continue
            items = _extract_string_literal_sequence(node.value)
            if items is None:
                continue
            _add_function_body_static(name, node.lineno, items)
            continue
        if isinstance(node, ast.AnnAssign) and node.value is not None:
            name = _module_assign_target_name(node.target)
            if name is None:
                continue
            items = _extract_string_literal_sequence(node.value)
            if items is None:
                continue
            _add_function_body_static(name, node.lineno, items)
            continue
        # Inline ``for k in (literal, ...)`` loops -- the real #858 shape.
        # Synthesize a stable pseudo-name keyed on file:line so the
        # pairing logic can still match by literal-set membership without
        # collapsing two different for-loops in the same module.
        if isinstance(node, ast.For):
            items = _extract_string_literal_sequence(node.iter)
            if items is None or len(items) < _MIN_STATIC_LIST_SIZE:
                continue
            synthetic_name = f"<for-loop:line-{node.lineno}>"
            _add_function_body_static(synthetic_name, node.lineno, items)
            continue

    return static_lists, canonical_sources


# ---------------------------------------------------------------------------
# Pairing & drift detection
# ---------------------------------------------------------------------------


def _items_look_like_same_domain(static: _LiteralList, canonical: _LiteralList) -> bool:
    """Return True iff *static*'s items look like a same-domain subset of *canonical*.

    "Same domain" is approximated by strict-subset overlap: every static
    element appears in the canonical set.  This avoids pairing arbitrary
    disjoint lists that happen to share the same "list of strings" shape.
    """
    if not static.items:
        return False
    return static.item_set < canonical.item_set


def _pair_drifts(
    static_lists: Sequence[_LiteralList],
    canonical_sources: Sequence[_LiteralList],
) -> List[StaticListDriftFinding]:
    """For each (static, canonical) pair where the static list is a strict
    subset of the canonical, emit a ``StaticListDriftFinding``.

    A static list and a canonical source pointing at the same
    ``(name, path, line)`` triple are the same node — never paired
    against each other.
    """
    findings: List[StaticListDriftFinding] = []
    for static in static_lists:
        if len(static.items) < _MIN_STATIC_LIST_SIZE:
            continue
        # The deduped item set must also be at least the minimum size --
        # ``["", "", ""]`` deduplicates to ``{""}``, a singleton in
        # disguise that produces noise when the canonical set happens
        # to contain ``""`` as a sentinel (e.g.,
        # ``EXTERNAL_STATUS_AREAS = ("", "check", ..., "workflow")``).
        if len(static.item_set) < _MIN_STATIC_LIST_SIZE:
            continue
        # Best canonical match per static list = largest superset.  This
        # avoids emitting M*N findings for one drift when several
        # canonical sources share most items.
        best: Optional[_LiteralList] = None
        for canonical in canonical_sources:
            if (
                static.name == canonical.name
                and static.path == canonical.path
                and static.line == canonical.line
            ):
                # Same node; not a drift.
                continue
            if not _items_look_like_same_domain(static, canonical):
                continue
            if best is None or len(canonical.items) > len(best.items):
                best = canonical
        if best is None:
            continue
        missing = tuple(sorted(set(best.items) - set(static.items)))
        findings.append(
            StaticListDriftFinding(
                static_list_name=static.name,
                static_path=static.path,
                static_line=static.line,
                static_size=len(static.items),
                canonical_source_name=best.name,
                canonical_path=best.path,
                canonical_line=best.line,
                canonical_size=len(best.items),
                missing_items=missing,
            )
        )
    return findings


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------


def detect_static_list_drift(
    paths: Iterable[PathLike],
) -> List[StaticListDriftFinding]:
    """Scan *paths* and return all ``StaticListDriftFinding`` instances.

    Args:
        paths: An iterable of Python file paths (``str`` or ``Path``).
            Non-existent or non-Python paths are skipped silently.
            Directories are not recursed; the caller scopes the input
            (e.g., to PR-changed files).

    Returns:
        Stable-sorted list of drift findings.  The list is empty when
        no drift is detected, no Python files are parseable, or every
        candidate pair was filtered out.

    Notes:
        Static lists with fewer than 2 elements are not flagged
        (``_MIN_STATIC_LIST_SIZE``).  Strict-subset semantics
        (``set(static) ⊊ set(canonical)``) avoid spurious pairing of
        disjoint lists.
    """
    all_static: List[_LiteralList] = []
    all_canonical: List[_LiteralList] = []

    for raw in paths:
        path = Path(raw)
        if not path.is_file():
            continue
        if path.suffix != ".py":
            continue
        static_lists, canonical_sources = _scan_module(path)
        all_static.extend(static_lists)
        all_canonical.extend(canonical_sources)

    findings = _pair_drifts(all_static, all_canonical)
    findings.sort(
        key=lambda f: (str(f.static_path), f.static_line, f.static_list_name)
    )
    return findings
