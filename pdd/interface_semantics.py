"""Semantic compatibility helpers for PDD interface conformance.

This module keeps language-specific extraction at the edge.  Python callers may
parse annotation or signature text into these common models, while the
compatibility decisions below operate on lightweight language-neutral contracts.
"""

from __future__ import annotations

import ast
import re
from dataclasses import dataclass
from enum import Enum
from typing import Iterable, Optional


_TYPING_ALIASES = {
    "Dict": "dict",
    "List": "list",
    "Set": "set",
    "Tuple": "tuple",
    "FrozenSet": "frozenset",
}
_SPECIAL_FORMS = {"Optional", "Union"}


@dataclass(frozen=True)
class SemanticType:
    """Normalized type annotation shape used for compatibility checks."""

    base: str
    args: tuple["SemanticType", ...] = ()
    optional: bool = False
    raw: str = ""

    def without_optional(self) -> "SemanticType":
        if not self.optional:
            return self
        return SemanticType(
            base=self.base,
            args=self.args,
            optional=False,
            raw=self.raw,
        )


@dataclass(frozen=True)
class ParamContract:
    """Callable parameter contract independent of any concrete language AST."""

    name: str
    kind: str
    annotation: Optional[SemanticType] = None
    default: Optional[str] = None
    has_default: bool = False

    @property
    def positional_capable(self) -> bool:
        return self.kind in {"posonly", "positional"}

    @property
    def keyword_capable(self) -> bool:
        return self.kind in {"positional", "keyword_only"}

    @property
    def required(self) -> bool:
        return self.kind not in {"vararg", "kwarg"} and not self.has_default


@dataclass(frozen=True)
class CallableContract:
    """Callable public-surface contract with strict binding-kind identity."""

    binding_kind: str
    params: tuple[ParamContract, ...] = ()
    return_annotation: Optional[SemanticType] = None
    is_async: bool = False


def parse_semantic_type(annotation: Optional[str]) -> Optional[SemanticType]:
    """Parse a Python annotation string into a normalized semantic type.

    Returns ``None`` when the annotation is missing or cannot be parsed
    confidently.  Callers treat one-sided missing annotations as non-blocking.
    """
    if not annotation or not isinstance(annotation, str):
        return None
    text = annotation.strip()
    if not text:
        return None
    try:
        node = ast.parse(text, mode="eval").body
    except SyntaxError:
        return None
    return _semantic_from_ast(node, raw=text)


def semantic_types_compatible(
    expected: Optional[SemanticType],
    actual: Optional[SemanticType],
) -> bool:
    """Return True when two semantic types preserve the same public type base."""
    if expected is None or actual is None:
        return True
    if expected.optional != actual.optional:
        return False
    left = expected.without_optional()
    right = actual.without_optional()
    if left.base != right.base:
        return False
    if left.base == "Union":
        # Union members are an unordered set: ``Union[str, int]`` and
        # ``Union[int, str]`` are the same type.  Compare order-insensitively.
        # ``None`` membership is carried by ``optional`` (checked above), so a
        # narrowing like ``str | int | None`` -> ``str | int`` is already
        # rejected by the optional mismatch.
        return _union_args_compatible(left.args, right.args)
    if not left.args or not right.args:
        return True
    if len(left.args) != len(right.args):
        return False
    return all(
        semantic_types_compatible(left_arg, right_arg)
        for left_arg, right_arg in zip(left.args, right.args)
    )


def _union_args_compatible(
    left_args: tuple["SemanticType", ...],
    right_args: tuple["SemanticType", ...],
) -> bool:
    """Return True when two union member tuples match as unordered sets.

    Each left member must pair with a distinct compatible right member.  We
    find a perfect bipartite matching via augmenting paths (Kuhn's algorithm,
    polynomial) rather than trying every permutation (factorial — a wide union
    like ``Union[T0, ..., T11]`` would otherwise take minutes and look hung).
    A plain greedy match is not enough: the per-member leniency
    (``list[str]`` ~ ``list``) makes edges non-exclusive, so a greedy pick can
    strand a later member that had only one valid partner.
    """
    if len(left_args) != len(right_args):
        return False
    size = len(left_args)
    right_to_left = [-1] * size

    def _augment(left_index: int, seen: list[bool]) -> bool:
        for right_index in range(size):
            if seen[right_index]:
                continue
            if not semantic_types_compatible(
                left_args[left_index], right_args[right_index]
            ):
                continue
            seen[right_index] = True
            if right_to_left[right_index] == -1 or _augment(
                right_to_left[right_index], seen
            ):
                right_to_left[right_index] = left_index
                return True
        return False

    return all(_augment(left_index, [False] * size) for left_index in range(size))


def annotations_compatible(
    expected_annotation: Optional[str],
    actual_annotation: Optional[str],
) -> bool:
    """Compatibility predicate for raw annotation strings."""
    return semantic_types_compatible(
        parse_semantic_type(expected_annotation),
        parse_semantic_type(actual_annotation),
    )


def parse_callable_contract(signature_entry: str) -> Optional[CallableContract]:
    """Parse a ``_snapshot_public_signatures`` value into a contract.

    Non-callable entries such as ``[assignment]`` and import re-exports return
    ``None`` so callers can fall back to exact string comparison.
    """
    if not isinstance(signature_entry, str):
        return None
    match = re.match(r"^\[([^\]]+)\]\s*(.*)$", signature_entry.strip())
    if not match:
        return None
    binding_kind, signature = match.groups()
    if not signature:
        return None
    signature = signature.strip()
    is_async = False
    if signature.startswith("async "):
        is_async = True
        signature = signature[len("async ") :].strip()
    if not signature.startswith("("):
        return None

    try:
        func = ast.parse(f"def _pdd{signature}: pass").body[0]
    except SyntaxError:
        return None
    if not isinstance(func, ast.FunctionDef):
        return None

    class_context = binding_kind == "class"
    return CallableContract(
        binding_kind=binding_kind,
        params=tuple(_params_from_arguments(func.args, class_context=class_context)),
        return_annotation=(
            _semantic_from_ast(func.returns, raw=ast.unparse(func.returns))
            if func.returns is not None
            else None
        ),
        is_async=is_async,
    )


def callable_contracts_compatible(
    old: CallableContract,
    new: CallableContract,
    *,
    old_symbols: Optional[dict] = None,
    new_symbols: Optional[dict] = None,
) -> bool:
    """Return True when ``new`` preserves all existing call forms of ``old``.

    ``old_symbols`` / ``new_symbols`` are per-side module default-symbol tables
    forwarded to :func:`_existing_param_compatible` so a parameter default
    written as a same-module constant resolves to its literal when the two
    contracts come from different module versions (issue #1558).
    """
    if old.binding_kind != new.binding_kind:
        return False
    if old.is_async != new.is_async:
        return False
    if not semantic_types_compatible(old.return_annotation, new.return_annotation):
        return False

    old_positional = [param for param in old.params if param.positional_capable]
    new_positional = [param for param in new.params if param.positional_capable]
    if len(new_positional) < len(old_positional):
        return False
    for old_param, new_param in zip(old_positional, new_positional):
        if not _existing_param_compatible(
            old_param, new_param, old_symbols=old_symbols, new_symbols=new_symbols
        ):
            return False
        if old_param.kind == "positional" and new_param.kind == "posonly":
            return False

    new_by_name = {
        param.name: param
        for param in new.params
        if param.kind not in {"vararg", "kwarg"}
    }
    for old_param in old.params:
        if old_param.kind == "vararg":
            if not any(param.kind == "vararg" for param in new.params):
                return False
            continue
        if old_param.kind == "kwarg":
            if not any(param.kind == "kwarg" for param in new.params):
                return False
            continue
        new_param = new_by_name.get(old_param.name)
        if new_param is None:
            return False
        if not _existing_param_compatible(
            old_param, new_param, old_symbols=old_symbols, new_symbols=new_symbols
        ):
            return False
        if old_param.keyword_capable and not new_param.keyword_capable:
            return False
        if old_param.positional_capable and not new_param.positional_capable:
            return False

    old_names = {
        param.name
        for param in old.params
        if param.kind not in {"vararg", "kwarg"}
    }
    old_has_vararg = any(param.kind == "vararg" for param in old.params)
    old_has_kwarg = any(param.kind == "kwarg" for param in old.params)
    for new_param in new.params:
        if new_param.kind in {"vararg", "kwarg"}:
            continue
        if new_param.name in old_names:
            continue
        if new_param.required:
            return False
        # A new positional-capable parameter is a regression when the old
        # signature had ``*args``: a positional argument that previously landed
        # in ``*args`` now binds to this parameter instead -- ``def f(a, *args)``
        # -> ``def f(a, b=0, *args)`` rebinds the second positional of
        # ``f(1, 2)`` from ``args`` to ``b``.  Keyword-only additions after
        # ``*args`` do not intercept positional slots and remain allowed.
        if old_has_vararg and new_param.positional_capable:
            return False
        # The symmetric case for ``**kwargs``: a new keyword-capable parameter
        # captures a keyword that previously flowed into ``**kwargs`` --
        # ``def f(**kwargs)`` -> ``def f(a=0, **kwargs)`` rebinds ``f(a=5)`` from
        # ``kwargs['a']`` to ``a``.  A positional-only addition cannot be passed
        # by keyword, so it never steals from ``**kwargs`` and stays allowed.
        if old_has_kwarg and new_param.keyword_capable:
            return False
    return True


def signature_entries_compatible(
    old_entry: str,
    new_entry: str,
    *,
    old_symbols: Optional[dict] = None,
    new_symbols: Optional[dict] = None,
) -> Optional[bool]:
    """Return semantic compatibility for snapshot entries, or None if unknown.

    ``old_symbols`` / ``new_symbols`` are per-side module default-symbol tables
    (see :func:`build_module_default_symbols`). They let a parameter default
    written as a same-module constant resolve to the literal it stands for when
    each snapshot comes from a DIFFERENT module version: the existing module for
    ``old_entry`` and the generated module for ``new_entry`` (issue #1558). With
    no tables, defaults compare by literal normalization only and a same-module
    constant stays UNKNOWN (conservatively treated as a change — fail closed).
    """
    old_contract = parse_callable_contract(old_entry)
    new_contract = parse_callable_contract(new_entry)
    if old_contract is None or new_contract is None:
        return None
    return callable_contracts_compatible(
        old_contract,
        new_contract,
        old_symbols=old_symbols,
        new_symbols=new_symbols,
    )


class DefaultCompatibility(Enum):
    """Tri-state verdict for comparing two parameter default expressions.

    ``COMPATIBLE``   — both defaults resolve to the SAME safe literal value
                       (``25000`` vs ``25_000``, or a module constant
                       ``_LIMIT = 25000`` standing in for ``25000``); every
                       caller observes identical behavior.
    ``INCOMPATIBLE`` — both resolve to safe literals that DIFFER (``25000`` vs
                       ``5000``); a real contract break.
    ``UNKNOWN``      — at least one side cannot be resolved to a safe literal
                       without executing code (a call, an imported name, a
                       dynamic expression). Conformance callers fail closed on
                       this, so an unresolvable change is never silently
                       accepted.
    """

    COMPATIBLE = "compatible"
    INCOMPATIBLE = "incompatible"
    UNKNOWN = "unknown"


def compare_default_sources(
    left_default: Optional[str],
    right_default: Optional[str],
    symbols: Optional[dict] = None,
    *,
    left_symbols: Optional[dict] = None,
    right_symbols: Optional[dict] = None,
) -> DefaultCompatibility:
    """Compare two parameter-default source strings semantically.

    Each side is resolved against its OWN module symbol table (a mapping of
    module-level constant names to normalized values, see
    :func:`build_module_default_symbols`). Pass ``symbols`` to apply ONE table
    to both sides — correct when both defaults live in the same module namespace
    (the ``<pdd-interface>`` gate: the prompt and the generated code describe the
    same generated module). Pass ``left_symbols`` / ``right_symbols`` for PER-SIDE
    tables — correct when the two defaults come from different module versions
    (the public-surface gate: ``left`` is the existing module, ``right`` the
    generated one). A per-side argument overrides ``symbols`` for that side; an
    omitted side falls back to ``symbols`` then to an empty table, so a bare name
    with no table is ``UNKNOWN``.

    The comparison NEVER executes code, imports a module, or evaluates an
    arbitrary expression. It only folds safe AST literals, unary ``+``/``-``/
    ``~`` on numbers, literal containers, and same-module constants bound to
    those — anything else is ``UNKNOWN`` (fail closed).
    """
    left_table = left_symbols if left_symbols is not None else (symbols or {})
    right_table = right_symbols if right_symbols is not None else (symbols or {})
    left_norm = _normalize_default_source(left_default, left_table)
    right_norm = _normalize_default_source(right_default, right_table)
    if left_norm is None or right_norm is None:
        return DefaultCompatibility.UNKNOWN
    if left_norm == right_norm:
        return DefaultCompatibility.COMPATIBLE
    return DefaultCompatibility.INCOMPATIBLE


def build_module_default_symbols(module_source: Optional[str]) -> dict:
    """Map module-level constant names to normalized safe-literal values.

    A name qualifies ONLY when it is bound exactly once at MODULE scope AND that
    single binding is a top-level ``X = <literal>`` / ``X: T = <literal>``
    assignment to a safe literal/container. Any second module-scope binding of
    the name — reassignment, augmented assignment, a conditional override inside
    ``if``/``try``/``TYPE_CHECKING``, a tuple-unpacking rebind, or a
    ``def``/``class``/``import`` that shadows it — disqualifies it, because the
    value a caller would observe is then not statically knowable. Such names stay
    out of the table and resolve as ``UNKNOWN`` (fail closed). Counting is
    module-scope-aware (see :func:`_count_module_bindings`): a name reused inside
    a function/class/comprehension scope is local and does NOT disqualify the
    module constant, but every binding that can reach the module global — a
    second module-level binding, a nested ``global X``-plus-assignment, or a
    walrus that leaks to module scope — still does. Over-eviction only ever moves
    a constant toward ``UNKNOWN``, never a false match.
    Name-to-name aliases are not resolved transitively — the right-hand side is
    normalized with an empty table — so ``B = A`` never enters the table. A
    ``from x import *`` anywhere in the module empties the whole table, since it
    binds a statically-unknowable set of names that could shadow any constant.

    Resolution is purely static and assumes the constant is not rebound or
    removed by dynamic means the analyzer cannot see (``globals()[name] = ...``,
    ``exec``, ``setattr`` on the module, or a top-level ``del X`` after the
    binding) — consistent with the comparator's contract of never executing
    code. None of these is a realistic generated-code shape, no non-executing
    analyzer can detect them, and none can mask a real default *change* (each
    would require one statically-single literal name to resolve to two different
    runtime values).

    Returns an empty dict when ``module_source`` is absent or unparseable.
    """
    if not module_source or not isinstance(module_source, str):
        return {}
    try:
        tree = ast.parse(module_source)
    except SyntaxError:
        return {}
    return _symbols_from_module_ast(tree)


def _symbols_from_module_ast(tree: ast.Module) -> dict:
    if _has_star_import(tree):
        # ``from x import *`` binds a statically-unknowable set of names at
        # runtime, any of which could shadow a module constant. We cannot trust
        # a single value in the module, so the whole table is empty (every
        # constant resolves as UNKNOWN — fail closed).
        return {}
    binding_counts = _count_module_bindings(tree)
    table: dict[str, tuple] = {}
    for node in tree.body:
        if isinstance(node, ast.Assign):
            targets = node.targets
            value: Optional[ast.AST] = node.value
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            targets = [node.target]
            value = node.value
        else:
            continue
        plain_names = [t.id for t in targets if isinstance(t, ast.Name)]
        if len(plain_names) != len(targets):
            # Attribute/subscript/unpacking target — not a simple constant.
            continue
        normalized = _normalize_default_node(value, {})
        # Only IMMUTABLE values are trusted. A constant bound to a list/set/dict
        # can be mutated in place after binding (``_ITEMS = []`` then
        # ``_ITEMS.append(x)`` at import time), so the value a parameter default
        # ``=_ITEMS`` would observe is not the empty container we see here. Such
        # method-call mutations leave no ``Store`` node, so the binding count
        # cannot catch them — we conservatively keep mutable-container constants
        # out of the table (they resolve as UNKNOWN — fail closed).
        if normalized is None or not _is_immutable_default(normalized):
            continue
        for name in plain_names:
            if binding_counts.get(name, 0) == 1:
                table[name] = normalized
    return table


_MUTABLE_DEFAULT_TAGS = frozenset({"list", "set", "dict"})


def _is_immutable_default(normalized: tuple) -> bool:
    """Return True when a normalized default cannot be mutated in place.

    ``list``/``set``/``dict`` are mutable; a ``tuple`` is immutable only when
    every element is (``(1, [2])`` is not, because the inner list can change).
    """
    if not normalized:
        return False
    tag = normalized[0]
    if tag in _MUTABLE_DEFAULT_TAGS:
        return False
    if tag == "tuple":
        return all(_is_immutable_default(item) for item in normalized[1])
    return True


# Nodes that open a new lexical scope. A name bound inside their body is local
# to that scope and cannot rebind a module global (a ``def``/``class`` is handled
# separately because its NAME does bind in the enclosing scope). Sub-expressions
# that run in the ENCLOSING scope (decorator/default-arg expressions, a
# comprehension's outermost iterable) and any ``global``/walrus that leaks out of
# them are handled by the whole-tree scan in :func:`_count_module_bindings`.
_NEW_SCOPE_NODES = (
    ast.Lambda,
    ast.ListComp,
    ast.SetComp,
    ast.DictComp,
    ast.GeneratorExp,
)


def _count_module_bindings(tree: ast.Module) -> dict:
    """Count how many times each name is bound in the MODULE (global) scope.

    A constant is trusted only if its name is bound exactly once at module scope
    (see :func:`build_module_default_symbols`). A parameter default
    ``def f(x=_LIMIT)`` reads ``_LIMIT`` from the module globals, so only a
    binding that can change that global counts. A name bound inside a
    ``def``/``async def``/``class``/``lambda``/comprehension body is local to
    that scope and does NOT rebind the module global, so those bodies are not
    descended into. Counting recurses by DEFAULT through everything else
    (module-level ``if``/``for``/``while``/``with``/``try``/``match`` blocks, and
    any node not explicitly handled), so an unfamiliar construct still has its
    ``Store`` names counted — fail closed, never a missed rebind.

    ``ast.Name`` in ``Store`` context covers assignment / augmented / annotated /
    ``for`` / ``with`` / tuple-unpacking targets; ``def``/``class``/``import``
    bind a name WITHOUT a ``Store`` node and are counted explicitly (otherwise
    ``X = 25000`` shadowed by ``import x as X`` would be wrongly admitted), as
    are ``except ... as X`` and ``match`` capture patterns. Two forms rebind a
    module global from a place this walk skips and are detected separately: a
    function or class body that BOTH declares ``global X`` and assigns it, and a
    walrus ``X := ...`` evaluated at module scope (directly or inside a module-level
    comprehension — comprehension scopes are transparent to walrus). A read-only
    ``global`` and a walrus inside a function/lambda body bind nothing at module
    scope, so neither disqualifies the constant. Where attribution is imprecise it
    errs toward an extra binding, which can only evict a constant toward
    ``UNKNOWN`` — never a false match.
    """
    counts: dict[str, int] = {}

    def _bump(name: Optional[str], amount: int = 1) -> None:
        if name:
            counts[name] = counts.get(name, 0) + amount

    def _count_in_global_scope(node: ast.AST) -> None:
        if isinstance(node, ast.Name):
            if isinstance(node.ctx, ast.Store):
                _bump(node.id)
            return
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            _bump(node.name)  # the def/class name binds in the enclosing scope...
            return  # ...but its body opens a new scope — do not descend into it.
        if isinstance(node, _NEW_SCOPE_NODES):
            return  # lambda / comprehension body is a new scope; no module binding.
        if isinstance(node, ast.Import):
            for alias in node.names:
                _bump(alias.asname or alias.name.split(".", 1)[0])
            return
        if isinstance(node, ast.ImportFrom):
            for alias in node.names:
                if alias.name != "*":
                    _bump(alias.asname or alias.name)
            return
        if isinstance(node, ast.ExceptHandler):
            _bump(node.name)  # ``except E as X`` (``name`` is None for bare except)
        elif isinstance(node, (ast.MatchAs, ast.MatchStar)):
            _bump(node.name)  # ``case ... as X`` / ``case [*X]`` (None for ``_``)
        elif isinstance(node, ast.MatchMapping):
            _bump(node.rest)  # ``case {**X}``
        for child in ast.iter_child_nodes(node):
            _count_in_global_scope(child)

    _count_in_global_scope(tree)

    # Two forms rebind a module global from a location the scope walk above
    # skips. Detect each PRECISELY: a construct that binds nothing at module scope
    # must NOT be treated as a rebind, or the gate reports drift on code that did
    # not change the default (the false sync failure #1558 exists to remove).
    #
    # (1) ``global X`` rebinds the module global only when the SAME scope also
    # assigns X; a read-only ``global`` rebinds nothing. ``global`` is valid in a
    # function AND a class body (in both, an assignment to a global-declared name
    # writes the module global), so check both. Intersect each scope's ``global``
    # declarations with the names it stores. ``ast.walk`` also sees a nested
    # scope's stores, but over-attributing one only over-evicts toward UNKNOWN
    # (safe) — never a false match.
    for scope in ast.walk(tree):
        if not isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        declared_global = {
            name
            for sub in ast.walk(scope)
            if isinstance(sub, ast.Global)
            for name in sub.names
        }
        if not declared_global:
            continue
        stored = {
            sub.id
            for sub in ast.walk(scope)
            if isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Store)
        }
        for name in declared_global & stored:
            _bump(name, 2)

    # (2) A walrus ``X := ...`` rebinds the module global only when evaluated at
    # module scope. Comprehension scopes are TRANSPARENT to walrus — a walrus in a
    # module-level comprehension leaks to the module and MUST disqualify — so only
    # a ``def``/``async def``/``lambda`` BODY hides a walrus from module scope.
    # Decorator, default-argument and annotation expressions run in the enclosing
    # scope (so a walrus there at module level still counts); a walrus inside a
    # function/lambda body binds a local and is ignored.
    def _count_module_walrus(node: ast.AST, in_func: bool) -> None:
        if isinstance(node, ast.NamedExpr) and isinstance(node.target, ast.Name):
            if not in_func:
                _bump(node.target.id, 2)
            _count_module_walrus(node.value, in_func)
            return
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            body = node.body if isinstance(node.body, list) else [node.body]
            body_ids = {id(stmt) for stmt in body}
            for child in ast.iter_child_nodes(node):
                # Body statements open the function scope; decorators, defaults,
                # annotations and type params run in the enclosing scope.
                _count_module_walrus(child, in_func or id(child) in body_ids)
            return
        for child in ast.iter_child_nodes(node):
            _count_module_walrus(child, in_func)

    _count_module_walrus(tree, False)
    return counts


def _has_star_import(tree: ast.Module) -> bool:
    """Return True if the module contains any ``from x import *``."""
    return any(
        isinstance(sub, ast.ImportFrom)
        and any(alias.name == "*" for alias in sub.names)
        for sub in ast.walk(tree)
    )


def _normalize_default_source(
    source: Optional[str],
    symbols: dict,
) -> Optional[tuple]:
    """Parse a default source string and normalize it, or ``None`` if unsafe."""
    if not source or not isinstance(source, str):
        return None
    try:
        node = ast.parse(source.strip(), mode="eval").body
    except SyntaxError:
        return None
    return _normalize_default_node(node, symbols)


def _normalize_default_node(
    node: ast.AST,
    symbols: dict,
) -> Optional[tuple]:
    """Fold a default expression AST into a hashable, type-tagged value.

    Returns ``None`` for anything that cannot be resolved without executing
    code. The leading type tag keeps equality both value- AND type-exact so
    ``("int", 1)`` != ``("bool", True)`` and an ``int`` never equals a
    ``float`` of the same magnitude. Floats are keyed by ``repr`` so ``-0.0``
    stays distinct from ``0.0``.
    """
    if isinstance(node, ast.Constant):
        return _tag_constant(node.value)
    if isinstance(node, ast.UnaryOp):
        operand = _normalize_default_node(node.operand, symbols)
        if operand is None or len(operand) != 2:
            return None
        tag, value = operand
        if tag == "int":
            if isinstance(node.op, ast.USub):
                return ("int", -value)
            if isinstance(node.op, ast.UAdd):
                return ("int", +value)
            if isinstance(node.op, ast.Invert):
                return ("int", ~value)
            return None
        if tag == "float" and isinstance(node.op, (ast.USub, ast.UAdd)):
            # ``value`` is the ``repr`` string (see ``_tag_constant``); round-
            # trip it through ``float`` to apply the sign, then re-tag so
            # ``-0.0`` stays distinct from ``0.0``.
            number = float(value)
            number = -number if isinstance(node.op, ast.USub) else +number
            return ("float", repr(number))
        return None
    if isinstance(node, ast.Name):
        return symbols.get(node.id)
    if isinstance(node, (ast.Tuple, ast.List)):
        items = _normalize_sequence(node.elts, symbols)
        if items is None:
            return None
        return ("tuple" if isinstance(node, ast.Tuple) else "list", items)
    if isinstance(node, ast.Set):
        items = _normalize_sequence(node.elts, symbols)
        if items is None:
            return None
        # Order-insensitive: ``{1, 2}`` and ``{2, 1}`` are the same default.
        return ("set", frozenset(items))
    if isinstance(node, ast.Dict):
        return _normalize_dict(node, symbols)
    return None


def _tag_constant(value: object) -> Optional[tuple]:
    if value is None:
        return ("none",)
    if value is Ellipsis:
        return ("ellipsis",)
    # ``bool`` MUST precede ``int``: ``bool`` is an ``int`` subclass, but
    # ``True`` and ``1`` are different defaults that must not compare equal.
    if isinstance(value, bool):
        return ("bool", value)
    if isinstance(value, int):
        return ("int", value)
    if isinstance(value, float):
        # ``repr`` is the shortest round-tripping form, so it canonicalizes
        # equal floats written differently (``1e3`` and ``1000.0`` both ->
        # ``'1000.0'``) while keeping ``-0.0`` distinct from ``0.0`` (their
        # reprs differ). Signed zero is behaviorally observable
        # (``math.copysign``, ``1 / -0.0``, formatting), so the two must NOT
        # compare equal — fail closed toward reporting drift.
        return ("float", repr(value))
    if isinstance(value, complex):
        return ("complex", repr(value))
    if isinstance(value, str):
        return ("str", value)
    if isinstance(value, bytes):
        return ("bytes", value)
    return None


def _normalize_sequence(
    elts: Iterable[ast.AST],
    symbols: dict,
) -> Optional[tuple]:
    out = []
    for elt in elts:
        if isinstance(elt, ast.Starred):
            return None  # ``[*spread, 1]`` — not statically resolvable.
        norm = _normalize_default_node(elt, symbols)
        if norm is None:
            return None
        out.append(norm)
    return tuple(out)


def _normalize_dict(node: ast.Dict, symbols: dict) -> Optional[tuple]:
    items: dict = {}
    for key_node, value_node in zip(node.keys, node.values):
        if key_node is None:
            return None  # ``{**other}`` unpacking — not statically resolvable.
        key = _normalize_default_node(key_node, symbols)
        value = _normalize_default_node(value_node, symbols)
        if key is None or value is None:
            return None
        # Last value wins for identically-normalized keys. Keys that differ by
        # type (``1`` vs ``1.0``) stay distinct here rather than collapsing as a
        # live dict would — that can only make two dicts compare unequal, i.e.
        # fail closed toward reporting drift, never a false match.
        items[key] = value
    return ("dict", frozenset(items.items()))


def _existing_param_compatible(
    old: ParamContract,
    new: ParamContract,
    *,
    old_symbols: Optional[dict] = None,
    new_symbols: Optional[dict] = None,
) -> bool:
    if old.name != new.name:
        return False
    # Adding a default to a previously-required parameter preserves every call
    # form the old signature accepted (callers always supplied it), so widening
    # required -> optional is backward compatible.  Dropping a default the old
    # signature had IS a regression: callers that omitted the argument break.
    if old.has_default and not new.has_default:
        return False
    if old.has_default and new.has_default:
        # Each side resolves against its OWN module symbol table, so a default
        # written as a same-module constant (``max_chars=_LIMIT`` where
        # ``_LIMIT = 25000``) compares equal to the literal ``25000`` it stands
        # for. A provably-different default is ALWAYS a regression — including
        # the SAME constant name resolving to two different values across the
        # old and generated modules (``_LIMIT = 25000`` -> ``_LIMIT = 5000``),
        # whose signature text is identical yet whose value changed.
        verdict = compare_default_sources(
            old.default,
            new.default,
            left_symbols=old_symbols,
            right_symbols=new_symbols,
        )
        if verdict is DefaultCompatibility.INCOMPATIBLE:
            return False
        if verdict is DefaultCompatibility.UNKNOWN:
            # At least one side is opaque (a call, an imported name, a constant
            # the module rebinds). A default is backward compatible here ONLY
            # when BOTH sides are opaque AND the source text is identical: an
            # unchanged dynamic default such as ``x=helper()`` -> ``x=helper()``
            # changed nothing. When exactly ONE side resolves to a safe literal
            # while the other stays opaque — existing ``_LIMIT = load_limit()``
            # (or ``from cfg import _LIMIT``) -> generated ``_LIMIT = 5000``,
            # with identical ``_LIMIT`` text — we have positive evidence the
            # effective default MAY have changed, so matching text must not wave
            # it through. Fail closed, consistent with the gate's contract that
            # dynamic/imported defaults are not silently accepted.
            old_resolves = (
                _normalize_default_source(old.default, old_symbols or {}) is not None
            )
            new_resolves = (
                _normalize_default_source(new.default, new_symbols or {}) is not None
            )
            if old_resolves != new_resolves or old.default != new.default:
                return False
    # Annotation comparison is intentionally symmetric: ANY change to a public
    # parameter's type annotation trips the gate, including a backward-compatible
    # widening such as ``str`` -> ``str | int``.  This differs from the default
    # handling above on purpose -- adding a default only changes the calling
    # convention (a required argument becomes omittable; unambiguous, no
    # variance), whereas a type annotation is the value contract and its
    # variance is direction-dependent (widening a parameter is safe, but the
    # same change to a return type is a regression, and this comparator is also
    # used for returns and for declared-vs-actual conformance where the prompt
    # is the source of truth).  Rather than model per-use variance, the gate
    # conservatively flags every annotation change; an intentional one is
    # acknowledged with a ``BREAKING-CHANGE: change signature <symbol>`` line in
    # the prompt (honored by ``_prompt_breaking_change_signature_symbols`` in
    # the public-surface gate), which is the correct channel for a deliberate
    # public-API edit in a prompt-driven repo.
    return semantic_types_compatible(old.annotation, new.annotation)


def _params_from_arguments(
    args: ast.arguments,
    *,
    class_context: bool,
) -> Iterable[ParamContract]:
    positional = list(args.posonlyargs) + list(args.args)
    defaults = [None] * (len(positional) - len(args.defaults)) + list(args.defaults)

    for arg, default in zip(args.posonlyargs, defaults[: len(args.posonlyargs)]):
        yield _param_from_arg(
            arg,
            "posonly",
            default,
            class_context=class_context,
        )

    offset = len(args.posonlyargs)
    for arg, default in zip(args.args, defaults[offset:]):
        yield _param_from_arg(
            arg,
            "positional",
            default,
            class_context=class_context,
        )

    if args.vararg is not None:
        yield _param_from_arg(
            args.vararg,
            "vararg",
            None,
            class_context=class_context,
        )

    for arg, default in zip(args.kwonlyargs, args.kw_defaults):
        yield _param_from_arg(
            arg,
            "keyword_only",
            default,
            class_context=class_context,
        )

    if args.kwarg is not None:
        yield _param_from_arg(
            args.kwarg,
            "kwarg",
            None,
            class_context=class_context,
        )


def _param_from_arg(
    arg: ast.arg,
    kind: str,
    default: Optional[ast.AST],
    *,
    class_context: bool,
) -> ParamContract:
    has_default, default_text = _default_contract(
        default,
        class_context=class_context,
    )
    annotation = (
        _semantic_from_ast(arg.annotation, raw=ast.unparse(arg.annotation))
        if arg.annotation is not None
        else None
    )
    return ParamContract(
        name=arg.arg,
        kind=kind,
        annotation=annotation,
        default=default_text,
        has_default=has_default,
    )


def _default_contract(
    default: Optional[ast.AST],
    *,
    class_context: bool,
) -> tuple[bool, Optional[str]]:
    if default is None:
        return False, None
    if class_context and _dataclass_field_default_is_missing(default):
        return False, None
    return True, ast.unparse(default).strip()


def _dataclass_field_default_is_missing(default: ast.AST) -> bool:
    if not isinstance(default, ast.Call):
        return False
    func = default.func
    is_field = False
    if isinstance(func, ast.Name):
        is_field = func.id == "field"
    elif isinstance(func, ast.Attribute):
        is_field = func.attr == "field"
    if not is_field:
        return False
    for keyword in default.keywords:
        if keyword.arg in {"default", "default_factory"}:
            return False
    return True


def _semantic_from_ast(node: ast.AST, *, raw: str = "") -> Optional[SemanticType]:
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return parse_semantic_type(node.value)

    union_parts = _flatten_union(node)
    if union_parts is not None:
        non_none = [part for part in union_parts if not _is_none_type(part)]
        if len(non_none) == 1:
            # A single non-None member collapses to that member (``Union[str]``
            # -> ``str``); ``optional`` records whether ``None`` was also a
            # member (the ``Optional[X]`` / ``X | None`` case).
            inner = _semantic_from_ast(non_none[0], raw=ast.unparse(non_none[0]))
            if inner is None:
                return None
            return SemanticType(
                base=inner.base,
                args=inner.args,
                optional=inner.optional or len(non_none) != len(union_parts),
                raw=raw or ast.unparse(node),
            )
        parsed_parts = tuple(
            part
            for part in (
                _semantic_from_ast(part_node, raw=ast.unparse(part_node))
                for part_node in non_none
            )
            if part is not None
        )
        if len(parsed_parts) == len(non_none) and parsed_parts:
            return SemanticType(
                base="Union",
                args=parsed_parts,
                # Carry ``None`` membership even for 3+-member unions so a
                # narrowing like ``Union[str, int, None]`` -> ``Union[str, int]``
                # is not treated as compatible (the 2-member ``Optional`` path
                # above already did this; this is the multi-member equivalent).
                optional=len(non_none) != len(union_parts),
                raw=raw or ast.unparse(node),
            )
        return None

    if isinstance(node, ast.Subscript):
        base_name = _qualified_name(node.value)
        if base_name is None:
            return None
        # ``Union[...]`` and ``Optional[...]`` special forms are normalized
        # earlier by ``_flatten_union``; only ordinary generics reach here.
        items = _slice_items(node.slice)
        args = tuple(
            parsed
            for parsed in (
                _semantic_from_ast(item, raw=ast.unparse(item)) for item in items
            )
            if parsed is not None
        )
        if len(args) != len(items):
            return None
        return SemanticType(
            base=_canonical_base(base_name),
            args=args,
            optional=False,
            raw=raw or ast.unparse(node),
        )

    name = _qualified_name(node)
    if name is None:
        return None
    return SemanticType(
        base=_canonical_base(name),
        args=(),
        optional=False,
        raw=raw or ast.unparse(node),
    )


def _flatten_union(node: ast.AST) -> Optional[list[ast.AST]]:
    # PEP 604 ``X | Y`` form.
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        left = _flatten_union(node.left) or [node.left]
        right = _flatten_union(node.right) or [node.right]
        return left + right
    # ``Union[...]`` / ``Optional[...]`` subscript forms (also ``typing.``
    # prefixed).  Flatten members recursively so every union spelling
    # normalizes to the same flat member set:
    #   - nested unions: ``Union[Union[str, int], bytes]`` == ``Union[str, int, bytes]``
    #   - ``Optional[X]`` == ``Union[X, None]``, so a nested optional member
    #     hoists its ``None`` to the enclosing union
    #     (``Union[Optional[str], int]`` == ``Union[str, int, None]``).
    if isinstance(node, ast.Subscript):
        base_name = _qualified_name(node.value)
        special = _special_form_name(base_name) if base_name is not None else None
        if special in {"Union", "Optional"}:
            parts: list[ast.AST] = []
            for item in _slice_items(node.slice):
                parts.extend(_flatten_union(item) or [item])
            if special == "Optional":
                parts.append(ast.Constant(value=None))
            return parts
    return None


def _slice_items(node: ast.AST) -> list[ast.AST]:
    if isinstance(node, ast.Tuple):
        return list(node.elts)
    return [node]


def _qualified_name(node: ast.AST) -> Optional[str]:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        base = _qualified_name(node.value)
        if base:
            return f"{base}.{node.attr}"
    if isinstance(node, ast.Constant) and node.value is None:
        return "None"
    return None


def _special_form_name(name: str) -> Optional[str]:
    short = name.rsplit(".", 1)[-1]
    if short in _SPECIAL_FORMS and (
        "." not in name or name.startswith("typing.")
    ):
        return short
    return None


def _canonical_base(name: str) -> str:
    if name.startswith("typing."):
        name = name.split(".", 1)[1]
    elif name.startswith("builtins."):
        name = name.split(".", 1)[1]
    return _TYPING_ALIASES.get(name, name)


def _is_none_type(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant) and node.value is None:
        return True
    if isinstance(node, ast.Name) and node.id in {"None", "NoneType"}:
        return True
    if isinstance(node, ast.Attribute):
        return _qualified_name(node) in {"types.NoneType", "NoneType"}
    return False
