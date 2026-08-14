"""Static introspection of a Python module's public API.

Answers what a module exposes to importers and what shape each public callable
has, from source alone -- the module under inspection is never imported or
executed. One notion of "public" governs both answers, so the removed-symbol
diff and the signature diff cannot contradict each other.
"""

import ast
from typing import Dict, Iterator, List, Optional, Set


def _collect_bound_module_names(tree: ast.Module) -> Set[str]:
    """Return the set of all module-level names bound by ``tree``.

    Captures every name a ``from X import *`` would see, regardless of
    underscore prefix — used to filter ``__all__`` entries down to ones
    that are actually defined. The same kinds of bindings as
    :func:`_snapshot_public_surface` (functions, classes, Assign,
    AnnAssign-with-value, Import, ImportFrom) but without the
    underscore-prefix filter.
    """
    bound: Set[str] = set()

    def _walk_target(target: ast.AST) -> None:
        if isinstance(target, ast.Name):
            bound.add(target.id)
        elif isinstance(target, (ast.Tuple, ast.List)):
            for elt in target.elts:
                _walk_target(elt)
        elif isinstance(target, ast.Starred):
            _walk_target(target.value)

    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            bound.add(node.name)
        elif isinstance(node, ast.ClassDef):
            bound.add(node.name)
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                _walk_target(target)
        elif isinstance(node, ast.AnnAssign):
            if node.value is not None:
                _walk_target(node.target)
        elif isinstance(node, ast.Import):
            for alias in node.names:
                bound.add(alias.asname or alias.name.split(".", 1)[0])
        elif isinstance(node, ast.ImportFrom):
            # ``from __future__ import …`` is a compiler directive, not
            # a runtime module attribute callers can rely on. Excluding
            # it here means ``__all__ = ["annotations"]`` does NOT
            # promote the future-import binding into the public surface
            # (which would otherwise diff as ``removed: annotations``
            # when the directive is cleaned up after a Python-version
            # bump). Mirrors the same skip in `_snapshot_public_surface`
            # and `_snapshot_public_signatures`.
            if node.module == "__future__":
                continue
            for alias in node.names:
                if alias.name == "*":
                    continue
                bound.add(alias.asname or alias.name)
    return bound

# Scope and comprehension node groups used by the ``__all__`` mutation scan.
_SCOPE_NODE_TYPES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda,
)

_COMPREHENSION_TYPES = (
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
)

# List methods that mutate the receiver in place. A call to any of these on
# ``__all__`` (``__all__.append(...)`` etc.) changes the runtime export list,
# so a clean literal can no longer be trusted. Read-only methods like
# ``.copy()`` / ``.index()`` are deliberately excluded so they do not force the
# fallback needlessly.
_DUNDER_ALL_MUTATOR_METHODS = frozenset({
    "append", "extend", "insert", "remove", "pop", "clear",
    "sort", "reverse", "__setitem__", "__delitem__", "__iadd__",
})

def _scannable_children(node: ast.AST) -> Iterator[ast.AST]:
    """Yield the children of *node* to scan for module-level ``__all__`` writes,
    with two scope-aware adjustments:

    * A nested scope (def / async def / class / lambda) yields NOTHING — its
      body executes later (or never) against a LOCAL ``__all__``, and its header
      (decorators / defaults / annotations) is not scanned either: a write to
      ``__all__`` from there is absurd in generated code AND, for annotations
      under ``from __future__ import annotations``, never evaluated, so scanning
      it produced false positives. Such writes are an accepted limitation.
    * A comprehension / generator expression omits the loop TARGETS (Python-3
      comprehension-local) but yields the iterables, filter conditions, and
      element/key/value expressions, so a walrus (``(__all__ := ...)``) — which
      leaks to the enclosing scope — is still seen.

    Every other node yields all children unchanged.
    """
    if isinstance(node, _SCOPE_NODE_TYPES):
        return
    if isinstance(node, _COMPREHENSION_TYPES):
        for generator in node.generators:
            yield generator.iter
            yield from generator.ifs
        if isinstance(node, ast.DictComp):
            yield node.key
            yield node.value
        else:
            yield node.elt
        return
    yield from ast.iter_child_nodes(node)

def _node_writes_dunder_all(node: ast.AST) -> bool:
    """True if *node* itself is a direct write / in-place mutation of the bare
    module ``__all__`` name. ``_subtree_mutates_dunder_all`` applies it across a
    statement's whole subtree, so a non-literal rebind trips it through its
    target ``Name(__all__, Store)``. Clean literal rebinds never rely on this:
    ``_extract_dunder_all`` resolves them via ``_clean_dunder_all_literal``
    before the scan, so any ``__all__`` store/delete reaching here is an
    unresolvable (computed / conditional / unpacked) write."""
    store_del = (ast.Store, ast.Del)
    if isinstance(node, ast.Name):
        return node.id == "__all__" and isinstance(node.ctx, store_del)
    if isinstance(node, ast.Subscript):
        return (
            isinstance(node.value, ast.Name)
            and node.value.id == "__all__"
            and isinstance(node.ctx, store_del)
        )
    if isinstance(node, ast.Call):
        func = node.func
        return (
            isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)
            and func.value.id == "__all__"
            and func.attr in _DUNDER_ALL_MUTATOR_METHODS
        )
    # Pattern / exception captures bind a bare name given as a STRING field, so
    # they never appear as a Store ``Name`` node.
    if isinstance(node, ast.ExceptHandler):
        return node.name == "__all__"
    if isinstance(node, ast.MatchAs):
        return node.name == "__all__"
    if isinstance(node, ast.MatchStar):
        return node.name == "__all__"
    if isinstance(node, ast.MatchMapping):
        return node.rest == "__all__"
    # An import that BINDS ``__all__`` (``from exports import __all__`` /
    # ``from m import x as __all__`` / ``import __all__``) replaces the module's
    # ``__all__`` with an imported value we cannot resolve statically — so it is
    # an unreadable rebind, not just a normal import. (A plain ``from typing
    # import Any`` binds ``Any``, not ``__all__``, and is ignored here.)
    if isinstance(node, ast.ImportFrom):
        return any(
            (alias.asname or alias.name) == "__all__" for alias in node.names
        )
    if isinstance(node, ast.Import):
        return any(
            (alias.asname or alias.name.split(".", 1)[0]) == "__all__"
            for alias in node.names
        )
    return False

def _subtree_mutates_dunder_all(node: ast.AST) -> bool:
    """Recursively scan *node* (module-level execution) for any ``__all__``
    write/mutation, honouring scope and comprehension boundaries via
    ``_scannable_children``."""
    if _node_writes_dunder_all(node):
        return True
    return any(
        _subtree_mutates_dunder_all(child) for child in _scannable_children(node)
    )

def _clean_dunder_all_literal(node: ast.AST) -> Optional[Set[str]]:
    """Return the set of names when *node* is a top-level ``__all__ = <list /
    tuple of string literals>`` (or the bound-``AnnAssign`` form ``__all__: T =
    <same>``) — the ONLY statically readable ``__all__`` declaration. Returns
    ``None`` for any other statement (a non-literal/computed value, a non-string
    element, or a node that is not a direct ``__all__`` name assignment)."""
    if isinstance(node, ast.Assign):
        targets: List[ast.AST] = list(node.targets)
        value: Optional[ast.AST] = node.value
    elif isinstance(node, ast.AnnAssign) and node.value is not None:
        targets = [node.target]
        value = node.value
    else:
        return None
    if not any(isinstance(t, ast.Name) and t.id == "__all__" for t in targets):
        return None
    if not isinstance(value, (ast.List, ast.Tuple)):
        return None
    names: Set[str] = set()
    for elt in value.elts:
        if isinstance(elt, ast.Constant) and isinstance(elt.value, str):
            names.add(elt.value)
        else:
            return None
    return names

def _extract_dunder_all(tree: ast.Module) -> Optional[Set[str]]:
    """Return module-level ``__all__`` names if declared as a clean literal list.

    Walks every top-level assignment to ``__all__`` in source order and
    tracks a "current parse" state matching Python runtime semantics
    (subsequent assignments override earlier ones — the LAST assignment
    wins):

    - ``__all__ = [...]`` / ``__all__ = (...)`` whose elements are all
      ``ast.Constant`` string literals → set state to that set of
      strings.
    - ``__all__ = sorted(...)`` / ``__all__ = X + Y`` / any other
      non-literal RHS → set state to ``None``. The value is computed at
      runtime so a static parser cannot trust it, and the heuristic
      ("non-underscore") falls back.
    - ``__all__ += [...]`` (``ast.AugAssign``) → set state to ``None``.
      AugAssign mutates the previous list in place; even when the RHS
      is a clean literal we cannot statically be sure what's in the
      target object at that point (it could have been computed earlier).
      The safest correct rule is "any AugAssign to __all__ → fall back".
    - Bound ``ast.AnnAssign`` (``__all__: list[str] = [...]``) →
      treated the same as a plain assignment.

    Returns ``None`` when no clean ``__all__`` literal survives to the end of
    the module, when ``__all__`` is never assigned at module scope, OR when the
    last thing to touch ``__all__`` is a runtime write the literal cannot
    capture — a computed/imported rebind, an ``ast.AugAssign``, an in-place
    mutation (``__all__.append(...)``, ``__all__[i] = ...``, ``del __all__``), a
    conditional/looped rebind, etc. (see ``_subtree_mutates_dunder_all``). The
    scan is SOURCE-ORDER: an earlier mutation is OVERRIDDEN by a later clean
    literal rebind (``__all__ = [...]; __all__.append(...); __all__ = [...]`` is
    resolvable again), matching Python's last-write-wins runtime semantics. When
    the result is ``None`` the fallback "non-underscore" heuristic applies, which
    still protects defined symbols added via a mutation (e.g. a function appended
    to ``__all__``) while keeping imports re-export-only.
    """
    state: Optional[Set[str]] = None
    for node in tree.body:
        # A value-less annotation (``__all__: T``, ``__all__[0]: T``, ``x: T``)
        # does NOT assign or mutate at runtime — it is purely a type hint — so it
        # is a no-op for ``__all__`` resolution (leaves any prior clean literal
        # in place). Its target's ``Store`` ctx is an AST artifact, not a write.
        # (An annotation EXPRESSION that mutates ``__all__`` — ``x:
        # __all__.append(...)`` — is absurd and, under ``from __future__ import
        # annotations``, never even evaluated; treated as an accepted limitation.)
        if isinstance(node, ast.AnnAssign) and node.value is None:
            continue
        literal = _clean_dunder_all_literal(node)
        if literal is not None:
            # Clean top-level literal rebind — authoritative. A later one wins
            # and RESTORES resolvability even after an earlier mutation.
            state = literal
        elif _subtree_mutates_dunder_all(node):
            # Any other write to ``__all__`` (computed/imported rebind, augmented
            # assignment, in-place mutation, conditional/looped rebind, tuple
            # unpacking, walrus, ``for``/``with``/``except``/``case`` target):
            # the runtime value diverges from any static literal, so fall back.
            state = None
        # else: this statement does not touch ``__all__`` → state unchanged.
    return state

def _assign_target_matches(target: ast.AST, symbol: str) -> bool:
    """Return True when *symbol* is bound by an assignment target subtree."""
    if isinstance(target, ast.Name):
        return target.id == symbol
    if isinstance(target, (ast.Tuple, ast.List)):
        return any(_assign_target_matches(elt, symbol) for elt in target.elts)
    if isinstance(target, ast.Starred):
        return _assign_target_matches(target.value, symbol)
    return False

def _symbol_exists_in_module(tree: ast.Module, symbol: str) -> bool:
    """Return True when *symbol* is defined in *tree* (supports dotted class paths)."""
    if "." not in symbol:
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                if node.name == symbol:
                    return True
            elif isinstance(node, ast.Assign):
                for target in node.targets:
                    if _assign_target_matches(target, symbol):
                        return True
            elif isinstance(node, ast.AnnAssign):
                if node.value is not None and _assign_target_matches(node.target, symbol):
                    return True
        return False
    # Dotted: walk the leading segments as nested ``ClassDef`` containers, then
    # match the final segment as a method OR a (nested) class. Resolving the final
    # segment as a class too — not method-only — means a declared NESTED class
    # constructor whose path includes an underscore (``_Outer.Inner`` /
    # ``Outer._Inner``) is recognized as defined and captured via the patch-target
    # path, mirroring how the public recursion already keys nested classes as
    # ``Outer.Inner`` (codex round-9). This only ever recognizes MORE names as
    # defined, so no previously-matched name stops matching.
    parts = symbol.split(".")
    body: List[ast.stmt] = list(tree.body)
    for part in parts[:-1]:
        cls_node = next(
            (node for node in body if isinstance(node, ast.ClassDef) and node.name == part),
            None,
        )
        if cls_node is None:
            return False
        body = list(cls_node.body)
    last = parts[-1]
    return any(
        isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
        and child.name == last
        for child in body
    )

def _effective_patch_targets(
    existing_code: str,
    language: str,
    file_path: Optional[str],
) -> Set[str]:
    """Patch targets referenced by tests that are actually defined in *existing_code*."""
    candidates = _collect_patch_targets(file_path)
    if not candidates or (language or "").lower() not in {"python", "py"}:
        return set()
    try:
        tree = ast.parse(existing_code or "")
    except SyntaxError:
        return set()
    return {symbol for symbol in candidates if _symbol_exists_in_module(tree, symbol)}

def _collect_patch_targets(file_path: Optional[str]) -> Set[str]:
    """Return dotted symbol names patched by sibling tests for *file_path*."""
    from ..split_validation import collect_patch_symbols_for_module  # pylint: disable=import-outside-toplevel

    return set(collect_patch_symbols_for_module(file_path))

def _reexport_binding(alias: ast.alias) -> Optional[str]:
    """Return the bound name when an import *alias* is an explicit re-export.

    Imported names are implementation details by default: ``from typing import
    Any``, ``import json``, ``from dataclasses import dataclass`` and the like
    are tools the module uses, NOT part of the contract a downstream caller
    relies on. Removing such an import when a regeneration no longer needs it
    is a routine cleanup, not a public-API regression (issues #1662 / #1663 /
    pdd_cloud#2256 — the public-surface gate was hard-failing real syncs over
    `removed: Any, Literal, dataclass, field, json` and similar).

    An import counts as public surface ONLY when it is *deliberately*
    re-exported, following Python's own re-export convention (PEP 484, the
    same rule mypy enforces under ``implicit_reexport = False``):

    - a redundant alias ``import x as x`` / ``from m import y as y`` where the
      bound name equals the imported name (handled here), or
    - membership in a declared ``__all__`` (handled authoritatively by the
      ``__all__`` branches in the snapshot helpers, not here).

    Plain imports (``import git``) and *renaming* aliases (``from m import y as
    z``, ``z != y``) are NOT re-exports — to keep them protected a module must
    list them in ``__all__`` or use the redundant-alias form. Underscore
    (private) names are never public outside ``__all__``. Returns ``None`` for
    anything that is not an explicit, public re-export.
    """
    asname = alias.asname
    if asname is None or asname != alias.name or asname.startswith("_"):
        return None
    return asname

def _snapshot_public_surface(
    code_text: str,
    language: str,
    patch_targets: Optional[Set[str]] = None,
) -> Set[str]:
    """Collect public top-level functions/classes plus public class methods.

    Recurses into public nested classes so a method on ``Outer.Inner`` is
    recorded as ``Outer.Inner.method``; removing it would otherwise escape
    both the removed-symbol diff and the signature-change diff because the
    enclosing class ``Outer.Inner`` is unchanged.

    Module-level ``ast.Assign`` / ``ast.AnnAssign`` targets are ALSO captured
    as public surface — removing a public constant like ``PUBLIC_SETTING =
    ...`` is a real downstream-breaking change.

    Imports are captured ONLY when they are explicit re-exports: a redundant
    alias ``import x as x`` / ``from m import y as y`` (see
    ``_reexport_binding``) or a name listed in ``__all__``. Plain imports
    (``from typing import Any``, ``import json``) and renaming aliases are
    implementation details, so removing them does NOT trigger a regression
    (issues #1662 / #1663 / pdd_cloud#2256). ``from X import *`` and
    ``from __future__ import ...`` never contribute a fixed public name.

    When the module declares ``__all__`` as a clean list/tuple of string
    constants, that list is AUTHORITATIVE per Python semantics: a name is
    public if and only if it appears in ``__all__``, even if the name is
    underscore-prefixed (e.g. ``__all__ = ["_public_helper"]``). Symbols
    not in ``__all__`` are NOT considered part of the public surface when
    ``__all__`` is declared. If ``__all__`` is missing or malformed
    (computed expression, non-string elements), the fallback heuristic
    applies: capture top-level non-underscore names, skip private/dunder.
    ``from X import *`` contributes no fixed name and is ignored.
    """
    if (language or "").lower() not in {"python", "py"}:
        return set()
    try:
        tree = ast.parse(code_text or "")
    except SyntaxError:
        return set()

    dunder_all = _extract_dunder_all(tree)

    names: set[str] = set()

    def _walk_class(
        class_node: ast.ClassDef,
        qualname: str,
        include_underscore: bool = False,
    ) -> None:
        """Recursively add dotted names for class members.

        ``include_underscore=True`` is used when the enclosing top-level
        class was explicitly opted into the public surface via
        ``__all__``: in that case the user's intent is that the class
        and its members ARE the public API, so underscore-prefixed
        methods/nested classes are NOT silently excluded (consistent
        with the existing ``__all__`` semantics where listing an
        underscore-prefixed top-level name like ``_helper`` makes it
        public). Outside of ``__all__`` scope the previous heuristic
        applies and underscores filter out.
        """
        for child in class_node.body:
            if not isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                continue
            if not include_underscore and child.name.startswith("_"):
                continue
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                names.add(f"{qualname}.{child.name}")
            else:  # ast.ClassDef
                nested_qualname = f"{qualname}.{child.name}"
                names.add(nested_qualname)
                _walk_class(child, nested_qualname, include_underscore)

    if dunder_all is not None:
        # __all__ is authoritative. Names declared in __all__ that are
        # actually bound at module scope (anything in __all__ that isn't
        # defined would be a runtime ImportError on `from X import *`,
        # which is the module author's bug, not this gate's concern)
        # form the public surface — INCLUDING the recursively-walked
        # members of any class entry in __all__. Without that recursion
        # a removal like `Service.run` would slip past the gate even
        # though it's clearly part of the declared public class.
        class_defs: Dict[str, ast.ClassDef] = {
            node.name: node
            for node in tree.body
            if isinstance(node, ast.ClassDef)
        }
        bound = _collect_bound_module_names(tree)
        for name in dunder_all:
            if name not in bound:
                continue
            names.add(name)
            if name in class_defs:
                # User opted the whole class into __all__; treat its
                # members (including underscore-prefixed) as public.
                _walk_class(class_defs[name], name, include_underscore=True)
        if patch_targets:
            names.update(patch_targets)
        return names

    def _add_assign_targets(target: ast.AST) -> None:
        """Walk an assignment target, adding public bare-name identifiers.

        Handles tuple/list unpacking (``a, b = foo()`` and ``[a, b] = foo()``)
        by recursing into element lists. Attribute/subscript targets are
        ignored — those mutate existing objects, they don't create a new
        module-level name.
        """
        if isinstance(target, ast.Name):
            if not target.id.startswith("_"):
                names.add(target.id)
        elif isinstance(target, (ast.Tuple, ast.List)):
            for elt in target.elts:
                _add_assign_targets(elt)
        elif isinstance(target, ast.Starred):
            _add_assign_targets(target.value)

    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if not node.name.startswith("_"):
                names.add(node.name)
        elif isinstance(node, ast.ClassDef):
            if not node.name.startswith("_"):
                names.add(node.name)
                _walk_class(node, node.name)
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                _add_assign_targets(target)
        elif isinstance(node, ast.AnnAssign):
            # Only bound annotations bind a runtime module attribute: a bare
            # `PUBLIC_NAME: int` declaration is a type hint, not an export,
            # so it would create false-positive regressions when removed.
            # `PUBLIC_NAME: int = None` (explicit None value) still binds and
            # is captured because `node.value` is the `ast.Constant(None)`
            # node, not Python `None`.
            if node.value is not None:
                _add_assign_targets(node.target)
        elif isinstance(node, ast.Import):
            for alias in node.names:
                # Only explicit re-exports (``import foo as foo``) are public
                # surface; a plain ``import foo`` / ``import foo.bar`` is an
                # implementation detail (see ``_reexport_binding``). Names in a
                # clean ``__all__`` are handled by the authoritative branch
                # above (which returns before this fallback).
                exposed = _reexport_binding(alias)
                if exposed:
                    names.add(exposed)
        elif isinstance(node, ast.ImportFrom):
            # ``from __future__ import annotations`` (and other future
            # imports) are compiler directives, not module attributes —
            # callers never write `mymodule.annotations`. Treating them
            # as public surface would block harmless cleanup like
            # removing the directive after a Python-version bump.
            if node.module == "__future__":
                continue
            for alias in node.names:
                # ``from X import *`` has alias.name == "*"; no fixed
                # identifier is bound, so it does not contribute.
                if alias.name == "*":
                    continue
                # Only redundant-alias re-exports (``from m import y as y``)
                # are public surface; a plain ``from typing import Any`` or a
                # renaming alias ``from m import y as z`` is an implementation
                # detail (see ``_reexport_binding``).
                exposed = _reexport_binding(alias)
                if exposed:
                    names.add(exposed)

    if patch_targets:
        names.update(patch_targets)

    return names

def _diff_public_surface(pre: Set[str], post: Set[str]) -> List[str]:
    """Return public symbols present before generation but absent after it."""
    return sorted(set(pre) - set(post))

def _format_python_signature(node: ast.AST, *, skip_first: bool = False) -> str:
    """Return a stable public-call signature string for a function-like AST node."""
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return ""
    args = node.args
    parts: List[str] = []

    def add_arg(arg: ast.arg, default: Optional[ast.AST] = None) -> None:
        text = arg.arg
        if arg.annotation is not None:
            text += f": {ast.unparse(arg.annotation)}"
        if default is not None:
            text += f"={ast.unparse(default)}"
        parts.append(text)

    posonly = list(args.posonlyargs)
    regular = list(args.args)
    # ``skip_first=True`` drops the implicit receiver (``self`` /
    # ``cls``) so an instance method is compared receiver-stripped. The
    # receiver lives in posonly when present (rare — e.g. PEP 570
    # methods), otherwise in ``args.args``. Strip from the correct list
    # so the remaining count used for the ``/`` marker insertion below
    # stays accurate (external review PR #1015).
    if skip_first:
        if posonly:
            posonly = posonly[1:]
        elif regular:
            regular = regular[1:]
    positional = posonly + regular
    defaults: List[Optional[ast.AST]] = [None] * (
        len(positional) - len(args.defaults)
    ) + list(args.defaults)
    parts_before_positional = len(parts)
    for arg, default in zip(positional, defaults):
        add_arg(arg, default)
    # Emit a literal ``/`` separator IMMEDIATELY after the
    # positional-only group so ``def f(x, /, y)`` and ``def f(x, y)``
    # produce DIFFERENT signature snapshots — kwarg-only callers
    # (``f(x=1, y=2)``) succeed against the second but break against
    # the first, and the public-surface gate must catch the
    # regression. Mirror the ``*`` insertion below for ``kwonlyargs``.
    # Skip when no posonly args remain after ``skip_first`` (a
    # stripped lone-receiver posonly leaves zero, in which case the
    # function is effectively a regular method and no ``/`` is
    # needed). External review PR #1015.
    if posonly:
        parts.insert(parts_before_positional + len(posonly), "/")
    if args.vararg:
        text = "*" + args.vararg.arg
        if args.vararg.annotation is not None:
            text += f": {ast.unparse(args.vararg.annotation)}"
        parts.append(text)
    elif args.kwonlyargs:
        parts.append("*")
    for arg, default in zip(args.kwonlyargs, args.kw_defaults):
        add_arg(arg, default)
    if args.kwarg:
        text = "**" + args.kwarg.arg
        if args.kwarg.annotation is not None:
            text += f": {ast.unparse(args.kwarg.annotation)}"
        parts.append(text)
    returns = ""
    if node.returns is not None:
        returns = f" -> {ast.unparse(node.returns)}"
    prefix = "async " if isinstance(node, ast.AsyncFunctionDef) else ""
    return f"{prefix}({', '.join(parts)}){returns}"

def _python_method_binding_kind(node: ast.AST) -> str:
    """Return the binding kind ('instance', 'staticmethod', 'classmethod',
    'property', 'property_accessor') for a class-body function-like node
    based on its decorators.

    Used by :func:`_snapshot_public_signatures` to prefix the captured
    signature string so that a binding-kind flip (e.g. ``def f(self, x)``
    becoming ``@staticmethod def f(x)``) is detected as a signature change
    even though the receiver-stripped parameter list is identical. Without
    this prefix, callers doing ``Class.f(1)`` would silently break across
    generations because the gate compared only normalized params.

    The ``property_accessor`` kind covers ``@x.setter`` / ``@x.getter`` /
    ``@x.deleter`` Attribute decorators — the caller is expected to merge
    these with the matching ``@property`` getter into a single combined
    snapshot per property name (see ``_walk_class``). Returning a
    dedicated kind for accessors prevents the last-write-wins overwrite
    that previously let a setter-decorated function be classified as a
    plain ``[instance]`` method.
    """
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return "instance"
    for decorator in getattr(node, "decorator_list", []):
        # Recognize property accessor decorators FIRST so ``@x.setter``
        # (an Attribute node with ``attr in {"setter","getter","deleter"}``)
        # is not silently flattened to ``instance`` by the generic
        # Attribute fallthrough below.
        if (
            isinstance(decorator, ast.Attribute)
            and decorator.attr in {"setter", "getter", "deleter"}
        ):
            return "property_accessor"
        name: Optional[str] = None
        if isinstance(decorator, ast.Name):
            name = decorator.id
        elif isinstance(decorator, ast.Attribute):
            name = decorator.attr
        elif isinstance(decorator, ast.Call):
            inner = decorator.func
            if isinstance(inner, ast.Name):
                name = inner.id
            elif isinstance(inner, ast.Attribute):
                name = inner.attr
        if name == "staticmethod":
            return "staticmethod"
        if name == "classmethod":
            return "classmethod"
        if name == "property":
            return "property"
    return "instance"

def _python_property_accessor_role(node: ast.AST) -> Optional[str]:
    """Return ``'getter'`` / ``'setter'`` / ``'deleter'`` when ``node`` is a
    property accessor — that is, decorated with ``@property`` (getter),
    ``@<name>.setter``, ``@<name>.getter``, or ``@<name>.deleter``.

    Returns ``None`` otherwise. Used by ``_walk_class`` to accumulate
    accessor roles per property name so the final snapshot reflects ALL
    accessors that exist (e.g. ``getter+setter``). Without this merge the
    setter would overwrite the getter entry and a rewrite that replaced
    the descriptor with a plain ``def x(self, value)`` could produce an
    identical snapshot string.
    """
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return None
    for decorator in getattr(node, "decorator_list", []):
        if isinstance(decorator, ast.Name) and decorator.id == "property":
            return "getter"
        if (
            isinstance(decorator, ast.Attribute)
            and decorator.attr in {"setter", "getter", "deleter"}
        ):
            return decorator.attr
    return None

def _is_dataclass_decorator(decorator: ast.AST) -> bool:
    """Return True when ``decorator`` is a stdlib ``@dataclass`` form.

    Recognises ALL four AST shapes the parser produces for the stdlib
    ``dataclasses.dataclass`` decorator:

    * ``@dataclass``                       -> ``ast.Name(id="dataclass")``
    * ``@dataclasses.dataclass``           -> ``ast.Attribute(attr="dataclass",
      value=ast.Name(id="dataclasses"))``
    * ``@dataclass(frozen=True)``          -> ``ast.Call`` wrapping the Name form
    * ``@dataclasses.dataclass(frozen=True)`` -> ``ast.Call`` wrapping the
      Attribute form

    SCOPE NOTE: this intentionally does NOT handle third-party
    dataclass-like decorators such as ``@attr.s`` / ``@attrs.define`` /
    ``@attr.define`` / ``@pydantic.dataclasses.dataclass`` (their
    field-resolution rules diverge — e.g. ``attrs`` filters by
    ``attr.ib()`` / ``attr.field()`` markers, ``pydantic`` honours
    ``Field(...)`` defaults differently). The synthesised init signature
    for those decorators falls back to the existing ``()`` shape and
    field changes there are NOT yet detected by this snapshot. Future
    iteration may extend coverage.
    """
    target = decorator.func if isinstance(decorator, ast.Call) else decorator
    if isinstance(target, ast.Name) and target.id == "dataclass":
        return True
    if (
        isinstance(target, ast.Attribute)
        and target.attr == "dataclass"
        and isinstance(target.value, ast.Name)
        and target.value.id == "dataclasses"
    ):
        return True
    return False

def _dataclass_decorator_is_kw_only(decorator: ast.AST) -> bool:
    """Return True when ``decorator`` is ``@dataclass(kw_only=True)``.

    Companion to :func:`_is_dataclass_decorator`. The caller is expected
    to invoke this on a decorator that ALREADY passed the dataclass
    check, so this helper focuses only on the ``kw_only`` keyword
    extraction. Returns False for the bare ``@dataclass`` form (no Call
    wrapper) and for any explicit ``kw_only=False`` — matching the
    runtime default where fields are positional unless opted out.
    """
    if not isinstance(decorator, ast.Call):
        return False
    for keyword in decorator.keywords:
        if (
            keyword.arg == "kw_only"
            and isinstance(keyword.value, ast.Constant)
            and keyword.value.value is True
        ):
            return True
    return False

def _dataclass_decorator_synthesizes_init(decorator: ast.AST) -> bool:
    """Return True when this dataclass decorator synthesises ``__init__``.

    The stdlib ``@dataclass`` decorator synthesises an ``__init__`` by
    default. Callers that opt out via ``@dataclass(init=False)`` keep
    the class's natural ``__init__`` (typically ``object.__init__`` —
    zero positional args). The reviewer reproduced both directions of
    the resulting regression:

    * Flipping ``@dataclass(init=False)`` → ``@dataclass`` adds a
      synthesised constructor; the gate must trip.
    * Adding fields under ``@dataclass(init=False)`` leaves the runtime
      ``__init__`` untouched; the gate must NOT trip.

    Returns ``True`` for the bare ``@dataclass`` Name form (no Call
    wrapper), the ``@dataclasses.dataclass`` Attribute form, and any
    ``Call`` form whose keywords either omit ``init`` or set
    ``init=True``. Returns ``False`` ONLY when an explicit
    ``init=False`` keyword is present.

    Companion to :func:`_is_dataclass_decorator`. Callers are expected
    to invoke this on a decorator that ALREADY passed the dataclass
    check.
    """
    if not isinstance(decorator, ast.Call):
        # Bare ``@dataclass`` / ``@dataclasses.dataclass`` — default
        # ``init=True``.
        return True
    for keyword in decorator.keywords:
        if (
            keyword.arg == "init"
            and isinstance(keyword.value, ast.Constant)
            and keyword.value.value is False
        ):
            return False
    return True

def _is_kw_only_sentinel(annotation: Optional[ast.AST]) -> bool:
    """Return True when ``annotation`` is the stdlib ``KW_ONLY`` sentinel.

    Accepts bare ``KW_ONLY`` (``ast.Name``) and the module-qualified
    ``dataclasses.KW_ONLY`` (``ast.Attribute``) forms. Used by
    :func:`_synthesize_dataclass_init_signature` to recognise the
    in-body marker that splits earlier positional fields from later
    keyword-only fields.
    """
    if annotation is None:
        return False
    if isinstance(annotation, ast.Name) and annotation.id == "KW_ONLY":
        return True
    if isinstance(annotation, ast.Attribute) and annotation.attr == "KW_ONLY":
        return True
    return False

def _dataclass_field_call_is_init_false(value: Optional[ast.AST]) -> bool:
    """Return True for a ``field(init=False, ...)`` / ``dataclasses.field(init=False, ...)`` call.

    Mirrors the stdlib ``dataclasses`` rule that a field whose
    ``field(init=False)`` call excludes the attribute from the
    synthesised ``__init__``. Used by
    :func:`_synthesize_dataclass_init_signature` to drop such fields
    from the snapshot — including them was a false-positive source
    (``cache: dict = field(init=False, default_factory=dict)`` is an
    implementation detail, not a constructor parameter).

    Defensive about everything else: ``field(init=True)``,
    ``field(default=...)`` without ``init``, or any non-``field`` call
    return False so the field stays IN the snapshot. Matching the bare
    ``field`` name and the ``dataclasses.field`` attribute form covers
    the common import styles.
    """
    if not isinstance(value, ast.Call):
        return False
    func = value.func
    if isinstance(func, ast.Name):
        if func.id != "field":
            return False
    elif isinstance(func, ast.Attribute):
        if func.attr != "field":
            return False
    else:
        return False
    for keyword in value.keywords:
        if (
            keyword.arg == "init"
            and isinstance(keyword.value, ast.Constant)
            and keyword.value.value is False
        ):
            return True
    return False

def _collect_dataclass_own_parts(class_node: ast.ClassDef) -> List[str]:
    """Return the per-field signature tokens for a single dataclass's body.

    Returns a list of strings that mix actual field tokens (``name:
    annotation = default``) with the kw-only marker ``"*"`` inserted at
    the correct positions. The caller stitches base-class tokens in
    front of this list and post-processes the combined sequence.

    Field-extraction rules mirror :func:`_synthesize_dataclass_init_signature`'s
    historical body (kw-only decorator, ``KW_ONLY`` sentinel,
    underscore skip, ``ClassVar`` skip, ``field(init=False)`` skip,
    annotation/default verbatim text, ``InitVar`` left in).
    """
    decorator_kw_only = any(
        _dataclass_decorator_is_kw_only(dec)
        for dec in class_node.decorator_list
        if _is_dataclass_decorator(dec)
    )
    parts: List[str] = []
    kw_only_marker_inserted = False
    if decorator_kw_only:
        # ``@dataclass(kw_only=True)`` short-circuits to a single ``*``
        # at the front; any ``_: KW_ONLY`` sentinel inside the body
        # becomes redundant and must NOT emit a second marker.
        parts.append("*")
        kw_only_marker_inserted = True
    for child in class_node.body:
        if not isinstance(child, ast.AnnAssign):
            continue
        target = child.target
        if not isinstance(target, ast.Name):
            continue
        # ``_: KW_ONLY`` is the canonical sentinel — its name starts
        # with ``_`` so the underscore-prefix skip below would otherwise
        # swallow it. Recognise the sentinel FIRST and translate it into
        # a positional ``*`` marker (unless the decorator already
        # injected one).
        if _is_kw_only_sentinel(child.annotation):
            if not kw_only_marker_inserted:
                parts.append("*")
                kw_only_marker_inserted = True
            continue
        name = target.id
        if name.startswith("_"):
            continue
        annotation_text = ast.unparse(child.annotation) if child.annotation else ""
        # ``ClassVar`` annotations are class-level constants per PEP
        # 557, NOT init params. ``InitVar`` is intentionally NOT
        # filtered: it IS an init parameter; the annotation text rides
        # through verbatim so an ``InitVar[int]`` ↔ ``int`` flip diffs.
        if "ClassVar" in annotation_text:
            continue
        if _dataclass_field_call_is_init_false(child.value):
            # ``cache: dict = field(init=False, default_factory=dict)``
            # — runtime constructor omits this field, so the snapshot
            # must too.
            continue
        part = f"{name}: {annotation_text}" if annotation_text else name
        if child.value is not None:
            part += f" = {ast.unparse(child.value)}"
        parts.append(part)
    return parts

def _part_field_name(part: str) -> Optional[str]:
    """Extract the field name from a single synth token.

    Tokens look like ``name: annotation = default`` or ``name`` — the
    name is the substring up to the first ``:`` / ``=``. The kw-only
    marker ``"*"`` and the ``[inherited_unresolved]`` sentinel return
    ``None`` so callers know to leave them in place rather than dedupe.
    """
    if not part or part in {"*", "[inherited_unresolved]"}:
        return None
    head = part.split(":", 1)[0]
    head = head.split("=", 1)[0]
    head = head.strip()
    return head or None

def _collect_dataclass_inherited_parts(
    class_node: ast.ClassDef,
    class_defs: Optional[Dict[str, ast.ClassDef]],
    imported_names: Optional[Set[str]],
    visited: frozenset,
) -> List[str]:
    """Return synth tokens from this class's ``@dataclass`` base classes.

    Walks base classes in REVERSE order (matching Python's
    ``@dataclass`` runtime: ``__dataclass_fields__`` is populated in
    reverse-MRO so later bases override earlier ones in the field-dict
    insertion order, and the synthesised ``__init__`` parameter order
    reflects that walk). For ``class C(A, B)`` we therefore yield
    ``B``'s contributions first, then ``A``'s, and the outer merge in
    :func:`_synthesize_dataclass_init_signature` appends ``C``'s own
    fields last to produce ``(b, a, c)``.

    For each ``Name`` base that resolves to a same-module ``ClassDef``
    with a dataclass decorator, recursively gather ITS inherited parts
    first and then ITS own parts. Bases that don't resolve locally
    (cross-module imports, attribute-form references like ``pkg.Base``)
    emit a single ``"[inherited_unresolved]"`` token so the final
    signature is annotated as uncertain — local field changes still
    diff, but we don't claim authoritative knowledge of the imported
    base's fields.

    The ``visited`` set guards against accidental self-reference cycles
    (``class A(A): ...`` is illegal at runtime but the AST permits it).

    A base decorated with ``@dataclass(init=False)`` STILL contributes
    its annotated fields to a derived ``@dataclass``'s synth: the
    ``init=False`` flag only suppresses the BASE's own ``__init__``
    synthesis, while Python's dataclass machinery still records the
    fields in ``__dataclass_fields__`` and the derived class picks
    them up. We therefore walk a base's fields whenever it carries
    ANY ``@dataclass`` decorator, regardless of the ``init`` flag.

    Known limitation (documented for future iteration): ``KW_ONLY``
    sentinel propagation across the inheritance boundary is not
    modelled — the derived class re-emits its own marker.
    """
    if class_defs is None:
        return []
    inherited: List[str] = []
    for base in reversed(class_node.bases):
        if not isinstance(base, ast.Name):
            # Attribute-form base (``pkg.Base``) or other expression —
            # we can't see the source from here.
            inherited.append("[inherited_unresolved]")
            continue
        base_name = base.id
        if base_name in visited:
            # Cycle guard. Real Python would raise ``TypeError`` at
            # class creation; bail out gracefully so the snapshot stays
            # well-formed.
            continue
        base_def = class_defs.get(base_name)
        if base_def is None:
            # Base is an imported name or otherwise not declared in
            # this module — mark uncertain.
            if imported_names is None or base_name in imported_names:
                inherited.append("[inherited_unresolved]")
            else:
                # Base is a free name that's not a same-module class
                # and not imported (e.g. ``object`` builtin) — no
                # dataclass fields to merge.
                continue
            continue
        base_dataclass_decorators = [
            dec for dec in base_def.decorator_list if _is_dataclass_decorator(dec)
        ]
        if not base_dataclass_decorators:
            # Non-dataclass base contributes no fields to the
            # synthesised init.
            continue
        # NOTE: We intentionally do NOT skip bases decorated with
        # ``@dataclass(init=False)``. Their fields still live in
        # ``__dataclass_fields__`` and the derived dataclass merges
        # them when synthesising ITS own ``__init__``. The
        # ``init=False`` flag only matters to the BASE class's own
        # init synthesis (handled in pass-3, not here).
        new_visited = visited | {base_name}
        inherited.extend(
            _collect_dataclass_inherited_parts(
                base_def, class_defs, imported_names, new_visited
            )
        )
        inherited.extend(_collect_dataclass_own_parts(base_def))
    return inherited

def _synthesize_dataclass_init_signature(
    class_node: ast.ClassDef,
    class_defs: Optional[Dict[str, ast.ClassDef]] = None,
    imported_names: Optional[Set[str]] = None,
) -> str:
    """Build a constructor signature for an ``@dataclass`` class with no explicit init.

    Walks the class body in source order, treating each top-level
    ``ast.AnnAssign`` (annotated assignment) whose target is a bare
    ``ast.Name`` as a constructor field — matching the stdlib
    ``dataclasses`` runtime behaviour (field order in the synthesised
    ``__init__`` is the source order of the annotated attributes).

    Keyword-only handling:

    * ``@dataclass(kw_only=True)`` on the class decorator: ALL fields
      go after a single ``*`` marker. Detected by
      :func:`_dataclass_decorator_is_kw_only`.
    * ``_: KW_ONLY`` sentinel inside the class body (``KW_ONLY`` or
      ``dataclasses.KW_ONLY``): fields BEFORE the sentinel are
      positional; fields AFTER are kw-only. Detected by
      :func:`_is_kw_only_sentinel`. The sentinel itself contributes no
      param. When the decorator already opts the whole class into
      kw-only mode, the sentinel is redundant — emit only one ``*``.

    Excluded from the synth:

    * Underscore-prefixed field names: dataclass DOES synthesise an
      init param for them at runtime, but they are NOT part of the
      *public* API surface this snapshot tracks. The ``KW_ONLY``
      sentinel check runs BEFORE this skip so the canonical ``_:
      KW_ONLY`` marker still splits the signature.
    * ``ClassVar[...]`` annotations: dataclasses skip these per PEP
      557. Substring match on the unparsed annotation handles both
      bare ``ClassVar`` and the ``typing.ClassVar`` / ``t.ClassVar``
      forms.
    * ``field(init=False, ...)`` defaults: the stdlib excludes these
      from the synthesised ``__init__``. Detected by
      :func:`_dataclass_field_call_is_init_false`.
    * Plain ``ast.Assign`` without annotation: ``x = 5`` is a class-
      level constant, NOT a dataclass field.

    Included (vs. the previous iteration):

    * ``InitVar[...]`` annotations: dataclasses DO pass these to
      ``__init__`` (and ``__post_init__``) — they ARE constructor
      parameters even though they are not stored as instance
      attributes. Treating them as fields keeps ``inspect.signature``
      and the snapshot in sync. Flipping an ``InitVar[int]`` to a
      regular ``int`` annotation surfaces as a diff naturally because
      the snapshot prints the verbatim annotation text.

    Inheritance handling (added for PR #1015, iter-6; refined iter-7):

    * When ``class_defs`` is provided, base classes named directly
      (``class User(_Base)``) are resolved against the same-module
      ``ClassDef`` map. Resolved bases that are themselves
      ``@dataclass``-decorated contribute their fields FIRST, matching
      the runtime constructor ordering (``base_fields ++
      derived_own_fields``).
    * Multiple inheritance follows REVERSE-MRO order, matching the
      stdlib ``@dataclass`` rule that ``__dataclass_fields__`` is
      populated by walking bases right-to-left so later bases overwrite
      earlier ones in dict-insertion order. For ``class C(A, B)`` the
      synth is therefore ``(b, a, c)`` — B's fields, then A's, then C's
      own. Implemented by iterating ``reversed(class_node.bases)`` in
      :func:`_collect_dataclass_inherited_parts`.
    * Diamond inheritance dedupes by field name via the outer dict
      merge: when both ``A`` and ``B`` inherit ``X`` (with field ``x``),
      the synth contains ``x`` exactly once. In walk order the LAST
      contribution wins, which under reverse-base iteration is the
      LEFTMOST base's branch.
    * ``@dataclass(init=False)`` bases STILL contribute their fields:
      ``init=False`` only suppresses the BASE's own ``__init__`` synth;
      derived dataclasses still merge those fields per
      ``__dataclass_fields__`` semantics.
    * Override semantics: if a base and the derived class declare the
      same field name, the derived class's annotation/default text
      replaces the base's WHILE PRESERVING the base's position. This
      mirrors what ``@dataclass`` actually synthesises — Python's
      insertion-order dict keeps the original slot when a key is
      reassigned.
    * Unresolved bases (cross-module imports, attribute-form
      references) annotate the signature with an
      ``[inherited_unresolved]`` token. Local field changes still
      shift the snapshot; invisible upstream field changes do not — the
      gate is intentionally conservative for cases it cannot see.

    Default values are emitted verbatim via ``ast.unparse``. This
    includes ``field(default_factory=...)`` and
    ``field(default=sentinel)`` expressions — the snapshot diff
    therefore reflects ANY change to the literal default text, even if
    runtime semantics are equivalent. That is the conservative
    behaviour callers expect from the public-surface gate.
    """
    own_parts = _collect_dataclass_own_parts(class_node)
    inherited_parts = _collect_dataclass_inherited_parts(
        class_node,
        class_defs,
        imported_names,
        frozenset({class_node.name}),
    )

    # Merge inherited and own parts. Preserve the inherited slot for
    # an override (derived class re-declares a base field): the
    # position is the base's, but the annotation/default come from the
    # derived class. ``dict[str, str]`` insertion order is stable on
    # Python 3.7+ and update-in-place is positionally idempotent so
    # this matches what ``@dataclass`` actually does.
    merged_named: Dict[str, str] = {}
    leading_markers: List[str] = []
    seen_field = False
    for part in inherited_parts:
        field_name = _part_field_name(part)
        if field_name is None:
            if not seen_field:
                # Leading kw-only / unresolved markers from inherited
                # walk land in front of all fields.
                leading_markers.append(part)
            else:
                # ``*`` inside an inherited sequence preserves
                # positioning by encoding the marker as a synthetic
                # entry whose key is unique (so dict lookups don't
                # collide).
                marker_key = f"__marker_{len(merged_named)}__"
                merged_named[marker_key] = part
            continue
        seen_field = True
        merged_named[field_name] = part
    for part in own_parts:
        field_name = _part_field_name(part)
        if field_name is None:
            marker_key = f"__marker_{len(merged_named)}__"
            merged_named[marker_key] = part
            continue
        if field_name in merged_named:
            # Override: keep base's slot, replace text with derived's.
            merged_named[field_name] = part
        else:
            merged_named[field_name] = part

    parts: List[str] = list(leading_markers) + list(merged_named.values())

    # Strip a trailing ``*`` if no kw-only fields followed the sentinel
    # — ``(*)`` is not a valid signature and would falsely diff against
    # an empty ``()`` synth.
    if parts and parts[-1] == "*":
        parts.pop()
    return f"({', '.join(parts)})"

def _resolve_class_node(
    tree: ast.Module, symbol: str
) -> Optional[ast.ClassDef]:
    """Resolve a (possibly dotted / nested) class path to its ``ClassDef`` node.

    Walks each dotted segment through nested class bodies (``Outer.Inner`` ->
    the ``Inner`` node inside ``Outer``). Returns ``None`` when any segment is not
    a class — so a dotted method path (``Outer.method``) resolves to ``None`` and
    the caller falls back to method-signature capture. Used to give a patch-target
    nested class its ``[class]`` constructor-ABI entry (codex round-9).
    """
    body: List[ast.stmt] = list(tree.body)
    node: Optional[ast.ClassDef] = None
    for part in symbol.split("."):
        node = next(
            (child for child in body if isinstance(child, ast.ClassDef) and child.name == part),
            None,
        )
        if node is None:
            return None
        body = list(node.body)
    return node

def _class_constructor_signature(
    class_node: ast.ClassDef,
    class_defs: Dict[str, ast.ClassDef],
    imported_names: Set[str],
) -> str:
    """Return a class's constructor-ABI signature string (no ``[class]`` prefix).

    Mirrors an explicit receiver-stripped ``__init__``, a synthesised stdlib
    ``@dataclass`` init, or the bare ``()`` fallback — the exact logic
    :func:`_snapshot_public_signatures` uses for the ``[class]`` entry, extracted
    so a patch-target class (e.g. a declared underscore class whose constructor is
    the contract) can reuse it (codex round-8 finding 3).
    """
    explicit_init: Optional[ast.AST] = None
    for child in class_node.body:
        if (
            isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
            and child.name == "__init__"
        ):
            explicit_init = child
            break
    if explicit_init is not None:
        return _format_python_signature(explicit_init, skip_first=True)
    dataclass_decorators = [
        dec for dec in class_node.decorator_list if _is_dataclass_decorator(dec)
    ]
    is_dataclass = bool(dataclass_decorators)
    init_synthesized = all(
        _dataclass_decorator_synthesizes_init(dec) for dec in dataclass_decorators
    )
    if is_dataclass and init_synthesized:
        return _synthesize_dataclass_init_signature(
            class_node, class_defs=class_defs, imported_names=imported_names
        )
    return "()"

def _patch_target_signature_entry(
    tree: ast.Module,
    symbol: str,
    class_defs: Dict[str, ast.ClassDef],
) -> Optional[str]:
    """Return a snapshot signature string for a patched callable *symbol*."""
    if "." not in symbol:
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == symbol:
                kind = "async_function" if isinstance(node, ast.AsyncFunctionDef) else "function"
                return f"[{kind}] {_format_python_signature(node)}"
        return None

    parts = symbol.split(".")
    cls_name = parts[0]
    cls_node = class_defs.get(cls_name)
    if cls_node is None:
        return None

    if len(parts) == 2:
        method_name = parts[1]
        for child in cls_node.body:
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)) and child.name == method_name:
                binding_kind = _python_method_binding_kind(child)
                skip_first = binding_kind != "staticmethod"
                return f"[{binding_kind}] {_format_python_signature(child, skip_first=skip_first)}"
        return None

    inner_cls, method_name = parts[1], parts[2]
    for child in cls_node.body:
        if isinstance(child, ast.ClassDef) and child.name == inner_cls:
            for method in child.body:
                if isinstance(method, (ast.FunctionDef, ast.AsyncFunctionDef)) and method.name == method_name:
                    binding_kind = _python_method_binding_kind(method)
                    skip_first = binding_kind != "staticmethod"
                    return (
                        f"[{binding_kind}] {_format_python_signature(method, skip_first=skip_first)}"
                    )
    return None

def _snapshot_public_signatures(
    code_text: str,
    language: str,
    patch_targets: Optional[Set[str]] = None,
) -> Dict[str, str]:
    """Collect signatures for public top-level functions, classes, and class methods.

    Recurses into public nested classes so a method like ``Outer.Inner.method``
    has its signature snapshot keyed by the same fully qualified name used in
    :func:`_snapshot_public_surface`. Without this the removed-symbol diff and
    the signature diff disagree on nested methods.

    When the module declares ``__all__`` as a clean list/tuple of string
    constants, that list is authoritative (same rule as
    :func:`_snapshot_public_surface`): a top-level function/class is
    captured only if it appears in ``__all__``, even when underscore-
    prefixed. Without that mirror the removed-symbol diff and the
    signature-drift diff would disagree on what is "public".

    Class methods are stored with a leading ``[<kind>]`` binding prefix
    (``[instance]``, ``[staticmethod]``, ``[classmethod]``, ``[property:...]``)
    so that a binding flip — e.g. ``def f(self, v)`` → ``@staticmethod def
    f(v)`` — produces a snapshot diff even when the receiver-stripped
    parameter list matches. Property descriptors carry a sorted accessor
    list (``[property:getter]``, ``[property:getter+setter]``, ...) so a
    rewrite that drops the descriptor in favor of a plain ``def x(self,
    value)`` cannot collide with the original snapshot.

    Top-level functions / async functions / classes carry a symbol-kind
    prefix (``[function]`` / ``[async_function]`` / ``[class]``) so a
    replacement that swaps a public class with a same-named function (or
    vice versa) is detected even when the receiver-stripped parameter
    list happens to match. Callers that ``Service()`` against a class and
    a function may both succeed on construction, but ``isinstance`` and
    subclass checks break — the kind prefix surfaces the regression
    before generation completes.
    """
    if (language or "").lower() not in {"python", "py"}:
        return {}
    try:
        tree = ast.parse(code_text or "")
    except SyntaxError:
        return {}

    dunder_all = _extract_dunder_all(tree)
    # When __all__ is authoritative, a top-level name is "public" iff it's
    # in __all__. Build a predicate that captures this.
    if dunder_all is not None:
        def _is_public_top_level(name: str) -> bool:
            return name in dunder_all
        # Classes opted into __all__ have their members treated as
        # public regardless of underscore prefix, consistent with the
        # __all__-authoritative branch in `_snapshot_public_surface`.
        include_methods_underscore_for_top_class = True
    else:
        def _is_public_top_level(name: str) -> bool:
            return not name.startswith("_")
        include_methods_underscore_for_top_class = False

    signatures: Dict[str, str] = {}

    # Build a top-level ``name -> ClassDef`` map and the set of names
    # introduced by imports. The synthesised-dataclass-init helper uses
    # both to resolve same-module base classes (for inherited fields)
    # and to mark cross-module bases as ``[inherited_unresolved]``.
    # Nested classes are NOT registered: dataclass inheritance from a
    # nested class is rare and the snapshot already tracks nested
    # classes via their qualified name, so a regression in a nested
    # base is caught by its own entry.
    class_defs: Dict[str, ast.ClassDef] = {
        node.name: node for node in tree.body if isinstance(node, ast.ClassDef)
    }
    imported_names: Set[str] = set()
    for node in tree.body:
        if isinstance(node, ast.Import):
            for alias in node.names:
                exposed = alias.asname or alias.name.split(".", 1)[0]
                if exposed:
                    imported_names.add(exposed)
        elif isinstance(node, ast.ImportFrom):
            for alias in node.names:
                if alias.name == "*":
                    continue
                exposed = alias.asname or alias.name
                if exposed:
                    imported_names.add(exposed)

    def _walk_class(
        class_node: ast.ClassDef,
        qualname: str,
        include_underscore: bool = False,
    ) -> None:
        # Record the class itself with its constructor signature so that
        # ADDING a required `__init__` parameter is caught (#1012, P1.B).
        # The ``[class]`` kind prefix mirrors the top-level
        # function/async-function/class kind tagging so a replacement
        # that swaps the class for a function with a matching constructor
        # signature is still flagged.
        # Record the class with its constructor-ABI signature (explicit
        # receiver-stripped ``__init__`` / synthesised stdlib ``@dataclass`` init /
        # bare ``()``). Shared with the patch-target class path via
        # :func:`_class_constructor_signature`.
        class_signature = _class_constructor_signature(
            class_node, class_defs, imported_names
        )
        signatures[qualname] = f"[class] {class_signature}"

        # First pass: accumulate property accessor roles per name so a
        # getter + setter combination collapses into ONE merged
        # ``[property:getter+setter]`` snapshot. Last-write-wins on the
        # dict (the previous behaviour) let ``@x.setter`` overwrite
        # ``@property`` and then misclassify the setter as ``[instance]``,
        # which let a real rewrite to ``def x(self, value)`` produce the
        # same snapshot string.
        property_accessors: Dict[str, Set[str]] = {}
        property_getter_nodes: Dict[str, ast.AST] = {}
        for child in class_node.body:
            if not isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            role = _python_property_accessor_role(child)
            if role is None:
                continue
            if not (include_underscore or not child.name.startswith("_")):
                continue
            property_accessors.setdefault(child.name, set()).add(role)
            # Remember the getter node so we can capture its parameter
            # signature in the final snapshot (the setter's ``(self,
            # value)`` shape is intentionally NOT used as the canonical
            # signature — accessors share the property identity but not
            # the param list).
            if role == "getter" and child.name not in property_getter_nodes:
                property_getter_nodes[child.name] = child

        for name, roles in property_accessors.items():
            sorted_roles = "+".join(sorted(roles))
            getter_node = property_getter_nodes.get(name)
            if getter_node is not None:
                getter_signature = _format_python_signature(
                    getter_node, skip_first=True
                )
            else:
                # ``@x.setter`` without an accompanying ``@property`` is
                # syntactically valid but unusual; fall back to ``()`` so
                # the entry still has a stable shape.
                getter_signature = "()"
            signatures[f"{qualname}.{name}"] = (
                f"[property:{sorted_roles}] {getter_signature}"
            )

        # Note: when a class body redefines the same name with mixed
        # binding kinds (e.g. plain ``def x`` followed by
        # ``@property def x``), the snapshot reflects the last *plain*
        # def encountered, not Python's runtime last-binding-wins
        # semantics. This is a rare source pattern; the gate may emit a
        # benign no-op diff in such cases. Documented for future
        # tightening.
        for child in class_node.body:
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                # __init__ already recorded above against ``qualname``;
                # do not re-add as ``qualname.__init__``.
                if child.name == "__init__":
                    continue
                # Property-decorated functions are handled in the
                # accumulator pass above — skip them here so a
                # last-write-wins overwrite cannot bury the merged
                # ``[property:...]`` entry under an ``[instance]``
                # snapshot from the setter.
                if _python_property_accessor_role(child) is not None:
                    continue
                binding_kind = _python_method_binding_kind(child)
                # ``staticmethod`` does NOT receive an implicit first arg
                # so its signature should NOT strip the leading positional.
                # ``classmethod`` / ``property`` / ``instance`` all bind
                # implicitly and skip the receiver. ``property`` getters
                # have a single ``self`` param that would otherwise vanish
                # from the snapshot, but the binding-kind prefix makes the
                # property-vs-method distinction observable on its own.
                skip_first = binding_kind != "staticmethod"
                if include_underscore or not child.name.startswith("_"):
                    base_signature = _format_python_signature(
                        child, skip_first=skip_first
                    )
                    signatures[f"{qualname}.{child.name}"] = (
                        f"[{binding_kind}] {base_signature}"
                    )
            elif isinstance(child, ast.ClassDef) and (
                include_underscore or not child.name.startswith("_")
            ):
                _walk_class(child, f"{qualname}.{child.name}", include_underscore)

    def _record_assignment_target(target: ast.AST) -> None:
        """Walk an assignment target, recording bare-name targets as ``[assignment]``.

        Mirrors :func:`_snapshot_public_surface`'s ``_add_assign_targets`` so
        an ``assignment ↔ def`` / ``assignment ↔ class`` kind flip becomes
        a snapshot diff in BOTH directions (``Foo = type(...)`` → ``def
        Foo()`` was previously invisible: surface kept ``Foo`` and the
        signatures dict had no ``Foo`` entry, so the new ``def Foo()``
        looked like an ADDED symbol, not a kind flip). Tuple/list/starred
        unpacking recurses; subscript/attribute targets are ignored
        (consistent with the surface helper — they mutate an existing
        object rather than binding a module attribute).
        """
        if isinstance(target, ast.Name):
            if _is_public_top_level(target.id):
                # Source order in the outer loop means a later ``def``/
                # ``class`` of the same name will overwrite this entry,
                # matching Python's last-binding-wins runtime semantics.
                signatures[target.id] = "[assignment]"
        elif isinstance(target, (ast.Tuple, ast.List)):
            for elt in target.elts:
                _record_assignment_target(elt)
        elif isinstance(target, ast.Starred):
            _record_assignment_target(target.value)

    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and _is_public_top_level(node.name):
            # Top-level kind prefix so swapping a public class with a
            # same-named function (or vice versa) is detected even when
            # the normalized parameter list matches. ``[function]`` vs
            # ``[async_function]`` keeps an ``async def`` flip
            # observable too — callers awaiting the result of a former
            # sync function would otherwise silently see a coroutine.
            kind = "async_function" if isinstance(node, ast.AsyncFunctionDef) else "function"
            signatures[node.name] = (
                f"[{kind}] {_format_python_signature(node)}"
            )
        elif isinstance(node, ast.ClassDef) and _is_public_top_level(node.name):
            _walk_class(
                node,
                node.name,
                include_underscore=include_methods_underscore_for_top_class,
            )
        elif isinstance(node, ast.Assign):
            # Record module-level assignments as ``[assignment]`` so a
            # rewrite that flips an ``assignment → def/class`` (e.g.
            # ``Foo = type("Foo", (), {})`` → ``def Foo(): pass``) shows
            # up as a snapshot diff. Without this entry the surface
            # helper keeps ``Foo`` in the public set unchanged and the
            # signatures dict sees ``Foo`` as a NEW symbol, missing the
            # kind flip. The reverse direction (``def`` → assignment)
            # was already covered by the line-1128 fallback before this
            # change; with this entry both directions now hit the
            # primary ``changed_set`` path.
            for target in node.targets:
                _record_assignment_target(target)
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            # Only annotated assignments with a bound value bind a
            # runtime module attribute; a bare ``PUBLIC_NAME: int``
            # declaration is a type hint, not an export. Mirrors the
            # corresponding branch in ``_snapshot_public_surface``.
            _record_assignment_target(node.target)
        elif isinstance(node, ast.Import):
            # Record re-exports so a silent break — ``import pathlib`` →
            # ``pathlib = None``, or ``from pathlib import Path`` →
            # ``def Path(): ...`` — registers as a snapshot diff instead
            # of looking like a brand-new symbol. Without this entry the
            # public-surface set still contains the bound name on both
            # sides, but the signatures dict has nothing to compare the
            # new ``def`` against; the regression slipped past iter-3
            # (external review PR #1015).
            for alias in node.names:
                exposed = alias.asname or alias.name.split(".", 1)[0]
                if not exposed or not _is_public_top_level(exposed):
                    continue
                # Mirror ``_snapshot_public_surface``: with NO ``__all__`` an
                # import is public surface only as an explicit re-export
                # (``import x as x``). Without this the primary signature
                # comparison would still flag a non-public import flipping to
                # a same-named def (``from typing import Any`` →
                # ``def Any()``) as a regression even though ``Any`` was never
                # public (issues #1662 / #1663 / pdd_cloud#2256).
                if dunder_all is None and _reexport_binding(alias) is None:
                    continue
                if alias.asname and alias.asname != alias.name:
                    # ``import pathlib as p`` → ``p`` binds to the
                    # ``pathlib`` module. Encoding the source module so
                    # ``import os as p`` would still produce a distinct
                    # entry.
                    signatures[exposed] = f"[import:{alias.name}]"
                else:
                    # ``import pathlib`` and ``import a.b.c`` both bind
                    # a single top-level name; record as plain
                    # ``[import]`` — the diff key is the bound name
                    # itself, the source is whatever's documented in
                    # the prompt body. A redundant alias ``import pathlib as
                    # pathlib`` binds the SAME object as the plain form, so it
                    # canonicalizes to ``[import]`` too — otherwise an
                    # alias-style normalization under ``__all__`` would diff as
                    # a phantom signature change.
                    signatures[exposed] = "[import]"
        elif isinstance(node, ast.ImportFrom):
            # ``from X import *`` does NOT bind a fixed name (the
            # surface helper already skips these) so it contributes
            # nothing to the signatures dict either.
            # Mirror ``_snapshot_public_surface``: ``from __future__
            # import …`` is a compiler directive, not a runtime
            # attribute callers would import. Without this skip a
            # follow-up generation that drops the directive and adds a
            # real ``annotations = …`` would falsely diff as a
            # signature change (``[import:from __future__]`` →
            # ``[assignment]``) on the same name.
            if node.module == "__future__":
                continue
            # Encode the relative-import level so a re-export's source package
            # is part of its fingerprint: ``from . import Foo`` and ``from ..
            # import Foo`` bind the same name to DIFFERENT modules and must not
            # collide on ``[import:from ]``. ``node.level`` is 0 for absolute
            # imports (``from pathlib import Path`` stays ``pathlib``).
            module = "." * node.level + (node.module or "")
            for alias in node.names:
                if alias.name == "*":
                    continue
                exposed = alias.asname or alias.name
                if not exposed or not _is_public_top_level(exposed):
                    continue
                # Mirror ``_snapshot_public_surface``: with NO ``__all__`` only
                # redundant-alias re-exports (``from m import y as y``) are
                # public surface; a plain ``from typing import Any`` or a
                # renaming alias ``from m import y as z`` is an implementation
                # detail (issues #1662 / #1663 / pdd_cloud#2256).
                if dunder_all is None and _reexport_binding(alias) is None:
                    continue
                if alias.asname and alias.asname != alias.name:
                    # ``from pathlib import Path as P`` records the
                    # source identifier so re-pointing the alias at a
                    # different attribute (``from os.path import join
                    # as P``) flips the snapshot.
                    signatures[exposed] = f"[import:from {module}:{alias.name}]"
                else:
                    # ``from pathlib import Path`` — the bound name is
                    # ``alias.name`` so encoding the source module is
                    # sufficient to distinguish it from a same-named
                    # ``def Path()`` later in the file. A redundant alias
                    # ``from pathlib import Path as Path`` binds the SAME object
                    # as the plain form, so it canonicalizes here too —
                    # otherwise an alias-style normalization under ``__all__``
                    # would diff as a phantom signature change.
                    signatures[exposed] = f"[import:from {module}]"
    if patch_targets:
        for symbol in sorted(patch_targets):
            if symbol in signatures:
                continue
            # A patch-target that is a CLASS — top-level OR a nested
            # ``Outer.Inner`` (incl. underscore paths) — gets its ``[class]``
            # constructor-ABI entry, so a declared (possibly underscore) class or
            # ``Class.__init__`` / ``Outer.Inner.__init__`` is validated like a
            # public class rather than skipped for lack of a signature entry (codex
            # round-8 finding 3 + round-9). ``_patch_target_signature_entry`` only
            # builds function/method entries.
            class_node = _resolve_class_node(tree, symbol)
            if class_node is not None:
                class_signature = _class_constructor_signature(
                    class_node, class_defs, imported_names
                )
                signatures[symbol] = f"[class] {class_signature}"
                continue
            entry = _patch_target_signature_entry(tree, symbol, class_defs)
            if entry is not None:
                signatures[symbol] = entry
    return signatures

def _collect_python_public_surface(source: str) -> List[str]:
    """Backward-compatible wrapper for older tests and local imports."""
    return sorted(_snapshot_public_surface(source, "python"))
