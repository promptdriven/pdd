"""The public-surface regression gate and its annotation reconciler.

Rejects a regeneration that removes or reshapes public API, judging declared
symbols against the prompt declaration and everything else against the previous
generation. Reconciles annotation-only drift first, since a retry loop cannot
converge on a spelling difference the model keeps reproducing.
"""

import ast
import logging
import re
from typing import Dict, List, Optional, Set, Tuple

from ..architecture_sync import parse_prompt_tags
from ..interface_semantics import (
    annotations_compatible,
    build_module_default_symbols,
    parse_callable_contract,
    signature_entries_compatible,
)
from .directives import (
    _env_flag_enabled,
    _prompt_breaking_change_removed_symbols,
    _prompt_breaking_change_signature_symbols,
)
from .gate_errors import ArchitectureConformanceError, PublicSurfaceRegressionError
from .surface import (
    _diff_public_surface,
    _effective_patch_targets,
    _format_python_signature,
    _snapshot_public_signatures,
    _snapshot_public_surface,
    _symbol_exists_in_module,
)
from .test_churn import _is_python_generation, _is_test_output_path

logger = logging.getLogger(__name__)


def _collect_declared_surface(
    prompt_content: Optional[str],
    prompt_name: str,
) -> Dict[str, Optional[str]]:
    """Collect declared public symbols and raw signatures from ``<pdd-interface>``.

    Returns ``{name -> raw_signature_or_None}`` for every function the prompt's
    ``type: "module"`` ``<pdd-interface>`` declares (``module.functions``).
    Unlike :func:`_extract_pdd_interface_signatures`, a missing or non-paren
    signature is KEPT (mapped to ``None``) so the surface gate can enforce
    presence-only for description-only declarations (issue #1900).

    Scoped to ``type: "module"`` ONLY. ``type: "cli"`` / ``type: "command"``
    interfaces declare COMMAND strings (e.g. ``"sync-architecture"``,
    ``"pdd extracts prune"`` — hyphens/spaces, not valid Python identifiers), not
    module symbols; feeding those to the surface gate produced phantom
    ``removed:`` diffs on valid generated code (codex review finding 1). CLI/
    command signature conformance stays owned by the conformance gate
    (:func:`_extract_pdd_interface_signatures` still covers them).

    Returns ``{}`` when there is no prompt, no ``type: "module"``
    ``<pdd-interface>`` block, or the JSON is malformed. The conformance gate owns
    the parse-error warning, so this stays silent to avoid a duplicate warning.
    """
    declared: Dict[str, Optional[str]] = {}
    if not prompt_content:
        return declared
    tags = parse_prompt_tags(prompt_content)
    if tags.get("interface_parse_error"):
        return declared
    interface = tags.get("interface")
    if not isinstance(interface, dict) or interface.get("type") != "module":
        return declared

    module_spec = interface.get("module") or {}
    for item in module_spec.get("functions") or []:
        if not isinstance(item, dict):
            continue
        name = item.get("name")
        if not name or not isinstance(name, str):
            continue
        sig = item.get("signature")
        declared[name] = sig if isinstance(sig, str) else None
    return declared

def _declared_signature_to_entry(
    raw_signature: Optional[str],
    binding_kind: str,
    *,
    is_async: bool = False,
    strip_receiver: bool = False,
) -> Optional[str]:
    """Normalize a declared ``<pdd-interface>`` signature into a snapshot entry.

    Produces an entry shaped like :func:`_snapshot_public_signatures` values
    (``[<kind>] (params) -> ret``) so :func:`signature_entries_compatible` can
    compare the DECLARED contract against the generated one. The binding kind and
    async marker are copied from the GENERATED symbol (``binding_kind`` /
    ``is_async``) because a ``<pdd-interface>`` signature cannot express
    ``self`` / property / ``async``; matching them by construction means only the
    parameter list and return annotation are actually compared, and no
    binding-kind drift is ever invented from the declaration.

    ``strip_receiver=True`` (used for receiver-bound methods and constructors:
    ``instance`` / ``classmethod`` / ``class`` kinds) drops a leading ``self`` /
    ``cls`` positional so the declared ``(self, x)`` matches the snapshot's
    receiver-stripped ``(x)``. An already-stripped ``(x)`` is left unchanged.

    Returns ``None`` (presence-only: the symbol must exist but its signature is
    not checked) when the declared signature is not a parseable paren-list — a
    missing signature, ``None``, a class header (``class Foo(Base)``),
    ``dataclass ...``, ``...`` — or when the composed entry does not parse as a
    callable contract.
    """
    if not raw_signature or not isinstance(raw_signature, str):
        return None
    sig = raw_signature.strip()
    # Strip a leading ``async`` and/or ``def <name>`` prefix so a declaration
    # written as ``async def foo(x)`` or ``def foo(x)`` reduces to the bare
    # parameter list. The entry's async-ness is taken from the generated symbol,
    # not the declaration, so any declared ``async`` is dropped here.
    if sig.startswith("async "):
        sig = sig[len("async "):].strip()
    def_match = re.match(r"^def\s+[A-Za-z_]\w*\s*(.*)$", sig, re.DOTALL)
    if def_match:
        sig = def_match.group(1).strip()
        if sig.startswith("async "):
            sig = sig[len("async "):].strip()
    if not sig.startswith("("):
        return None
    if strip_receiver:
        # Mirror the snapshot's receiver stripping: parse the declared paren
        # signature and drop a leading ``self``/``cls`` positional so a declared
        # ``(self, x)`` compares against the snapshot's ``(x)``. A signature that
        # does not parse or whose first positional is not a receiver is left
        # unchanged (an already receiver-free ``(x)`` stays ``(x)``).
        try:
            parsed = ast.parse(f"def _pdd{sig}: pass").body[0]
        except SyntaxError:
            return None
        if isinstance(parsed, (ast.FunctionDef, ast.AsyncFunctionDef)):
            positional = list(parsed.args.posonlyargs) + list(parsed.args.args)
            if positional and positional[0].arg in {"self", "cls"}:
                sig = _format_python_signature(parsed, skip_first=True)
    async_prefix = "async " if is_async else ""
    entry = f"[{binding_kind}] {async_prefix}{sig}"
    if parse_callable_contract(entry) is None:
        return None
    return entry

def _entry_binding_context(entry: Optional[str]) -> Optional[Tuple[str, bool]]:
    """Return ``(binding_kind, is_async)`` parsed off a snapshot entry.

    Reads the ``[<kind>]`` prefix and a leading ``async `` from a
    :func:`_snapshot_public_signatures` value (e.g. ``[async_function] async
    (x)`` -> ``("async_function", True)``). Returns ``None`` when the entry has
    no binding-kind prefix.
    """
    if not entry:
        return None
    match = re.match(r"^\[([^\]]+)\]\s*(.*)$", entry.strip())
    if match is None:
        return None
    return match.group(1), match.group(2).lstrip().startswith("async ")

def _declared_presence_name(name: str) -> str:
    """Map a declared symbol to the surface name whose presence satisfies it.

    A constructor's ABI is keyed on the CLASS symbol (``Foo``), never
    ``Foo.__init__`` (see :func:`_snapshot_public_surface`), so a prompt that
    declares ``Foo.__init__`` is present as long as ``Foo`` is — flagging it as
    a removed symbol on valid code was a false positive (codex review finding 2).
    Every other declared name maps to itself.
    """
    if name.endswith(".__init__"):
        return name[: -len(".__init__")]
    return name

def _declared_patch_targets(
    code: Optional[str],
    declared_names: Set[str],
    language: Optional[str],
) -> Set[str]:
    """Return the declared symbols DEFINED in *code*, as snapshot surface keys.

    The prompt's ``<pdd-interface>`` declaration is authoritative (like ``__all__``),
    so a declared ``_``-prefixed helper (real: ``_extract_step_report``) must be
    captured in the public-surface / signature snapshots even though the default
    heuristic filters underscore names out (codex round-7 finding 1). These are
    fed as ``patch_targets`` (which force a defined name into the snapshot), so only
    names actually DEFINED in *code* are returned — a genuinely removed declared
    symbol stays out of the ``after`` snapshot and is still reported as removed.

    Each declared name is mapped through :func:`_declared_presence_name` (so a
    declared ``Class.__init__`` contributes the CLASS key, matching where the
    snapshot puts the constructor ABI, and never injects a phantom ``Class.__init__``
    signature entry that would bypass the declared-vs-old-code routing).
    """
    if not declared_names or (language or "").lower() not in {"python", "py"}:
        return set()
    try:
        tree = ast.parse(code or "")
    except SyntaxError:
        return set()
    targets: Set[str] = set()
    for name in declared_names:
        presence = _declared_presence_name(name)
        if _symbol_exists_in_module(tree, presence):
            targets.add(presence)
    return targets

def _verify_public_surface_regression(
    existing_code: Optional[str],
    generated_code: str,
    prompt_name: str,
    output_path: Optional[str],
    language: Optional[str],
    prompt_content: Optional[str],
) -> None:
    """Fail when a mature Python module generation removes public symbols."""
    if (
        not existing_code
        or not existing_code.strip()
        or _env_flag_enabled("PDD_SKIP_PUBLIC_SURFACE_GATE")
        or _env_flag_enabled("PDD_SKIP_CONFORMANCE")
        or _is_test_output_path(output_path)
        or not _is_python_generation(language, output_path)
    ):
        return

    # The prompt's ``<pdd-interface>`` declaration is the stable surface contract
    # (issue #1900), and it is authoritative like ``__all__``. Collect it BEFORE
    # the snapshots so declared symbols — including ``_``-prefixed helpers the
    # default heuristic would filter out (codex round-7 finding 1) — are forced
    # into the surface/signature snapshots via ``patch_targets`` (only when
    # actually DEFINED in the respective code, so a genuinely removed declared
    # symbol still diffs as removed). Empty when there is no parseable
    # ``<pdd-interface>`` (also on a JSON parse error — the conformance gate owns
    # that warning), so undeclared modules behave exactly as before.
    declared = _collect_declared_surface(prompt_content, prompt_name)
    declared_names = set(declared)

    patch_targets = _effective_patch_targets(
        existing_code, language or "python", output_path
    ) | _declared_patch_targets(existing_code, declared_names, language or "python")
    before = _snapshot_public_surface(
        existing_code,
        language or "python",
        patch_targets=patch_targets,
    )
    # Syntax gate (issue #1612 Bug 2): if the freshly generated Python is
    # unparseable, ``_snapshot_public_surface`` silently returns an empty set,
    # which would misroute the failure as a phantom public-surface regression
    # (``post_surface_size: 0``) and send the repair loop chasing removed
    # symbols instead of the real problem. Raise a syntax-focused
    # ``ArchitectureConformanceError`` so the repair loop targets the syntax
    # error while still listing the expected public symbols to restore.
    if before:
        try:
            ast.parse(generated_code or "")
        except SyntaxError as syntax_err:
            expected = sorted(before)
            raise ArchitectureConformanceError(
                prompt_name=prompt_name,
                output_path=output_path or "",
                architecture_entry={},
                expected_symbols=expected,
                found_symbols=[],
                missing_symbols=expected,
                message=(
                    f"Architecture conformance error for {prompt_name}: "
                    f"generated Python has a syntax error: {syntax_err}"
                ),
                repair_directive=(
                    f"Fix the Python syntax error in the generated code: "
                    f"{syntax_err}\n"
                    f"Then restore all expected public symbols: "
                    f"{', '.join(expected)}."
                ),
            ) from syntax_err
    after_patch_targets = _effective_patch_targets(
        generated_code, language or "python", output_path
    ) | _declared_patch_targets(generated_code, declared_names, language or "python")
    after = _snapshot_public_surface(
        generated_code,
        language or "python",
        patch_targets=after_patch_targets,
    )
    if not before:
        return
    allowed_removed = _prompt_breaking_change_removed_symbols(prompt_content)
    # ``BREAKING-CHANGE: remove Service`` is unambiguous about the whole
    # class going away — auto-include every descendant ``Service.run``,
    # ``Service.Inner.method`` etc. that the snapshot captured. Without
    # this the caller has to list every member by hand, which defeats the
    # opt-out. Only mirrors `_snapshot_public_surface`'s class-member
    # recursion, so no new naming convention to learn.
    expanded_allowed = set(allowed_removed)
    for name in allowed_removed:
        prefix = f"{name}."
        for sym in before:
            if sym.startswith(prefix):
                expanded_allowed.add(sym)
    # Per-symbol hybrid (issue #1900): DECLARED symbols are validated against the
    # declaration (a stable target) so a legit ``pdd change`` that also drifts an
    # unrelated declared signature no longer dead-ends the change->sync loop;
    # UNDECLARED symbols keep the old-code baseline. ``declared`` was collected
    # above (it also seeds ``patch_targets``).

    # Removal, per-symbol. UNDECLARED: a public name dropped between before and
    # after regresses unless BREAKING-CHANGE opts it out (today's behavior).
    # DECLARED: a still-declared symbol absent from the generated surface
    # regresses regardless — the declaration is authoritative, so a
    # BREAKING-CHANGE: remove does NOT excuse it, and its absence counts even if
    # it was never in ``before``.
    undeclared_removed = [
        symbol
        for symbol in _diff_public_surface(before, after)
        if symbol not in declared_names and symbol not in expanded_allowed
    ]
    # ``Foo.__init__`` is present when the ``Foo`` class symbol is (the
    # constructor ABI is keyed on the class, not ``Class.__init__``), so map each
    # declared name through its presence-name before the surface membership test
    # (codex review finding 2). The presence-name is also what gets reported when
    # a declared symbol is genuinely missing.
    declared_missing = [
        presence
        for symbol in declared_names
        for presence in (_declared_presence_name(symbol),)
        if presence not in after
    ]
    removed = sorted(set(undeclared_removed) | set(declared_missing))
    before_signatures = _snapshot_public_signatures(
        existing_code,
        language or "python",
        patch_targets=patch_targets,
    )
    after_signatures = _snapshot_public_signatures(
        generated_code,
        language or "python",
        patch_targets=after_patch_targets,
    )
    # Per-side module default-symbol tables (issue #1558): a parameter default
    # written as a same-module constant (``max_chars=_LIMIT`` where
    # ``_LIMIT = 25000``) resolves to the literal it stands for. For the
    # UNDECLARED old-vs-new comparison each side is resolved against its OWN
    # module — the existing code for the ``before`` signature and the generated
    # code for the ``after`` — so a literal <-> same-module-constant refactor of a
    # default is not flagged as a regression, while the same constant name
    # resolving to a different value across the two versions still is.
    before_default_symbols = build_module_default_symbols(existing_code)
    after_default_symbols = build_module_default_symbols(generated_code)
    allowed_signature_changes = _prompt_breaking_change_signature_symbols(prompt_content)
    changed_set: Set[str] = set()
    signature_details: List[Tuple[str, str, str, str]] = []
    # Declared symbols that were ACTUALLY validated against the declaration below
    # (top-level functions with a parseable declared signature). Only these are
    # excluded from the undeclared old-code loops, so the declaration can
    # authorize a change old code would flag (the #2971 case). A declared symbol
    # that is PRESENCE-ONLY here — a dotted method, or a non-paren declared
    # signature where ``_declared_signature_to_entry`` returns None — is NOT
    # added, so it falls back to the exact old-code baseline (added-required-param
    # / binding-kind flip / ctor ABI drift stay caught; codex over-skip fix).
    declared_validated: Set[str] = set()

    # DECLARED symbols: validate the generated signature against the DECLARED
    # PARAM/return contract (a stable target), NEVER re-comparing params against
    # the old code. Top-level functions AND dotted methods/constructors are all
    # first-class declared-contract citizens here — the declaration is the permit
    # for their params/return, while the un-declarable binding-kind/async are
    # anchored to old code (below). Defaults on BOTH sides resolve in the
    # GENERATED module namespace — the prompt describes the generated module
    # (issue #1558's declared-vs-generated resolution).
    for symbol in sorted(declared_names):
        # A constructor's ABI is keyed on the CLASS symbol as a ``[class]`` entry,
        # so a declared ``Class.__init__`` validates against the class entry;
        # every other declared name (top-level function or ``Class.method``) keys
        # on itself.
        if symbol.endswith(".__init__"):
            snapshot_key = symbol[: -len(".__init__")]
        else:
            snapshot_key = symbol
        actual_entry = after_signatures.get(snapshot_key)
        if actual_entry is None:
            # Absent from the generated signature table (missing symbol or a
            # non-callable form). Presence is enforced by the removal check
            # above; not validated -> left out of ``declared_validated`` so it
            # falls back to the old-code baseline.
            continue
        actual_ctx = _entry_binding_context(actual_entry)
        if actual_ctx is None:
            continue
        # Binding kind + async are un-declarable (``<pdd-interface>`` cannot
        # express ``self`` / property / ``async`` / function-vs-class), so their
        # baseline is the PRIOR generation: an async->sync or function->class drift
        # on a declared symbol is a real regression (codex round-2 finding 1a),
        # anchored to the OLD entry when the symbol already existed and was
        # callable there. A ``BREAKING-CHANGE: change signature <sym>`` opt-out
        # relaxes ONLY these un-declarable facets — it uses the GENERATED kind/
        # async — but the declared PARAM/return contract is STILL enforced below,
        # so prose cannot wave through an added-required-param that violates the
        # declaration (codex FM2). A newly-added declared symbol (or one whose
        # prior form was a non-callable assignment/import) has no prior callable
        # contract, so it also falls back to the generated kind/async.
        if symbol in allowed_signature_changes:
            expected_kind, expected_async = actual_ctx
        else:
            before_entry = before_signatures.get(snapshot_key)
            before_ctx = (
                _entry_binding_context(before_entry)
                if before_entry is not None
                and parse_callable_contract(before_entry) is not None
                else None
            )
            expected_kind, expected_async = (
                before_ctx if before_ctx is not None else actual_ctx
            )
        # The snapshot receiver-strips ``self``/``cls`` for receiver-bound methods
        # and constructors, so strip a leading receiver from the declared signature
        # for those kinds before comparing (a declared ``(self, x)`` must match the
        # snapshot's ``(x)``; a plain function/staticmethod is left as declared).
        strip_receiver = expected_kind in {"instance", "classmethod", "class"}
        expected_entry = _declared_signature_to_entry(
            declared[symbol],
            expected_kind,
            is_async=expected_async,
            strip_receiver=strip_receiver,
        )
        if expected_entry is None:
            # Declared signature is not a parseable paren-list -> presence-only:
            # the symbol must exist (enforced above) but its signature is NOT
            # validated against the declaration here. It is intentionally left out
            # of ``declared_validated`` so the undeclared old-code loops below
            # still protect its signature (codex over-skip fix, e.g. a declared
            # class with a non-paren ``"class Service"`` signature).
            continue
        compatible = signature_entries_compatible(
            expected_entry,
            actual_entry,
            old_symbols=after_default_symbols,
            new_symbols=after_default_symbols,
        )
        if compatible is None:
            # The GENERATED symbol is not a callable contract — a declared
            # callable regenerated as a non-callable (``def f`` -> ``f = 1`` /
            # ``from pkg import f as f``). If the OLD form WAS a callable, the
            # declared callable became non-callable: flag it DIRECTLY here — that
            # break is not authorized by ``BREAKING-CHANGE: change signature``
            # (which relaxes params, not de-callable-ing; de-callable-ing is a
            # ``BREAKING-CHANGE: remove``), and the old-code loop would otherwise
            # skip the symbol under such an opt-out (codex round-8 finding 1).
            before_entry = before_signatures.get(snapshot_key)
            before_ctx = (
                _entry_binding_context(before_entry)
                if before_entry is not None
                and parse_callable_contract(before_entry) is not None
                else None
            )
            if before_ctx is not None:
                strip = before_ctx[0] in {"instance", "classmethod", "class"}
                callable_expected = (
                    _declared_signature_to_entry(
                        declared[symbol],
                        before_ctx[0],
                        is_async=before_ctx[1],
                        strip_receiver=strip,
                    )
                    or before_entry
                )
                changed_set.add(symbol)
                signature_details.append(
                    (symbol, callable_expected, actual_entry, "pdd-interface")
                )
            # else: the OLD form was ALSO non-callable (e.g. ``f = lambda: x`` that
            # stayed an ``[assignment]``). Not validated -> falls through to the
            # OLD-CODE baseline, which compares equal old-vs-new -> no false
            # positive. Not added to ``declared_validated`` either way.
            continue
        # A real callable-vs-callable decision was made, so the declaration owns
        # this symbol: exclude its SNAPSHOT KEY from the old-code loops below (the
        # class entry for a validated ``__init__``, the ``X.method`` entry for a
        # validated method).
        declared_validated.add(snapshot_key)
        if compatible is False:
            # Report the ORIGINAL declared name (``Foo.method`` /
            # ``Service.__init__``), not the snapshot key.
            changed_set.add(symbol)
            signature_details.append(
                (symbol, expected_entry, actual_entry, "pdd-interface")
            )
        # ``compatible is True`` -> compatible (nothing to flag).

    # UNDECLARED (and presence-only DECLARED) symbols: keep the historical
    # old-vs-new comparison EXACTLY. Only symbols VALIDATED against the
    # declaration above are skipped here — a presence-only declared symbol (dotted
    # method / non-paren class) falls through to this old-code baseline so its
    # signature drift is still caught (codex over-skip fix).
    for symbol, signature in before_signatures.items():
        if symbol in declared_validated:
            continue
        if symbol not in after_signatures or symbol in allowed_signature_changes:
            continue
        after_signature = after_signatures[symbol]
        compatible = signature_entries_compatible(
            signature,
            after_signature,
            old_symbols=before_default_symbols,
            new_symbols=after_default_symbols,
        )
        if compatible is True:
            continue
        # ``None`` means at least one side is not a callable contract we
        # understand (an ``[assignment]`` or an import re-export). Keep the
        # historical exact string comparison for those so binding-kind and
        # re-export changes stay strict while unchanged entries are not flagged.
        # Callable entries are decided semantically above — the equal-string
        # case is NOT short-circuited first, so a default written as a
        # same-module constant whose resolved value changed across the old and
        # generated modules is caught even when the signature text is identical
        # (issue #1558).
        if compatible is None and after_signature == signature:
            continue
        changed_set.add(symbol)
    for symbol in before_signatures:
        if symbol in declared_validated:
            continue
        if symbol in after_signatures or symbol in changed_set:
            continue
        if "." in symbol:
            continue
        if symbol in after and symbol not in allowed_signature_changes:
            changed_set.add(symbol)
    changed_signatures = sorted(changed_set)
    if removed or changed_signatures:
        raise PublicSurfaceRegressionError(
            prompt_name=prompt_name,
            output_path=output_path or "",
            removed_symbols=removed,
            changed_signatures=changed_signatures,
            pre_surface_size=len(before),
            post_surface_size=len(after),
            signature_details=signature_details,
        )

def _index_function_defs(tree: ast.Module) -> Dict[str, ast.AST]:
    """Map dotted qualnames (``foo``, ``Class.method``) to their AST nodes.

    Classes contribute both their own key (so a declared class is locatable) and
    the recursively-qualified keys of their nested functions/classes, matching the
    dotted symbol names :func:`_snapshot_public_signatures` produces. First
    definition wins on a name clash.
    """
    index: Dict[str, ast.AST] = {}

    def _walk(prefix: str, body: List[ast.stmt]) -> None:
        for node in body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                index.setdefault(f"{prefix}{node.name}", node)
            elif isinstance(node, ast.ClassDef):
                qual = f"{prefix}{node.name}"
                index.setdefault(qual, node)
                _walk(f"{qual}.", node.body)

    _walk("", tree.body)
    return index

def _parse_declared_def(raw_signature: Optional[str]) -> Optional[ast.FunctionDef]:
    """Parse a declared ``<pdd-interface>`` signature into a ``FunctionDef`` node.

    Mirrors :func:`_declared_signature_to_entry`'s normalization: strip a leading
    ``async`` / ``def <name>`` prefix down to the bare parameter list, then parse
    ``def _pdd<sig>: pass``. Returns ``None`` when the declaration is not a
    parseable paren-list (a presence-only declaration is never reconciled).
    """
    if not raw_signature or not isinstance(raw_signature, str):
        return None
    sig = raw_signature.strip()
    if sig.startswith("async "):
        sig = sig[len("async "):].strip()
    def_match = re.match(r"^def\s+[A-Za-z_]\w*\s*(.*)$", sig, re.DOTALL)
    if def_match:
        sig = def_match.group(1).strip()
        if sig.startswith("async "):
            sig = sig[len("async "):].strip()
    if not sig.startswith("("):
        return None
    try:
        parsed = ast.parse(f"def _pdd{sig}: pass").body[0]
    except SyntaxError:
        return None
    if not isinstance(parsed, ast.FunctionDef):
        return None
    return parsed

def _signature_slots(
    func: ast.AST,
) -> List[Tuple[str, str, bool, Optional[str], Optional[ast.AST]]]:
    """Ordered ``(name, kind, has_default, default_text, annotation_node)`` slots.

    Mirrors :func:`pdd.interface_semantics._params_from_arguments` so the
    structural comparison in :func:`_annotation_only_edits` matches exactly what
    the public-surface gate compares (posonly / positional / vararg /
    keyword_only / kwarg, defaults normalized by :func:`ast.unparse`).
    """
    args = func.args
    slots: List[Tuple[str, str, bool, Optional[str], Optional[ast.AST]]] = []

    def _add(arg: ast.arg, kind: str, default: Optional[ast.AST]) -> None:
        has_default = default is not None
        default_text = ast.unparse(default).strip() if default is not None else None
        slots.append((arg.arg, kind, has_default, default_text, arg.annotation))

    positional = list(args.posonlyargs) + list(args.args)
    defaults = [None] * (len(positional) - len(args.defaults)) + list(args.defaults)
    for arg, default in zip(args.posonlyargs, defaults[: len(args.posonlyargs)]):
        _add(arg, "posonly", default)
    for arg, default in zip(args.args, defaults[len(args.posonlyargs):]):
        _add(arg, "positional", default)
    if args.vararg is not None:
        _add(args.vararg, "vararg", None)
    for arg, default in zip(args.kwonlyargs, args.kw_defaults):
        _add(arg, "keyword_only", default)
    if args.kwarg is not None:
        _add(args.kwarg, "kwarg", None)
    return slots

def _line_start_byte_offsets(source: str) -> List[int]:
    """UTF-8 byte offset at which each 1-indexed source line begins."""
    data = source.encode("utf-8")
    offsets = [0]
    for index, byte in enumerate(data):
        if byte == 0x0A:  # newline
            offsets.append(index + 1)
    return offsets

def _node_byte_span(
    node: ast.AST, line_offsets: List[int]
) -> Optional[Tuple[int, int]]:
    """Absolute UTF-8 byte ``(start, end)`` of a node, or ``None`` if unlocatable.

    ``ast`` column offsets are UTF-8 byte offsets into their line, so the caller
    splices the encoded bytes (see :func:`_apply_byte_edits`).
    """
    lineno = getattr(node, "lineno", None)
    end_lineno = getattr(node, "end_lineno", None)
    col = getattr(node, "col_offset", None)
    end_col = getattr(node, "end_col_offset", None)
    if lineno is None or end_lineno is None or col is None or end_col is None:
        return None
    if lineno > len(line_offsets) or end_lineno > len(line_offsets):
        return None
    return line_offsets[lineno - 1] + col, line_offsets[end_lineno - 1] + end_col

def _apply_byte_edits(source: str, edits: List[Tuple[int, int, str]]) -> str:
    """Apply non-overlapping ``(start, end, replacement)`` byte edits to *source*."""
    data = bytearray(source.encode("utf-8"))
    # Apply right-to-left so earlier offsets stay valid; skip any overlap defensively.
    ordered = sorted(edits, key=lambda edit: edit[0], reverse=True)
    last_start: Optional[int] = None
    for start, end, replacement in ordered:
        if start < 0 or end > len(data) or start > end:
            continue
        if last_start is not None and end > last_start:
            continue
        data[start:end] = replacement.encode("utf-8")
        last_start = start
    return data.decode("utf-8")

def _annotation_only_edits(
    declared_def: ast.FunctionDef,
    gen_node: ast.AST,
    line_offsets: List[int],
) -> List[Tuple[int, int, str]]:
    """Byte edits rewriting ``gen_node``'s annotations to the declared text.

    Returns an empty list unless the ONLY drift between the declaration and the
    generated signature is annotation spelling on one or more parameters or the
    return type (identical names, order, kinds and defaults). Only annotations the
    public-surface gate considers INCOMPATIBLE are rewritten, so a compatible
    alias (``Dict`` vs ``dict``) is never churned. Any structural difference
    disqualifies the whole symbol (real drift the gate must still fire on).
    """
    declared_slots = _signature_slots(declared_def)
    gen_slots = _signature_slots(gen_node)
    # A ``<pdd-interface>`` signature cannot express ``self`` / ``cls``; the gate
    # strips a leading receiver from the generated method before comparing, so
    # drop it here too when the declaration does not carry one.
    if (
        gen_slots
        and gen_slots[0][0] in {"self", "cls"}
        and (not declared_slots or declared_slots[0][0] not in {"self", "cls"})
    ):
        gen_slots = gen_slots[1:]
    if len(declared_slots) != len(gen_slots):
        return []
    edits: List[Tuple[int, int, str]] = []
    for declared_slot, gen_slot in zip(declared_slots, gen_slots):
        d_name, d_kind, d_has_def, d_def, d_ann = declared_slot
        g_name, g_kind, g_has_def, g_def, g_ann = gen_slot
        if (
            d_name != g_name
            or d_kind != g_kind
            or d_has_def != g_has_def
            or d_def != g_def
        ):
            return []
        if d_ann is None or g_ann is None:
            continue
        d_text = ast.unparse(d_ann).strip()
        g_text = ast.unparse(g_ann).strip()
        if d_text == g_text or annotations_compatible(d_text, g_text):
            continue
        span = _node_byte_span(g_ann, line_offsets)
        if span is None:
            return []
        edits.append((span[0], span[1], d_text))
    d_ret = declared_def.returns
    g_ret = getattr(gen_node, "returns", None)
    if d_ret is not None and g_ret is not None:
        d_ret_text = ast.unparse(d_ret).strip()
        g_ret_text = ast.unparse(g_ret).strip()
        if d_ret_text != g_ret_text and not annotations_compatible(
            d_ret_text, g_ret_text
        ):
            span = _node_byte_span(g_ret, line_offsets)
            if span is None:
                return []
            edits.append((span[0], span[1], d_ret_text))
    return edits

def _reconcile_declared_annotation_drift(
    existing_code: Optional[str],
    generated_code: str,
    prompt_name: str,
    output_path: Optional[str],
    language: Optional[str],
    prompt_content: Optional[str],
) -> Optional[str]:
    """Rewrite annotation-only drift on a declared symbol back to the declared text.

    Issue #1968: when a regeneration drifts a declared ``<pdd-interface>``
    signature ONLY in annotation spelling — the declaration says ``object`` but
    the model emitted ``Any``, or it broadened a parameter's declared type with
    extra ``|`` union members — the public-surface gate correctly rejects it, but
    the LLM repair retry keeps re-emitting the same "equivalent" spelling and
    never converges. This deterministic pass runs BEFORE the gate: for every
    declared symbol whose generated signature differs from the declaration ONLY
    in annotation text (identical parameter names, order, kinds and defaults), it
    rewrites the offending annotation(s) in the generated SOURCE to the declared
    spelling, so the gate passes on the reconciled code with no further
    generation attempt.

    Returns the rewritten ``generated_code`` when at least one annotation was
    reconciled, or ``None`` when nothing safe to rewrite was found. It is
    fail-safe: only annotations the gate considers INCOMPATIBLE are rewritten,
    structural drift is left untouched, and the whole rewrite is discarded if the
    result no longer parses. Bypass with ``PDD_SKIP_ANNOTATION_RECONCILE=1``.
    """
    if (
        not existing_code
        or not existing_code.strip()
        or _env_flag_enabled("PDD_SKIP_ANNOTATION_RECONCILE")
        or _env_flag_enabled("PDD_SKIP_PUBLIC_SURFACE_GATE")
        or _env_flag_enabled("PDD_SKIP_CONFORMANCE")
        or _is_test_output_path(output_path)
        or not _is_python_generation(language, output_path)
    ):
        return None
    declared = _collect_declared_surface(prompt_content, prompt_name)
    if not declared:
        return None
    try:
        tree = ast.parse(generated_code)
    except SyntaxError:
        return None
    func_index = _index_function_defs(tree)
    line_offsets = _line_start_byte_offsets(generated_code)
    edits: List[Tuple[int, int, str]] = []
    try:
        for name, raw_sig in declared.items():
            if not raw_sig:
                continue
            node = func_index.get(name)
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            declared_def = _parse_declared_def(raw_sig)
            if declared_def is None:
                continue
            edits.extend(_annotation_only_edits(declared_def, node, line_offsets))
    except (ValueError, TypeError, AttributeError):
        return None
    if not edits:
        return None
    reconciled = _apply_byte_edits(generated_code, edits)
    if reconciled == generated_code:
        return None
    try:
        ast.parse(reconciled)
    except SyntaxError:
        return None
    return reconciled
