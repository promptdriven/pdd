"""Semantic compatibility helpers for PDD interface conformance.

This module keeps language-specific extraction at the edge.  Python callers may
parse annotation or signature text into these common models, while the
compatibility decisions below operate on lightweight language-neutral contracts.
"""

from __future__ import annotations

import ast
import re
from dataclasses import dataclass
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
) -> bool:
    """Return True when ``new`` preserves all existing call forms of ``old``."""
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
        if not _existing_param_compatible(old_param, new_param):
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
        if not _existing_param_compatible(old_param, new_param):
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


def signature_entries_compatible(old_entry: str, new_entry: str) -> Optional[bool]:
    """Return semantic compatibility for snapshot entries, or None if unknown."""
    old_contract = parse_callable_contract(old_entry)
    new_contract = parse_callable_contract(new_entry)
    if old_contract is None or new_contract is None:
        return None
    return callable_contracts_compatible(old_contract, new_contract)


def _existing_param_compatible(old: ParamContract, new: ParamContract) -> bool:
    if old.name != new.name:
        return False
    # Adding a default to a previously-required parameter preserves every call
    # form the old signature accepted (callers always supplied it), so widening
    # required -> optional is backward compatible.  Dropping a default the old
    # signature had IS a regression: callers that omitted the argument break.
    if old.has_default and not new.has_default:
        return False
    if old.has_default and new.has_default and old.default != new.default:
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
