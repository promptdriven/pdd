"""Architecture and ``<pdd-interface>`` conformance verification.

Verifies that generated code exports the symbols its ``architecture.json`` entry
and its own prompt declare, with the declared parameter shapes.
"""

import ast
import json
import logging
import pathlib
import re
from typing import Any, Dict, List, Optional, Set, Tuple

from ..architecture_registry import extract_modules
from ..architecture_sync import get_architecture_entry_for_prompt, parse_prompt_tags
from ..interface_semantics import (
    DefaultCompatibility,
    annotations_compatible,
    build_module_default_symbols,
    compare_default_sources,
    parse_callable_contract,
    signature_entries_compatible,
)
from .gate_errors import ArchitectureConformanceError

logger = logging.getLogger(__name__)


def _collect_python_symbols(body: List[ast.stmt], prefix: str) -> List[str]:
    """Recursively collect symbol names from a Python AST body.

    At the module level (``prefix=""``), returns top-level functions, classes,
    and module constants (``X = ...`` / ``X: T = ...``). Inside a class
    (``prefix="ClassName."``), returns ``ClassName.method`` for each
    direct-child method and ``ClassName.Inner`` / ``ClassName.Inner.method``
    for nested classes.

    Methods defined inside ``if``/``try``/``with`` branches inside a class
    body are deliberately NOT collected: conformance is a hard validator and
    must not accept a symbol whose existence at runtime depends on branch
    evaluation (``if False: def maybe(self): ...`` must not satisfy
    ``ClassName.maybe``).
    """
    symbols: List[str] = []
    for node in body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            symbols.append(f"{prefix}{node.name}")
        elif isinstance(node, ast.ClassDef):
            class_name = f"{prefix}{node.name}"
            symbols.append(class_name)
            symbols.extend(_collect_python_symbols(node.body, prefix=f"{class_name}."))
        elif not prefix and isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    symbols.append(target.id)
        elif (
            not prefix
            and isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name)
            and node.value is not None
        ):
            # Only ``X: T = value`` binds at runtime; bare ``X: T`` does not
            # create a module export, so it must not satisfy conformance.
            symbols.append(node.target.id)
    return symbols

# ``ParamSpec`` carries the three pieces of a parameter the signature
# conformance check compares: parameter name, annotation source (or
# ``None``), and default source (or ``None``). Sources are kept as
# whitespace-stripped strings (via ``ast.unparse``) so equality compares
# the canonical form and not the original quoting.
ParamSpec = Tuple[str, Optional[str], Optional[str]]

def _ast_args_to_specs(args: ast.arguments) -> List[ParamSpec]:
    """Return ``(name, annotation, default)`` tuples for positional+keyword args.

    Defaults align to the END of ``posonlyargs + args``. Variadic
    ``*args``/``**kwargs`` are intentionally omitted (a catch-all does not
    satisfy a contract that declares a specific named parameter).
    """
    out: List[ParamSpec] = []
    positional = list(args.posonlyargs) + list(args.args)
    defaults = list(args.defaults)
    default_offset = len(positional) - len(defaults)
    for i, arg in enumerate(positional):
        annotation = ast.unparse(arg.annotation).strip() if arg.annotation else None
        idx = i - default_offset
        default = (
            ast.unparse(defaults[idx]).strip() if 0 <= idx < len(defaults) else None
        )
        out.append((arg.arg, annotation, default))
    for arg, default in zip(args.kwonlyargs, args.kw_defaults):
        annotation = ast.unparse(arg.annotation).strip() if arg.annotation else None
        default_src = ast.unparse(default).strip() if default is not None else None
        out.append((arg.arg, annotation, default_src))
    return out

def _parse_declared_param_specs(signature: str) -> Optional[List[ParamSpec]]:
    """Parse a ``(arg: T, arg2=default, ...)`` signature into ``ParamSpec`` tuples.

    Returns ``None`` for non-paren-list signatures (e.g. class headers) so
    the caller can skip the signature check, mirroring
    :func:`_parse_declared_param_names`.
    """
    if not signature or not isinstance(signature, str):
        return None
    sig = signature.strip()
    if not sig.startswith("("):
        return None
    try:
        tree = ast.parse(f"def _f{sig}: pass")
    except SyntaxError:
        return None
    fn = tree.body[0]
    if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return None
    return _ast_args_to_specs(fn.args)

def _collect_actual_param_specs(func_node: ast.AST) -> List[ParamSpec]:
    """Return ``(name, annotation, default)`` tuples from an AST function node."""
    if not isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return []
    return _ast_args_to_specs(func_node.args)

def _find_target_function(
    tree: ast.Module, name: str
) -> Optional[ast.AST]:
    """Locate a declared function in the generated code.

    Resolution rules:
    * Bare name ``foo``:
        1. module-level ``def foo`` / ``async def foo``;
        2. module-level ``class foo`` — returns its ``__init__`` method if any
           (covers the "class methods: only check ``__init__``" rule).
    * Dotted name ``Outer.method`` / ``Outer.Inner.method``: descend through
      nested ``ClassDef`` nodes by name, then match the final segment as a
      method ``def`` / ``async def`` inside the resolved class body. This
      covers prompts whose ``pdd-interface`` declares class methods directly
      (e.g. ``ContentSelector.select``).

    Returns ``None`` if no matching definition exists.
    """
    if not isinstance(tree, ast.Module):
        return None

    parts = name.split(".") if name else []
    if not parts or any(not p for p in parts):
        return None

    # Walk through class containers for every segment except the last.
    body: List[ast.stmt] = list(tree.body)
    for part in parts[:-1]:
        cls: Optional[ast.ClassDef] = None
        for node in body:
            if isinstance(node, ast.ClassDef) and node.name == part:
                cls = node
                break
        if cls is None:
            return None
        body = list(cls.body)

    last = parts[-1]

    # Look for a direct function/method match first.
    for node in body:
        if (
            isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            and node.name == last
        ):
            return node

    # Bare-name fallback: a module-level class — return its ``__init__``.
    if len(parts) == 1:
        for node in body:
            if isinstance(node, ast.ClassDef) and node.name == last:
                for child in node.body:
                    if (
                        isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
                        and child.name == "__init__"
                    ):
                        return child
                # Class exists but has no __init__ — nothing to compare against.
                return None

    return None

def _extract_pdd_interface_signatures(
    prompt_content: Optional[str],
    prompt_name: str,
) -> Tuple[List[Tuple[str, List[ParamSpec]]], bool]:
    """Extract ``(name, [ParamSpec])`` tuples from a prompt's ``<pdd-interface>``.

    Each ``ParamSpec`` is ``(param_name, annotation_source, default_source)``
    where the source strings are ``ast.unparse``-normalized or ``None``. This
    lets the verifier check name presence (the original Issue #928 case) plus
    annotation/default drift in a single pass.

    Returns ``(declarations, parse_error_logged)``:
      - ``declarations``: list of ``(function_name, declared_param_specs)``.
        Functions whose signature is not a parseable paren-list (class headers,
        TypeScript signatures, etc.) are skipped — they're outside the scope
        of this check.
      - ``parse_error_logged``: ``True`` when malformed JSON was found and a
        warning was emitted; caller should skip the signature check.

    Returns ``([], False)`` when no ``<pdd-interface>`` block is present (the
    new check is silent in that case to preserve existing behavior).
    """
    declarations: List[Tuple[str, List[ParamSpec]]] = []
    if not prompt_content:
        return declarations, False

    # parse_prompt_tags is imported at module top level (architecture_sync is a
    # hard dependency imported there), so it is always available here.
    tags = parse_prompt_tags(prompt_content)
    parse_error = tags.get("interface_parse_error")
    if parse_error:
        logger.warning(
            "pdd-interface JSON parse error in %s: %s — skipping signature "
            "conformance check.",
            prompt_name,
            parse_error,
        )
        return declarations, True

    interface = tags.get("interface")
    if not isinstance(interface, dict):
        return declarations, False

    iface_type = interface.get("type", "")
    candidates: List[Dict[str, Any]] = []
    if iface_type == "module":
        module_spec = interface.get("module") or {}
        candidates.extend(module_spec.get("functions") or [])
    elif iface_type == "cli":
        cli_spec = interface.get("cli") or {}
        candidates.extend(cli_spec.get("commands") or [])
    elif iface_type == "command":
        # The "command" interface type comes in two shapes used in the repo
        # today: a single ``command: {name, ...}`` dict, or a multi-command
        # ``command: {commands: [...]}`` list. Most current command prompts
        # omit ``signature`` (description-only), so the loop below silently
        # skips them via the ``params is None`` check — same fall-through
        # behavior as a class-header signature. Prompts that do declare a
        # signature get the same param-name conformance treatment as cli/
        # module entries.
        command_spec = interface.get("command") or {}
        commands_list = command_spec.get("commands")
        if isinstance(commands_list, list):
            candidates.extend(commands_list)
        elif command_spec.get("name"):
            candidates.append(command_spec)
    # Other iface_types (page, component, api) don't carry callable signatures
    # we can check this way.

    for item in candidates:
        if not isinstance(item, dict):
            continue
        name = item.get("name")
        sig = item.get("signature")
        if not name or not isinstance(name, str):
            continue
        params = _parse_declared_param_specs(sig) if isinstance(sig, str) else None
        if params is None:
            # Non-paren signature (e.g. "class Foo(BaseModel)") — skip.
            continue
        declarations.append((name, params))
    return declarations, False

def _collect_pdd_interface_names(prompt_content: Optional[str]) -> Set[str]:
    """Collect declared ``module.functions`` *names* from a prompt's ``<pdd-interface>``.

    Mirrors the architecture.json declared-symbol collection (the function ``name``
    fields under a ``type: "module"`` interface) but sourced from the prompt, so the
    camelCase naming exemption honors a name the author declared in the
    source-of-truth prompt even before ``architecture.json`` is regenerated to match
    (issue #1446). Unlike :func:`_extract_pdd_interface_signatures`, this keeps
    description-only declarations (no paren signature), because the exemption keys on
    the name alone.

    The camelCase guard only ever runs for ``type: "module"`` interfaces (the only
    shape that populates declared symbols and reaches the guard), so collection is
    scoped to that type. Returns an empty set when ``prompt_content`` is absent or
    has no parseable ``<pdd-interface>`` — the exemption is best-effort and never
    blocks generation (the ``<pdd-interface>`` signature check owns parse-error
    logging, so we stay silent here to avoid a double warning).
    """
    names: Set[str] = set()
    if not prompt_content:
        return names
    tags = parse_prompt_tags(prompt_content)
    if tags.get("interface_parse_error"):
        return names
    interface = tags.get("interface")
    if not isinstance(interface, dict) or interface.get("type") != "module":
        return names
    for func in (interface.get("module") or {}).get("functions") or []:
        if isinstance(func, dict):
            name = func.get("name")
            if isinstance(name, str) and name:
                names.add(name)
    return names

def _verify_pdd_interface_signatures(
    generated_code: str,
    prompt_content: Optional[str],
    prompt_name: str,
    output_path: Optional[str],
    architecture_entry: Dict[str, Any],
) -> None:
    """Check that param names declared in ``<pdd-interface>`` exist in the code.

    Operates ONLY on functions/commands whose signature is a parseable paren
    list. Variadic ``*args``/``**kwargs`` in generated code do NOT satisfy a
    declared named parameter (e.g. ``def f(**kwargs)`` does not satisfy a
    declared ``sync_metadata`` kwarg — callers pass it by name).

    Raises ``ArchitectureConformanceError`` listing the missing parameters as
    dotted ``funcname.paramname`` entries so the existing repair-loop
    machinery surfaces them. Silently returns when:
      - no ``<pdd-interface>`` block is present in the prompt;
      - the JSON inside the block is malformed (a warning is logged);
      - none of the declared functions exists at module top-level (the
        existing symbol-existence check owns that error).
    """
    declarations, parse_error_logged = _extract_pdd_interface_signatures(
        prompt_content, prompt_name
    )
    if parse_error_logged or not declarations:
        return

    try:
        tree = ast.parse(generated_code)
    except SyntaxError:
        return  # Can't parse — defer to existing checks/recovery paths.

    # Module-level constants the generated code binds to safe literals, so a
    # default written as ``max_chars=_COMMENT_MAX_CHARS`` can be resolved back
    # to the literal it stands for when comparing against the prompt's declared
    # default (issue #1558). The prompt and the generated code describe the SAME
    # generated module namespace, so one table applies to both sides — unlike the
    # public-surface gate, which compares two different module versions and needs
    # per-side tables. A prompt that declares its default AS a bare constant name
    # the generated code inlined (so the name is absent from this table) resolves
    # UNKNOWN and is conservatively reported as drift; that fail-closed asymmetry
    # is intentional (the prompt is the source of truth and rarely names a bare
    # constant), not a latent false positive. Empty when the code defines no such
    # constants.
    module_symbols = build_module_default_symbols(generated_code)

    missing_params: List[str] = []
    missing_funcs: List[str] = []
    # Signature drift detection:
    # * Annotations are checked conservatively — only raise when BOTH sides
    #   specify the annotation and the canonical sources differ. Adding an
    #   annotation later (gradual typing) should not churn the gate.
    # * Defaults are checked strictly — defaults are runtime signature
    #   behavior, not static metadata. A prompt declaring
    #   ``sync_metadata=False`` advertises that callers may omit the kwarg;
    #   generated code lacking the default breaks those callers with
    #   ``TypeError`` at runtime, so a missing default raises drift even
    #   if the annotation is intact.
    drifted: List[Tuple[str, str, str, str, str]] = []  # (func, param, kind, declared, actual)
    declared_expected: List[str] = []
    found_in_code: List[str] = []

    for func_name, declared_specs in declarations:
        target = _find_target_function(tree, func_name)
        if target is None:
            # Function/method declared by the prompt but absent from the
            # generated code. The prompt is the source of truth even when
            # architecture.json has no matching entry, so surface this here.
            # When architecture.json *does* declare the same symbol, its
            # check runs first and raises before this point, so no
            # double-fire occurs.
            missing_funcs.append(func_name)
            declared_expected.append(func_name)
            continue
        actual_specs = _collect_actual_param_specs(target)
        actual_by_name = {spec[0]: spec for spec in actual_specs}
        for declared_name, declared_ann, declared_default in declared_specs:
            dotted = f"{func_name}.{declared_name}"
            declared_expected.append(dotted)
            if declared_name not in actual_by_name:
                missing_params.append(dotted)
                continue
            found_in_code.append(dotted)
            _, actual_ann, actual_default = actual_by_name[declared_name]
            if (
                declared_ann
                and actual_ann
                and not annotations_compatible(declared_ann, actual_ann)
            ):
                drifted.append(
                    (func_name, declared_name, "annotation", declared_ann, actual_ann)
                )
            if declared_default is not None:
                if actual_default is None:
                    # Prompt declared a default; generated code dropped it.
                    # Callers relying on the optional kwarg would now break.
                    drifted.append(
                        (
                            func_name,
                            declared_name,
                            "default",
                            declared_default,
                            "<no default>",
                        )
                    )
                elif declared_default != actual_default and (
                    # The sources differ textually (the raw ``!=`` is the fast
                    # path), but only a PROVABLY-different default is real drift.
                    # ``25000`` vs ``25_000`` vs a same-module constant
                    # ``_LIMIT = 25000`` resolve to the same value and must NOT
                    # churn the gate (issue #1558). An unresolvable default (a
                    # call, an imported name) stays UNKNOWN and is conservatively
                    # reported — same as the prior exact-string behavior, so no
                    # false negative is introduced. Both the prompt-declared and
                    # generated-code defaults live in the generated module's
                    # namespace, so the same symbol table applies to both sides.
                    compare_default_sources(
                        declared_default,
                        actual_default,
                        symbols=module_symbols,
                    )
                    is not DefaultCompatibility.COMPATIBLE
                ):
                    drifted.append(
                        (
                            func_name,
                            declared_name,
                            "default",
                            declared_default,
                            actual_default,
                        )
                    )

    if not missing_params and not missing_funcs and not drifted:
        return

    # Dedup drift-dotted entries: one parameter can hit both annotation and
    # default drift in the same call, but ``missing_symbols`` should list the
    # canonical dotted symbol once (the per-kind detail lives in the message
    # and directive, not in the symbol set).
    seen: set = set()
    drifted_dotted: List[str] = []
    for func, param, *_ in drifted:
        dotted = f"{func}.{param}"
        if dotted in seen:
            continue
        seen.add(dotted)
        drifted_dotted.append(dotted)
    missing: List[str] = missing_funcs + missing_params + drifted_dotted
    output_display = output_path or "<unknown>"
    # Emit each failure category in a distinct sentence so the subprocess
    # parser can route each to the correct repair directive. A bare dotted
    # name like ``ContentSelector.select`` under the parameter shape would
    # otherwise be misread as ``func.param`` (= "On ContentSelector, add
    # parameter select").
    message_parts: List[str] = [
        f"Architecture conformance error for {prompt_name}:"
    ]
    if missing_funcs:
        message_parts.append(
            "the prompt's <pdd-interface> declares function(s)/method(s) "
            f"missing from the generated code: {', '.join(missing_funcs)}."
        )
    if missing_params:
        message_parts.append(
            "the prompt's <pdd-interface> declares parameter(s) missing "
            f"from the generated code: {', '.join(missing_params)}."
        )
    if drifted:
        drift_summary = ", ".join(
            f"{func}.{param} ({kind}: declared `{decl}`, found `{actual}`)"
            for func, param, kind, decl, actual in drifted
        )
        message_parts.append(
            "the prompt's <pdd-interface> declares parameter(s) whose "
            "signature drifted in the generated code: "
            f"{drift_summary}."
        )
    message_parts.append(f"Output: {output_display}.")
    message = " ".join(message_parts)

    directive_lines: List[str] = [
        f"Architecture conformance error for {prompt_name}: "
        "the prompt's <pdd-interface> declares function(s)/parameter(s) "
        "that are missing from or differ from the generated code.",
    ]
    if missing_funcs:
        directive_lines.append(
            "- Add the following missing function(s)/method(s) declared in "
            f"the prompt: `{', '.join(missing_funcs)}`."
        )
    missing_by_func: Dict[str, List[str]] = {}
    for dotted in missing_params:
        # rpartition so dotted method names like "ContentSelector.select.mode"
        # group as ("ContentSelector.select", "mode") rather than
        # ("ContentSelector", "select.mode"). partition() at the first dot
        # would misattribute the param to the class instead of the method.
        func, _, param = dotted.rpartition(".")
        missing_by_func.setdefault(func, []).append(param)
    for func, params in missing_by_func.items():
        directive_lines.append(
            f"- On `{func}`, add the following missing parameter(s) to the "
            f"signature and corresponding code paths: `{', '.join(params)}`."
        )
    for func, param, kind, declared_src, actual_src in drifted:
        directive_lines.append(
            f"- On `{func}`, update parameter `{param}` so its {kind} "
            f"matches the prompt: declared `{declared_src}`, "
            f"found `{actual_src}`."
        )
    directive_lines.append("")
    directive_lines.append(
        "Do not remove the declared parameters from the prompt's "
        "<pdd-interface>. The prompt is the source of truth — update the "
        "generated code to match it."
    )

    raise ArchitectureConformanceError(
        prompt_name=prompt_name,
        output_path=output_path or "",
        architecture_entry=architecture_entry or {},
        expected_symbols=declared_expected,
        found_symbols=found_in_code,
        missing_symbols=missing,
        message=message,
        repair_directive="\n".join(directive_lines),
    )

def _verify_architecture_conformance(
    generated_code: str,
    prompt_name: str,
    arch_path: Optional[str],
    language: Optional[str],
    verbose: bool,
    output_path: Optional[str] = None,
    prompt_content: Optional[str] = None,
) -> None:
    """Check generated code exports against architecture.json interface declarations.

    Raises ``click.UsageError`` on hard mismatch (missing declared symbols or
    naming convention violations).  Silently returns when no architecture entry
    exists or when the interface section is absent.

    Additionally, when ``prompt_content`` is provided and contains a
    ``<pdd-interface>`` block, verifies that each declared function/command's
    declared parameter names exist in the generated code's function signature
    (Issue #928). This catches cases where the existing symbol-existence
    check passes but the generated code silently drops a declared kwarg
    (e.g. ``sync_metadata=False``). The prompt is the source of truth for
    the interface contract, so this check runs even when ``architecture.json``
    has no matching entry.
    """
    # Names declared in the prompt's <pdd-interface> are also intentional public
    # API for the camelCase naming check (issue #1446), even when architecture.json
    # has not yet been regenerated to match — the prompt is the source of truth.
    camel_exempt_names = _collect_pdd_interface_names(prompt_content)
    entry = _verify_architecture_json_conformance(
        generated_code=generated_code,
        prompt_name=prompt_name,
        arch_path=arch_path,
        language=language,
        output_path=output_path,
        camel_exempt_names=camel_exempt_names,
    )

    # Additionally enforce the prompt's <pdd-interface> signature contract.
    # This catches "missing kwarg" bugs (Issue #928) where the function exists
    # (so the symbol-existence check above passes) but a declared parameter
    # like ``sync_metadata=False`` is silently absent from the signature.
    # The prompt is source of truth for parameter names, so this fires even
    # if architecture.json has no matching entry.
    _verify_pdd_interface_signatures(
        generated_code=generated_code,
        prompt_content=prompt_content,
        prompt_name=prompt_name,
        output_path=output_path,
        architecture_entry=entry or {},
    )

def _verify_architecture_json_conformance(
    generated_code: str,
    prompt_name: str,
    arch_path: Optional[str],
    language: Optional[str],
    output_path: Optional[str],
    *,
    camel_exempt_names: Optional[Set[str]] = None,
) -> Optional[Dict[str, Any]]:
    """Pre-existing architecture.json symbol-existence + camelCase check.

    Extracted from :func:`_verify_architecture_conformance` so the new
    ``<pdd-interface>`` signature check (Issue #928) can run independently
    even when the architecture.json side returns early. Returns the matched
    architecture entry (or ``None``) so callers can forward it to the
    secondary check.
    """
    if not arch_path:
        arch_path = "architecture.json"
    arch_file = pathlib.Path(arch_path)
    if not arch_file.exists():
        return None

    try:
        arch_data = json.loads(arch_file.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None

    # Find the matching architecture entry
    entry: Optional[Dict[str, Any]] = None
    basename = pathlib.Path(prompt_name).stem  # e.g. "models_Python"
    for item in extract_modules(arch_data):
        item_filename = item.get("filename", "")
        if item_filename == prompt_name or pathlib.Path(item_filename).stem == basename:
            entry = item
            break

    if entry is None:
        return None

    interface = entry.get("interface")
    if not isinstance(interface, dict):
        return entry

    # Collect declared symbols from the interface
    declared_symbols: List[str] = []
    iface_type = interface.get("type", "")

    if iface_type == "module":
        module_spec = interface.get("module", {})
        for func in module_spec.get("functions", []):
            name = func.get("name")
            if name:
                declared_symbols.append(name)
    elif iface_type == "api":
        api_spec = interface.get("api", {})
        for ep in api_spec.get("endpoints", []):
            # For API modules we don't check symbol names by default
            pass
    elif iface_type in {"page", "entrypoint"}:
        # Pages and runtime entrypoints typically export framework-discovered
        # defaults rather than named symbols — skip symbol checking.
        return entry
    elif iface_type == "component":
        comp_spec = interface.get("component", {})
        for prop in comp_spec.get("props", []):
            pass  # Props aren't exported symbols
        return entry

    if not declared_symbols:
        return entry

    # Extract actual exports from generated code
    actual_symbols: List[str] = []
    detected_lang = (language or "").lower()

    if detected_lang in ("python", "py") or prompt_name.endswith("_Python.prompt"):
        try:
            tree = ast.parse(generated_code)
            actual_symbols.extend(_collect_python_symbols(tree.body, prefix=""))
        except SyntaxError:
            return entry  # Can't parse — skip conformance
    elif detected_lang in ("typescript", "javascript", "ts", "js") or any(
        prompt_name.endswith(sfx) for sfx in ("_TypeScript.prompt", "_TypeScriptReact.prompt", "_JavaScript.prompt", "_JavaScriptReact.prompt")
    ):
        export_pattern = re.compile(
            r"export\s+(?:default\s+)?(?:function|const|class|let|var|type|interface|enum)\s+(\w+)"
        )
        actual_symbols = export_pattern.findall(generated_code)
    else:
        return entry  # Unsupported language

    # Compare declared vs actual
    missing = [s for s in declared_symbols if s not in actual_symbols]
    if missing:
        raise ArchitectureConformanceError(
            prompt_name=prompt_name,
            output_path=output_path or "",
            architecture_entry=entry or {},
            expected_symbols=declared_symbols,
            found_symbols=actual_symbols,
            missing_symbols=missing,
        )

    # Check naming convention: if architecture specifies snake_case but code has camelCase.
    # Dotted symbols (``ClassName.method``) are split on ``.`` so the camelCase
    # guard inspects the method segment, not only the class-name prefix.
    if detected_lang in ("python", "py") or prompt_name.endswith("_Python.prompt"):
        camel_pattern = re.compile(r"^[a-z]+[A-Z]")
        # Exempt declared interface names from the camelCase naming check only:
        # a name declared in architecture.json (``declared_symbols``) OR in the
        # prompt's ``<pdd-interface>`` (``camel_exempt_names``, the source of
        # truth, supplied by the caller) is intentional public API (e.g. Firebase
        # Cloud Function exports like ``generateCode``), not accidental drift — so
        # only UNDECLARED camelCase is flagged (issue #1446). This exemption is
        # scoped to naming and never weakens the missing-symbol check above.
        exempt_names = set(declared_symbols)
        if camel_exempt_names:
            exempt_names |= camel_exempt_names
        camel_exports: List[str] = []
        for s in actual_symbols:
            if s in exempt_names:
                continue
            for part in s.split("."):
                if not part.startswith("_") and camel_pattern.match(part):
                    camel_exports.append(s)
                    break
        if camel_exports:
            camel_message = (
                f"Architecture conformance error for {prompt_name}: "
                f"Python code uses camelCase names ({', '.join(camel_exports[:5])}) "
                f"but Python convention requires snake_case. "
                f"Output: {output_path or '<unknown>'}. "
                f"Expected: {declared_symbols}. Found: {actual_symbols}."
            )
            raise ArchitectureConformanceError(
                prompt_name=prompt_name,
                output_path=output_path or "",
                architecture_entry=entry or {},
                expected_symbols=declared_symbols,
                found_symbols=actual_symbols,
                missing_symbols=camel_exports,
                message=camel_message,
            )

    return entry
