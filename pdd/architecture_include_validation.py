"""
Cross-validate architecture.json dependency entries against <include> tags in prompts.

Phase 5: surface drift between declarative architecture dependencies and the module
prompts the LLM actually pulls in via <include>.
"""
from __future__ import annotations

import json
import ast
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, FrozenSet, List, Optional, Set

from .architecture_registry import BUNDLED_SAMPLE_TOPLEVEL_DIRS, extract_modules
from .sync_order import extract_includes_from_file, extract_module_from_include


def _path_preserving_module_key(filename: str) -> Optional[str]:
    """Return a path-preserving module key for an include or arch filename.

    Mirrors ``auto_deps_architecture._path_preserving_module_key``. We
    duplicate the helper here (rather than importing it) because
    ``auto_deps_architecture`` already imports
    ``resolve_architecture_prompt_path`` from this module — sharing the
    helper would create a circular import. Both copies must stay in
    sync; F4 third-party codex review.

    Strategy:
      * Reject inputs ``extract_module_from_include`` does not recognize
        as module references — this preserves the long-standing filter
        that drops non-language-suffix prompts (e.g.
        ``context/python_preamble.prompt`` is a context preamble, not a
        module prompt).
      * For accepted ``.prompt`` paths, canonicalize via
        ``architecture_sync._normalize_prompt_filename`` (strip ``./`` /
        leading ``prompts/``) and derive the basename via
        ``agentic_sync_runner._basename_from_architecture_filename`` so
        directory segments are preserved
        (``"commands/fix_python.prompt"`` → ``"commands/fix"``,
        ``"fix_python.prompt"`` → ``"fix"``).
      * For accepted non-prompt context paths (example ``.py`` files,
        kept as a known case), degrade to the bare-stem
        ``extract_module_from_include`` result so the long-standing
        example-path → module mapping is preserved.

    Returns ``None`` when no module key can be derived (no recognized
    language suffix, LLM-only prompt, empty string, etc.).
    """
    if not filename:
        return None
    # Gate: keep the original module-recognition filter so non-module
    # paths (preambles, doc fragments) continue to be ignored.
    if not extract_module_from_include(filename):
        return None
    from .agentic_sync_runner import _basename_from_architecture_filename
    from .architecture_sync import _normalize_prompt_filename

    normalized = _normalize_prompt_filename(filename)
    if normalized.lower().endswith(".prompt"):
        return _basename_from_architecture_filename(normalized)
    # Non-prompt module reference (e.g. ``context/foo_example.py``).
    # Preserve the bare-stem mapping used by callers that rely on
    # example-path → module aliasing.
    return extract_module_from_include(normalized)


def _module_prompt_include_target(include_path: str) -> Optional[str]:
    """
    Map an <include> path to a path-preserving module key only when it names another module prompt.

    Context/example ``.py`` files and non-language-suffix ``.prompt`` files
    (e.g. ``context/python_preamble.prompt``) are ignored so validation
    matches architecture.json, which lists dependencies between module prompts,
    not every referenced artifact.

    Returns a directory-qualified key (``"commands/fix"``) when the include path is
    path-qualified, so the validator can distinguish same-tail module prompts that
    live in different folders (F4 third-party codex review). A bare include path
    (``"fix_python.prompt"``) returns the bare stem (``"fix"``) — flat-layout
    behavior is preserved by the natural degradation of
    ``_basename_from_architecture_filename``.
    """
    p = (include_path or "").strip()
    if not p.lower().endswith(".prompt"):
        return None
    return _path_preserving_module_key(p)


# Re-export for backwards compatibility with external imports that still
# reference this name from the validation module.
_BUNDLED_SAMPLE_TOPLEVEL_DIRS: FrozenSet[str] = BUNDLED_SAMPLE_TOPLEVEL_DIRS


def collect_architecture_include_validation_warnings(
    project_root: Path,
    *,
    skip_bundled_sample_arch: bool = True,
) -> List[str]:
    """
    Run cross-validation for every ``architecture.json`` under ``project_root``.

    Each file is validated with its **parent directory** as the project root for
    resolving ``prompts/…`` paths, so nested packages (e.g. ``services/api/``) work.

    When ``skip_bundled_sample_arch`` is true (default), discovery skips trees like
    ``examples/`` used in the PDD repository so routine sync stays focused on app code.
    """
    from .architecture_registry import find_architecture_for_project

    warnings: List[str] = []
    for arch_path in find_architecture_for_project(
        project_root, skip_bundled_sample_arch=skip_bundled_sample_arch
    ):
        try:
            with open(arch_path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except (OSError, json.JSONDecodeError):
            continue
        modules = extract_modules(data)
        if not modules:
            continue
        base = arch_path.parent
        for w in cross_validate_architecture_with_prompt_includes(modules, base):
            warnings.append(f"{arch_path}: {w}")
    return warnings


def run_validate_arch_includes_cli(
    project_root: Path,
    *,
    strict: bool,
    quiet: bool,
) -> None:
    """
    Print validation messages and exit with code 1 if there are issues.

    Used by ``pdd checkup --validate-arch-includes``.
    """
    import click

    warnings = list_validate_arch_include_warnings(project_root, strict=strict)
    if not warnings:
        if not quiet:
            click.echo("No architecture / <include> mismatches found.")
        return
    for w in warnings:
        if not quiet:
            click.echo(click.style(f"Warning: {w}", fg="yellow"), err=True)
    raise click.exceptions.Exit(1)


def list_validate_arch_include_warnings(project_root: Path, *, strict: bool) -> List[str]:
    """
    Return cross-validation issues for ``project_root``.

    When ``strict`` is False (default CLI), skip bundled sample trees under
    ``examples/``, ``example_project/``, etc. When True, validate those too
    (useful for maintainer / CI runs against the full repo).
    """
    return collect_architecture_include_validation_warnings(
        project_root,
        skip_bundled_sample_arch=not strict,
    )


def print_architecture_include_validation_warnings(*, quiet: bool, verbose: bool = False) -> None:
    """Print yellow warnings for the current project only when ``--verbose`` (and not ``--quiet``)."""
    if quiet or not verbose:
        return
    from rich import print as rprint

    from .architecture_registry import find_project_root

    for w in collect_architecture_include_validation_warnings(find_project_root()):
        rprint(f"[yellow]Warning: {w}[/yellow]")


def _resolve_architecture_prompt_path(filename: str, project_root: Path) -> Path:
    """Resolve architecture ``filename`` to an on-disk path under the project."""
    rel = filename.replace("\\", "/").lstrip("/")
    if rel.startswith("prompts/"):
        return (project_root / rel).resolve()
    return (project_root / "prompts" / rel).resolve()


def resolve_architecture_prompt_path(filename: str, project_root: Path) -> Path:
    """Public API for resolving an architecture ``filename`` to an on-disk path."""
    return _resolve_architecture_prompt_path(filename, project_root)


@dataclass(frozen=True)
class _IncludeReference:
    """A parsed prompt ``<include>`` tag."""

    path: str
    attrs: Dict[str, str]

    @property
    def is_interface_mode(self) -> bool:
        """Return True when the include asks preprocessing to strip bodies."""
        return self.attrs.get("mode", "").strip().lower() == "interface"

    @property
    def is_partial(self) -> bool:
        """Return True when the include does not provide full implementation source."""
        return self.is_interface_mode or any(
            self.attrs.get(k, "").strip() for k in ("select", "lines", "query")
        )


_INCLUDE_RE = re.compile(
    r"<include(?P<attrs>\s+[^>]*?)?>(?P<content>.*?)</include>|"
    r"<include(?P<attrs_self>\s+[^>]*?)\s*/>",
    re.IGNORECASE | re.DOTALL,
)
_ATTR_RE = re.compile(
    r"""([A-Za-z_:][\w:.-]*)\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s>]+))"""
)


def _parse_include_attrs(raw_attrs: str) -> Dict[str, str]:
    """Parse simple XML-style attributes from an ``<include>`` tag."""
    attrs: Dict[str, str] = {}
    for match in _ATTR_RE.finditer(raw_attrs or ""):
        value = match.group(2)
        if value is None:
            value = match.group(3)
        if value is None:
            value = match.group(4)
        attrs[match.group(1).lower()] = value or ""
    return attrs


def _extract_include_references(prompt_content: str) -> List[_IncludeReference]:
    """Return parsed ``<include>`` tags with their target paths and attributes."""
    refs: List[_IncludeReference] = []
    for match in _INCLUDE_RE.finditer(prompt_content or ""):
        attrs = _parse_include_attrs(
            match.group("attrs") or match.group("attrs_self") or ""
        )
        body_path = (match.group("content") or "").strip()
        path = (attrs.get("path") or body_path).strip()
        if not path:
            continue
        refs.append(_IncludeReference(path=path, attrs=attrs))
    return refs


@dataclass(frozen=True)
class _PythonSymbolSpan:
    """A public Python symbol and its 1-based inclusive source line span."""

    name: str
    start_line: int
    end_line: int


def _node_line_span(node: ast.AST) -> tuple[int, int]:
    """Return the 1-based inclusive source span for an AST node."""
    start_line = getattr(node, "lineno", 0) or 0
    decorators = getattr(node, "decorator_list", [])
    if decorators:
        start_line = min(
            [start_line]
            + [
                getattr(decorator, "lineno", start_line) or start_line
                for decorator in decorators
            ]
        )
    end_line = getattr(node, "end_lineno", None) or start_line
    return start_line, end_line


def _collect_python_public_symbols(body: List[ast.stmt], prefix: str = "") -> List[str]:
    """Collect public Python exports using the same shape as architecture conformance."""
    symbols: List[str] = []
    for node in body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if not node.name.startswith("_"):
                symbols.append(f"{prefix}{node.name}")
        elif isinstance(node, ast.ClassDef):
            if not node.name.startswith("_"):
                class_name = f"{prefix}{node.name}"
                symbols.append(class_name)
                symbols.extend(_collect_python_public_symbols(node.body, f"{class_name}."))
        elif not prefix and isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and not target.id.startswith("_"):
                    symbols.append(target.id)
        elif (
            not prefix
            and isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name)
            and node.value is not None
            and not node.target.id.startswith("_")
        ):
            symbols.append(node.target.id)
    return symbols


def _collect_python_public_symbol_spans(
    body: List[ast.stmt], prefix: str = ""
) -> List[_PythonSymbolSpan]:
    """Collect public Python exports with their source line spans."""
    spans: List[_PythonSymbolSpan] = []
    for node in body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if not node.name.startswith("_"):
                start_line, end_line = _node_line_span(node)
                spans.append(
                    _PythonSymbolSpan(f"{prefix}{node.name}", start_line, end_line)
                )
        elif isinstance(node, ast.ClassDef):
            if not node.name.startswith("_"):
                class_name = f"{prefix}{node.name}"
                start_line, end_line = _node_line_span(node)
                spans.append(_PythonSymbolSpan(class_name, start_line, end_line))
                spans.extend(
                    _collect_python_public_symbol_spans(node.body, f"{class_name}.")
                )
        elif not prefix and isinstance(node, ast.Assign):
            start_line, end_line = _node_line_span(node)
            for target in node.targets:
                if isinstance(target, ast.Name) and not target.id.startswith("_"):
                    spans.append(_PythonSymbolSpan(target.id, start_line, end_line))
        elif (
            not prefix
            and isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name)
            and node.value is not None
            and not node.target.id.startswith("_")
        ):
            start_line, end_line = _node_line_span(node)
            spans.append(_PythonSymbolSpan(node.target.id, start_line, end_line))
    return spans


def _python_top_level_public_symbols(source: str) -> List[str]:
    """Return public symbols exported by a Python source file."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []
    seen: Set[str] = set()
    ordered: List[str] = []
    for symbol in _collect_python_public_symbols(tree.body):
        if symbol not in seen:
            seen.add(symbol)
            ordered.append(symbol)
    return ordered


def _python_public_symbol_spans(source: str) -> Dict[str, _PythonSymbolSpan]:
    """Return public Python symbol source spans keyed by symbol name."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return {}

    spans: Dict[str, _PythonSymbolSpan] = {}
    for span in _collect_python_public_symbol_spans(tree.body):
        spans.setdefault(span.name, span)
    return spans


def _interface_function_names(interface: Any) -> List[str]:
    """Extract declared public symbols from an architecture/prompt interface block."""
    if not isinstance(interface, dict):
        return []
    if interface.get("type") != "module":
        return []

    module_spec = interface.get("module")
    if not isinstance(module_spec, dict):
        return []

    names: List[str] = []
    for key in ("functions", "classes", "constants", "exports"):
        values = module_spec.get(key, [])
        if not isinstance(values, list):
            continue
        for value in values:
            name: Optional[str] = None
            if isinstance(value, dict):
                raw_name = value.get("name")
                if isinstance(raw_name, str):
                    name = raw_name
            elif isinstance(value, str):
                name = value
            if name and not name.startswith("_") and name not in names:
                names.append(name)
    return names


def _prompt_interface(prompt_content: str) -> Optional[Dict[str, Any]]:
    """Extract the prompt-local ``<pdd-interface>`` block if present."""
    try:
        from .architecture_sync import parse_prompt_tags

        interface = parse_prompt_tags(prompt_content).get("interface")
    except Exception:
        return None
    return interface if isinstance(interface, dict) else None


def _entry_matches_prompt_or_output(
    entry: Dict[str, Any],
    prompt_path: Path,
    output_path: Path,
    project_root: Path,
) -> bool:
    """Return True when an architecture entry names the prompt or output path."""
    filename = str(entry.get("filename") or "").replace("\\", "/")
    prompt_name = prompt_path.name
    if filename:
        if filename == prompt_name or Path(filename).name == prompt_name:
            return True
        if Path(filename).stem == prompt_path.stem:
            return True

    filepath = entry.get("filepath")
    if isinstance(filepath, str) and filepath.strip():
        normalized = filepath.replace("\\", "/").lstrip("/")
        try:
            if (project_root / normalized).resolve() == output_path.resolve():
                return True
        except OSError:
            pass
        try:
            rel_output = output_path.resolve().relative_to(project_root.resolve()).as_posix()
            if rel_output == normalized:
                return True
        except ValueError:
            pass
    return False


def _load_architecture_interface(
    architecture_path: Optional[Path],
    prompt_path: Path,
    output_path: Path,
    project_root: Path,
) -> Optional[Dict[str, Any]]:
    """Load the matching architecture.json interface block, if any."""
    arch_path = architecture_path or (project_root / "architecture.json")
    if not arch_path.exists():
        return None
    try:
        arch_data = json.loads(arch_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None

    for entry in extract_modules(arch_data):
        if _entry_matches_prompt_or_output(entry, prompt_path, output_path, project_root):
            interface = entry.get("interface")
            return interface if isinstance(interface, dict) else None
    return None


def _include_matches_output(include_path: str, output_path: Path, project_root: Path) -> bool:
    """Return True when an include target is the same file as the output path."""
    raw = include_path.replace("\\", "/").strip()
    if not raw:
        return False
    candidate = Path(raw)
    if not candidate.is_absolute():
        candidate = project_root / raw
    try:
        if candidate.resolve() == output_path.resolve():
            return True
    except OSError:
        pass
    try:
        rel_output = output_path.resolve().relative_to(project_root.resolve()).as_posix()
        return raw.lstrip("/") == rel_output
    except ValueError:
        return False


def _parse_line_ranges(lines_value: str, total_lines: int) -> List[tuple[int, int]]:
    """
    Parse ContentSelector ``lines:`` syntax into 1-based inclusive spans.

    Supported forms intentionally mirror ``pdd.content_selector``: ``N``, ``N-M``,
    ``N-``, ``-M``, and comma-separated combinations.
    """
    ranges: List[tuple[int, int]] = []
    for part in (lines_value or "").split(","):
        token = part.strip()
        if not token:
            continue
        try:
            if "-" in token:
                split_at = token.index("-")
                left = token[:split_at].strip()
                right = token[split_at + 1 :].strip()
                if left == "" and right == "":
                    continue
                start = int(left) if left else 1
                end = int(right) if right else total_lines
            else:
                start = end = int(token)
        except ValueError:
            continue

        start = max(1, start)
        end = min(total_lines, end)
        if start <= end:
            ranges.append((start, end))
    return ranges


def _symbols_covered_by_line_ranges(source: str, lines_value: str) -> Set[str]:
    """Map deterministic ``lines=``/``lines:`` selectors to covered symbols."""
    line_ranges = _parse_line_ranges(lines_value, len(source.splitlines()))
    if not line_ranges:
        return set()

    covered: Set[str] = set()
    for symbol, span in _python_public_symbol_spans(source).items():
        if any(
            start <= span.start_line and span.end_line <= end for start, end in line_ranges
        ):
            covered.add(symbol)
    return covered


def _symbols_covered_by_selectors(
    selectors: List[str],
    existing_symbols: List[str],
    existing_source: str,
) -> Set[str]:
    """Map ``<include select=...>`` selectors to covered source symbols."""
    covered: Set[str] = set()
    symbol_set = set(existing_symbols)
    for selector_list in selectors:
        for raw_token in (selector_list or "").split(","):
            token = raw_token.strip()
            if not token:
                continue
            kind = ""
            value = token
            if ":" in token:
                kind, value = token.split(":", 1)
                kind = kind.strip().lower()
                value = value.strip()
            if not value:
                continue
            if kind in {"class", "cls"}:
                for symbol in existing_symbols:
                    if symbol == value or symbol.startswith(f"{value}."):
                        covered.add(symbol)
            elif kind == "lines":
                covered.update(_symbols_covered_by_line_ranges(existing_source, value))
            elif value in symbol_set:
                covered.add(value)
    return covered


def _symbols_covered_by_partial_includes(
    self_includes: List[_IncludeReference],
    existing_symbols: List[str],
    existing_source: str,
) -> tuple[Set[str], List[str]]:
    """Return deterministic implementation symbols covered by partial self-includes."""
    covered: Set[str] = set()
    unsupported: List[str] = []

    for ref in self_includes:
        select_value = ref.attrs.get("select", "").strip()
        query_value = ref.attrs.get("query", "").strip()
        lines_value = ref.attrs.get("lines", "").strip()

        if ref.is_interface_mode:
            unsupported.append(
                'mode="interface" self-include does not provide implementation context'
            )
            continue

        if select_value:
            covered.update(
                _symbols_covered_by_selectors(
                    [select_value],
                    existing_symbols,
                    existing_source,
                )
            )
            if lines_value:
                covered.update(_symbols_covered_by_line_ranges(existing_source, lines_value))
            continue

        if query_value:
            unsupported.append("query= self-include cannot prove symbol coverage")
            continue

        if lines_value:
            covered.update(_symbols_covered_by_line_ranges(existing_source, lines_value))

    return covered, unsupported


def validate_prompt_contract_context(
    prompt_path: Path,
    output_path: Path,
    project_root: Path,
    architecture_path: Optional[Path] = None,
    prompt_content: Optional[str] = None,
    require_prompt_local_source_context: bool = False,
) -> List[str]:
    """
    Validate that broad module interface declarations have matching source context.

    This preflight catches the issue-798 failure shape: an existing module prompt
    declares a wide public interface but includes only a small selected slice of
    the existing implementation, leaving the LLM without enough context to
    preserve declared exports. A full self-include satisfies the contract. A
    partial self-include must select every declared symbol that already exists in
    the output source file.
    """
    prompt_path = Path(prompt_path)
    output_path = Path(output_path)
    project_root = Path(project_root)

    if prompt_content is None:
        try:
            prompt_content = prompt_path.read_text(encoding="utf-8")
        except OSError:
            return []

    try:
        existing_source = output_path.read_text(encoding="utf-8")
    except OSError:
        return []
    if not existing_source.strip():
        return []

    prompt_interface = _prompt_interface(prompt_content)
    prompt_declared_symbols = _interface_function_names(prompt_interface)

    declared_symbols: List[str] = []
    for interface in (
        prompt_interface,
        _load_architecture_interface(architecture_path, prompt_path, output_path, project_root),
    ):
        for symbol in _interface_function_names(interface):
            if symbol not in declared_symbols:
                declared_symbols.append(symbol)
    if not declared_symbols:
        return []

    existing_symbols = _python_top_level_public_symbols(existing_source)
    existing_symbol_set = set(existing_symbols)
    declared_existing = [symbol for symbol in declared_symbols if symbol in existing_symbol_set]
    if not declared_existing:
        return []

    self_includes = [
        ref
        for ref in _extract_include_references(prompt_content)
        if _include_matches_output(ref.path, output_path, project_root)
    ]
    if not self_includes:
        prompt_declared_existing = [
            symbol for symbol in prompt_declared_symbols if symbol in existing_symbol_set
        ]
        if require_prompt_local_source_context and prompt_declared_existing:
            return [
                (
                    f"{prompt_path}: prompt-local interface declares "
                    f"{len(prompt_declared_existing)} public symbols already present "
                    f"in {output_path} but includes no existing module source context: "
                    f"missing {', '.join(prompt_declared_existing)}. Use a full "
                    "<include> of the existing module or select every declared "
                    "existing public symbol."
                )
            ]
        return []
    if any(not ref.is_partial for ref in self_includes):
        return []

    covered, unsupported = _symbols_covered_by_partial_includes(
        self_includes,
        existing_symbols,
        existing_source,
    )
    missing = [symbol for symbol in declared_existing if symbol not in covered]
    if not missing:
        return []

    covered_declared_count = len([s for s in declared_existing if s in covered])
    unsupported_note = ""
    if unsupported:
        unsupported_note = " Unsupported partial self-include context: " + "; ".join(
            sorted(set(unsupported))
        ) + "."
    return [
        (
            f"{prompt_path}: prompt declares {len(declared_existing)} public symbols "
            f"already present in {output_path} but only includes source context for "
            f"{covered_declared_count}: missing {', '.join(missing)}. "
            "Use a full <include> of the existing module or select every declared "
            f"existing public symbol.{unsupported_note}"
        )
    ]


def _pdd_dependency_modules(
    prompt_path: Path,
    self_mod: str,
    arch_data: Optional[List[Dict[str, Any]]] = None,
) -> set[str]:
    """
    Return path-preserving module keys declared via ``<pdd-dependency>`` tags in
    the prompt header.

    Per ``docs/prompting_guide.md``, ``<pdd-dependency>`` is the authoritative
    architectural declaration and ``<include>`` of a module prompt is also an
    architecture edge. The forward check treats a ``<pdd-dependency>`` tag as
    proof that the prompt has declared the dependency, so arch-listed deps
    backed only by a tag (no ``<include>`` of the module's prompt) are not
    flagged as drift.

    F4 third-party codex review: keys are path-preserving so a tag like
    ``<pdd-dependency>server/fix_python.prompt</pdd-dependency>`` matches an
    arch dep entry ``"server/fix_python.prompt"`` without colliding with a
    same-tail ``"commands/fix_python.prompt"`` entry.

    F7 third-party codex review: when ``arch_data`` is supplied, raw declarations
    are first run through ``_normalize_dependency_filenames`` so a bare
    ``<pdd-dependency>fix_python.prompt</pdd-dependency>`` resolves to its
    unambiguous path-qualified arch entry (e.g. ``server/fix_python.prompt``)
    before path-preserving keying. Without this step a bare declaration would
    key to ``"fix"`` while the arch dep keys to ``"server/fix"`` and the
    validator would falsely warn that the prompt is missing a declaration.
    """
    try:
        content = prompt_path.read_text(encoding="utf-8")
    except OSError:
        return set()
    if not content:
        return set()

    from .architecture_sync import parse_prompt_tags, _normalize_dependency_filenames

    modules: set[str] = set()
    tags = parse_prompt_tags(content)
    raw_deps = list(tags.get("dependencies", []) or [])
    if arch_data:
        resolved = _normalize_dependency_filenames(raw_deps, arch_data)
    else:
        resolved = raw_deps
    for dep in resolved:
        m = _path_preserving_module_key(dep)
        if m and m != self_mod:
            modules.add(m)
    return modules


def cross_validate_architecture_with_prompt_includes(
    arch_data: List[Dict[str, Any]],
    project_root: Path,
) -> List[str]:
    """
    Compare each architecture entry's ``dependencies`` (as path-preserving module
    keys) with module targets of ``<include>`` tags in the corresponding prompt file.

    A declared dependency is satisfied if the prompt either ``<include>``s the
    dependency's prompt OR declares it via ``<pdd-dependency>`` (the metadata
    tag the prompting guide calls the authoritative architectural declaration).

    The reverse direction (``<include>`` of a module prompt without a matching
    arch dep) still warns; drift between ``<pdd-dependency>`` tags and
    ``architecture.json`` is handled by ``architecture_sync``, not this check.

    Non-module includes (docs, preambles, etc.) are ignored via
    ``_module_prompt_include_target`` which only accepts ``.prompt`` paths.

    F4 third-party codex review: comparisons use ``_path_preserving_module_key``
    so directory-qualified entries like ``"commands/fix_python.prompt"`` and
    ``"server/fix_python.prompt"`` are distinguishable. Unqualified inputs
    degrade to the bare module stem so flat-layout architectures still work.

    Returns:
        Human-readable warning strings (empty if no mismatches / nothing to check).
    """
    warnings: List[str] = []

    # F4 third-party codex review: path-preserving keys throughout so a
    # path-qualified arch entry like ``"commands/fix_python.prompt"`` is
    # not collapsed to the bare stem ``"fix"`` and silently aliased with
    # ``"server/fix_python.prompt"``. Unqualified arch filenames degrade
    # to their bare stem via ``_basename_from_architecture_filename`` so
    # flat-layout architectures continue to work as before.
    filename_to_basename: Dict[str, str] = {}
    for entry in arch_data:
        fn = entry.get("filename") or ""
        if not fn:
            continue
        b = _path_preserving_module_key(fn)
        if b:
            filename_to_basename[fn] = b

    for entry in arch_data:
        fn = entry.get("filename") or ""
        if not fn:
            continue
        mod_base = filename_to_basename.get(fn)
        if not mod_base:
            continue

        prompt_path = _resolve_architecture_prompt_path(fn, project_root)
        if not prompt_path.is_file():
            warnings.append(
                f"Cross-validation skipped for architecture entry {fn!r}: "
                f"prompt file not found at {prompt_path}"
            )
            continue

        includes = extract_includes_from_file(prompt_path)
        include_modules: set[str] = set()
        include_proof: Dict[str, str] = {}
        for inc in includes:
            m = _module_prompt_include_target(inc)
            if m and m != mod_base:
                include_modules.add(m)
                include_proof.setdefault(m, inc)

        tag_modules = _pdd_dependency_modules(prompt_path, mod_base, arch_data)
        forward_declared = include_modules | tag_modules

        arch_modules: set[str] = set()
        for dep_fn in entry.get("dependencies", []):
            db = filename_to_basename.get(dep_fn)
            if db and db != mod_base:
                arch_modules.add(db)

        for d in sorted(arch_modules - forward_declared):
            dep_fn_proof = next(
                (
                    df
                    for df in entry.get("dependencies", [])
                    if filename_to_basename.get(df) == d
                ),
                None,
            )
            extra = f" ({dep_fn_proof!r})" if dep_fn_proof else ""
            warnings.append(
                f"architecture.json / <include> mismatch: {fn!r} declares dependency on module "
                f"{d!r}{extra} but the prompt has no <include> or <pdd-dependency> of that module's prompt"
            )

        for i in sorted(include_modules - arch_modules):
            inc_s = include_proof.get(i, "")
            warnings.append(
                f"architecture.json / <include> mismatch: {fn!r} <include>s module {i!r} "
                f"({inc_s!r}) but architecture.json dependencies do not list that module"
            )

    return warnings
