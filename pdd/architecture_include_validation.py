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
    *,
    dep_resolver: Optional[Any] = None,
    return_proof: bool = False,
) -> Any:
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

    PR #1073 reverse-symmetry fix: when ``return_proof`` is True the helper
    additionally returns a ``Dict[str, str]`` mapping each module key to the
    raw ``<pdd-dependency>`` text that produced it. The reverse-drift check
    needs this so the warning message can name the tag the user actually wrote
    (not the resolved arch filename). Default behavior (``return_proof=False``)
    preserves the original ``set[str]``-only signature so existing callers and
    tests do not have to change.
    """
    if return_proof:
        empty: tuple[set[str], Dict[str, str]] = (set(), {})
    try:
        content = prompt_path.read_text(encoding="utf-8")
    except OSError:
        return empty if return_proof else set()
    if not content:
        return empty if return_proof else set()

    from .architecture_sync import parse_prompt_tags, build_dependency_resolver

    modules: set[str] = set()
    proof: Dict[str, str] = {}
    tags = parse_prompt_tags(content)
    raw_deps = list(tags.get("dependencies", []) or [])
    # F11 third-party codex review: prefer a precomputed resolver when the caller
    # passes one (saves rebuilding the resolution index per arch entry). Fall back
    # to building one on demand if only arch_data was provided, or skip resolution
    # entirely when neither is available.
    if dep_resolver is None and arch_data:
        dep_resolver = build_dependency_resolver(arch_data)
    for raw in raw_deps:
        resolved = dep_resolver(raw) if dep_resolver is not None else raw
        m = _path_preserving_module_key(resolved)
        if m and m != self_mod:
            modules.add(m)
            proof.setdefault(m, raw)
    if return_proof:
        return modules, proof
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

    The reverse direction (a prompt-declared edge with no matching arch dep)
    warns symmetrically: a module-prompt ``<include>`` OR a
    ``<pdd-dependency>`` tag that names a module not listed in
    ``architecture.json`` both surface as drift. PR #1073 review: the prior
    asymmetric check ignored ``<pdd-dependency>`` drift here on the
    assumption that ``architecture_sync`` would heal it, but a user running
    ``pdd checkup --validate-arch-includes`` without first running ``pdd
    sync`` would never see the drift. Validation must be authoritative on
    its own.

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

    # F11 third-party codex review: build the dependency resolver index ONCE
    # for the whole validation run instead of rebuilding it per arch entry in
    # _pdd_dependency_modules. Each entry then reuses the same precomputed
    # indices via dep_resolver(dep). Avoids O(N) index construction per entry.
    from .architecture_sync import build_dependency_resolver
    dep_resolver = build_dependency_resolver(arch_data)

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
            # First gate: only module-prompt paths participate (drops context,
            # preambles, example .py files).
            if _module_prompt_include_target(inc) is None:
                continue
            # PR #1073 finding 1: bare includes like ``<include>b_python.prompt</include>``
            # written from a path-qualified prompt (``commands/a_python.prompt``)
            # would key to bare ``"b"`` while sync's ``_normalize_dependency_filenames``
            # writes the arch dep as ``commands/b_python.prompt`` (keyed
            # ``"commands/b"``). The two sides then diverge and the validator
            # raises a false-positive mismatch on a perfectly-synced repo. Resolve
            # the include through the same precomputed ``dep_resolver`` so disk
            # and arch keying converge. When the resolver can't disambiguate
            # (genuine ambiguity or no matching arch entry), it returns the input
            # unchanged and the original bare-stem keying still applies.
            resolved_inc = dep_resolver(inc)
            m = _path_preserving_module_key(resolved_inc)
            if m and m != mod_base:
                include_modules.add(m)
                include_proof.setdefault(m, inc)

        tag_modules, tag_proof = _pdd_dependency_modules(
            prompt_path, mod_base, dep_resolver=dep_resolver, return_proof=True
        )
        forward_declared = include_modules | tag_modules

        # F10 third-party codex review: arch-listed deps may be bare (stale
        # hand-edits like ``["fix_python.prompt"]`` when the real entry is
        # ``server/fix_python.prompt``). Resolve via the same precomputed
        # dep_resolver before keying so the validator sees the same edges the
        # graph builder will resolve to.
        #
        # PR #1073 finding 2 follow-up: when ``filename_to_basename`` has no
        # entry for the resolved dep (the prompt named in the dep is not a
        # tracked arch module), fall back to ``_path_preserving_module_key``
        # directly so the dep still produces a key. Otherwise an
        # arch-declared dep on an untracked module silently vanishes from
        # ``arch_modules``, while the SAME dep declared as a
        # ``<pdd-dependency>`` on the prompt side keys via the same helper
        # and sticks in ``forward_declared`` — producing a false reverse
        # mismatch on a perfectly aligned pair of declarations. Both sides
        # of the comparison now use the same keying rule. If the dep names
        # something that isn't a module-prompt path at all (no language
        # suffix), the helper returns ``None`` and the dep is correctly
        # skipped.
        arch_modules: set[str] = set()
        dep_fn_to_resolved: Dict[str, str] = {}
        for dep_fn in entry.get("dependencies", []):
            if not isinstance(dep_fn, str):
                continue
            resolved_fn = dep_resolver(dep_fn)
            dep_fn_to_resolved[dep_fn] = resolved_fn
            db = filename_to_basename.get(resolved_fn)
            if db is None:
                db = _path_preserving_module_key(resolved_fn)
            if db and db != mod_base:
                arch_modules.add(db)

        for d in sorted(arch_modules - forward_declared):
            dep_fn_proof = next(
                (
                    df
                    for df in entry.get("dependencies", [])
                    if isinstance(df, str)
                    and filename_to_basename.get(dep_fn_to_resolved.get(df, df)) == d
                ),
                None,
            )
            extra = f" ({dep_fn_proof!r})" if dep_fn_proof else ""
            warnings.append(
                f"architecture.json / <include> mismatch: {fn!r} declares dependency on module "
                f"{d!r}{extra} but the prompt has no <include> or <pdd-dependency> of that module's prompt"
            )

        # PR #1073 finding 2: reverse direction must also catch
        # ``<pdd-dependency>`` drift. The forward and reverse checks must be
        # symmetric — both kinds of tag are architecture edges under the union
        # semantics, so both kinds must be reported when arch.json omits them.
        # The warning text distinguishes the two artifact kinds so users know
        # which tag to fix.
        for m in sorted(forward_declared - arch_modules):
            inc_s = include_proof.get(m)
            tag_s = tag_proof.get(m)
            if inc_s is not None:
                warnings.append(
                    f"architecture.json / <include> mismatch: {fn!r} <include>s module {m!r} "
                    f"({inc_s!r}) but architecture.json dependencies do not list that module"
                )
            else:
                proof_extra = f" ({tag_s!r})" if tag_s else ""
                warnings.append(
                    f"architecture.json / <include> mismatch: {fn!r} declares "
                    f"<pdd-dependency> on module {m!r}{proof_extra} but architecture.json "
                    f"dependencies do not list that module"
                )

    return warnings
