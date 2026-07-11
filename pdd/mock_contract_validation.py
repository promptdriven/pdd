"""Validate generated mock data against repository-backed interface contracts.

The fix workflows already re-run generated tests independently.  That proves
the tests execute, but it cannot prove that a mock describes the production
interface correctly.  This module closes that gap for Python data lookups by
comparing newly introduced query fields and mock payload fields with explicit
schema documents and corroborating production usages in the repository.

The validator is deliberately conservative: absence is a failure only when an
authoritative schema section for the exact resource exists.  Missing or
conflicting evidence is surfaced as ``inconclusive`` rather than guessed from a
field name.
"""
from __future__ import annotations

import ast
import json
import re
import subprocess
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping, Optional, Sequence


_QUERY_CALLS = {"query_collection", "count_collection"}
_WRITE_CALLS = {
    "add_document",
    "create_document",
    "set_document",
    "update_document",
}
_MOCK_FACTORIES = {"AsyncMock", "MagicMock", "Mock", "patch"}
_SCHEMA_SUFFIXES = {".json", ".md", ".markdown"}
_SKIP_DIRS = {
    ".git",
    ".pdd",
    ".tox",
    ".venv",
    "__pycache__",
    "build",
    "dist",
    "node_modules",
    "research",
    "staging",
    "venv",
}


@dataclass(frozen=True)
class QueryFieldUse:
    """A concrete field lookup against a named external resource."""

    resource: str
    field_name: str
    source_path: str
    line: int
    callee: str


@dataclass(frozen=True)
class MockFieldUse:
    """A literal field supplied by a test mock payload."""

    field_name: str
    source_path: str
    line: int
    target: str


@dataclass(frozen=True)
class ContractEvidence:
    """Allowed fields proven by a repository contract source."""

    resource: str
    fields: frozenset[str]
    source_path: str
    line: int
    kind: str


@dataclass(frozen=True)
class MockContractFinding:
    """One query/mock shape that contradicts authoritative evidence."""

    resource: str
    field_name: str
    code_path: str
    code_line: int
    mock_paths: tuple[str, ...]
    contract_paths: tuple[str, ...]
    message: str


@dataclass(frozen=True)
class MockContractReport:
    """Structured result consumed by manual and agentic fix workflows."""

    status: str
    findings: tuple[MockContractFinding, ...] = ()
    warnings: tuple[str, ...] = ()
    queries: tuple[QueryFieldUse, ...] = ()
    mock_fields: tuple[MockFieldUse, ...] = ()
    contracts: tuple[ContractEvidence, ...] = ()

    @property
    def diverged(self) -> bool:
        """Return whether a real contract contradiction was found."""
        return self.status == "diverged"


class MockContractDivergenceError(RuntimeError):
    """Raised when passing tests rely on a schema-divergent mock."""

    def __init__(self, report: MockContractReport):
        self.report = report
        super().__init__(format_mock_contract_report(report))


def _literal_string(node: Optional[ast.AST]) -> Optional[str]:
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    return None


def _call_name(node: ast.AST) -> str:
    parts: list[str] = []
    current = node
    while isinstance(current, ast.Attribute):
        parts.append(current.attr)
        current = current.value
    if isinstance(current, ast.Name):
        parts.append(current.id)
    return ".".join(reversed(parts))


def _keyword(call: ast.Call, name: str) -> Optional[ast.AST]:
    for item in call.keywords:
        if item.arg == name:
            return item.value
    return None


def _resource_from_collection_chain(node: ast.AST) -> Optional[str]:
    """Find ``collection(<literal>)`` inside a chained Firestore call."""
    for child in ast.walk(node):
        if not isinstance(child, ast.Call):
            continue
        if _call_name(child.func).rsplit(".", maxsplit=1)[-1] != "collection":
            continue
        resource_node = child.args[0] if child.args else _keyword(child, "collection_name")
        resource = _literal_string(resource_node)
        if resource:
            return resource
    return None


def _filter_fields(node: Optional[ast.AST]) -> list[tuple[str, int]]:
    """Extract literal field names from tuple filters or ``FieldFilter`` calls."""
    if node is None:
        return []
    found: list[tuple[str, int]] = []
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        direct = _literal_string(node.elts[0]) if node.elts else None
        if direct and len(node.elts) >= 2:
            found.append((direct, getattr(node.elts[0], "lineno", node.lineno)))
        else:
            for child in node.elts:
                found.extend(_filter_fields(child))
    elif isinstance(node, ast.Call):
        tail = _call_name(node.func).rsplit(".", maxsplit=1)[-1]
        if tail in {"FieldFilter", "where"}:
            field_node = node.args[0] if node.args else _keyword(node, "field_path")
            value = _literal_string(field_node)
            if value:
                found.append((value, getattr(field_node, "lineno", node.lineno)))
        for child in node.args:
            found.extend(_filter_fields(child))
        for item in node.keywords:
            found.extend(_filter_fields(item.value))
    return found


def extract_query_fields(  # pylint: disable=too-many-locals
    source: str,
    source_path: str = "<memory>",
) -> tuple[QueryFieldUse, ...]:
    """Return literal external-resource query fields from Python source."""
    try:
        tree = ast.parse(source, filename=source_path)
    except SyntaxError:
        return ()

    uses: list[QueryFieldUse] = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        callee = _call_name(node.func)
        tail = callee.rsplit(".", maxsplit=1)[-1]
        resource: Optional[str] = None
        fields: list[tuple[str, int]] = []

        if tail in _QUERY_CALLS:
            resource_node = node.args[0] if node.args else _keyword(node, "collection_name")
            resource = _literal_string(resource_node)
            filters_node = (
                node.args[1]
                if len(node.args) > 1
                else _keyword(node, "filters")
            )
            fields = _filter_fields(filters_node)
        elif tail == "where":
            resource = _resource_from_collection_chain(node.func)
            field_node = node.args[0] if node.args else _keyword(node, "field_path")
            value = _literal_string(field_node)
            if value:
                fields = [(value, getattr(field_node, "lineno", node.lineno))]
            else:
                fields = _filter_fields(_keyword(node, "filter"))
        elif tail == "filter":
            resource = _resource_from_collection_chain(node.func)
            filter_node = node.args[0] if node.args else _keyword(node, "filter")
            fields = _filter_fields(filter_node)

        if not resource:
            continue
        for field_name, line in fields:
            uses.append(
                QueryFieldUse(
                    resource=resource,
                    field_name=field_name,
                    source_path=source_path,
                    line=line,
                    callee=callee,
                )
            )
    return tuple(uses)


def _dict_fields(node: ast.AST) -> list[tuple[str, int]]:
    found: list[tuple[str, int]] = []
    for child in ast.walk(node):
        if not isinstance(child, ast.Dict):
            continue
        for key in child.keys:
            value = _literal_string(key)
            if value:
                found.append((value, getattr(key, "lineno", child.lineno)))
    return found


def _assignment_target(node: ast.AST) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        prefix = _assignment_target(node.value)
        return f"{prefix}.{node.attr}" if prefix else node.attr
    return ""


def extract_mock_fields(  # pylint: disable=too-many-branches,too-many-locals
    source: str,
    source_path: str = "<memory>",
) -> tuple[MockFieldUse, ...]:
    """Return literal fields that are actually supplied through mock payloads."""
    try:
        tree = ast.parse(source, filename=source_path)
    except SyntaxError:
        return ()

    functions = {
        node.name: node
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }
    relevant_functions: set[str] = {
        name for name in functions if name.lower().startswith(("fake", "mock"))
    }
    payload_nodes: list[tuple[ast.AST, str]] = []

    for node in ast.walk(tree):
        if isinstance(node, (ast.Assign, ast.AnnAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            value = node.value
            for target_node in targets:
                target = _assignment_target(target_node)
                lower = target.lower()
                if lower.endswith((".return_value", ".side_effect")) or lower.startswith(
                    ("mock", "fake")
                ):
                    payload_nodes.append((value, target))
                    if lower.endswith(".side_effect") and isinstance(value, ast.Name):
                        relevant_functions.add(value.id)
        elif isinstance(node, ast.Call):
            callee = _call_name(node.func)
            tail = callee.rsplit(".", maxsplit=1)[-1]
            if tail not in _MOCK_FACTORIES and not callee.endswith("patch.object"):
                continue
            for item in node.keywords:
                if item.arg in {"return_value", "side_effect"}:
                    payload_nodes.append((item.value, f"{tail}.{item.arg}"))
                    if item.arg == "side_effect" and isinstance(item.value, ast.Name):
                        relevant_functions.add(item.value.id)

    for name in relevant_functions:
        function = functions.get(name)
        if function is not None:
            for node in ast.walk(function):
                if isinstance(node, ast.Return) and node.value is not None:
                    payload_nodes.append((node.value, name))

    uses: list[MockFieldUse] = []
    seen: set[tuple[str, int, str]] = set()
    for payload, target in payload_nodes:
        for field_name, line in _dict_fields(payload):
            key = (field_name, line, target)
            if key in seen:
                continue
            seen.add(key)
            uses.append(
                MockFieldUse(
                    field_name=field_name,
                    source_path=source_path,
                    line=line,
                    target=target,
                )
            )
    return tuple(uses)


def _markdown_contracts(  # pylint: disable=too-many-branches,too-many-locals
    path: Path,
    text: str,
    resource: str,
) -> list[ContractEvidence]:
    """Parse indentation-defined fields under an exact ``resource/`` block."""
    lines = text.splitlines()
    evidence: list[ContractEvidence] = []
    resource_re = re.compile(rf"^(?P<indent>\s*){re.escape(resource)}/\s*$")
    field_re = re.compile(r"^(?P<indent>\s*)(?P<field>[A-Za-z_][\w-]*)\s*:")

    for index, line in enumerate(lines):
        match = resource_re.match(line)
        if not match:
            continue
        root_indent = len(match.group("indent").expandtabs(4))
        candidates: list[tuple[int, str]] = []
        for following in lines[index + 1 :]:
            stripped = following.strip()
            if stripped.startswith("```"):
                break
            leading = following[: len(following) - len(following.lstrip(" \t"))]
            indent = len(leading.expandtabs(4))
            if stripped and indent <= root_indent:
                break
            field_match = field_re.match(following)
            if field_match:
                candidates.append((indent, field_match.group("field")))
        if not candidates:
            continue
        field_indent = min(indent for indent, _ in candidates)
        field_paths: set[str] = set()
        parents: list[tuple[int, str]] = []
        for indent, name in candidates:
            while parents and indent <= parents[-1][0]:
                parents.pop()
            if indent == field_indent:
                field_path = name
            elif parents:
                field_path = f"{parents[-1][1]}.{name}"
            else:
                # A malformed indentation jump cannot establish a safe field
                # path, so do not accidentally authorize the nested bare name.
                continue
            field_paths.add(field_path)
            parents.append((indent, field_path))
        fields = frozenset(field_paths)
        if fields:
            evidence.append(
                ContractEvidence(
                    resource=resource,
                    fields=fields,
                    source_path=str(path),
                    line=index + 1,
                    kind="schema",
                )
            )
    return evidence


def _json_property_paths(properties: Mapping[str, Any]) -> frozenset[str]:
    """Return top-level and dotted nested field paths from JSON schema fields."""
    found: set[str] = set()
    for raw_name, definition in properties.items():
        name = str(raw_name)
        found.add(name)
        if not isinstance(definition, dict):
            continue
        nested = definition.get("properties") or definition.get("fields")
        if not isinstance(nested, dict):
            items = definition.get("items")
            if isinstance(items, dict):
                nested = items.get("properties") or items.get("fields")
        if isinstance(nested, dict):
            found.update(
                f"{name}.{child}" for child in _json_property_paths(nested)
            )
    return frozenset(found)


def _json_field_sets(value: Any, resource: str) -> list[frozenset[str]]:
    found: list[frozenset[str]] = []
    if isinstance(value, dict):
        properties = value.get("properties")
        fields = value.get("fields")
        identity = str(value.get("title") or value.get("name") or "")
        if identity == resource and isinstance(properties, dict):
            found.append(_json_property_paths(properties))
        if identity == resource and isinstance(fields, dict):
            found.append(_json_property_paths(fields))
        for key, child in value.items():
            if key == resource and isinstance(child, dict):
                child_properties = child.get("properties") or child.get("fields")
                if isinstance(child_properties, dict):
                    found.append(_json_property_paths(child_properties))
            found.extend(_json_field_sets(child, resource))
    elif isinstance(value, list):
        for child in value:
            found.extend(_json_field_sets(child, resource))
    return found


def _schema_files(project_root: Path) -> Iterable[Path]:
    roots = [project_root / "context", project_root / "docs", project_root / "schemas"]
    seen: set[Path] = set()
    for path in project_root.glob("*schema*"):
        if path.is_file():
            roots.append(path)
    for root in roots:
        candidates = [root] if root.is_file() else (root.rglob("*") if root.is_dir() else [])
        for path in candidates:
            if not path.is_file() or path.suffix.lower() not in _SCHEMA_SUFFIXES:
                continue
            if "schema" not in path.name.lower() and path.parent.name.lower() != "schemas":
                continue
            if any(part in _SKIP_DIRS for part in path.parts):
                continue
            resolved = path.resolve()
            if resolved in seen:
                continue
            seen.add(resolved)
            try:
                if path.stat().st_size > 2_000_000:
                    continue
            except OSError:
                continue
            yield path


def _load_schema_contracts(project_root: Path, resources: set[str]) -> list[ContractEvidence]:
    contracts: list[ContractEvidence] = []
    for path in _schema_files(project_root):
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError):
            continue
        if path.suffix.lower() in {".md", ".markdown"}:
            for resource in resources:
                if resource in text:
                    contracts.extend(_markdown_contracts(path, text, resource))
            continue
        try:
            payload = json.loads(text)
        except (json.JSONDecodeError, ValueError):
            continue
        for resource in resources:
            for fields in _json_field_sets(payload, resource):
                if fields:
                    contracts.append(
                        ContractEvidence(
                            resource=resource,
                            fields=fields,
                            source_path=str(path),
                            line=1,
                            kind="schema",
                        )
                    )
    return contracts


def _writer_fields(source: str, source_path: str) -> list[tuple[str, str, int]]:
    try:
        tree = ast.parse(source, filename=source_path)
    except SyntaxError:
        return []
    found: list[tuple[str, str, int]] = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        tail = _call_name(node.func).rsplit(".", maxsplit=1)[-1]
        if tail not in _WRITE_CALLS:
            continue
        resource_node = node.args[0] if node.args else _keyword(node, "collection_name")
        resource = _literal_string(resource_node)
        payload = node.args[2] if len(node.args) > 2 else _keyword(node, "data")
        if not resource or payload is None:
            continue
        for field_name, line in _dict_fields(payload):
            found.append((resource, field_name, line))
    return found


def _is_test_path(path: Path) -> bool:
    name = path.name.lower()
    return name.startswith("test_") or ".test." in name or ".spec." in name or any(
        part.lower() in {"test", "tests", "__test__", "__tests__"}
        for part in path.parts
    )


def _source_files(project_root: Path) -> Iterable[Path]:
    for path in project_root.rglob("*.py"):
        if any(part in _SKIP_DIRS for part in path.parts):
            continue
        if _is_test_path(path):
            continue
        try:
            if path.stat().st_size > 1_000_000:
                continue
        except OSError:
            continue
        yield path


def _repository_evidence(  # pylint: disable=too-many-locals
    project_root: Path,
    resources: set[str],
    excluded_paths: set[Path],
) -> list[ContractEvidence]:
    """Collect corroborating fields from independent production readers/writers."""
    by_resource: dict[str, set[str]] = {resource: set() for resource in resources}
    first_source: dict[str, tuple[str, int]] = {}
    for path in _source_files(project_root):
        try:
            resolved = path.resolve()
        except OSError:
            continue
        if resolved in excluded_paths:
            continue
        try:
            source = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError):
            continue
        relevant = {resource for resource in resources if resource in source}
        if not relevant:
            continue
        rel = str(path.relative_to(project_root))
        for use in extract_query_fields(source, rel):
            if use.resource in relevant:
                by_resource[use.resource].add(use.field_name)
                first_source.setdefault(use.resource, (rel, use.line))
        for resource, field_name, line in _writer_fields(source, rel):
            if resource in relevant:
                by_resource[resource].add(field_name)
                first_source.setdefault(resource, (rel, line))

    evidence: list[ContractEvidence] = []
    for resource, fields in by_resource.items():
        if not fields:
            continue
        source_path, line = first_source[resource]
        evidence.append(
            ContractEvidence(
                resource=resource,
                fields=frozenset(fields),
                source_path=source_path,
                line=line,
                kind="sibling",
            )
        )
    return evidence


def _normalize_sources(sources: Mapping[str | Path, str]) -> dict[str, str]:
    return {str(path): content for path, content in sources.items()}


def validate_mock_contracts(  # pylint: disable=too-many-locals,too-many-statements
    *,
    project_root: Path,
    production_sources: Mapping[str | Path, str],
    test_sources: Mapping[str | Path, str],
    baseline_production_sources: Optional[Mapping[str | Path, str]] = None,
    baseline_test_sources: Optional[Mapping[str | Path, str]] = None,
) -> MockContractReport:
    """Compare new query/mock shapes with repository-backed contracts.

    Baseline maps make the gate diff-aware: pre-existing query/mock pairs are
    ignored, while a newly introduced query or newly fabricated mock field is
    checked.  When baselines are unavailable all supplied pairs are treated as
    candidates, which is conservative for resumed workflows.
    """
    root = Path(project_root).resolve()
    production = _normalize_sources(production_sources)
    tests = _normalize_sources(test_sources)
    baseline_production = _normalize_sources(baseline_production_sources or {})
    baseline_tests = _normalize_sources(baseline_test_sources or {})

    queries = tuple(
        use
        for path, source in production.items()
        for use in extract_query_fields(source, path)
    )
    mock_fields = tuple(
        use
        for path, source in tests.items()
        for use in extract_mock_fields(source, path)
    )
    baseline_query_counts = Counter(
        (use.resource, use.field_name)
        for path, source in baseline_production.items()
        for use in extract_query_fields(source, path)
    )
    current_query_counts: Counter[tuple[str, str]] = Counter()
    baseline_mock_counts = Counter(
        use.field_name
        for path, source in baseline_tests.items()
        for use in extract_mock_fields(source, path)
    )
    current_mock_counts = Counter(use.field_name for use in mock_fields)
    new_mock_names = {
        name
        for name, count in current_mock_counts.items()
        if count > baseline_mock_counts[name]
    }
    test_text = "\n".join(tests.values())

    candidates: list[QueryFieldUse] = []
    for use in queries:
        pair = (use.resource, use.field_name)
        current_query_counts[pair] += 1
        new_query = current_query_counts[pair] > baseline_query_counts[pair]
        mock_introduced = (
            use.field_name in new_mock_names and use.resource in test_text
        )
        if new_query or mock_introduced:
            candidates.append(use)

    if not candidates:
        return MockContractReport(
            status="not_applicable",
            queries=queries,
            mock_fields=mock_fields,
        )

    resources = {use.resource for use in candidates}
    contracts = _load_schema_contracts(root, resources)
    excluded: set[Path] = set()
    # Exclude both prospective-output and original input paths. Iterative
    # ``pdd fix`` tests candidates in place at the original path before this
    # gate runs; allowing that file into sibling evidence would let the bad
    # candidate certify itself under a second mapping key.
    for source_path in (*production, *baseline_production):
        path = Path(source_path)
        candidate = path if path.is_absolute() else root / path
        try:
            excluded.add(candidate.resolve())
        except OSError:
            pass
    # Repository-wide source scanning is the expensive portion of this gate.
    # Skip it on the common valid-schema path and only seek sibling evidence
    # for resources whose candidate field is not already declared.
    schema_fields: dict[str, set[str]] = {resource: set() for resource in resources}
    for contract in contracts:
        if contract.kind == "schema":
            schema_fields[contract.resource].update(contract.fields)
    sibling_resources = {
        use.resource
        for use in candidates
        if use.field_name not in schema_fields.get(use.resource, set())
    }
    if sibling_resources:
        contracts.extend(_repository_evidence(root, sibling_resources, excluded))

    findings: list[MockContractFinding] = []
    warnings: list[str] = []
    checked: set[tuple[str, str, str, int]] = set()
    for use in candidates:
        identity = (use.resource, use.field_name, use.source_path, use.line)
        if identity in checked:
            continue
        checked.add(identity)
        resource_contracts = [item for item in contracts if item.resource == use.resource]
        schema_contracts = [item for item in resource_contracts if item.kind == "schema"]
        sibling_contracts = [item for item in resource_contracts if item.kind == "sibling"]
        schema_allows = any(use.field_name in item.fields for item in schema_contracts)
        sibling_allows = any(use.field_name in item.fields for item in sibling_contracts)
        if schema_allows or sibling_allows:
            continue
        if not schema_contracts:
            warnings.append(
                f"{use.source_path}:{use.line}: could not verify "
                f"{use.resource}.{use.field_name}; no authoritative schema "
                "section for that exact resource was found"
            )
            continue

        mock_paths = tuple(
            sorted(
                {
                    f"{item.source_path}:{item.line}"
                    for item in mock_fields
                    if item.field_name == use.field_name
                }
            )
        )
        contract_paths = tuple(
            sorted({f"{item.source_path}:{item.line}" for item in schema_contracts})
        )
        mock_clause = (
            " The passing test fabricates the same field in a mock payload at "
            + ", ".join(mock_paths)
            + "."
            if mock_paths
            else ""
        )
        findings.append(
            MockContractFinding(
                resource=use.resource,
                field_name=use.field_name,
                code_path=use.source_path,
                code_line=use.line,
                mock_paths=mock_paths,
                contract_paths=contract_paths,
                message=(
                    f"Query targets field {use.resource}.{use.field_name}, but "
                    "that field is absent from the exact repository schema "
                    f"section.{mock_clause}"
                ),
            )
        )

    status = "diverged" if findings else ("inconclusive" if warnings else "clean")
    return MockContractReport(
        status=status,
        findings=tuple(findings),
        warnings=tuple(warnings),
        queries=queries,
        mock_fields=mock_fields,
        contracts=tuple(contracts),
    )


def _git_source(project_root: Path, ref: str, relative_path: str) -> Optional[str]:
    try:
        result = subprocess.run(
            ["git", "show", f"{ref}:{relative_path}"],
            cwd=project_root,
            capture_output=True,
            text=True,
            timeout=15,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    return result.stdout if result.returncode == 0 else None


def validate_changed_files(  # pylint: disable=too-many-branches,too-many-locals,too-many-statements
    *,
    project_root: Path,
    changed_files: Sequence[str],
    baseline_ref: Optional[str] = None,
) -> MockContractReport:
    """Load changed Python code/tests and validate their new mock contracts."""
    root = Path(project_root).resolve()
    production: dict[str, str] = {}
    tests: dict[str, str] = {}
    baseline_production: dict[str, str] = {}
    baseline_tests: dict[str, str] = {}
    for raw in changed_files:
        raw_path = Path(raw)
        if raw_path.is_absolute():
            try:
                relative = raw_path.resolve().relative_to(root).as_posix()
            except (OSError, ValueError):
                continue
        else:
            relative = raw_path.as_posix()
        path = root / relative
        if path.suffix.lower() != ".py" or not path.is_file():
            continue
        try:
            source = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError):
            continue
        target = tests if _is_test_path(Path(relative)) else production
        target[relative] = source
        if baseline_ref:
            prior = _git_source(root, baseline_ref, relative)
            if prior is not None:
                baseline_target = (
                    baseline_tests if _is_test_path(Path(relative)) else baseline_production
                )
                baseline_target[relative] = prior

    # A generated test can add a fabricated payload for an unchanged production
    # query.  Such a test-only edit still has to be checked: locate exact query
    # uses that match a newly added mock field and are tied to a resource named
    # by the changed test.  Treat the unchanged reader as its own baseline so
    # candidate selection is driven by the new mock, not by legacy code.
    current_mock_counts = Counter(
        use.field_name
        for source_path, source in tests.items()
        for use in extract_mock_fields(source, source_path)
    )
    baseline_mock_counts = Counter(
        use.field_name
        for source_path, source in baseline_tests.items()
        for use in extract_mock_fields(source, source_path)
    )
    new_mock_names = {
        name
        for name, count in current_mock_counts.items()
        if count > baseline_mock_counts[name]
    }
    if new_mock_names and tests:
        test_text = "\n".join(tests.values())
        supplied_paths = {
            (root / path).resolve() if not Path(path).is_absolute() else Path(path).resolve()
            for path in production
        }
        for path in _source_files(root):
            try:
                resolved = path.resolve()
            except OSError:
                continue
            if resolved in supplied_paths:
                continue
            try:
                source = path.read_text(encoding="utf-8")
            except (OSError, UnicodeError):
                continue
            if not any(name in source for name in new_mock_names):
                continue
            relative = path.relative_to(root).as_posix()
            matching_queries = [
                use
                for use in extract_query_fields(source, relative)
                if use.field_name in new_mock_names and use.resource in test_text
            ]
            if not matching_queries:
                continue
            production[relative] = source
            baseline_production[relative] = source

    return validate_mock_contracts(
        project_root=root,
        production_sources=production,
        test_sources=tests,
        baseline_production_sources=baseline_production,
        baseline_test_sources=baseline_tests,
    )


def format_mock_contract_report(report: MockContractReport) -> str:
    """Render a bounded, evidence-linked workflow diagnostic."""
    if report.status == "not_applicable":
        return "Mock-contract validation: not applicable (no new query/mock contract pair)."
    if report.status == "clean":
        return (
            "Mock-contract validation: clean; queried fields are backed by "
            "repository contract evidence."
        )
    if report.status == "inconclusive":
        details = "\n".join(f"- {warning}" for warning in report.warnings)
        return f"Mock-contract validation: inconclusive.\n{details}"

    lines = [
        "MOCK_CONTRACT_DIVERGENCE: passing tests contradict the real interface/schema contract."
    ]
    for finding in report.findings:
        lines.append(
            f"- {finding.code_path}:{finding.code_line} "
            f"[{finding.resource}.{finding.field_name}] {finding.message}"
        )
        if finding.contract_paths:
            lines.append(f"  Contract evidence: {', '.join(finding.contract_paths)}")
        if finding.mock_paths:
            lines.append(f"  Divergent mock evidence: {', '.join(finding.mock_paths)}")
    return "\n".join(lines)


def enforce_mock_contracts(report: MockContractReport) -> None:
    """Raise a typed hard failure when a schema/mock contradiction exists."""
    if report.diverged:
        raise MockContractDivergenceError(report)


__all__ = [
    "ContractEvidence",
    "MockContractDivergenceError",
    "MockContractFinding",
    "MockContractReport",
    "MockFieldUse",
    "QueryFieldUse",
    "enforce_mock_contracts",
    "extract_mock_fields",
    "extract_query_fields",
    "format_mock_contract_report",
    "validate_changed_files",
    "validate_mock_contracts",
]
