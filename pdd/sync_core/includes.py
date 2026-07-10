"""Canonical parser for every supported prompt include syntax."""

from __future__ import annotations

import re
import hashlib
import json
import posixpath
from dataclasses import dataclass
from enum import Enum
from pathlib import PurePosixPath

from .path_policy import PathPolicy, PathPolicyError


class IncludeSyntax(str, Enum):
    """Source grammar that produced an include reference."""

    XML = "xml"
    XML_MANY = "xml-many"
    BACKTICK = "backtick"


@dataclass(frozen=True, order=True)
class IncludeReference:
    """One ordered include declaration and its behavior-bearing attributes."""

    position: int
    path: str
    syntax: IncludeSyntax
    select: str | None = None
    query: str | None = None
    optional: bool = False
    expand_dependencies: bool = False


class IncludeGraphError(ValueError):
    """Raised when an include closure is missing, cyclic, or policy-invalid."""


@dataclass(frozen=True, order=True)
class IncludeEdge:
    """Resolved dependency edge including behavior-bearing parser attributes."""

    source: PurePosixPath
    target: PurePosixPath
    reference: IncludeReference
    target_exists: bool


@dataclass(frozen=True, order=True)
class IncludedArtifact:
    """Content and mode snapshot for one resolved expansion input."""

    relpath: PurePosixPath
    digest: str
    git_mode: str


@dataclass(frozen=True)
class IncludeClosure:
    """Deterministic transitive expansion closure for one prompt."""

    root: PurePosixPath
    artifacts: tuple[IncludedArtifact, ...]
    edges: tuple[IncludeEdge, ...]
    has_nondeterministic_query: bool

    def digest(self) -> str:
        """Hash all resolved bytes, modes, edges, and include attributes."""
        payload = {
            "root": self.root.as_posix(),
            "artifacts": [
                {
                    "path": item.relpath.as_posix(),
                    "digest": item.digest,
                    "git_mode": item.git_mode,
                }
                for item in self.artifacts
            ],
            "edges": [
                {
                    "source": edge.source.as_posix(),
                    "target": edge.target.as_posix(),
                    "path": edge.reference.path,
                    "syntax": edge.reference.syntax.value,
                    "select": edge.reference.select,
                    "query": edge.reference.query,
                    "optional": edge.reference.optional,
                    "expand_dependencies": edge.reference.expand_dependencies,
                    "target_exists": edge.target_exists,
                }
                for edge in self.edges
            ],
            "has_nondeterministic_query": self.has_nondeterministic_query,
        }
        encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
        return hashlib.sha256(encoded).hexdigest()


_INCLUDE_PATTERN = re.compile(
    r'<include(?P<attrs>\s[^>]*?)?(?<!/)>'
    r'\s*(?P<content>[^<>\r\n]+?)\s*</include>'
    r'|<include(?P<attrs_self>\s[^>]*?)/>',
)
_INCLUDE_MANY_PATTERN = re.compile(
    r'<include-many(?P<attrs>\s[^>]*+)?>(?P<inner>.*?)</include-many>',
    re.DOTALL,
)
_BACKTICK_PATTERN = re.compile(r"```<([^>]*+)>```")
_ATTRIBUTE_PATTERN = re.compile(r'(\w+)\s*=\s*["\']([^"\']*)["\']')


def _parse_attrs(raw: str) -> dict[str, str]:
    attrs = {match.group(1): match.group(2) for match in _ATTRIBUTE_PATTERN.finditer(raw)}
    for boolean_name in ("optional", "expand"):
        pattern = rf"(?<![A-Za-z0-9_]){boolean_name}(?![A-Za-z0-9_])"
        if boolean_name not in attrs and re.search(pattern, raw):
            attrs[boolean_name] = "true"
    return attrs


def _enabled(value: str | None) -> bool:
    return value is not None and value.strip().casefold() not in {
        "",
        "0",
        "false",
        "no",
        "off",
    }


def parse_include_references(text: str) -> tuple[IncludeReference, ...]:
    """Parse includes once, preserving duplicates and deterministic source order."""
    if not text:
        return ()
    references: list[IncludeReference] = []
    for match in _INCLUDE_PATTERN.finditer(text):
        attrs = _parse_attrs(match.group("attrs") or match.group("attrs_self") or "")
        body = match.group("content") or ""
        path = (attrs.get("path") or body).strip()
        if path:
            references.append(
                IncludeReference(
                    match.start(),
                    path,
                    IncludeSyntax.XML,
                    attrs.get("select"),
                    attrs.get("query"),
                    _enabled(attrs.get("optional")),
                    _enabled(attrs.get("expand")),
                )
            )
    for match in _INCLUDE_MANY_PATTERN.finditer(text):
        attrs = _parse_attrs(match.group("attrs") or "")
        values = (
            item.strip()
            for line in match.group("inner").splitlines()
            for item in line.split(",")
        )
        for offset, path in enumerate(value for value in values if value):
            references.append(
                IncludeReference(
                    match.start() + offset,
                    path,
                    IncludeSyntax.XML_MANY,
                    optional=_enabled(attrs.get("optional")),
                    expand_dependencies=_enabled(attrs.get("expand")),
                )
            )
    for match in _BACKTICK_PATTERN.finditer(text):
        path = match.group(1).strip()
        if path:
            references.append(
                IncludeReference(match.start(), path, IncludeSyntax.BACKTICK)
            )
    return tuple(sorted(references))


def include_paths(text: str) -> set[str]:
    """Return path membership for preprocessing's user-intent guard."""
    return {reference.path for reference in parse_include_references(text)}


def _normalized(path: PurePosixPath, raw_path: str) -> PurePosixPath:
    normalized = PurePosixPath(posixpath.normpath(path.as_posix()))
    if normalized.is_absolute() or ".." in normalized.parts:
        raise IncludeGraphError(f"include path escapes repository: {raw_path}")
    return normalized


def _candidate_paths(
    source: PurePosixPath,
    raw_path: str,
    aliases: tuple[PurePosixPath, ...] = (),
) -> tuple[PurePosixPath, ...]:
    # pylint: disable=too-many-branches,too-many-locals
    declared = PurePosixPath(raw_path)
    if declared.is_absolute():
        raise IncludeGraphError(f"absolute include path is not allowed: {raw_path}")
    candidates = [source.parent / declared]
    candidates.extend(alias.parent / declared for alias in aliases)
    leading_parents = 0
    for part in declared.parts:
        if part != "..":
            break
        leading_parents += 1
    if leading_parents:
        repository_tail = PurePosixPath(*declared.parts[leading_parents:])
        if repository_tail.parts:
            candidates.append(repository_tail)
    prompt_index = (
        max(index for index, part in enumerate(source.parts) if part == "prompts")
        if "prompts" in source.parts
        else None
    )
    project_prefix = PurePosixPath(".")
    project_namespace = None
    if prompt_index is not None:
        project_prefix = PurePosixPath(*source.parts[:prompt_index])
        remainder = source.parts[prompt_index + 1 :]
        if remainder:
            project_namespace = remainder[0]
            projected = PurePosixPath(
                *source.parts[:prompt_index], *remainder
            )
            candidates.append(projected.parent / declared)
    if ".." not in declared.parts:
        candidates.append(declared)
        candidates.append(project_prefix / declared)
        candidates.append(project_prefix / "prompts" / declared)
        if project_namespace:
            candidates.append(project_prefix / project_namespace / declared)
        candidates.extend(parent / declared for parent in source.parents)
    if raw_path.startswith("@/"):
        alias = PurePosixPath(raw_path[2:])
        if project_namespace:
            candidates.append(
                project_prefix / project_namespace / "src" / alias
            )
        candidates.append(project_prefix / "src" / alias)
        for parent in source.parents:
            candidates.extend((parent / "src" / alias, parent / "frontend/src" / alias))
    normalized: list[PurePosixPath] = []
    for candidate in candidates:
        try:
            path = _normalized(candidate, raw_path)
        except IncludeGraphError:
            continue
        variants = [path]
        if not path.suffix and not any(character in path.name for character in "*?["):
            suffixes = (".py", ".ts", ".tsx", ".js", ".jsx")
            variants.extend(path.with_suffix(suffix) for suffix in suffixes)
        normalized.extend(variants)
    unique = tuple(dict.fromkeys(normalized))
    if not unique:
        raise IncludeGraphError(f"include path escapes repository: {raw_path}")
    return unique


def _resolved_targets(
    source: PurePosixPath,
    reference: IncludeReference,
    policy: PathPolicy,
    aliases: tuple[PurePosixPath, ...] = (),
) -> tuple[PurePosixPath, ...]:
    candidates = _candidate_paths(source, reference.path, aliases)
    wildcard = any(character in reference.path for character in "*?[")
    for candidate in candidates:
        if wildcard:
            matches = tuple(
                sorted(
                    PurePosixPath(path.relative_to(policy.checkout_root).as_posix())
                    for path in policy.checkout_root.glob(candidate.as_posix())
                    if path.is_file()
                )
            )
            if matches:
                return matches
            continue
        try:
            policy.resolve(candidate)
            return (candidate,)
        except (FileNotFoundError, PathPolicyError):
            continue
    return (candidates[0],)


def _external_package_reference(raw_path: str) -> bool:
    """Return whether an unresolved include names a package, not a repo path."""
    path = PurePosixPath(raw_path.split(" ", 1)[0])
    local_prefixes = {
        "@", "app", "backend", "components", "context", "docs", "frontend", "pdd", "src"
    }
    return (
        not path.suffix
        and not raw_path.endswith("/")
        and ".." not in path.parts
        and path.parts[0] not in local_prefixes
    )


def build_include_closure(
    root: PurePosixPath,
    policy: PathPolicy,
    *,
    root_aliases: tuple[PurePosixPath, ...] = (),
) -> IncludeClosure:
    """Resolve, validate, and hash the full recursive include dependency closure."""
    policy.resolve(root)
    artifacts: dict[PurePosixPath, IncludedArtifact] = {}
    edges: list[IncludeEdge] = []
    visited: set[PurePosixPath] = set()

    def visit(source: PurePosixPath, stack: tuple[PurePosixPath, ...]) -> None:
        if source in stack:
            cycle = " -> ".join(path.as_posix() for path in stack + (source,))
            raise IncludeGraphError(f"include cycle detected: {cycle}")
        if source in visited:
            return
        visited.add(source)
        resolved_source = policy.resolve(source)
        try:
            text = resolved_source.canonical_path.read_text(encoding="utf-8")
        except UnicodeDecodeError as exc:
            raise IncludeGraphError(
                f"included artifact is not UTF-8 text: {source}"
            ) from exc
        for reference in parse_include_references(text):
            targets = _resolved_targets(
                source,
                reference,
                policy,
                root_aliases if source == root else (),
            )
            for target in targets:
                try:
                    snapshot = policy.snapshot("include", target)
                except (FileNotFoundError, PathPolicyError) as exc:
                    if reference.optional and isinstance(exc, FileNotFoundError):
                        edges.append(IncludeEdge(source, target, reference, False))
                        continue
                    raise IncludeGraphError(
                        f"include cannot be resolved from {source}: {reference.path}"
                    ) from exc
                if snapshot.digest is None or snapshot.git_mode is None:
                    if reference.optional:
                        edges.append(IncludeEdge(source, target, reference, False))
                        continue
                    if _external_package_reference(reference.path):
                        edges.append(IncludeEdge(source, target, reference, False))
                        continue
                    raise IncludeGraphError(f"required include is missing: {target}")
                edges.append(IncludeEdge(source, target, reference, True))
                artifacts[target] = IncludedArtifact(
                    target, snapshot.digest, snapshot.git_mode
                )
                visit(target, stack + (source,))

    visit(root, ())
    return IncludeClosure(
        root,
        tuple(sorted(artifacts.values())),
        tuple(sorted(edges)),
        any(
            edge.reference.query
            or (not edge.target_exists and not edge.reference.optional)
            for edge in edges
        ),
    )
