"""Canonical parser for every supported prompt include syntax."""

from __future__ import annotations

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


def _is_attribute_name_char(character: str) -> bool:
    """Return whether a character belongs to a Python ``\\w`` attribute name."""
    return character == "_" or character.isalnum()


def _has_boolean_attr(raw: str, name: str) -> bool:
    """Find one bare boolean attribute with the legacy ASCII boundaries."""
    cursor = 0
    while True:
        start = raw.find(name, cursor)
        if start < 0:
            return False
        end = start + len(name)
        before_is_word = start > 0 and (
            raw[start - 1].isascii() and _is_attribute_name_char(raw[start - 1])
        )
        after_is_word = end < len(raw) and (
            raw[end].isascii() and _is_attribute_name_char(raw[end])
        )
        if not before_is_word and not after_is_word:
            return True
        cursor = end


def _parse_attrs(raw: str) -> dict[str, str]:
    """Parse quoted and boolean include attributes with forward-only scans."""
    attrs: dict[str, str] = {}
    cursor = 0
    while cursor < len(raw):
        while cursor < len(raw) and not _is_attribute_name_char(raw[cursor]):
            cursor += 1
        name_start = cursor
        while cursor < len(raw) and _is_attribute_name_char(raw[cursor]):
            cursor += 1
        if name_start == cursor:
            break
        name = raw[name_start:cursor]
        while cursor < len(raw) and raw[cursor].isspace():
            cursor += 1
        if cursor == len(raw) or raw[cursor] != "=":
            continue
        cursor += 1
        while cursor < len(raw) and raw[cursor].isspace():
            cursor += 1
        if cursor == len(raw) or raw[cursor] not in "\"'":
            continue
        quote = raw[cursor]
        value_start = cursor + 1
        value_end = raw.find(quote, value_start)
        if value_end < 0:
            break
        attrs[name] = raw[value_start:value_end]
        cursor = value_end + 1
    for boolean_name in ("optional", "expand"):
        if boolean_name not in attrs and _has_boolean_attr(raw, boolean_name):
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


def _tag_end(text: str, start: int) -> int:
    """Return the exclusive end of an opening tag, or ``-1`` when incomplete."""
    return text.find(">", start)


def _is_tag_boundary(text: str, index: int) -> bool:
    """Return whether *index* is a valid character after an include tag name."""
    return index == len(text) or text[index].isspace() or text[index] in ">/"


def _parse_xml_includes(text: str) -> list[IncludeReference]:
    """Scan ``<include>`` markup without regex backtracking over user text."""
    references: list[IncludeReference] = []
    cursor = 0
    tag_name = "<include"
    close_tag = "</include>"
    while True:
        start = text.find(tag_name, cursor)
        if start < 0:
            return references
        name_end = start + len(tag_name)
        if not _is_tag_boundary(text, name_end):
            cursor = name_end
            continue
        opening_end = _tag_end(text, name_end)
        if opening_end < 0:
            return references
        raw_attrs = text[name_end:opening_end]
        self_closing = raw_attrs.rstrip().endswith("/")
        if self_closing:
            raw_attrs = raw_attrs.rstrip()[:-1]
        attrs = _parse_attrs(raw_attrs)
        if self_closing:
            path = attrs.get("path", "").strip()
            cursor = opening_end + 1
        else:
            close_start = text.find(close_tag, opening_end + 1)
            if close_start < 0:
                cursor = opening_end + 1
                continue
            body = text[opening_end + 1:close_start]
            path = (attrs.get("path") or body).strip()
            if any(character in path for character in "<>\r\n"):
                cursor = opening_end + 1
                continue
            cursor = close_start + len(close_tag)
        if path:
            references.append(
                IncludeReference(
                    start,
                    path,
                    IncludeSyntax.XML,
                    attrs.get("select"),
                    attrs.get("query"),
                    _enabled(attrs.get("optional")),
                    _enabled(attrs.get("expand")),
                )
            )


def _parse_include_many(text: str) -> list[IncludeReference]:
    """Scan ``<include-many>`` markup with a single forward cursor."""
    references: list[IncludeReference] = []
    cursor = 0
    tag_name = "<include-many"
    close_tag = "</include-many>"
    while True:
        start = text.find(tag_name, cursor)
        if start < 0:
            return references
        name_end = start + len(tag_name)
        if not _is_tag_boundary(text, name_end):
            cursor = name_end
            continue
        opening_end = _tag_end(text, name_end)
        if opening_end < 0:
            return references
        raw_attrs = text[name_end:opening_end]
        close_start = text.find(close_tag, opening_end + 1)
        if close_start < 0:
            cursor = opening_end + 1
            continue
        attrs = _parse_attrs(raw_attrs)
        inner = text[opening_end + 1:close_start]
        for offset, path in enumerate(
            item.strip() for line in inner.splitlines() for item in line.split(",") if item.strip()
        ):
            references.append(
                IncludeReference(
                    start + offset,
                    path,
                    IncludeSyntax.XML_MANY,
                    optional=_enabled(attrs.get("optional")),
                    expand_dependencies=_enabled(attrs.get("expand")),
                )
            )
        cursor = close_start + len(close_tag)


def _parse_backtick_includes(text: str) -> list[IncludeReference]:
    """Scan backtick include fences without regex matching on prompt text."""
    references: list[IncludeReference] = []
    cursor = 0
    opening = "```<"
    closing = ">```"
    while True:
        start = text.find(opening, cursor)
        if start < 0:
            return references
        path_end = text.find(closing, start + len(opening))
        if path_end < 0:
            return references
        path = text[start + len(opening):path_end].strip()
        if path:
            references.append(IncludeReference(start, path, IncludeSyntax.BACKTICK))
        cursor = path_end + len(closing)


def parse_include_references(text: str) -> tuple[IncludeReference, ...]:
    """Parse includes once, preserving duplicates and deterministic source order."""
    if not text:
        return ()
    references = _parse_xml_includes(text)
    references.extend(_parse_include_many(text))
    references.extend(_parse_backtick_includes(text))
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
            try:
                matches = tuple(
                    sorted(
                        PurePosixPath(path.relative_to(policy.checkout_root).as_posix())
                        for path in policy.checkout_root.glob(candidate.as_posix())
                        if path.is_file()
                    )
                )
            except ValueError as exc:
                raise IncludeGraphError(
                    f"include wildcard pattern is invalid: {reference.path}"
                ) from exc
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
