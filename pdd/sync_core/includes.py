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
    """Find one bare boolean attribute outside quoted attribute values."""
    cursor = 0
    quote: str | None = None
    while True:
        if cursor >= len(raw):
            return False
        character = raw[cursor]
        if quote is not None:
            if character == quote:
                quote = None
            cursor += 1
            continue
        if character in "\"'":
            quote = character
            cursor += 1
            continue
        start = raw.find(name, cursor)
        if start < 0:
            return False
        intervening = raw[cursor:start]
        quote_positions = [position for position in (
            intervening.find("\""), intervening.find("'")) if position >= 0]
        if quote_positions:
            cursor += min(quote_positions)
            continue
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


_LEGACY_OPEN = "```<"
_LEGACY_CLOSE = ">```"


def _contains_blank_line(segment: str) -> bool:
    """True when ``segment`` holds a line that is empty or all whitespace."""
    index = segment.find("\n")
    while index >= 0:
        probe = index + 1
        while probe < len(segment) and segment[probe] in " \t\r":
            probe += 1
        if probe < len(segment) and segment[probe] == "\n":
            return True
        index = segment.find("\n", index + 1)
    return False


def _legacy_include_spans(text: str) -> list[tuple[int, int, int, int]]:
    """Locate complete ```<path>``` tokens -- PDD's legacy include syntax.

    Yields ``(token_start, token_end, path_start, path_end)`` per token. A
    token must open and close on one line, so a stray ``` later in the
    document cannot swallow unrelated text into a single combined path.

    Shared by the literal mask (which must not mangle these tokens) and by
    :func:`_parse_backtick_includes` (which reads their paths), so the two
    can never disagree about where a legacy token begins and ends.
    """
    spans: list[tuple[int, int, int, int]] = []
    cursor = 0
    while True:
        start = text.find(_LEGACY_OPEN, cursor)
        if start < 0:
            return spans
        path_start = start + len(_LEGACY_OPEN)
        path_end = text.find(_LEGACY_CLOSE, path_start)
        if path_end < 0:
            return spans
        if "\n" in text[path_start:path_end]:
            # Not a token; resume just past this opener so a later, complete
            # token on a following line is still found.
            cursor = path_start
            continue
        spans.append((start, path_end + len(_LEGACY_CLOSE), path_start, path_end))
        cursor = path_end + len(_LEGACY_CLOSE)


def _markdown_literal_mask(text: str) -> str:
    """Mask fenced and inline Markdown code without changing source offsets."""
    masked = list(text)
    legacy = _legacy_include_spans(text)
    legacy_starts = {start for start, _end, _ps, _pe in legacy}

    def legacy_end_at_or_after(index: int) -> int | None:
        """End offset of the legacy token covering ``index``, if any."""
        for start, end, _ps, _pe in legacy:
            if start <= index < end:
                return end
        return None

    def hide(start: int, end: int) -> None:
        for index in range(start, end):
            if masked[index] not in "\r\n":
                masked[index] = " "

    cursor = 0
    line_start = 0
    while cursor < len(text):
        line_end = text.find("\n", cursor)
        if line_end < 0:
            line_end = len(text)
        line = text[line_start:line_end]
        indent = len(line) - len(line.lstrip(" "))
        if indent <= 3 and indent < len(line) and line[indent] in "`~":
            delimiter = line[indent]
            run_end = indent
            while run_end < len(line) and line[run_end] == delimiter:
                run_end += 1
            run_length = run_end - indent
            # ```<path>``` is PDD's legacy include syntax, not a Markdown
            # fence. Only a *complete* token is exempt: an ordinary fence may
            # legitimately carry an info string that starts with "<", such as
            # ```<html>, and masking must not skip it.
            if run_length >= 3 and (line_start + indent) not in legacy_starts:
                close_cursor = line_end + (line_end < len(text))
                while close_cursor < len(text):
                    close_end = text.find("\n", close_cursor)
                    if close_end < 0:
                        close_end = len(text)
                    close_line = text[close_cursor:close_end]
                    close_indent = len(close_line) - len(close_line.lstrip(" "))
                    close_run_end = close_indent
                    while (
                        close_run_end < len(close_line)
                        and close_line[close_run_end] == delimiter
                    ):
                        close_run_end += 1
                    if (
                        close_indent <= 3
                        and close_run_end - close_indent >= run_length
                        and close_line[close_run_end:].strip() == ""
                    ):
                        hide(line_start, close_end)
                        cursor = close_end + (close_end < len(text))
                        line_start = cursor
                        break
                    close_cursor = close_end + (close_end < len(text))
                else:
                    hide(line_start, len(text))
                    break
                continue
        cursor = line_end + (line_end < len(text))
        line_start = cursor

    cursor = 0
    while cursor < len(text):
        legacy_end = legacy_end_at_or_after(cursor)
        if legacy_end is not None:
            # A complete legacy token is an include, not a code span. Stepping
            # over it whole stops its backticks from pairing with a neighbour's
            # and collapsing two tokens into one combined path.
            cursor = legacy_end
            continue
        if masked[cursor] != "`":
            cursor += 1
            continue
        run_end = cursor
        while run_end < len(text) and masked[run_end] == "`":
            run_end += 1
        delimiter_length = run_end - cursor
        # A code span closes on a backtick run of exactly the opening length.
        # Longer and shorter runs are literal content, so keep scanning
        # instead of abandoning the span at the first run that does not match.
        scan = run_end
        close = close_end = -1
        while scan < len(text):
            probe = text.find("`", scan)
            if probe < 0:
                break
            probe_legacy_end = legacy_end_at_or_after(probe)
            if probe_legacy_end is not None:
                scan = probe_legacy_end
                continue
            probe_end = probe
            while probe_end < len(text) and text[probe_end] == "`":
                probe_end += 1
            if probe_end - probe == delimiter_length:
                close, close_end = probe, probe_end
                break
            scan = probe_end
        if close < 0:
            cursor = run_end
            continue
        # CommonMark allows a code span to cross lines but not a blank line,
        # which ends the paragraph the span lives in.
        if _contains_blank_line(text[run_end:close]):
            cursor = run_end
            continue
        # A backtick run touching a tilde on either side is a botched,
        # non-homogeneous fence (``~~` `` or `` `~~ ``), not a span opener.
        # It may still close on its own line, but it must never swallow whole
        # lines -- that is how an invalid fence hides a real include.
        touches_tilde = (cursor > 0 and text[cursor - 1] == "~") or (
            run_end < len(text) and text[run_end] == "~"
        )
        if "\n" in text[run_end:close] and touches_tilde:
            cursor = run_end
            continue
        hide(cursor, close_end)
        cursor = close_end
    return "".join(masked)


def markdown_literal_spans(text: str) -> list[tuple[int, int]]:
    """Return ``[start, end)`` offsets of Markdown fences and code spans.

    Prompt expansion shares this with canonical dependency discovery so the
    two can never disagree about which include directives are literal
    examples. Divergence would either inline a file the dependency graph
    never recorded, or silently drop a real include.
    """
    if not text:
        return []
    masked = _markdown_literal_mask(text)
    spans: list[tuple[int, int]] = []
    start: int | None = None
    for index, (original, replaced) in enumerate(zip(text, masked)):
        if original != replaced:
            if start is None:
                start = index
        elif start is not None and original in "\r\n":
            # Line breaks are left verbatim by the mask; keep them inside the
            # span so a multi-line literal stays one contiguous range.
            continue
        elif start is not None:
            spans.append((start, index))
            start = None
    if start is not None:
        spans.append((start, len(text)))
    return spans


def _parse_xml_includes(text: str, source: str | None = None) -> list[IncludeReference]:
    """Scan ``<include>`` markup without regex backtracking over user text."""
    source = text if source is None else source
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
        raw_attrs = source[name_end:opening_end]
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
            body = source[opening_end + 1:close_start]
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


def _parse_include_many(text: str, source: str | None = None) -> list[IncludeReference]:
    """Scan ``<include-many>`` markup with a single forward cursor."""
    source = text if source is None else source
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
        raw_attrs = source[name_end:opening_end]
        close_start = text.find(close_tag, opening_end + 1)
        if close_start < 0:
            cursor = opening_end + 1
            continue
        attrs = _parse_attrs(raw_attrs)
        inner = source[opening_end + 1:close_start]
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


def _parse_backtick_includes(text: str, source: str | None = None) -> list[IncludeReference]:
    """Scan backtick include fences without regex matching on prompt text."""
    source = text if source is None else source
    references: list[IncludeReference] = []
    for start, _end, path_start, path_end in _legacy_include_spans(text):
        path = source[path_start:path_end].strip()
        if path:
            references.append(IncludeReference(start, path, IncludeSyntax.BACKTICK))
    return references


def parse_include_references(text: str) -> tuple[IncludeReference, ...]:
    """Parse includes once, preserving duplicates and deterministic source order."""
    if not text:
        return ()
    scanned = _markdown_literal_mask(text)
    references = _parse_xml_includes(scanned, text)
    references.extend(_parse_include_many(scanned, text))
    references.extend(_parse_backtick_includes(scanned, text))
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
    if declared.parts and declared.parts[0] == "..":
        _normalized(source.parent / declared, raw_path)
    candidates = [source.parent / declared]
    candidates.extend(alias.parent / declared for alias in aliases)
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
