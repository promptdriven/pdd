# pdd/get_test_command.py
"""Get language-appropriate test commands.

This module provides functions to resolve the appropriate test command
for a given test file based on:
1. CSV run_test_command (if non-empty)
2. Smart detection via default_verify_cmd_for()
3. None (triggers agentic fallback)
"""
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Optional, Tuple
import csv
import json
import os
import re
import shlex

import yaml

from .agentic_langtest import default_verify_cmd_for
from .get_language import get_language


@dataclass
class TestCommand:
    """Bundles a test command string with its required working directory.

    cwd=None means the caller decides the working directory (backward compatible).
    cwd=Path(...) means the test runner config was found there and must be used as cwd.
    """
    __test__ = False  # Prevent pytest from collecting this as a test class
    command: str
    cwd: Optional[Path] = None


_MAX_WORKSPACE_PATTERNS = 128
_MAX_WORKSPACE_PATTERN_LENGTH = 1024
_MAX_WORKSPACE_SEGMENTS = 128
_MAX_BRACE_ALTERNATIVES = 32
_MAX_WORKSPACE_MATCH_STATES = 250_000
_MAX_WORKSPACE_DISCOVERY_MATCH_STATES = 250_000
_MAX_WORKSPACE_MANIFEST_BYTES = 1_048_576
_MAX_WORKSPACE_MANIFEST_NESTING = 64
_EXTGLOB_MARKERS = ("?(", "*(", "+(", "@(", "!(")


class _WorkspaceProvider(Enum):
    """Resolver whose declaration semantics must be preserved."""

    NPM = "npm-yarn"
    LERNA = "lerna"
    PNPM = "pnpm"


@dataclass(frozen=True)
class _WorkspaceDeclaration:
    """One provider declaration; empty patterns mark an invalid declaration."""

    provider: _WorkspaceProvider
    patterns: tuple[str, ...]


@dataclass
class _WorkspaceMatchBudget:
    """Request-scoped deterministic budget for workspace matching states."""

    limit: int
    spent: int = 0
    exhausted: bool = False

    def charge(self, states: int) -> bool:
        """Reserve ``states`` before evaluation, failing closed on exhaustion."""
        if self.exhausted or states > self.limit - self.spent:
            self.exhausted = True
            return False
        self.spent += states
        return True


def _match_workspace_segment(
    value: str, pattern: str, *, wildcards_match_dot: bool = True
) -> bool:
    """Match one path segment with case-sensitive literal, ``*``, and ``?`` rules."""
    if not wildcards_match_dot and value.startswith(".") and not pattern.startswith("."):
        return False
    previous = [False] * (len(value) + 1)
    previous[0] = True
    for token in pattern:
        current = [False] * (len(value) + 1)
        if token == "*":
            current[0] = previous[0]
            for index in range(1, len(value) + 1):
                current[index] = previous[index] or current[index - 1]
        elif token == "?":
            for index in range(1, len(value) + 1):
                current[index] = previous[index - 1]
        else:
            for index in range(1, len(value) + 1):
                current[index] = previous[index - 1] and value[index - 1] == token
        previous = current
    return previous[-1]


def _expand_workspace_braces(pattern: str) -> Optional[list[str]]:
    """Expand simple, non-nested ``{a,b}`` groups within a fixed result budget."""
    expanded = [""]
    cursor = 0
    while cursor < len(pattern):
        opening = pattern.find("{", cursor)
        closing = pattern.find("}", cursor)
        if closing != -1 and (opening == -1 or closing < opening):
            return None
        if opening == -1:
            return [prefix + pattern[cursor:] for prefix in expanded]
        end = pattern.find("}", opening + 1)
        if end == -1 or "{" in pattern[opening + 1:end]:
            return None
        options = pattern[opening + 1:end].split(",")
        if len(options) < 2 or any(not option for option in options):
            return None
        literal = pattern[cursor:opening]
        if len(expanded) * len(options) > _MAX_BRACE_ALTERNATIVES:
            return None
        expanded = [
            prefix + literal + option
            for prefix in expanded
            for option in options
        ]
        cursor = end + 1
    return expanded


def _normalize_workspace_pattern_prefix(pattern: str) -> str:
    """Remove the supported leading ``./`` spelling from a workspace pattern."""
    while pattern.startswith("./"):
        pattern = pattern[2:]
    return pattern


def _prepare_workspace_pattern(pattern: str) -> Optional[list[Tuple[str, ...]]]:
    """Validate and expand one bounded workspace pattern into segment tuples."""
    if not pattern or len(pattern) > _MAX_WORKSPACE_PATTERN_LENGTH:
        return None
    has_control = any(ord(char) < 32 for char in pattern)
    if has_control or any(char in pattern for char in "[]\\!"):
        return None
    if pattern.startswith("/"):
        return None
    pattern = _normalize_workspace_pattern_prefix(pattern)
    if pattern.endswith("/"):
        pattern = pattern[:-1]
    alternatives = _expand_workspace_braces(pattern)
    if alternatives is None:
        return None
    prepared = []
    for alternative in alternatives:
        segments = tuple(alternative.split("/"))
        if (
            not segments
            or len(segments) > _MAX_WORKSPACE_SEGMENTS
            or any(segment in ("", ".", "..") for segment in segments)
            or any("**" in segment and segment != "**" for segment in segments)
        ):
            return None
        prepared.append(segments)
    return prepared


def _workspace_match_state_cost(
    rel_parts: Tuple[str, ...], segments: Tuple[str, ...]
) -> int:
    """Return a deterministic upper bound for path and segment DP states."""
    path_states = (len(rel_parts) + 1) * (len(segments) + 1)
    relative_character_states = sum(len(part) + 1 for part in rel_parts)
    pattern_character_states = sum(
        len(segment) + 1 for segment in segments if segment != "**"
    )
    return path_states + relative_character_states * pattern_character_states


def _workspace_segments_match(
    rel_parts: Tuple[str, ...],
    segments: Tuple[str, ...],
    *,
    wildcards_match_dot: bool = True,
) -> bool:
    """Match one already-prepared alternative with iterative dynamic programming."""
    previous = [False] * (len(rel_parts) + 1)
    previous[0] = True
    for segment in segments:
        current = [False] * (len(rel_parts) + 1)
        if segment == "**":
            current[0] = previous[0]
            for index in range(1, len(rel_parts) + 1):
                can_consume = wildcards_match_dot or not rel_parts[index - 1].startswith(
                    "."
                )
                current[index] = previous[index] or (
                    can_consume and current[index - 1]
                )
        else:
            for index in range(1, len(rel_parts) + 1):
                current[index] = previous[index - 1] and _match_workspace_segment(
                    rel_parts[index - 1],
                    segment,
                    wildcards_match_dot=wildcards_match_dot,
                )
        previous = current
    return previous[-1]


def _workspace_alternative_cost(
    rel_parts: Tuple[str, ...],
    segments: Tuple[str, ...],
    *,
    include_prefixes: bool,
) -> int:
    """Charge every path shape that provider-specific matching will evaluate."""
    if not include_prefixes:
        return _workspace_match_state_cost(rel_parts, segments)
    return sum(
        _workspace_match_state_cost(rel_parts[:depth], segments)
        for depth in range(1, len(rel_parts) + 1)
    )


def _relative_matches_workspace_glob(rel_parts: Tuple[str, ...], pattern: str) -> bool:
    """Match a relative path against one bounded workspace glob, fail closed."""
    if (
        not rel_parts
        or len(rel_parts) > _MAX_WORKSPACE_SEGMENTS
        or any(part in ("", ".", "..") for part in rel_parts)
    ):
        return False
    alternatives = _prepare_workspace_pattern(pattern)
    if alternatives is None:
        return False
    work_states = sum(
        _workspace_match_state_cost(rel_parts, segments)
        for segments in alternatives
    )
    if work_states > _MAX_WORKSPACE_MATCH_STATES:
        return False
    return any(
        _workspace_segments_match(rel_parts, segments)
        for segments in alternatives
    )


def _prepare_workspace_declaration(
    rel_parts: Tuple[str, ...],
    declaration: _WorkspaceDeclaration,
    budget: Optional[_WorkspaceMatchBudget] = None,
) -> Optional[list[tuple[bool, list[Tuple[str, ...]]]]]:
    """Validate, prepare, and reserve work for one provider declaration."""
    patterns = declaration.patterns
    if budget is not None and budget.exhausted:
        return None
    if (
        not patterns
        or len(patterns) > _MAX_WORKSPACE_PATTERNS
        or len(rel_parts) > _MAX_WORKSPACE_SEGMENTS
        or any(
            marker in raw_pattern
            for raw_pattern in patterns
            for marker in _EXTGLOB_MARKERS
        )
    ):
        return None
    prepared_patterns = []
    work_states = 0
    for raw_pattern in patterns:
        excluded = raw_pattern.startswith("!")
        pattern = raw_pattern[1:] if excluded else raw_pattern
        normalized_pattern = _normalize_workspace_pattern_prefix(pattern)
        if (
            declaration.provider is _WorkspaceProvider.NPM
            and not excluded
            and normalized_pattern.startswith("#")
        ):
            # npm's map-workspaces treats hash-prefixed positive entries as
            # comments. They are neither a membership proof nor a malformed
            # declaration, so a separate valid provider remains usable.
            continue
        alternatives = _prepare_workspace_pattern(pattern)
        if alternatives is None:
            return None
        for segments in alternatives:
            work_states += _workspace_alternative_cost(
                rel_parts,
                segments,
                include_prefixes=(
                    excluded and declaration.provider is not _WorkspaceProvider.PNPM
                ),
            )
            if work_states > _MAX_WORKSPACE_MATCH_STATES:
                return None
        prepared_patterns.append((excluded, alternatives))

    if budget is not None and not budget.charge(work_states):
        return None
    return prepared_patterns


def _declared_workspace_membership(
    rel_parts: Tuple[str, ...],
    declaration: _WorkspaceDeclaration,
    budget: Optional[_WorkspaceMatchBudget] = None,
) -> Optional[bool]:
    """Apply provider semantics; ``None`` means exact evaluation is unsupported."""
    prepared_patterns = _prepare_workspace_declaration(
        rel_parts, declaration, budget
    )
    if prepared_patterns is None:
        return None
    wildcards_match_dot = declaration.provider is not _WorkspaceProvider.NPM

    if declaration.provider is not _WorkspaceProvider.PNPM:
        seen_exclusion = False
        for excluded, _alternatives in prepared_patterns:
            if excluded:
                seen_exclusion = True
            elif seen_exclusion:
                # npm/Yarn/Lerna traversal and re-inclusion details differ across
                # versions. Do not reinterpret pnpm's ordered behavior here.
                return None
        positive = any(
            not excluded
            and any(
                _workspace_segments_match(
                    rel_parts,
                    segments,
                    wildcards_match_dot=wildcards_match_dot,
                )
                for segments in alternatives
            )
            for excluded, alternatives in prepared_patterns
        )
        excluded = any(
            excluded
            and any(
                _workspace_segments_match(
                    rel_parts[:depth],
                    segments,
                    wildcards_match_dot=wildcards_match_dot,
                )
                for depth in range(1, len(rel_parts) + 1)
                for segments in alternatives
            )
            for excluded, alternatives in prepared_patterns
        )
        return (
            positive
            and not excluded
            and not (
                declaration.provider is _WorkspaceProvider.NPM
                and "node_modules" in rel_parts
            )
        )

    member = False
    for excluded, alternatives in prepared_patterns:
        if any(
            _workspace_segments_match(rel_parts, segments)
            for segments in alternatives
        ):
            member = not excluded
    return member


def _string_pattern_list(value: object) -> Optional[list[str]]:
    """Validate a workspace pattern list without coercing non-string entries."""
    if not isinstance(value, list) or len(value) > _MAX_WORKSPACE_PATTERNS:
        return None
    if any(not isinstance(pattern, str) for pattern in value):
        return None
    return value


def _workspace_manifest_depth_is_bounded(contents: str) -> bool:
    """Reject parser-hostile collection nesting before object construction."""
    nesting = 0
    collection_starts = (
        yaml.tokens.BlockSequenceStartToken,
        yaml.tokens.BlockMappingStartToken,
        yaml.tokens.FlowSequenceStartToken,
        yaml.tokens.FlowMappingStartToken,
    )
    collection_ends = (
        yaml.tokens.BlockEndToken,
        yaml.tokens.FlowSequenceEndToken,
        yaml.tokens.FlowMappingEndToken,
    )
    try:
        for token in yaml.scan(contents):
            if isinstance(token, collection_starts):
                nesting += 1
                if nesting > _MAX_WORKSPACE_MANIFEST_NESTING:
                    return False
            elif isinstance(token, collection_ends):
                nesting = max(0, nesting - 1)
    except (
        RecursionError,
        yaml.YAMLError,
        ValueError,
        TypeError,
        OverflowError,
    ):
        return False
    return True


def _read_workspace_manifest(path: Path) -> Optional[str]:
    """Read one byte- and depth-bounded UTF-8 manifest, failing closed."""
    try:
        with path.open("rb") as handle:
            contents = handle.read(_MAX_WORKSPACE_MANIFEST_BYTES + 1)
    except OSError:
        return None
    if len(contents) > _MAX_WORKSPACE_MANIFEST_BYTES:
        return None
    try:
        decoded = contents.decode("utf-8")
    except UnicodeError:
        return None
    if not _workspace_manifest_depth_is_bounded(decoded):
        return None
    return decoded


def _parse_package_manifest(contents: str) -> Optional[dict]:
    """Parse a package manifest as a JSON object, failing closed."""
    try:
        manifest = json.loads(contents)
    except (RecursionError, ValueError):
        return None
    if not isinstance(manifest, dict):
        return None
    return manifest


def _package_manifest_object(
    path: Path, cache: Optional[dict[Path, Optional[dict]]] = None
) -> Optional[dict]:
    """Read and parse one package manifest, optionally caching this lookup."""
    cache_key = Path(os.path.abspath(path))
    if cache is not None and cache_key in cache:
        return cache[cache_key]
    contents = _read_workspace_manifest(path)
    manifest = None if contents is None else _parse_package_manifest(contents)
    if cache is not None:
        cache[cache_key] = manifest
    return manifest


def _package_boundary_is_valid(
    package_dir: Path, cache: Optional[dict[Path, Optional[dict]]] = None
) -> bool:
    """Require a contained regular package manifest before crossing a boundary."""
    marker = package_dir / "package.json"
    try:
        package_root = package_dir.resolve(strict=True)
        resolved_marker = marker.resolve(strict=True)
        resolved_marker.relative_to(package_root)
    except (OSError, RuntimeError, ValueError):
        return False
    if not resolved_marker.is_file():
        return False
    return _package_manifest_object(marker, cache) is not None


def _pnpm_workspace_globs(path: Path) -> Optional[list[str]]:
    """Load an authoritative pnpm package declaration, failing closed."""
    contents = _read_workspace_manifest(path)
    if contents is None:
        return None
    try:
        data = yaml.safe_load(contents)
    except (
        RecursionError,
        yaml.YAMLError,
        ValueError,
        TypeError,
        OverflowError,
    ):
        return None
    if not isinstance(data, dict):
        return None
    return _string_pattern_list(data.get("packages"))


def _manifest_workspace_globs(
    path: Path, cache: Optional[dict[Path, Optional[dict]]] = None
) -> Optional[list[str]]:
    """Load npm/Yarn workspace patterns when a package manifest declares them."""
    if not os.path.lexists(path):
        return []
    manifest = _package_manifest_object(path, cache)
    if manifest is None:
        return None
    workspaces = manifest.get("workspaces")
    if isinstance(workspaces, dict):
        workspaces = workspaces.get("packages")
    if workspaces is None:
        return []
    return _string_pattern_list(workspaces)


def _lerna_workspace_globs(path: Path) -> Optional[list[str]]:
    """Load only explicit, valid Lerna package patterns, failing closed."""
    if not os.path.lexists(path):
        return []
    contents = _read_workspace_manifest(path)
    if contents is None:
        return None
    try:
        lerna = json.loads(contents)
    except (RecursionError, ValueError):
        return None
    if not isinstance(lerna, dict):
        return None
    if "packages" not in lerna:
        return []
    return _string_pattern_list(lerna["packages"])


def _workspace_declarations_for(
    ancestor: Path,
    cache: Optional[dict[Path, Optional[tuple[_WorkspaceDeclaration, ...]]]] = None,
    package_manifest_cache: Optional[dict[Path, Optional[dict]]] = None,
) -> Optional[tuple[_WorkspaceDeclaration, ...]]:
    """Return provider declarations, preserving provider-local invalidity.

    An existing ``pnpm-workspace.yaml`` is authoritative over package and Lerna
    manifests at the same root, so invalid pnpm data returns ``None``. Invalid
    npm/Yarn or Lerna data is retained as an empty-pattern declaration, allowing
    a separate valid provider to prove membership independently.
    """
    canonical_ancestor = ancestor.resolve()
    if cache is not None and canonical_ancestor in cache:
        return cache[canonical_ancestor]
    pnpm_path = canonical_ancestor / "pnpm-workspace.yaml"
    if os.path.lexists(pnpm_path):
        patterns = _pnpm_workspace_globs(pnpm_path)
        if patterns is None:
            if cache is not None:
                cache[canonical_ancestor] = None
            return None
        result = (_WorkspaceDeclaration(_WorkspaceProvider.PNPM, tuple(patterns)),)
        if cache is not None:
            cache[canonical_ancestor] = result
        return result
    declarations = []
    manifest_globs = _manifest_workspace_globs(
        canonical_ancestor / "package.json", package_manifest_cache
    )
    if manifest_globs is None:
        declarations.append(_WorkspaceDeclaration(_WorkspaceProvider.NPM, ()))
    elif manifest_globs:
        declarations.append(
            _WorkspaceDeclaration(_WorkspaceProvider.NPM, tuple(manifest_globs))
        )
    lerna_globs = _lerna_workspace_globs(canonical_ancestor / "lerna.json")
    if lerna_globs is None:
        declarations.append(_WorkspaceDeclaration(_WorkspaceProvider.LERNA, ()))
    elif lerna_globs:
        declarations.append(
            _WorkspaceDeclaration(_WorkspaceProvider.LERNA, tuple(lerna_globs))
        )
    result = tuple(declarations)
    if cache is not None:
        cache[canonical_ancestor] = result
    return result


def _ancestor_workspace_root(
    package_dir: Path,
    declaration_cache: Optional[
        dict[Path, Optional[tuple[_WorkspaceDeclaration, ...]]]
    ] = None,
    package_manifest_cache: Optional[dict[Path, Optional[dict]]] = None,
    match_budget: Optional[_WorkspaceMatchBudget] = None,
) -> Optional[Path]:
    """Return the nearest ancestor workspace that proves package membership."""
    canonical_package = package_dir.resolve()
    ancestor = canonical_package.parent
    for _ in range(80):
        declarations = _workspace_declarations_for(
            ancestor, declaration_cache, package_manifest_cache
        )
        if declarations is None:
            return None
        if declarations:
            try:
                rel_parts = tuple(canonical_package.relative_to(ancestor.resolve()).parts)
            except ValueError:
                rel_parts = ()
            memberships = [
                _declared_workspace_membership(
                    rel_parts, declaration, match_budget
                )
                for declaration in declarations
            ]
            if any(memberships):
                return ancestor.resolve()
            if any(membership is None for membership in memberships):
                return None
        if os.path.lexists(ancestor / "pnpm-workspace.yaml"):
            return None
        if os.path.lexists(ancestor / ".git"):
            break
        parent = ancestor.parent
        if parent == ancestor:
            break
        ancestor = parent
    return None


def _belongs_to_ancestor_workspace(
    package_dir: Path,
    declaration_cache: Optional[
        dict[Path, Optional[tuple[_WorkspaceDeclaration, ...]]]
    ] = None,
    package_manifest_cache: Optional[dict[Path, Optional[dict]]] = None,
    match_budget: Optional[_WorkspaceMatchBudget] = None,
) -> bool:
    """Return True if ``package_dir`` is a proven ancestor-workspace member.

    Membership is proven, not assumed: an ancestor's declared workspace globs
    (npm/yarn ``workspaces``, ``lerna.json`` ``packages``, ``pnpm-workspace.yaml``
    ``packages``) must actually match ``package_dir`` relative to that ancestor.
    An unrelated package (e.g. a vendored ``vendor/tool``) beneath a workspace
    root is therefore not treated as a member. The search never looks above the
    repository root (``.git``).
    """
    if not _package_boundary_is_valid(package_dir, package_manifest_cache):
        return False
    return (
        _ancestor_workspace_root(
            package_dir,
            declaration_cache,
            package_manifest_cache,
            match_budget,
        )
        is not None
    )


def _nearest_package_root_for(
    test_path: Path, repository_root: Optional[Path] = None
) -> Optional[Path]:
    """Return the nearest package root without crossing ``repository_root``."""
    current = test_path.resolve().parent
    repository_ceiling = (
        repository_root.resolve() if repository_root is not None else None
    )
    for _ in range(80):
        if os.path.lexists(current / "package.json"):
            return current
        if repository_ceiling is not None and current == repository_ceiling:
            break
        parent = current.parent
        if parent == current:
            break
        current = parent
    return None


def _repository_root_for(test_path: Path) -> Optional[Path]:
    """Return the canonical repository root containing ``test_path``, if any."""
    current = test_path.resolve().parent
    for _ in range(80):
        if os.path.lexists(current / ".git"):
            return current.resolve()
        parent = current.parent
        if parent == current:
            break
        current = parent
    return None


def _runner_ownership_root(
    test_path: Path,
    repository_root: Optional[Path],
    declaration_cache: Optional[
        dict[Path, Optional[tuple[_WorkspaceDeclaration, ...]]]
    ] = None,
    package_manifest_cache: Optional[dict[Path, Optional[dict]]] = None,
    match_budget: Optional[_WorkspaceMatchBudget] = None,
) -> Optional[Path]:
    """Return the canonical ceiling that may own a discovered runner config."""
    package_root = _nearest_package_root_for(test_path, repository_root)
    if package_root is None:
        return repository_root
    ownership_root = package_root.resolve()
    for _ in range(80):
        if not _package_boundary_is_valid(
            ownership_root, package_manifest_cache
        ):
            break
        workspace_root = _ancestor_workspace_root(
            ownership_root,
            declaration_cache,
            package_manifest_cache,
            match_budget,
        )
        if workspace_root is None or workspace_root == ownership_root:
            break
        if repository_root is not None:
            try:
                workspace_root.relative_to(repository_root)
            except ValueError:
                break
        ownership_root = workspace_root
    return ownership_root


def _runner_config_is_contained(config_path: Path, ownership_root: Optional[Path]) -> bool:
    """Accept only regular config targets contained by a proven owner.

    Without a Git, package, or workspace anchor, ordinary config files remain
    usable but symlinks are rejected because their ownership cannot be proven.
    """
    is_symlink = config_path.is_symlink()
    try:
        resolved_config = config_path.resolve(strict=True)
    except (OSError, RuntimeError):
        return False
    if not resolved_config.is_file():
        return False
    if ownership_root is None:
        return not is_symlink
    try:
        resolved_config.relative_to(ownership_root)
    except ValueError:
        return False
    return True


def _detect_ts_test_runner(test_path: Path) -> Optional[Tuple[str, Path]]:
    """Detect Playwright, Jest, or Vitest config by walking up from the test file.

    For .spec.ts/.spec.tsx files, checks for playwright.config first.
    Returns (command, config_directory) tuple if a config is found, otherwise None.
    The config_directory is where the test runner config lives — callers must use it as cwd.

    The nearest ancestor config wins. The upward walk stops at the JS project
    boundary — the nearest ``package.json`` — rather than after a fixed number of
    parents, so a colocated test many directories below its runner config (e.g. a
    page test under ``frontend/src/app/hackathon/[eventId]/team/__tests__/`` and
    the config at ``frontend/jest.config.js``) still finds it. Two refinements
    keep that boundary correct in monorepos:

    * A *workspace leaf* package has its own ``package.json`` yet inherits its
      runner config from the nearest declaring workspace root, so when the leaf
      belongs to an ancestor workspace (``workspaces`` field /
      ``pnpm-workspace.yaml`` / ``lerna.json``) the walk continues *through* the
      leaf to that root, but never above it unless the root is itself a valid
      package proven to belong to another declared workspace.
    * An *independent* package must not adopt an unrelated ancestor's config, so
      the walk stops at its ``package.json`` and never crosses the repository root
      (``.git``). A hard iteration cap guards against pathological paths.

    Jest is invoked with ``--runTestsByPath`` so the resolved absolute path is
    matched literally (see ``get_test_command_for_file`` for how the path is
    escaped/quoted per runner). Jest otherwise treats the trailing path as a
    regex, and Next.js dynamic-route segments such as ``[eventId]``/``[slug]`` are
    regex character classes that never match the literal bracketed path — leaving
    the generated suite unexecutable.
    """
    is_spec = test_path.name.endswith(('.spec.ts', '.spec.tsx'))
    search_dir = test_path.resolve().parent
    repository_root = _repository_root_for(test_path)
    declaration_cache: dict[
        Path, Optional[tuple[_WorkspaceDeclaration, ...]]
    ] = {}
    package_manifest_cache: dict[Path, Optional[dict]] = {}
    match_budget = _WorkspaceMatchBudget(_MAX_WORKSPACE_DISCOVERY_MATCH_STATES)
    ownership_root = _runner_ownership_root(
        test_path,
        repository_root,
        declaration_cache,
        package_manifest_cache,
        match_budget,
    )
    for _ in range(80):
        # For .spec.ts/.spec.tsx files, check Playwright first
        if is_spec and any(
            _runner_config_is_contained(search_dir / cfg, ownership_root)
            for cfg in (
                'playwright.config.ts',
                'playwright.config.js',
                'playwright.config.mjs',
            )
        ):
            return ("npx playwright test", search_dir)
        if any(
            _runner_config_is_contained(search_dir / cfg, ownership_root)
            for cfg in ('jest.config.js', 'jest.config.ts', 'jest.config.mjs')
        ):
            return ("npx jest --no-coverage --runTestsByPath", search_dir)
        if any(
            _runner_config_is_contained(search_dir / cfg, ownership_root)
            for cfg in ('vitest.config.ts', 'vitest.config.js', 'vitest.config.mjs')
        ):
            return ("npx vitest run", search_dir)
        # Stop at the JS project boundary (nearest package.json), but cross it when
        # this package is a member of an ancestor workspace whose config lives at
        # the workspace root.
        is_project = os.path.lexists(search_dir / "package.json")
        if is_project and not _belongs_to_ancestor_workspace(
            search_dir,
            declaration_cache,
            package_manifest_cache,
            match_budget,
        ):
            break
        # A declaration proves that its root may own this package; it does not
        # prove that an unrelated ancestor above that root may own it. Nested
        # workspace chaining is already reflected in ``ownership_root`` only
        # when every intervening declaring root is a valid package and a proven
        # member of the next workspace.
        if ownership_root is not None and search_dir == ownership_root:
            break
        # Never escape the repository, even absent an in-project config.
        if repository_root is not None and search_dir == repository_root:
            break
        parent = search_dir.parent
        if parent == search_dir:
            break
        search_dir = parent
    return None


def _load_language_format() -> dict:
    """Load language_format.csv into a dict keyed by extension."""
    # Try multiple paths: package-relative first, then project-root-relative
    candidates = [
        Path(__file__).parent / "data" / "language_format.csv",
        Path(__file__).parent.parent / "data" / "language_format.csv",
    ]
    for csv_path in candidates:
        if csv_path.exists():
            result = {}
            with open(csv_path, 'r', encoding='utf-8') as f:
                reader = csv.DictReader(f)
                for row in reader:
                    ext = row.get('extension', '')
                    if ext:
                        result[ext] = row
            return result
    # CSV not found - return empty dict so smart detection (step 2) can handle it
    return {}


def get_test_command_for_file(
    test_file: str, language: Optional[str] = None
) -> Optional[TestCommand]:
    """
    Get the appropriate test command for a test file.

    Resolution order:
    1. For TS/TSX: smart runner detection via _detect_ts_test_runner() which returns
       both the command and the config directory (cwd). Critical for monorepos where
       test runner configs live in subdirectories (e.g., frontend/jest.config.js).
    2. CSV run_test_command (if non-empty).
    3. Smart detection via default_verify_cmd_for().
    4. None (triggers agentic fallback)

    Args:
        test_file: Path to the test file
        language: Optional language override

    Returns:
        TestCommand with command string and optional cwd, or None
    """
    test_path = Path(test_file)
    ext = test_path.suffix

    resolved_language = language
    if resolved_language is None:
        resolved_language = get_language(ext)

    # 1. For TypeScript/TSX: detect Jest or Vitest config and use appropriate runner
    is_typescript = (
        ext in ('.ts', '.tsx')
        and resolved_language
        and resolved_language.lower() in ('typescript', 'typescriptreact')
    )
    if is_typescript:
        runner_result = _detect_ts_test_runner(test_path)
        if runner_result:
            runner_cmd, config_dir = runner_result
            resolved = str(test_path.resolve())
            # Playwright treats its positional argument as a regular expression, so
            # a literal path (e.g. a Next.js dynamic route like ``[slug]``) must be
            # regex-escaped to match. Jest ``--runTestsByPath`` and Vitest take the
            # path literally. In every case the argument is shell-quoted because
            # callers run the command string with ``shell=True`` — an unquoted path
            # with spaces or shell metacharacters would otherwise be re-split or
            # (for bracket globs / ``$()``) reinterpreted by the shell.
            #
            # ``command`` is a POSIX-shell command string, matching how every pdd
            # caller executes verify commands (``subprocess.run(..., shell=True)``
            # or ``shlex.split``). ``shlex.quote`` is therefore the correct quoting
            # here. Making runner execution safe under Windows ``cmd.exe`` would
            # require moving all callers to an argv list + ``shell=False`` — a
            # pre-existing, cross-cutting change to pdd's command-as-string
            # convention that is out of scope for runner detection.
            if runner_cmd.startswith("npx playwright"):
                target = shlex.quote(re.escape(resolved))
            else:
                target = shlex.quote(resolved)
            return TestCommand(command=f"{runner_cmd} {target}", cwd=config_dir)

    # 2. Check CSV for run_test_command
    lang_formats = _load_language_format()
    if ext in lang_formats:
        csv_cmd = lang_formats[ext].get('run_test_command', '').strip()
        if csv_cmd:
            return TestCommand(
                command=csv_cmd.replace('{file}', shlex.quote(str(test_file)))
            )

    # 3. Smart detection
    if resolved_language:
        smart_cmd = default_verify_cmd_for(resolved_language.lower(), str(test_file))
        if smart_cmd:
            return TestCommand(command=smart_cmd)

    # 4. No command available
    return None
