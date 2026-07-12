# pdd/get_test_command.py
"""Get language-appropriate test commands.

This module provides functions to resolve the appropriate test command
for a given test file based on:
1. CSV run_test_command (if non-empty)
2. Smart detection via default_verify_cmd_for()
3. None (triggers agentic fallback)
"""
from dataclasses import dataclass
from pathlib import Path
from typing import Optional, Tuple
import csv
import fnmatch
import json
import os
import re
import shlex
import stat

from .agentic_langtest import default_verify_cmd_for
from .get_language import get_language


# Upper bound on how many concrete patterns a single workspace glob may expand
# to via ``{a,b}`` brace alternation. Real workspace configs use a handful of
# alternatives; a manifest that expands past this bound is treated as
# pathological (untrusted brace-bomb) and membership is failed closed rather
# than materializing an exponential list. See ``_expand_braces``.
_MAX_BRACE_EXPANSION = 1024

# Upper bound on the number of ``/``-separated segments in a single workspace
# glob. Real globs have a handful; a manifest with thousands of segments (e.g.
# a wall of ``**`` components) is hostile and fails membership closed rather
# than driving the matcher into pathological cost. See
# ``_relative_matches_workspace_glob``.
_MAX_GLOB_SEGMENTS = 256

# Upper bound on the number of raw glob entries evaluated for a single package's
# membership. A declaration with more entries than this is treated as hostile
# and fails membership closed. Combined with ``_MAX_BRACE_EXPANSION`` (which is
# an *aggregate* budget shared across every glob in one membership check), this
# bounds total brace expansion regardless of how the manifest splits the work.
_MAX_RAW_GLOBS = 4096

# Upper bound on the size of a workspace-declaration file we will read/parse. A
# larger manifest is treated as hostile and contributes no globs. These caps are
# small on purpose: parsing a JSON/YAML array of N short entries materializes N
# Python objects *before* the ``_MAX_RAW_GLOBS`` count guard can run, so an
# under-cap-but-huge-cardinality manifest could otherwise peak at hundreds of MB
# and OOM a worker. Real manifests are tiny (a handful of workspace globs), so
# these bounds keep peak parse memory well under ~100 MB with generous headroom.
# ``pnpm-workspace.yaml`` gets the smaller cap because YAML parsing amplifies more
# per input byte and a real pnpm workspace file is only a few KB.
_MAX_MANIFEST_BYTES = 1 * 1024 * 1024
_MAX_PNPM_YAML_BYTES = 256 * 1024

# Upper bound on the length (chars) of a single raw glob string. Real globs are
# a few dozen characters; a much longer one is hostile. This bounds not just the
# result *count* of brace expansion but its total *bytes*: brace expansion copies
# a glob's prefix/suffix per option, so without a length cap a long-prefix glob
# with a few brace groups (still under the count budget) could multiply into
# gigabytes of strings. Capping the raw glob length keeps expansion bounded in
# both count and size.
_MAX_GLOB_LENGTH = 4096

# Upper bound on the *aggregate* dynamic-program cells the glob matcher may fill
# across one membership check. Each glob costs ``(path_depth+1) * (segments+1)``
# cells; the per-glob and per-declaration caps bound each factor, but their
# product across many globs (up to the brace budget) times a deep path could
# still be tens of millions of cells (seconds of CPU). This aggregate budget
# fails membership closed on such a crafted manifest. Real declarations use a
# handful of short globs against a shallow path — far under this bound.
_MAX_MATCH_CELLS = 2_000_000


def _read_manifest_text(path: Path, max_bytes: int = _MAX_MANIFEST_BYTES) -> Optional[str]:
    """Read ``path`` as UTF-8, or return ``None`` (so callers fail closed) if it is
    missing, not a regular file, larger than ``max_bytes``, unreadable, or not
    valid UTF-8.

    The file must resolve to a *regular* file: a manifest that is a symlink to a
    character device or FIFO (e.g. ``/dev/zero``) reports ``st_size == 0`` yet
    would stream forever, so a byte-capped read from a regular-file-only handle is
    required — ``st_size`` alone is not trusted."""
    try:
        st = path.stat()  # follows symlinks; the *target* must be a regular file
        if not stat.S_ISREG(st.st_mode):
            return None
        if st.st_size > max_bytes:
            return None
        with open(path, "rb") as handle:
            data = handle.read(max_bytes + 1)
        if len(data) > max_bytes:
            return None  # grew past the cap between stat and read
        return data.decode("utf-8")
    except (OSError, UnicodeError):
        return None


class _PatternBudgetError(Exception):
    """Raised when an untrusted workspace pattern exceeds a safety budget
    (brace expansion or segment count), so membership can fail closed."""


class _BraceBudgetError(_PatternBudgetError):
    """Raised when a brace pattern would expand past ``_MAX_BRACE_EXPANSION``."""


@dataclass
class TestCommand:
    """Bundles a test command string with its required working directory.

    cwd=None means the caller decides the working directory (backward compatible).
    cwd=Path(...) means the test runner config was found there and must be used as cwd.
    """
    __test__ = False  # Prevent pytest from collecting this as a test class
    command: str
    cwd: Optional[Path] = None


def _relative_matches_workspace_glob(rel_parts: Tuple[str, ...], pattern: str,
                                     cell_budget: Optional[list] = None) -> bool:
    """Match a package's path segments against a single workspace glob pattern.

    Supports the segment semantics workspace tools use: ``*`` matches exactly one
    path segment (with fnmatch inside the segment) and ``**`` matches zero or more
    segments. A trailing ``/*`` therefore matches direct children only, while
    ``**`` spans any depth.

    Matching is an iterative ``O(len(rel) * len(pattern))`` dynamic program (no
    recursion and no list slicing), so a hostile pattern with many ``**``
    segments cannot drive it into exponential backtracking or ``RecursionError``.
    The segment count is bounded *before* the pattern is split (a cheap
    ``count('/')`` check), and a pattern past ``_MAX_GLOB_SEGMENTS`` raises
    ``_PatternBudgetError`` so membership fails closed without materializing a
    huge segment list.

    Dot semantics follow npm/minimatch's default (``dot: false``): a wildcard
    segment (``*``/``**`` or an fnmatch pattern) does NOT match a path segment
    that begins with ``.`` unless the *pattern* segment also begins with ``.``.
    So ``packages/*`` does not match ``packages/.shadow``, but ``packages/.*``
    does.
    """
    # Cheap guard before allocating the split list (a "slash wall" attack).
    if pattern.count("/") > _MAX_GLOB_SEGMENTS:
        raise _PatternBudgetError
    pat_parts = [p for p in pattern.strip("/").split("/") if p not in ("", ".")]
    if len(pat_parts) > _MAX_GLOB_SEGMENTS:
        raise _PatternBudgetError
    rel = list(rel_parts)
    n, m = len(rel), len(pat_parts)
    # Charge this match's DP-table size against a shared aggregate budget so that
    # many long globs against a deep path cannot sum to tens of millions of cells.
    if cell_budget is not None:
        cell_budget[0] -= (n + 1) * (m + 1)
        if cell_budget[0] < 0:
            raise _PatternBudgetError
    # dp[i][j] is True when rel[i:] matches pat_parts[j:].
    dp = [[False] * (m + 1) for _ in range(n + 1)]
    dp[n][m] = True
    # rel exhausted: only trailing ``**`` segments can still match (each empty).
    for j in range(m - 1, -1, -1):
        dp[n][j] = pat_parts[j] == "**" and dp[n][j + 1]
    for i in range(n - 1, -1, -1):
        seg_is_dot = rel[i].startswith(".")
        for j in range(m - 1, -1, -1):
            head = pat_parts[j]
            if head == "**":
                # ``**`` matches zero segments (advance pattern) or one-or-more
                # (consume rel[i], stay on the same ``**``). Under dot:false a
                # leading-dot segment is not consumed by ``**``.
                dp[i][j] = dp[i][j + 1] or (not seg_is_dot and dp[i + 1][j])
            else:
                dp[i][j] = _segment_matches(rel[i], head) and dp[i + 1][j + 1]
    return dp[0][0]


def _segment_matches(name: str, pattern_segment: str) -> bool:
    """fnmatch a single path segment with minimatch ``dot:false`` semantics: a
    wildcard pattern segment does not match a ``name`` that begins with ``.``
    unless the pattern segment itself begins with ``.``."""
    if name.startswith(".") and not pattern_segment.startswith("."):
        return False
    return fnmatch.fnmatch(name, pattern_segment)


def _workspace_globs_for(ancestor: Path, cache: Optional[dict] = None) -> list:
    """Return the workspace package globs declared by ``ancestor`` (empty if none).

    Reads npm/yarn ``workspaces`` (list or ``{"packages": [...]}``), ``lerna.json``
    ``packages``, and ``pnpm-workspace.yaml`` ``packages``.

    ``pnpm-workspace.yaml``, when present, is *authoritative*: pnpm ignores the
    ``workspaces`` field in ``package.json``, so a stale or attacker-controlled
    ``workspaces`` list must not union in and broaden membership beyond what pnpm
    itself would honor. pnpm requires a YAML parser; if it is unavailable or the
    file cannot be parsed we conservatively return no globs so membership stays
    unproven rather than falsely asserted.

    Every source is validated to be the expected JSON/YAML shape (a mapping);
    a manifest whose top level is a non-object (e.g. ``[]``) contributes no
    globs instead of raising. Each declared package glob must be a genuine
    ``str`` — a list containing a non-string entry (e.g. ``[true]``, which would
    otherwise coerce to the glob ``"True"``) is treated as malformed and
    contributes no globs (fail closed).

    Results are memoized in ``cache`` (keyed by the canonical ancestor path) for
    the duration of one discovery walk so an ancestor manifest is parsed at most
    once even when the walk revisits it via ``_workspace_root_for``.
    """
    if cache is not None:
        try:
            key = os.path.realpath(str(ancestor))
        except (OSError, RuntimeError):
            key = str(ancestor)
        if key in cache:
            return cache[key]
        result = _workspace_globs_uncached(ancestor)
        cache[key] = result
        return result
    return _workspace_globs_uncached(ancestor)


def _workspace_globs_uncached(ancestor: Path) -> list:
    """See :func:`_workspace_globs_for`; this performs the actual filesystem read."""
    # ``pnpm-workspace.yaml`` is authoritative when *present at all* — even as a
    # dangling or unreadable symlink. ``Path.exists()`` returns False for a
    # dangling symlink, so use lexical presence; a present-but-unreadable pnpm
    # config yields no globs (fail closed) and must NOT fall through to a stale
    # ``package.json`` ``workspaces`` field.
    pnpm_path = ancestor / "pnpm-workspace.yaml"
    if pnpm_path.exists() or pnpm_path.is_symlink():
        try:
            import yaml  # optional dependency
        except ImportError:
            return []  # cannot parse pnpm config → membership unproven (fail closed)
        text = _read_manifest_text(pnpm_path, _MAX_PNPM_YAML_BYTES)  # None if missing/dangling/oversized/bad-utf8
        if text is None:
            return []
        try:
            data = yaml.safe_load(text)
        except (yaml.YAMLError, ValueError, TypeError, RecursionError, OverflowError):
            # Any construction failure on untrusted YAML → membership unproven
            # (fail closed). ``yaml.YAMLError`` does NOT cover errors raised by
            # scalar constructors: e.g. a malformed timestamp such as
            # ``2020-99-99`` makes PyYAML raise a bare ``ValueError``
            # ("month must be in 1..12"), and huge integers can raise
            # ``OverflowError`` — none of which are ``yaml.YAMLError`` subclasses.
            return []
        if isinstance(data, dict):
            return _string_globs(data.get("packages"))
        return []

    globs: list = []
    manifest_path = ancestor / "package.json"
    if manifest_path.exists():
        text = _read_manifest_text(manifest_path)
        try:
            manifest = json.loads(text) if text is not None else {}
        except (ValueError, RecursionError):
            # Malformed or deeply-nested (recursion-bomb) JSON → membership
            # unproven (fail closed) rather than crashing discovery.
            manifest = {}
        if isinstance(manifest, dict):
            ws = manifest.get("workspaces")
            if isinstance(ws, dict):
                ws = ws.get("packages")
            globs.extend(_string_globs(ws))
    lerna_path = ancestor / "lerna.json"
    if lerna_path.exists():
        text = _read_manifest_text(lerna_path)
        try:
            lerna = json.loads(text) if text is not None else None
        except (ValueError, RecursionError):
            lerna = None  # parse failed → contribute nothing (fail closed)
        if isinstance(lerna, dict):
            pkgs = lerna.get("packages")
            if pkgs is None:
                # Successfully parsed lerna.json with no ``packages`` key → the
                # documented lerna default. (A *parse failure* above sets
                # ``lerna=None`` and skips this, so a malformed/bomb lerna.json
                # does NOT silently grant the default glob.)
                globs.append("packages/*")
            else:
                globs.extend(_string_globs(pkgs))
    return globs


def _string_globs(value) -> list:
    """Return ``value`` as a list of string globs, or ``[]`` if it is not a list
    of strings. A single non-string entry makes the whole declaration malformed
    (fail closed) so a JSON/YAML ``true``/number cannot be coerced into a glob.

    A declaration with more than ``_MAX_RAW_GLOBS`` entries is rejected up front
    (before validating/copying the list) so a huge but under-byte-cap manifest
    fails membership closed without a second full-list traversal/copy."""
    if not isinstance(value, list):
        return []
    if len(value) > _MAX_RAW_GLOBS:
        return []
    if not all(isinstance(item, str) for item in value):
        return []
    return list(value)


def _split_top_level_commas(body: str, limit: int) -> list:
    """Split a brace body on commas that are not inside a nested brace group.

    Raises ``_BraceBudgetError`` once more than ``limit`` top-level options would
    be produced, so a brace body with millions of commas cannot materialize a
    huge list before the caller's budget is consulted.
    """
    parts, depth, current = [], 0, []
    for char in body:
        if char == "{":
            depth += 1
            current.append(char)
        elif char == "}":
            depth -= 1
            current.append(char)
        elif char == "," and depth == 0:
            parts.append("".join(current))
            current = []
            if len(parts) > limit:
                raise _BraceBudgetError
        else:
            current.append(char)
    parts.append("".join(current))
    if len(parts) > limit:
        raise _BraceBudgetError
    return parts


def _expand_braces(pattern: str, budget: Optional[list] = None) -> list:
    """Expand ``{a,b}`` brace alternations (as npm/Yarn workspace globs use) into
    concrete patterns. Unbalanced or single-option braces are left literal.

    Expansion is *iterative* (a worklist, not recursion) and bounded by a shared
    ``budget`` — a single-element mutable list holding the number of finished
    patterns still permitted. The caller passes one budget across every glob in a
    membership check, so total expansion is bounded regardless of how a manifest
    splits work across many globs; the transient worklist is bounded too. Any
    bound exceeded raises ``_BraceBudgetError`` so the caller fails membership
    closed instead of materializing an exponential list — or overflowing the
    recursion stack — from an untrusted manifest (a ``{a,b}`` brace bomb,
    including one with thousands of nested groups or millions of comma options).
    """
    if budget is None:
        budget = [_MAX_BRACE_EXPANSION]

    def _emit(value: str) -> None:
        budget[0] -= 1
        if budget[0] < 0:
            raise _BraceBudgetError
        out.append(value)

    out: list = []
    worklist = [pattern]
    while worklist:
        if len(worklist) > budget[0] + 1:
            raise _BraceBudgetError
        pat = worklist.pop()
        start = pat.find("{")
        if start == -1:
            _emit(pat)
            continue
        depth, end = 0, -1
        for i in range(start, len(pat)):
            if pat[i] == "{":
                depth += 1
            elif pat[i] == "}":
                depth -= 1
                if depth == 0:
                    end = i
                    break
        if end == -1:
            _emit(pat)  # unbalanced → treat literally
            continue
        options = _split_top_level_commas(pat[start + 1:end], budget[0] + 1)
        if len(options) < 2:
            _emit(pat)  # not a real alternation → literal
            continue
        prefix, suffix = pat[:start], pat[end + 1:]
        for option in options:
            worklist.append(prefix + option + suffix)
    return out


def _package_matches_workspace(rel_parts: Tuple[str, ...], globs: list,
                               cell_budget: Optional[list] = None) -> bool:
    """Return True when ``rel_parts`` matches the workspace globs' include/exclude
    semantics: at least one positive pattern matches and no ``!`` exclusion does.

    Exclusions (a leading ``!``, e.g. pnpm's ``!**/test/**``) are honored, and
    brace alternations are expanded before matching. All expansion for one
    membership check shares a single aggregate budget, so a declaration with many
    globs cannot multiply past the budget.
    """
    if len(globs) > _MAX_RAW_GLOBS:
        return False  # hostile declaration size → membership unproven (fail closed)
    try:
        budget = [_MAX_BRACE_EXPANSION]  # shared across every glob below
        # Aggregate DP-cell budget for matching. When the caller supplies one it is
        # shared across the *entire* discovery walk (so re-evaluating the same glob
        # set at each package boundary cannot sum to tens of millions of cells);
        # otherwise a fresh per-call budget is used (direct/standalone callers).
        cells = cell_budget if cell_budget is not None else [_MAX_MATCH_CELLS]
        positives, negatives = [], []
        for raw in globs:
            # Do NOT strip surrounding whitespace: workspace tools treat it
            # literally, so `" packages/* "` is a package literally named with
            # spaces (a non-match), not a broader `packages/*`. Normalizing it
            # would falsely prove membership. Skip only an exactly-empty entry.
            raw = str(raw)
            if not raw:
                continue
            if len(raw) > _MAX_GLOB_LENGTH:
                # An over-long glob would blow up expansion by bytes even under
                # the count budget → membership unproven (fail closed).
                raise _PatternBudgetError
            if raw.startswith("!"):
                negatives.extend(_expand_braces(raw[1:], budget))
            else:
                positives.extend(_expand_braces(raw, budget))
        if not any(_relative_matches_workspace_glob(rel_parts, p, cells) for p in positives):
            return False
        return not any(_relative_matches_workspace_glob(rel_parts, n, cells) for n in negatives)
    except (_PatternBudgetError, RecursionError):
        # Pathological pattern from an untrusted manifest (brace bomb, ``**``
        # wall, or deep nesting) → cannot be evaluated safely, so membership is
        # unproven (fail closed).
        return False


def _workspace_root_for(package_dir: Path, cache: Optional[dict] = None,
                        cell_budget: Optional[list] = None) -> Optional[Path]:
    """Return the ancestor workspace *root* that ``package_dir`` is a proven member
    of, or ``None`` when it is not a member of any ancestor workspace.

    Membership is proven, not assumed: an ancestor's declared workspace globs
    (npm/yarn ``workspaces``, ``lerna.json`` ``packages``, ``pnpm-workspace.yaml``
    ``packages``) must actually match ``package_dir`` relative to that ancestor,
    honoring ``!`` exclusions and brace expansion. An unrelated package (e.g. a
    vendored ``vendor/tool``) or an explicitly excluded one (e.g. under a pnpm
    ``!**/test/**``) beneath a workspace root is therefore not treated as a
    member. The search never looks above the repository root (``.git``).

    Returning the *declaring root* (not just a boolean) lets the runner walk use
    it as a traversal ceiling, so intermediate independent ``package.json``
    manifests sitting between the leaf and its workspace root do not prematurely
    stop the walk (e.g. a member ``vendor/container/packages/app`` under a root
    glob ``vendor/container/packages/*`` with an unrelated ``vendor/container``
    manifest in between).
    """
    ancestor = package_dir.parent
    for _ in range(80):
        globs = _workspace_globs_for(ancestor, cache)
        if globs:
            try:
                rel_parts = tuple(package_dir.resolve().relative_to(ancestor.resolve()).parts)
            except (ValueError, OSError, RuntimeError):
                rel_parts = ()
            if rel_parts and _package_matches_workspace(rel_parts, globs, cell_budget):
                return ancestor
        if (ancestor / ".git").exists():
            break
        parent = ancestor.parent
        if parent == ancestor:
            break
        ancestor = parent
    return None


def _belongs_to_ancestor_workspace(package_dir: Path) -> bool:
    """Return True if ``package_dir`` is a proven member of an ancestor JS
    workspace (see :func:`_workspace_root_for`)."""
    return _workspace_root_for(package_dir) is not None


def _is_within(child: Path, parent: Path) -> bool:
    """True if ``child`` is ``parent`` or a descendant of it (after resolving)."""
    try:
        child.resolve().relative_to(parent.resolve())
        return True
    except (ValueError, OSError, RuntimeError):
        return False


def _is_strict_ancestor(ancestor: Path, descendant: Path) -> bool:
    """True if ``ancestor`` is a strict (proper) ancestor of ``descendant``."""
    try:
        rel = descendant.resolve().relative_to(ancestor.resolve())
    except (ValueError, OSError, RuntimeError):
        return False
    return len(rel.parts) > 0


def _lexical_strict_ancestor(ancestor: Path, descendant: Path) -> bool:
    """True if ``ancestor`` is a strict ancestor of ``descendant`` comparing the
    paths *lexically* (no symlink resolution)."""
    try:
        rel = Path(descendant).relative_to(Path(ancestor))
    except ValueError:
        return False
    return len(rel.parts) > 0


def _lexical_repo_root(test_path: Path) -> Optional[Path]:
    """Find the repository root that lexically contains ``test_path``, or ``None``.

    The root is the nearest ``.git`` ancestor that lies at or above the *deepest
    symlinked directory* on the test file's lexical (``abspath``) path. Anchoring
    above the deepest symlink is what makes containment correct in the presence
    of symlinks:

    * A symlinked test directory escaping the repo (``repo/tests -> /outside``,
      only ``repo/.git``) anchors at ``repo``; the resolved path then escapes
      ``repo`` and is refused by :func:`_detect_ts_test_runner`.
    * A symlink whose target is itself a foreign checkout
      (``repo/link -> /outside`` where ``/outside/foreign/.git`` exists, test at
      ``repo/link/foreign/...``) still anchors at ``repo`` — the foreign
      ``.git`` sits *below* the symlink and is ignored — so the foreign config
      is refused.
    * A symlink that stays inside the repository still anchors at ``repo`` and
      the resolved path stays within it, so detection proceeds normally.

    Harmless system symlinks above the repository (e.g. macOS ``/var`` →
    ``/private/var``) are the deepest symlink only when there is no repo-internal
    symlink, in which case no ``.git`` lies above them and this returns ``None``
    (containment simply not required — the ordinary ``.git`` stop in the walk
    governs). The walk runs to the filesystem root (no artificial depth cap), so
    a deeply nested but legitimate repository is still anchored.
    """
    lex = Path(os.path.abspath(str(test_path)))
    # Deepest lexical directory on the path that is a symlink.
    deepest_link: Optional[Path] = None
    parts = lex.parts
    if parts:
        cursor = Path(parts[0])
        for part in parts[1:]:
            cursor = cursor / part
            try:
                if os.path.islink(str(cursor)):
                    deepest_link = cursor
            except OSError:
                pass
    directory = lex.parent
    for _ in range(4096):  # generous bound; real paths hit the fs root far sooner
        above_deepest_link = (
            deepest_link is None or _lexical_strict_ancestor(directory, deepest_link)
        )
        if above_deepest_link and (directory / ".git").exists():
            return directory
        parent = directory.parent
        if parent == directory:
            break
        directory = parent
    return None


_RUNNER_CONFIGS = (
    # (command prefix, (config filenames...), spec_only)
    ("npx playwright test", ("playwright.config.ts", "playwright.config.js", "playwright.config.mjs"), True),
    ("npx jest --no-coverage --runTestsByPath", ("jest.config.js", "jest.config.ts", "jest.config.mjs"), False),
    ("npx vitest run", ("vitest.config.ts", "vitest.config.js", "vitest.config.mjs"), False),
)


def _resolved_repo_root(test_path: Path) -> Optional[Path]:
    """Walk the *fully resolved* (canonical) test path up to the nearest ``.git``.

    Unlike the lexical anchor, this is reliable across harmless system symlinks
    (e.g. macOS ``/var`` → ``/private/var``) because every path is canonical, so
    it is the anchor used to bound a runner *config file* that may itself be a
    symlink escaping the repository."""
    try:
        directory = test_path.resolve().parent
    except (OSError, RuntimeError):
        return None
    for _ in range(4096):
        if (directory / ".git").exists():
            return directory
        parent = directory.parent
        if parent == directory:
            break
        directory = parent
    return None


def _config_allowed(config_path: Path, repo_root: Optional[Path]) -> bool:
    """A runner config is adoptable only if its *resolved* path is a regular file
    inside the anchored repository (``repo_root``). This refuses a config file
    that is itself a symlink escaping the repository, and a broken symlink. When
    no repository is anchored (``repo_root is None``) any existing regular file is
    allowed."""
    try:
        real = Path(os.path.realpath(str(config_path)))
        if not real.is_file():
            return False
    except OSError:
        return False
    if repo_root is None:
        return True
    return _is_within(real, repo_root)


def _find_runner_here(search_dir: Path, is_spec: bool, repo_root: Optional[Path]) -> Optional[Tuple[str, Path]]:
    """Return the runner ``(command_prefix, search_dir)`` for the highest-priority
    runner config present in ``search_dir`` and allowed by containment, else
    ``None``. Playwright is only considered for ``.spec`` files."""
    for command, names, spec_only in _RUNNER_CONFIGS:
        if spec_only and not is_spec:
            continue
        for name in names:
            cfg = search_dir / name
            if cfg.exists() and _config_allowed(cfg, repo_root):
                return (command, search_dir)
    return None


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
      runner config from the workspace root, so when the leaf belongs to an
      ancestor workspace (``workspaces`` field / ``pnpm-workspace.yaml`` /
      ``lerna.json``) the walk continues *through* the leaf to the workspace root.
    * An *independent* package must not adopt an unrelated ancestor's config, so
      the walk stops at its ``package.json`` and never crosses the repository root
      (``.git``). A hard iteration cap guards against pathological paths.

    When the leaf is a proven workspace member, the declaring workspace *root*
    becomes a traversal ceiling: intermediate independent ``package.json``
    manifests between the leaf and that root do not stop the walk, so the
    root-level runner config is still reached. A symlinked test directory that
    resolves outside the repository is refused (repository containment) so the
    walk cannot be smuggled into an out-of-repo config.

    Jest is invoked with ``--runTestsByPath`` so the resolved absolute path is
    matched literally (see ``get_test_command_for_file`` for how the path is
    escaped/quoted per runner). Jest otherwise treats the trailing path as a
    regex, and Next.js dynamic-route segments such as ``[eventId]``/``[slug]`` are
    regex character classes that never match the literal bracketed path — leaving
    the generated suite unexecutable.
    """
    # Reject a path where a ``..`` component traverses a symlink: ``os.path.abspath``
    # collapses ``..`` textually, which is unsound across symlinks and would let a
    # crafted path mis-anchor repository containment. When the naive collapse and
    # the true resolution disagree, fail closed.
    try:
        if os.path.realpath(os.path.abspath(str(test_path))) != os.path.realpath(str(test_path)):
            return None
    except OSError:
        return None

    is_spec = test_path.name.endswith(('.spec.ts', '.spec.tsx'))
    try:
        search_dir = test_path.resolve().parent
    except (OSError, RuntimeError):
        # A self-referential (looping) or otherwise unresolvable symlink path →
        # refuse smart-runner discovery rather than crash the caller.
        return None
    # Repository containment: anchor the repo root lexically (before symlinks are
    # resolved). If the resolved test path escapes that root, refuse to adopt any
    # out-of-repo runner config.
    contain = _lexical_repo_root(test_path)
    # Canonical repository of the (real) test file, used to reject a runner config
    # file that is itself a symlink escaping the repository — reliable even where
    # the lexical anchor is unset because of a harmless system symlink above it.
    repo_root = _resolved_repo_root(test_path)
    # Per-discovery cache so each ancestor manifest is parsed at most once even as
    # the walk revisits ancestors through _workspace_root_for (bounds O(n^2) reads).
    ws_cache: dict = {}
    # Per-discovery aggregate DP-cell budget shared across every membership check
    # in this walk, so repeated matching at each package boundary is bounded.
    match_cells: list = [_MAX_MATCH_CELLS]
    # Deepest ancestor-workspace root the original leaf must still reach; walk
    # *through* intermediate independent package.json manifests until then.
    ceiling: Optional[Path] = None
    for _ in range(80):
        # Never step outside the repository (e.g. via a symlink that resolves out).
        if contain is not None and not _is_within(search_dir, contain):
            break
        found = _find_runner_here(search_dir, is_spec, repo_root)
        if found is not None:
            return found
        # Lexical presence: a ``package.json`` that is a *dangling* symlink still
        # marks a JS project boundary. ``Path.exists()`` returns False for it, which
        # would let the walk slip past an independent package and adopt an unrelated
        # ancestor's config — so use ``os.path.lexists`` and fail closed (stop).
        pkg_here = os.path.lexists(str(search_dir / "package.json"))
        # Extend the workspace ceiling from a proven member manifest here — or when
        # we have reached the current ceiling, so a nested workspace root that lacks
        # its own package.json can still chain outward.
        member_root: Optional[Path] = None
        if pkg_here or (ceiling is not None and search_dir == ceiling):
            member_root = _workspace_root_for(search_dir, ws_cache, match_cells)
            if member_root is not None and (ceiling is None or _is_strict_ancestor(member_root, ceiling)):
                ceiling = member_root
        # Stop at the declaring workspace root, even when it has no package.json of
        # its own (e.g. a pnpm/lerna root). If it was itself proven a member of an
        # outer workspace, ``ceiling`` was extended above and this does not fire.
        if ceiling is not None and search_dir == ceiling:
            break
        # Independent JS project boundary that is not a workspace member and not
        # below the ceiling → stop.
        if pkg_here:
            below_ceiling = ceiling is not None and _is_strict_ancestor(ceiling, search_dir)
            if member_root is None and not below_ceiling:
                break
        # Never escape the repository, even absent an in-project config.
        if (search_dir / ".git").exists():
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
            with open(csv_path, 'r') as f:
                reader = csv.DictReader(f)
                for row in reader:
                    ext = row.get('extension', '')
                    if ext:
                        result[ext] = row
            return result
    # CSV not found - return empty dict so smart detection (step 2) can handle it
    return {}


def get_test_command_for_file(test_file: str, language: Optional[str] = None) -> Optional[TestCommand]:
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
    if ext in ('.ts', '.tsx') and resolved_language and resolved_language.lower() in ('typescript', 'typescriptreact'):
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
            # Shell-quote the substituted path: callers run this command string with
            # ``shell=True``, so an unquoted path with spaces or shell metacharacters
            # (e.g. ``/repo/$(touch PWN)/a.test.ts``) would be re-split or executed
            # via command substitution — a command-injection vector.
            return TestCommand(command=csv_cmd.replace('{file}', shlex.quote(str(test_file))))

    # 3. Smart detection
    if resolved_language:
        smart_cmd = default_verify_cmd_for(resolved_language.lower(), str(test_file))
        if smart_cmd:
            return TestCommand(command=smart_cmd)

    # 4. No command available
    return None
