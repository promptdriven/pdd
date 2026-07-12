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


def _relative_matches_workspace_glob(rel_parts: Tuple[str, ...], pattern: str) -> bool:
    """Match a package's path segments against a single workspace glob pattern.

    Supports the segment semantics workspace tools use: ``*`` matches exactly one
    path segment (with fnmatch inside the segment) and ``**`` matches zero or more
    segments. A trailing ``/*`` therefore matches direct children only, while
    ``**`` spans any depth.

    Matching is an iterative ``O(len(rel) * len(pattern))`` dynamic program (no
    recursion and no list slicing), so a hostile pattern with many ``**``
    segments cannot drive it into exponential backtracking or ``RecursionError``.
    A pattern longer than ``_MAX_GLOB_SEGMENTS`` raises ``_PatternBudgetError`` so
    membership fails closed.
    """
    pat_parts = [p for p in pattern.strip("/").split("/") if p not in ("", ".")]
    if len(pat_parts) > _MAX_GLOB_SEGMENTS:
        raise _PatternBudgetError
    rel = list(rel_parts)
    n, m = len(rel), len(pat_parts)
    # dp[i][j] is True when rel[i:] matches pat_parts[j:].
    dp = [[False] * (m + 1) for _ in range(n + 1)]
    dp[n][m] = True
    # rel exhausted: only trailing ``**`` segments can still match (each empty).
    for j in range(m - 1, -1, -1):
        dp[n][j] = pat_parts[j] == "**" and dp[n][j + 1]
    for i in range(n - 1, -1, -1):
        for j in range(m - 1, -1, -1):
            head = pat_parts[j]
            if head == "**":
                # ``**`` matches zero segments (advance pattern) or one-or-more
                # (consume rel[i], stay on the same ``**``).
                dp[i][j] = dp[i][j + 1] or dp[i + 1][j]
            else:
                dp[i][j] = fnmatch.fnmatch(rel[i], head) and dp[i + 1][j + 1]
    return dp[0][0]


def _workspace_globs_for(ancestor: Path) -> list:
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
    """
    pnpm_path = ancestor / "pnpm-workspace.yaml"
    if pnpm_path.exists():
        try:
            import yaml  # optional dependency
        except ImportError:
            return []  # cannot parse pnpm config → membership unproven (fail closed)
        try:
            data = yaml.safe_load(pnpm_path.read_text(encoding="utf-8"))
        except (yaml.YAMLError, OSError, UnicodeError):
            return []  # conservative: unparseable/invalid-encoding pnpm workspace
        if isinstance(data, dict):
            return _string_globs(data.get("packages"))
        return []

    globs: list = []
    manifest_path = ancestor / "package.json"
    if manifest_path.exists():
        try:
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        except (ValueError, OSError):
            manifest = {}
        if isinstance(manifest, dict):
            ws = manifest.get("workspaces")
            if isinstance(ws, dict):
                ws = ws.get("packages")
            globs.extend(_string_globs(ws))
    lerna_path = ancestor / "lerna.json"
    if lerna_path.exists():
        try:
            lerna = json.loads(lerna_path.read_text(encoding="utf-8"))
        except (ValueError, OSError):
            lerna = {}
        if isinstance(lerna, dict):
            pkgs = lerna.get("packages")
            if pkgs is None:
                globs.append("packages/*")  # lerna default
            else:
                globs.extend(_string_globs(pkgs))
    return globs


def _string_globs(value) -> list:
    """Return ``value`` as a list of string globs, or ``[]`` if it is not a list
    of strings. A single non-string entry makes the whole declaration malformed
    (fail closed) so a JSON/YAML ``true``/number cannot be coerced into a glob."""
    if not isinstance(value, list):
        return []
    if not all(isinstance(item, str) for item in value):
        return []
    return list(value)


def _split_top_level_commas(body: str) -> list:
    """Split a brace body on commas that are not inside a nested brace group."""
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
        else:
            current.append(char)
    parts.append("".join(current))
    return parts


def _expand_braces(pattern: str) -> list:
    """Expand ``{a,b}`` brace alternations (as npm/Yarn workspace globs use) into
    concrete patterns. Unbalanced or single-option braces are left literal.

    Expansion is *iterative* (a worklist, not recursion) and bounded on both the
    number of finished patterns and the transient worklist size. Either bound
    exceeded raises ``_BraceBudgetError`` so the caller fails membership closed
    instead of materializing an exponential list — or overflowing the recursion
    stack — from an untrusted manifest (a ``{a,b}`` brace bomb, including one with
    thousands of nested groups).
    """
    out: list = []
    worklist = [pattern]
    while worklist:
        if len(worklist) > _MAX_BRACE_EXPANSION:
            raise _BraceBudgetError
        pat = worklist.pop()
        start = pat.find("{")
        if start == -1:
            out.append(pat)
            if len(out) > _MAX_BRACE_EXPANSION:
                raise _BraceBudgetError
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
            out.append(pat)  # unbalanced → treat literally
            if len(out) > _MAX_BRACE_EXPANSION:
                raise _BraceBudgetError
            continue
        options = _split_top_level_commas(pat[start + 1:end])
        if len(options) < 2:
            out.append(pat)  # not a real alternation → literal
            if len(out) > _MAX_BRACE_EXPANSION:
                raise _BraceBudgetError
            continue
        prefix, suffix = pat[:start], pat[end + 1:]
        for option in options:
            worklist.append(prefix + option + suffix)
    return out


def _package_matches_workspace(rel_parts: Tuple[str, ...], globs: list) -> bool:
    """Return True when ``rel_parts`` matches the workspace globs' include/exclude
    semantics: at least one positive pattern matches and no ``!`` exclusion does.

    Exclusions (a leading ``!``, e.g. pnpm's ``!**/test/**``) are honored, and
    brace alternations are expanded before matching.
    """
    try:
        positives, negatives = [], []
        for raw in globs:
            raw = str(raw).strip()
            if not raw:
                continue
            if raw.startswith("!"):
                negatives.extend(_expand_braces(raw[1:]))
            else:
                positives.extend(_expand_braces(raw))
        if not any(_relative_matches_workspace_glob(rel_parts, p) for p in positives):
            return False
        return not any(_relative_matches_workspace_glob(rel_parts, n) for n in negatives)
    except (_PatternBudgetError, RecursionError):
        # Pathological pattern from an untrusted manifest (brace bomb, ``**``
        # wall, or deep nesting) → cannot be evaluated safely, so membership is
        # unproven (fail closed).
        return False


def _workspace_root_for(package_dir: Path) -> Optional[Path]:
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
        globs = _workspace_globs_for(ancestor)
        if globs:
            try:
                rel_parts = tuple(package_dir.resolve().relative_to(ancestor.resolve()).parts)
            except ValueError:
                rel_parts = ()
            if rel_parts and _package_matches_workspace(rel_parts, globs):
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
    except ValueError:
        return False


def _is_strict_ancestor(ancestor: Path, descendant: Path) -> bool:
    """True if ``ancestor`` is a strict (proper) ancestor of ``descendant``."""
    try:
        rel = descendant.resolve().relative_to(ancestor.resolve())
    except ValueError:
        return False
    return len(rel.parts) > 0


def _lexical_repo_root(test_path: Path) -> Optional[Path]:
    """Find the nearest ``.git`` ancestor of ``test_path`` on its *lexical*
    (un-resolved, ``abspath``) parent chain, or ``None`` if there is none.

    Only a *non-symlinked* directory may anchor the root: if ``directory`` is
    itself a symlink, its ``.git`` probe would follow the link out of the tree
    (e.g. ``repo/link -> /outside`` where ``/outside/.git`` exists), so such a
    directory is skipped. Combined with the resolved-path containment check in
    :func:`_detect_ts_test_runner`, this refuses both a symlinked test directory
    that escapes a repository and one whose target is itself a foreign checkout —
    without rejecting a symlink that stays inside the repository.
    """
    directory = Path(os.path.abspath(str(test_path))).parent
    for _ in range(200):
        if not os.path.islink(str(directory)) and (directory / ".git").exists():
            return directory
        parent = directory.parent
        if parent == directory:
            break
        directory = parent
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
    is_spec = test_path.name.endswith(('.spec.ts', '.spec.tsx'))
    search_dir = test_path.resolve().parent
    # Repository containment: anchor the repo root lexically (before symlinks are
    # resolved). If the resolved test path escapes that root, refuse to adopt any
    # out-of-repo runner config.
    contain = _lexical_repo_root(test_path)
    # Deepest ancestor-workspace root the original leaf must still reach; walk
    # *through* intermediate independent package.json manifests until then.
    ceiling: Optional[Path] = None
    for _ in range(80):
        # Never step outside the repository (e.g. via a symlink that resolves out).
        if contain is not None and not _is_within(search_dir, contain):
            break
        # For .spec.ts/.spec.tsx files, check Playwright first
        if is_spec and any((search_dir / cfg).exists() for cfg in ('playwright.config.ts', 'playwright.config.js', 'playwright.config.mjs')):
            return ("npx playwright test", search_dir)
        if any((search_dir / cfg).exists() for cfg in ('jest.config.js', 'jest.config.ts', 'jest.config.mjs')):
            return ("npx jest --no-coverage --runTestsByPath", search_dir)
        if any((search_dir / cfg).exists() for cfg in ('vitest.config.ts', 'vitest.config.js', 'vitest.config.mjs')):
            return ("npx vitest run", search_dir)
        # Stop at the JS project boundary (nearest package.json), but cross it when
        # this package is a member of an ancestor workspace whose config lives at
        # the workspace root — and keep crossing intermediate independent manifests
        # until that workspace root is reached.
        if (search_dir / "package.json").exists():
            root = _workspace_root_for(search_dir)
            if root is not None and (ceiling is None or _is_strict_ancestor(root, ceiling)):
                # Extend the ceiling to the shallowest (highest) workspace root,
                # so nested workspaces chain correctly.
                ceiling = root
            below_ceiling = ceiling is not None and _is_strict_ancestor(ceiling, search_dir)
            if root is None and not below_ceiling:
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
            return TestCommand(command=csv_cmd.replace('{file}', str(test_file)))

    # 3. Smart detection
    if resolved_language:
        smart_cmd = default_verify_cmd_for(resolved_language.lower(), str(test_file))
        if smart_cmd:
            return TestCommand(command=smart_cmd)

    # 4. No command available
    return None
