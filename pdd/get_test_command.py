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
import json
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


def _match_workspace_segment(value: str, pattern: str) -> bool:
    """Match one path segment with case-sensitive literal, ``*``, and ``?`` rules."""
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


def _prepare_workspace_pattern(pattern: str) -> Optional[list[Tuple[str, ...]]]:
    """Validate and expand one bounded workspace pattern into segment tuples."""
    if not pattern or len(pattern) > _MAX_WORKSPACE_PATTERN_LENGTH:
        return None
    has_control = any(ord(char) < 32 for char in pattern)
    if has_control or any(char in pattern for char in "[]\\!"):
        return None
    if pattern.startswith("/"):
        return None
    while pattern.startswith("./"):
        pattern = pattern[2:]
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
    rel_parts: Tuple[str, ...], segments: Tuple[str, ...]
) -> bool:
    """Match one already-prepared alternative with iterative dynamic programming."""
    previous = [False] * (len(rel_parts) + 1)
    previous[0] = True
    for segment in segments:
        current = [False] * (len(rel_parts) + 1)
        if segment == "**":
            current[0] = previous[0]
            for index in range(1, len(rel_parts) + 1):
                current[index] = previous[index] or current[index - 1]
        else:
            for index in range(1, len(rel_parts) + 1):
                current[index] = previous[index - 1] and _match_workspace_segment(
                    rel_parts[index - 1], segment
                )
        previous = current
    return previous[-1]


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


def _declared_workspace_membership(
    rel_parts: Tuple[str, ...], patterns: list[str]
) -> Optional[bool]:
    """Apply ordered workspace patterns; ``None`` means the declaration is invalid."""
    if not patterns or len(patterns) > _MAX_WORKSPACE_PATTERNS:
        return None
    if len(rel_parts) > _MAX_WORKSPACE_SEGMENTS:
        return None
    prepared_patterns = []
    work_states = 0
    for raw_pattern in patterns:
        if (
            not isinstance(raw_pattern, str)
            or len(raw_pattern) > _MAX_WORKSPACE_PATTERN_LENGTH
        ):
            return None
        excluded = raw_pattern.startswith("!")
        pattern = raw_pattern[1:] if excluded else raw_pattern
        alternatives = _prepare_workspace_pattern(pattern)
        if alternatives is None:
            return None
        for segments in alternatives:
            work_states += _workspace_match_state_cost(rel_parts, segments)
            if work_states > _MAX_WORKSPACE_MATCH_STATES:
                return None
        prepared_patterns.append((excluded, alternatives))

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
    if not isinstance(value, list):
        return None
    if any(not isinstance(pattern, str) for pattern in value):
        return None
    return value


def _pnpm_workspace_globs(path: Path) -> Optional[list[str]]:
    """Load an authoritative pnpm package declaration, failing closed."""
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, yaml.YAMLError):
        return None
    if not isinstance(data, dict):
        return None
    return _string_pattern_list(data.get("packages"))


def _manifest_workspace_globs(path: Path) -> Optional[list[str]]:
    """Load npm/Yarn workspace patterns when a package manifest declares them."""
    if not path.exists():
        return []
    try:
        manifest = json.loads(path.read_text(encoding="utf-8"))
    except (ValueError, OSError, UnicodeError):
        return []
    if not isinstance(manifest, dict):
        return None
    workspaces = manifest.get("workspaces")
    if isinstance(workspaces, dict):
        workspaces = workspaces.get("packages")
    if workspaces is None:
        return []
    return _string_pattern_list(workspaces)


def _lerna_workspace_globs(path: Path) -> Optional[list[str]]:
    """Load Lerna patterns, including its conventional ``packages/*`` default."""
    if not path.exists():
        return []
    try:
        lerna = json.loads(path.read_text(encoding="utf-8"))
    except (ValueError, OSError, UnicodeError):
        return None
    if not isinstance(lerna, dict):
        return None
    packages = lerna.get("packages")
    if packages is None:
        return ["packages/*"]
    return _string_pattern_list(packages)


def _workspace_globs_for(ancestor: Path) -> Optional[list[str]]:
    """Return workspace globs, or ``None`` for an invalid declaration.

    An existing ``pnpm-workspace.yaml`` is authoritative over package and Lerna
    manifests at the same root.
    """
    pnpm_path = ancestor / "pnpm-workspace.yaml"
    if pnpm_path.exists():
        return _pnpm_workspace_globs(pnpm_path)
    manifest_globs = _manifest_workspace_globs(ancestor / "package.json")
    lerna_globs = _lerna_workspace_globs(ancestor / "lerna.json")
    if manifest_globs is None or lerna_globs is None:
        return None
    return manifest_globs + lerna_globs


def _belongs_to_ancestor_workspace(package_dir: Path) -> bool:
    """Return True if ``package_dir`` (which holds a ``package.json``) is a member
    of an ancestor JS workspace, so its runner config may live at the workspace
    root rather than in the leaf package.

    Membership is proven, not assumed: an ancestor's declared workspace globs
    (npm/yarn ``workspaces``, ``lerna.json`` ``packages``, ``pnpm-workspace.yaml``
    ``packages``) must actually match ``package_dir`` relative to that ancestor.
    An unrelated package (e.g. a vendored ``vendor/tool``) beneath a workspace
    root is therefore not treated as a member. The search never looks above the
    repository root (``.git``).
    """
    ancestor = package_dir.parent
    for _ in range(80):
        globs = _workspace_globs_for(ancestor)
        if globs is None:
            return False
        if globs:
            try:
                rel_parts = tuple(package_dir.resolve().relative_to(ancestor.resolve()).parts)
            except ValueError:
                rel_parts = ()
            membership = _declared_workspace_membership(rel_parts, globs)
            if membership is None:
                return False
            if membership:
                return True
        if (ancestor / "pnpm-workspace.yaml").exists():
            return False
        if (ancestor / ".git").exists():
            break
        parent = ancestor.parent
        if parent == ancestor:
            break
        ancestor = parent
    return False


def _repository_root_for(test_path: Path) -> Optional[Path]:
    """Return the canonical repository root containing ``test_path``, if any."""
    current = test_path.resolve().parent
    for _ in range(80):
        if (current / ".git").exists():
            return current.resolve()
        parent = current.parent
        if parent == current:
            break
        current = parent
    return None


def _runner_config_is_contained(config_path: Path, repository_root: Optional[Path]) -> bool:
    """Accept only regular config targets contained by an anchored repository."""
    try:
        resolved_config = config_path.resolve(strict=True)
    except (OSError, RuntimeError):
        return False
    if not resolved_config.is_file():
        return False
    if repository_root is None:
        return True
    try:
        resolved_config.relative_to(repository_root)
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
      runner config from the workspace root, so when the leaf belongs to an
      ancestor workspace (``workspaces`` field / ``pnpm-workspace.yaml`` /
      ``lerna.json``) the walk continues *through* the leaf to the workspace root.
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
    for _ in range(80):
        # For .spec.ts/.spec.tsx files, check Playwright first
        if is_spec and any(
            _runner_config_is_contained(search_dir / cfg, repository_root)
            for cfg in (
                'playwright.config.ts',
                'playwright.config.js',
                'playwright.config.mjs',
            )
        ):
            return ("npx playwright test", search_dir)
        if any(
            _runner_config_is_contained(search_dir / cfg, repository_root)
            for cfg in ('jest.config.js', 'jest.config.ts', 'jest.config.mjs')
        ):
            return ("npx jest --no-coverage --runTestsByPath", search_dir)
        if any(
            _runner_config_is_contained(search_dir / cfg, repository_root)
            for cfg in ('vitest.config.ts', 'vitest.config.js', 'vitest.config.mjs')
        ):
            return ("npx vitest run", search_dir)
        # Stop at the JS project boundary (nearest package.json), but cross it when
        # this package is a member of an ancestor workspace whose config lives at
        # the workspace root.
        is_project = (search_dir / "package.json").exists()
        if is_project and not _belongs_to_ancestor_workspace(search_dir):
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
            return TestCommand(command=csv_cmd.replace('{file}', str(test_file)))

    # 3. Smart detection
    if resolved_language:
        smart_cmd = default_verify_cmd_for(resolved_language.lower(), str(test_file))
        if smart_cmd:
            return TestCommand(command=smart_cmd)

    # 4. No command available
    return None
