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
import re
import shlex

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


def _relative_matches_workspace_glob(rel_parts: Tuple[str, ...], pattern: str) -> bool:
    """Match a package's path segments against a single workspace glob pattern.

    Supports the segment semantics workspace tools use: ``*`` matches exactly one
    path segment (with fnmatch inside the segment) and ``**`` matches zero or more
    segments. A trailing ``/*`` therefore matches direct children only, while
    ``**`` spans any depth.
    """
    pat_parts = [p for p in pattern.strip("/").split("/") if p not in ("", ".")]
    return _match_segments(list(rel_parts), pat_parts)


def _match_segments(rel: list, pat: list) -> bool:
    if not pat:
        return not rel
    head, rest = pat[0], pat[1:]
    if head == "**":
        # Zero or more segments.
        for i in range(len(rel) + 1):
            if _match_segments(rel[i:], rest):
                return True
        return False
    if not rel:
        return False
    return fnmatch.fnmatch(rel[0], head) and _match_segments(rel[1:], rest)


def _workspace_globs_for(ancestor: Path) -> list:
    """Return the workspace package globs declared by ``ancestor`` (empty if none).

    Reads npm/yarn ``workspaces`` (list or ``{"packages": [...]}``), ``lerna.json``
    ``packages``, and ``pnpm-workspace.yaml`` ``packages``. pnpm requires a YAML
    parser; if unavailable we conservatively return no globs so membership stays
    unproven rather than falsely asserted.
    """
    globs: list = []
    manifest_path = ancestor / "package.json"
    if manifest_path.exists():
        try:
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        except (ValueError, OSError):
            manifest = {}
        ws = manifest.get("workspaces")
        if isinstance(ws, dict):
            ws = ws.get("packages")
        if isinstance(ws, list):
            globs.extend(str(p) for p in ws)
    lerna_path = ancestor / "lerna.json"
    if lerna_path.exists():
        try:
            lerna = json.loads(lerna_path.read_text(encoding="utf-8"))
            pkgs = lerna.get("packages")
            if isinstance(pkgs, list):
                globs.extend(str(p) for p in pkgs)
            elif pkgs is None:
                globs.append("packages/*")  # lerna default
        except (ValueError, OSError):
            pass
    pnpm_path = ancestor / "pnpm-workspace.yaml"
    if pnpm_path.exists():
        try:
            import yaml  # optional dependency
            data = yaml.safe_load(pnpm_path.read_text(encoding="utf-8")) or {}
            pkgs = data.get("packages")
            if isinstance(pkgs, list):
                globs.extend(str(p) for p in pkgs)
        except Exception:
            pass  # conservative: unparseable pnpm workspace → no membership claim
    return globs


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
        if globs:
            try:
                rel_parts = tuple(package_dir.resolve().relative_to(ancestor.resolve()).parts)
            except ValueError:
                rel_parts = ()
            if rel_parts and any(_relative_matches_workspace_glob(rel_parts, g) for g in globs):
                return True
        if (ancestor / ".git").exists():
            break
        parent = ancestor.parent
        if parent == ancestor:
            break
        ancestor = parent
    return False


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
    for _ in range(80):
        # For .spec.ts/.spec.tsx files, check Playwright first
        if is_spec and any((search_dir / cfg).exists() for cfg in ('playwright.config.ts', 'playwright.config.js', 'playwright.config.mjs')):
            return ("npx playwright test", search_dir)
        if any((search_dir / cfg).exists() for cfg in ('jest.config.js', 'jest.config.ts', 'jest.config.mjs')):
            return ("npx jest --no-coverage --runTestsByPath", search_dir)
        if any((search_dir / cfg).exists() for cfg in ('vitest.config.ts', 'vitest.config.js', 'vitest.config.mjs')):
            return ("npx vitest run", search_dir)
        # Stop at the JS project boundary (nearest package.json), but cross it when
        # this package is a member of an ancestor workspace whose config lives at
        # the workspace root.
        if (search_dir / "package.json").exists() and not _belongs_to_ancestor_workspace(search_dir):
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
