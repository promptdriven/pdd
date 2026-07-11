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


def _detect_ts_test_runner(test_path: Path) -> Optional[Tuple[str, Path]]:
    """Detect Playwright, Jest, or Vitest config by walking up from the test file.

    For .spec.ts/.spec.tsx files, checks for playwright.config first.
    Returns (command, config_directory) tuple if a config is found, otherwise None.
    The config_directory is where the test runner config lives — callers must use it as cwd.

    The walk continues up to the repository root (the nearest ancestor containing
    ``.git``) rather than stopping after a fixed number of parents: in
    Next.js/monorepo layouts a colocated test can live many directories below its
    runner config (e.g. a page test under
    ``frontend/src/app/hackathon/[eventId]/team/__tests__/`` and the config at
    ``frontend/jest.config.js``), so a shallow cap would miss the config and fall
    back to a non-test runner. The nearest ancestor config wins. The repository
    root — not the nearest ``package.json`` — is the boundary: a workspace leaf
    package has its own ``package.json`` yet inherits Jest/Vitest/Playwright
    configuration from the workspace root, so stopping at the leaf manifest would
    miss it. The search never escapes above the repository root, and a hard
    iteration cap guards against pathological paths.

    Jest is invoked with ``--runTestsByPath`` so the resolved absolute path is
    matched literally (see ``get_test_command_for_file`` for how the path is
    escaped/quoted per runner). Jest otherwise treats the trailing path as a
    regex, and Next.js dynamic-route segments such as ``[eventId]``/``[slug]`` are
    regex character classes that never match the literal bracketed path — leaving
    the generated suite unexecutable.
    """
    is_spec = test_path.name.endswith(('.spec.ts', '.spec.tsx'))
    search_dir = test_path.resolve().parent
    # Walk up until a config is found or we reach the repository root (a directory
    # holding ``.git``). Continue *through* intermediate ``package.json`` files so
    # a config that lives at the workspace root is still discovered. A hard
    # iteration cap guards against pathological paths.
    for _ in range(80):
        # For .spec.ts/.spec.tsx files, check Playwright first
        if is_spec and any((search_dir / cfg).exists() for cfg in ('playwright.config.ts', 'playwright.config.js', 'playwright.config.mjs')):
            return ("npx playwright test", search_dir)
        if any((search_dir / cfg).exists() for cfg in ('jest.config.js', 'jest.config.ts', 'jest.config.mjs')):
            return ("npx jest --no-coverage --runTestsByPath", search_dir)
        if any((search_dir / cfg).exists() for cfg in ('vitest.config.ts', 'vitest.config.js', 'vitest.config.mjs')):
            return ("npx vitest run", search_dir)
        # Stop at the repository root; the config would have been found by now.
        # ``.git`` is a directory in a normal clone and a file in a worktree.
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
