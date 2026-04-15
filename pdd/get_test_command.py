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


def _detect_py_project_root(test_path: Path) -> Optional[Path]:
    """Detect Python subproject root by walking up from the test file.

    Looks for Python project markers: .pddrc, pyproject.toml, pytest.ini,
    setup.cfg, or conftest.py. Stops at the repo root (.git directory).
    Returns the directory containing the first marker, or None.

    Mirrors _detect_ts_test_runner() for Python monorepos, ensuring tests
    in subdirectories (e.g., extensions/app/tests/) run with the correct cwd.
    """
    search_dir = test_path.resolve().parent
    for _ in range(5):  # Walk up at most 5 levels
        # Stop at repo root
        if (search_dir / ".git").exists():
            return None
        # Check markers in priority order
        if (search_dir / ".pddrc").exists():
            return search_dir
        pyproject = search_dir / "pyproject.toml"
        if pyproject.exists():
            try:
                content = pyproject.read_text()
                if "[tool.pytest" in content or "[project]" in content:
                    return search_dir
            except OSError:
                pass
        if (search_dir / "pytest.ini").exists():
            return search_dir
        if (search_dir / "setup.cfg").exists():
            try:
                content = (search_dir / "setup.cfg").read_text()
                if "[tool:pytest]" in content:
                    return search_dir
            except OSError:
                pass
        # conftest.py is only a project root signal if NOT in a test directory
        # (tests/ dirs commonly have conftest.py for fixtures, not as project markers)
        if (search_dir / "conftest.py").exists():
            dir_name = search_dir.name.lower()
            if dir_name not in ("tests", "test", "testing", "_tests"):
                return search_dir
        parent = search_dir.parent
        if parent == search_dir:
            break
        search_dir = parent
    return None


def _detect_ts_test_runner(test_path: Path) -> Optional[Tuple[str, Path]]:
    """Detect Playwright, Jest, or Vitest config by walking up from the test file.

    For .spec.ts/.spec.tsx files, checks for playwright.config first.
    Returns (command, config_directory) tuple if a config is found, otherwise None.
    The config_directory is where the test runner config lives — callers must use it as cwd.
    """
    is_spec = test_path.name.endswith(('.spec.ts', '.spec.tsx'))
    search_dir = test_path.resolve().parent
    for _ in range(5):  # Walk up at most 5 levels
        # For .spec.ts/.spec.tsx files, check Playwright first
        if is_spec and any((search_dir / cfg).exists() for cfg in ('playwright.config.ts', 'playwright.config.js', 'playwright.config.mjs')):
            return ("npx playwright test", search_dir)
        if any((search_dir / cfg).exists() for cfg in ('jest.config.js', 'jest.config.ts', 'jest.config.mjs')):
            return ("npx jest --no-coverage --", search_dir)
        if any((search_dir / cfg).exists() for cfg in ('vitest.config.ts', 'vitest.config.js', 'vitest.config.mjs')):
            return ("npx vitest run", search_dir)
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
    2. CSV run_test_command (if non-empty). cwd=None (caller decides).
    3. Smart detection via default_verify_cmd_for(). cwd=None.
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

    # Pre-step: For Python files, detect subproject root for cwd
    detected_cwd: Optional[Path] = None
    if ext == '.py':
        detected_cwd = _detect_py_project_root(test_path)

    # 1. For TypeScript/TSX: detect Jest or Vitest config and use appropriate runner
    if ext in ('.ts', '.tsx') and resolved_language and resolved_language.lower() in ('typescript', 'typescriptreact'):
        runner_result = _detect_ts_test_runner(test_path)
        if runner_result:
            runner_cmd, config_dir = runner_result
            return TestCommand(command=f"{runner_cmd} {test_path.resolve()}", cwd=config_dir)

    # 2. Check CSV for run_test_command
    lang_formats = _load_language_format()
    if ext in lang_formats:
        csv_cmd = lang_formats[ext].get('run_test_command', '').strip()
        if csv_cmd:
            return TestCommand(command=csv_cmd.replace('{file}', str(test_file)), cwd=detected_cwd)

    # 3. Smart detection
    if resolved_language:
        smart_cmd = default_verify_cmd_for(resolved_language.lower(), str(test_file))
        if smart_cmd:
            return TestCommand(command=smart_cmd, cwd=detected_cwd)

    # 4. No command available
    return None
