"""
E2E Test for Issue #349: sys.modules pollution during pytest collection.

This test verifies the bug at a system level by simulating what happens when
pytest collects test files that import context example files with module-level
sys.modules assignments.

The Bug:
- Context example files (e.g., context/commands/sessions_example.py) assign
  MagicMock() to sys.modules entries at module level
- These assignments happen during pytest collection when files are imported
- The mocks persist for the entire pytest session
- Subsequent test files importing real pdd modules get MagicMock instead

E2E Test Strategy:
- Use subprocess to run pytest in a fresh process
- This isolates the test from the current pytest session
- Run pytest --collect-only to trigger collection without executing tests
- Check if sys.modules is polluted after collection

The test should:
- FAIL on the current buggy code (pollution detected)
- PASS once the bug is fixed (no pollution)
"""

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Dict, List, Any

import pytest


def get_project_root() -> Path:
    """Get the project root directory."""
    current = Path(__file__).parent
    while current != current.parent:
        if (current / "context").is_dir():
            return current
        current = current.parent
    raise RuntimeError("Could not find project root with context/ directory")


class TestSysModulesPollutionE2E:
    """E2E tests verifying sys.modules pollution during pytest collection."""

    def test_context_example_import_does_not_pollute_sys_modules(self, tmp_path: Path):
        """
        E2E Test: Importing a context example file should not leave MagicMock
        objects in sys.modules after the file is loaded.

        This test simulates what happens during pytest collection:
        1. A new Python process imports a problematic context example file
        2. We check if sys.modules contains MagicMock objects for pdd.* modules

        Expected behavior (after fix):
        - sys.modules should not contain MagicMock objects for any pdd.* modules
        - The file either uses save/restore pattern or is excluded from collection

        Bug behavior (Issue #349):
        - sys.modules contains MagicMock objects for pdd.* modules
        - These persist and affect all subsequent imports
        """
        project_root = get_project_root()

        # Known problematic files from root cause analysis
        problematic_files = [
            "context/commands/sessions_example.py",
            "context/server/routes/auth_example.py",
            "context/server/routes/commands_example.py",
            "context/server/routes/prompts_example.py",
        ]

        # Test script that imports each file and checks sys.modules
        test_script = '''
import sys
import json

def check_pollution_after_import(file_path):
    """Import a file and check if sys.modules is polluted with MagicMock."""
    # Clear any pre-existing mocks
    pdd_modules_before = {k: type(v).__name__ for k, v in sys.modules.items() if k.startswith("pdd")}

    try:
        # Import the file (this triggers the module-level code)
        import importlib.util
        spec = importlib.util.spec_from_file_location("example_module", file_path)
        if spec and spec.loader:
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
    except Exception as e:
        # Import might fail, but we still want to check pollution
        pass

    # Check for MagicMock objects in sys.modules
    polluted = []
    for name, module in sys.modules.items():
        if name.startswith("pdd"):
            module_type = type(module).__name__
            # MagicMock is pollution
            if "Mock" in module_type or "MagicMock" in module_type:
                polluted.append({"module": name, "type": module_type})

    return polluted

if __name__ == "__main__":
    import sys
    file_path = sys.argv[1]
    result = check_pollution_after_import(file_path)
    print(json.dumps(result))
'''

        # Write the test script to a temp file
        script_file = tmp_path / "check_pollution.py"
        script_file.write_text(test_script)

        all_pollution = {}

        for relative_path in problematic_files:
            file_path = project_root / relative_path
            if not file_path.exists():
                continue

            # Run in a fresh subprocess to avoid pollution from our process
            result = subprocess.run(
                [sys.executable, str(script_file), str(file_path)],
                capture_output=True,
                text=True,
                cwd=str(project_root),
                timeout=30
            )

            if result.returncode == 0 and result.stdout.strip():
                try:
                    pollution = json.loads(result.stdout.strip())
                    if pollution:
                        all_pollution[relative_path] = pollution
                except json.JSONDecodeError:
                    pass

        # THE BUG CHECK: No files should leave MagicMock in sys.modules
        if all_pollution:
            pollution_details = []
            for file_path, modules in all_pollution.items():
                for m in modules:
                    pollution_details.append(f"  {file_path}: {m['module']} -> {m['type']}")

            pytest.fail(
                f"BUG DETECTED (Issue #349): Context example files pollute sys.modules!\n\n"
                f"The following files leave MagicMock objects in sys.modules after import:\n"
                f"{chr(10).join(pollution_details)}\n\n"
                f"This pollution persists during pytest collection and causes tests to:\n"
                f"- Pass when run individually\n"
                f"- Fail when run with other modules\n\n"
                f"Fix: Files should either:\n"
                f"1. Use save/mock/restore pattern (see context/pytest_isolation_example.py Pattern 7)\n"
                f"2. Be excluded from pytest collection via conftest.py collect_ignore_glob"
            )

    def test_pytest_collection_does_not_pollute_pdd_modules(self, tmp_path: Path):
        """
        E2E Test: Running pytest --collect-only should not leave MagicMock
        objects in pdd.* module entries in sys.modules.

        This tests the full pytest collection flow, which is how users
        encounter the bug (running `pytest tests/` after `pdd sync`).

        We run pytest --collect-only in a subprocess and check if it prints
        any warnings about MagicMock pollution in pdd modules.
        """
        project_root = get_project_root()

        # Create a conftest.py that checks for pollution after collection
        conftest_content = '''
import sys
import pytest

def pytest_collection_finish(session):
    """Hook that runs after all test collection is complete."""
    polluted = []
    for name, module in sys.modules.items():
        if name.startswith("pdd"):
            module_type = type(module).__name__
            if "Mock" in module_type or "MagicMock" in module_type:
                polluted.append(f"{name}={module_type}")

    if polluted:
        # Print pollution info that we can capture
        print(f"\\n[POLLUTION_DETECTED]: {','.join(polluted)}")
'''

        # Create a minimal test file that does nothing
        test_dir = tmp_path / "test_suite"
        test_dir.mkdir()

        test_file = test_dir / "test_minimal.py"
        test_file.write_text('''
def test_placeholder():
    """Minimal test to trigger collection."""
    pass
''')

        conftest_file = test_dir / "conftest.py"
        conftest_file.write_text(conftest_content)

        # Create pytest.ini to include context examples in collection
        pytest_ini = tmp_path / "pytest.ini"
        pytest_ini.write_text(f'''[pytest]
testpaths = {test_dir}
python_files = *.py
python_classes =
python_functions = test_*
collect_ignore_glob =
''')

        # We also need to trigger import of the problematic context files
        # We can do this by adding them to the testpaths or by importing them
        # from a conftest

        # Better approach: Create a conftest that explicitly imports the context files
        root_conftest = tmp_path / "conftest.py"
        context_imports = []
        for example in ["context/commands/sessions_example.py",
                        "context/server/routes/auth_example.py",
                        "context/server/routes/commands_example.py",
                        "context/server/routes/prompts_example.py"]:
            full_path = project_root / example
            if full_path.exists():
                context_imports.append(f'    "{full_path}",')

        root_conftest.write_text(f'''
import sys
import importlib.util

# Simulate what happens during collection: import context example files
_context_files = [
{chr(10).join(context_imports)}
]

_pollution_found = []

for fp in _context_files:
    try:
        spec = importlib.util.spec_from_file_location("ctx_example", fp)
        if spec and spec.loader:
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
    except:
        pass

# Check for pollution immediately after imports
for name, module in sys.modules.items():
    if name.startswith("pdd"):
        module_type = type(module).__name__
        if "Mock" in module_type or "MagicMock" in module_type:
            _pollution_found.append(f"{{name}}={{module_type}}")

if _pollution_found:
    print(f"\\n[POLLUTION_DETECTED]: {{','.join(_pollution_found)}}")
''')

        # Run pytest --collect-only to trigger collection
        result = subprocess.run(
            [sys.executable, "-m", "pytest", "--collect-only", "-v", str(test_dir)],
            capture_output=True,
            text=True,
            cwd=str(tmp_path),
            env={**os.environ, "PYTHONPATH": str(project_root)},
            timeout=60
        )

        # Check for pollution marker in output
        output = result.stdout + result.stderr
        if "[POLLUTION_DETECTED]:" in output:
            # Extract pollution details
            for line in output.split('\n'):
                if "[POLLUTION_DETECTED]:" in line:
                    pollution_info = line.split("[POLLUTION_DETECTED]:")[1].strip()
                    pytest.fail(
                        f"BUG DETECTED (Issue #349): sys.modules polluted during pytest collection!\n\n"
                        f"Polluted modules: {pollution_info}\n\n"
                        f"This happens because context example files assign MagicMock() to\n"
                        f"sys.modules at module level without restoration.\n\n"
                        f"When pytest collects tests, these files get imported and the mocks\n"
                        f"persist, causing subsequent tests to see MagicMock instead of real modules."
                    )

    def test_real_pdd_import_after_context_example_import(self, tmp_path: Path):
        """
        E2E Test: After importing a problematic context example file,
        importing the real pdd module should still work correctly.

        This is the user-facing symptom: after context files pollute sys.modules,
        real pdd imports return MagicMock objects instead of actual modules.
        """
        project_root = get_project_root()

        # Test script that:
        # 1. Imports a problematic context example
        # 2. Then tries to import real pdd modules
        # 3. Checks if they're MagicMock or real
        test_script = '''
import sys
import json

# First, import a problematic context example file
problematic_file = sys.argv[1]

try:
    import importlib.util
    spec = importlib.util.spec_from_file_location("example", problematic_file)
    if spec and spec.loader:
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
except Exception as e:
    pass

# Now try to import real pdd modules
pollution = []

# Check if pdd module entries are MagicMock
for name in ["pdd", "pdd.core", "pdd.utils"]:
    if name in sys.modules:
        module = sys.modules[name]
        module_type = type(module).__name__
        if "Mock" in module_type:
            pollution.append({"module": name, "type": module_type, "is_mock": True})
        else:
            pollution.append({"module": name, "type": module_type, "is_mock": False})

print(json.dumps(pollution))
'''

        script_file = tmp_path / "check_real_import.py"
        script_file.write_text(test_script)

        # Test with the known problematic file
        problematic_file = project_root / "context/commands/sessions_example.py"
        if not problematic_file.exists():
            pytest.skip("Problematic file not found")

        result = subprocess.run(
            [sys.executable, str(script_file), str(problematic_file)],
            capture_output=True,
            text=True,
            cwd=str(project_root),
            timeout=30
        )

        if result.returncode == 0 and result.stdout.strip():
            try:
                modules = json.loads(result.stdout.strip())
                mocked = [m for m in modules if m.get("is_mock")]

                if mocked:
                    mocked_names = [m["module"] for m in mocked]
                    pytest.fail(
                        f"BUG DETECTED (Issue #349): Real pdd modules are MagicMock after import!\n\n"
                        f"After importing context/commands/sessions_example.py:\n"
                        f"  Polluted modules: {', '.join(mocked_names)}\n\n"
                        f"This means any code trying to import these modules will get\n"
                        f"MagicMock objects instead of real functionality.\n\n"
                        f"User impact: Tests that import pdd modules will fail with\n"
                        f"AttributeError or unexpected MagicMock behavior."
                    )
            except json.JSONDecodeError:
                pass
