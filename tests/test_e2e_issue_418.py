"""
E2E Test for Issue #418: Temp Directory Resource Leak in _setup_repository()

This test verifies the bug at a system level by simulating what happens when
a user triggers a git clone failure through the agentic_change workflow.

The Bug:
- _setup_repository() creates a temp directory at line 112: tempfile.mkdtemp()
- When git clone fails, RuntimeError is raised at lines 129 or 131
- The temp directory is never cleaned up before the exception is raised
- Over time, this accumulates orphaned temp directories and wastes disk space

E2E Test Strategy:
- Use subprocess to run a Python script that:
  1. Calls _setup_repository() with a repository that will fail to clone
  2. Captures the created temp directory path
  3. Verifies the temp directory still exists after the exception
- This simulates real-world user behavior when clones fail
- The test should FAIL on buggy code (temp dir exists) and PASS once fixed

User-Facing Impact:
- Users running pdd commands on invalid/private repositories
- Network interruptions during git clone
- Authentication failures
- Rate limiting issues
- Disk space gradually filled with orphaned temp directories
- In extreme cases: "No space left on device" errors
"""

import glob
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest


def get_project_root() -> Path:
    """Get the project root directory."""
    current = Path(__file__).parent.parent
    return current


class TestTempDirLeakE2E:
    """
    E2E tests for Issue #418: Temp directory resource leak in _setup_repository()
    when git clone fails.
    """

    def test_temp_dir_leaked_on_clone_failure_nonexistent_repo(self, tmp_path: Path):
        """
        E2E Test: _setup_repository() leaks temp directory when clone fails.

        This test simulates the real-world scenario:
        1. User runs a pdd command that calls _setup_repository()
        2. Git clone fails (e.g., non-existent repo, auth failure, network issue)
        3. Temp directory should be cleaned up, but due to the bug, it persists

        Expected behavior (after fix):
        - Temp directory is deleted before RuntimeError is raised
        - No pdd_* directories remain in /tmp after the exception

        Bug behavior (Issue #418):
        - Temp directory remains in /tmp after RuntimeError
        - Multiple failures accumulate leaked temp directories
        - Disk space is gradually consumed
        """
        project_root = get_project_root()

        # Create a test script that simulates the bug scenario
        test_script = f'''
import sys
import json
import os
import glob
import tempfile
from pathlib import Path

# Add project root to path
sys.path.insert(0, "{project_root}")

from pdd.agentic_change import _setup_repository

def count_pdd_temp_dirs():
    """Count temp directories matching pdd_* pattern."""
    temp_root = tempfile.gettempdir()
    pattern = os.path.join(temp_root, "pdd_*")
    return len(glob.glob(pattern))

if __name__ == "__main__":
    # Count temp directories before
    before_count = count_pdd_temp_dirs()

    # Try to setup a repository that will fail to clone
    # Using a non-existent repository to trigger clone failure
    temp_dir = None
    exception_raised = False

    try:
        # This should create a temp directory and then fail during clone
        temp_dir = _setup_repository(
            owner="nonexistent-user-12345",
            repo="nonexistent-repo-67890",
            quiet=True
        )
    except RuntimeError as e:
        # Expected - clone should fail
        exception_raised = True
        error_message = str(e)

    # Count temp directories after
    after_count = count_pdd_temp_dirs()

    # Find any leaked pdd_* directories
    temp_root = tempfile.gettempdir()
    leaked_dirs = glob.glob(os.path.join(temp_root, "pdd_nonexistent-repo-*"))

    # Output results as JSON
    result = {{
        "before_count": before_count,
        "after_count": after_count,
        "exception_raised": exception_raised,
        "leaked_dirs": leaked_dirs,
        "temp_dirs_created": after_count - before_count,
        "bug_detected": after_count > before_count
    }}

    print(json.dumps(result))
'''

        # Write the test script to a temp file
        script_file = tmp_path / "test_clone_failure_leak.py"
        script_file.write_text(test_script)

        # Run the test script in a subprocess with proper environment
        env = os.environ.copy()
        env['PYTHONPATH'] = str(project_root)
        env['PDD_FORCE_LOCAL'] = '1'  # Prevent any real API calls if possible

        result = subprocess.run(
            [sys.executable, str(script_file)],
            capture_output=True,
            text=True,
            cwd=str(tmp_path),
            env=env,
            timeout=30
        )

        # Parse the output
        if result.returncode != 0:
            pytest.fail(
                f"Test script failed to run:\n"
                f"Return code: {result.returncode}\n"
                f"STDOUT:\n{result.stdout}\n"
                f"STDERR:\n{result.stderr}"
            )

        try:
            test_result = json.loads(result.stdout.strip())
        except json.JSONDecodeError as e:
            pytest.fail(
                f"Failed to parse test output as JSON:\n"
                f"Error: {e}\n"
                f"STDOUT:\n{result.stdout}\n"
                f"STDERR:\n{result.stderr}"
            )

        # THE BUG CHECK: Temp directories should NOT leak after clone failure
        if test_result['bug_detected']:
            leaked_dirs = test_result['leaked_dirs']

            pytest.fail(
                f"BUG DETECTED (Issue #418): Temp directory leaked after git clone failure!\n\n"
                f"Location: pdd/agentic_change.py:111-132\n\n"
                f"Scenario:\n"
                f"  1. _setup_repository() creates temp directory at line 112:\n"
                f"     temp_dir = Path(tempfile.mkdtemp(prefix=f'pdd_{{repo}}_'))\n"
                f"  2. Git clone fails (non-existent repo, auth failure, network issue)\n"
                f"  3. RuntimeError raised at line 129 or 131 WITHOUT cleanup\n"
                f"  4. Temp directory never deleted - LEAKED!\n\n"
                f"Results:\n"
                f"  - Temp dirs before: {test_result['before_count']}\n"
                f"  - Temp dirs after: {test_result['after_count']}\n"
                f"  - Leaked directories: {test_result['temp_dirs_created']}\n"
                f"  - Leaked paths:\n    " + "\n    ".join(leaked_dirs) + "\n\n"
                f"Impact:\n"
                f"  - Users with failed clones leak temp directories\n"
                f"  - Common scenarios: auth failures, network issues, typos in repo names\n"
                f"  - Accumulates over time, consuming disk space\n"
                f"  - Can lead to 'No space left on device' in extreme cases\n\n"
                f"Root Cause:\n"
                f"  - temp_dir created at line 112 but never cleaned up\n"
                f"  - RuntimeError raised at lines 129, 131 without calling shutil.rmtree()\n"
                f"  - No try-finally block to guarantee cleanup\n\n"
                f"Fix:\n"
                f"  Add cleanup before raising exceptions:\n"
                f"  if result.returncode != 0:\n"
                f"      shutil.rmtree(temp_dir, ignore_errors=True)  # Cleanup\n"
                f"      raise RuntimeError(...)\n\n"
                f"  Or use try-finally:\n"
                f"  try:\n"
                f"      result = subprocess.run(...)\n"
                f"  except Exception as e:\n"
                f"      shutil.rmtree(temp_dir, ignore_errors=True)  # Cleanup\n"
                f"      raise\n\n"
                f"Reference:\n"
                f"  - pdd/agentic_test.py:161-162 shows correct pattern:\n"
                f"    shutil.rmtree(temp_dir, ignore_errors=True)"
            )

    def test_temp_dir_leaked_on_subprocess_exception(self, tmp_path: Path):
        """
        E2E Test: _setup_repository() leaks temp dir when subprocess.run() raises exception.

        This test verifies that even when subprocess.run() itself raises an exception
        (not just returning non-zero exit code), the temp directory still leaks.

        User-facing scenarios:
        - Command not found (gh not installed)
        - Permission denied errors
        - System resource exhaustion
        - Disk space issues during subprocess execution
        """
        project_root = get_project_root()

        test_script = f'''
import sys
import json
import os
import glob
import tempfile
from pathlib import Path
from unittest.mock import patch, MagicMock

sys.path.insert(0, "{project_root}")

from pdd.agentic_change import _setup_repository

def count_pdd_temp_dirs():
    """Count temp directories matching pdd_* pattern."""
    temp_root = tempfile.gettempdir()
    pattern = os.path.join(temp_root, "pdd_*")
    return len(glob.glob(pattern))

if __name__ == "__main__":
    before_count = count_pdd_temp_dirs()

    exception_raised = False

    # Mock subprocess.run to raise an exception
    with patch('pdd.agentic_change.subprocess.run') as mock_run:
        mock_run.side_effect = OSError("Command not found: gh")

        try:
            _setup_repository(
                owner="test-owner",
                repo="test-repo",
                quiet=True
            )
        except (RuntimeError, OSError) as e:
            exception_raised = True

    after_count = count_pdd_temp_dirs()

    # Find leaked directories
    temp_root = tempfile.gettempdir()
    leaked_dirs = glob.glob(os.path.join(temp_root, "pdd_test-repo-*"))

    result = {{
        "before_count": before_count,
        "after_count": after_count,
        "exception_raised": exception_raised,
        "leaked_dirs": leaked_dirs,
        "temp_dirs_created": after_count - before_count,
        "bug_detected": after_count > before_count
    }}

    print(json.dumps(result))
'''

        script_file = tmp_path / "test_subprocess_exception_leak.py"
        script_file.write_text(test_script)

        env = os.environ.copy()
        env['PYTHONPATH'] = str(project_root)
        env['PDD_FORCE_LOCAL'] = '1'

        result = subprocess.run(
            [sys.executable, str(script_file)],
            capture_output=True,
            text=True,
            cwd=str(tmp_path),
            env=env,
            timeout=30
        )

        if result.returncode != 0:
            pytest.fail(f"Test script failed:\n{result.stderr}")

        try:
            test_result = json.loads(result.stdout.strip())
        except json.JSONDecodeError:
            pytest.fail(f"Failed to parse output:\n{result.stdout}")

        if test_result['bug_detected']:
            pytest.fail(
                f"BUG DETECTED (Issue #418): Temp directory leaked after subprocess exception!\n\n"
                f"This confirms the bug affects both failure modes:\n"
                f"  1. Non-zero exit code (line 129)\n"
                f"  2. Exception from subprocess.run() (line 131)\n\n"
                f"Leaked directories: {test_result['temp_dirs_created']}\n"
                f"Paths: {test_result['leaked_dirs']}\n\n"
                f"Both exception paths must cleanup temp_dir before raising."
            )

    def test_temp_dir_cleaned_up_on_successful_clone(self, tmp_path: Path):
        """
        E2E Test: Successful clone should NOT clean up temp directory.

        This is a regression test to ensure:
        1. Normal clone operation works correctly
        2. Temp directory is returned and used (NOT deleted)
        3. The fix doesn't break existing functionality

        Note: This test verifies that successful clones continue to work correctly.
        The temp directory is intentionally kept for successful clones (it's used
        as the working directory). Only FAILED clones should clean up.
        """
        project_root = get_project_root()

        test_script = f'''
import sys
import json
import os
from pathlib import Path
from unittest.mock import patch, MagicMock

sys.path.insert(0, "{project_root}")

from pdd.agentic_change import _setup_repository

if __name__ == "__main__":
    # Mock subprocess.run to simulate successful clone
    with patch('pdd.agentic_change.subprocess.run') as mock_run:
        # Simulate successful clone
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stderr = ""
        mock_run.return_value = mock_result

        try:
            result_dir = _setup_repository(
                owner="test-owner",
                repo="test-repo",
                quiet=True
            )

            # Successful clone should return the temp directory
            success = True
            temp_dir_exists = result_dir.exists()
            temp_dir_path = str(result_dir)
        except Exception as e:
            success = False
            temp_dir_exists = False
            temp_dir_path = ""

    result = {{
        "success": success,
        "temp_dir_exists": temp_dir_exists,
        "temp_dir_path": temp_dir_path
    }}

    print(json.dumps(result))
'''

        script_file = tmp_path / "test_successful_clone.py"
        script_file.write_text(test_script)

        env = os.environ.copy()
        env['PYTHONPATH'] = str(project_root)
        env['PDD_FORCE_LOCAL'] = '1'

        result = subprocess.run(
            [sys.executable, str(script_file)],
            capture_output=True,
            text=True,
            cwd=str(tmp_path),
            env=env,
            timeout=30
        )

        if result.returncode != 0:
            pytest.fail(f"Test script failed:\n{result.stderr}")

        try:
            test_result = json.loads(result.stdout.strip())
        except json.JSONDecodeError:
            pytest.fail(f"Failed to parse output:\n{result.stdout}")

        # Successful clone should work normally
        assert test_result['success'], (
            f"Successful clone failed! This is a regression.\n"
            f"The fix should only cleanup on FAILED clones, not successful ones."
        )

        assert test_result['temp_dir_exists'], (
            f"Temp directory was deleted after successful clone!\n"
            f"This is a regression - successful clones should keep the temp directory.\n"
            f"Path: {test_result['temp_dir_path']}\n\n"
            f"Only FAILED clones should cleanup temp_dir before raising exception."
        )

    def test_multiple_clone_failures_accumulate_leaked_dirs(self, tmp_path: Path):
        """
        E2E Test: Multiple clone failures accumulate leaked temp directories.

        This test demonstrates the cumulative impact of the bug:
        1. Each failed clone creates a new leaked temp directory
        2. Over time, this accumulates and wastes significant disk space
        3. In production, this can lead to disk space exhaustion

        This is an integration test showing the real-world impact when users
        experience multiple clone failures (common with typos, auth issues, etc.).
        """
        project_root = get_project_root()

        test_script = f'''
import sys
import json
import os
import glob
import tempfile

sys.path.insert(0, "{project_root}")

from pdd.agentic_change import _setup_repository

def count_pdd_temp_dirs():
    """Count temp directories matching pdd_* pattern."""
    temp_root = tempfile.gettempdir()
    pattern = os.path.join(temp_root, "pdd_*")
    return len(glob.glob(pattern))

if __name__ == "__main__":
    before_count = count_pdd_temp_dirs()

    # Simulate multiple clone failures (e.g., user keeps trying with typos)
    num_failures = 3
    failures = []

    for i in range(num_failures):
        try:
            _setup_repository(
                owner="nonexistent-user",
                repo=f"nonexistent-repo-{{i}}",
                quiet=True
            )
        except RuntimeError:
            failures.append(i)

    after_count = count_pdd_temp_dirs()

    result = {{
        "before_count": before_count,
        "after_count": after_count,
        "num_failures": len(failures),
        "leaked_count": after_count - before_count,
        "bug_detected": (after_count - before_count) >= num_failures
    }}

    print(json.dumps(result))
'''

        script_file = tmp_path / "test_accumulation.py"
        script_file.write_text(test_script)

        env = os.environ.copy()
        env['PYTHONPATH'] = str(project_root)
        env['PDD_FORCE_LOCAL'] = '1'

        result = subprocess.run(
            [sys.executable, str(script_file)],
            capture_output=True,
            text=True,
            cwd=str(tmp_path),
            env=env,
            timeout=60
        )

        if result.returncode != 0:
            pytest.fail(f"Test script failed:\n{result.stderr}")

        try:
            test_result = json.loads(result.stdout.strip())
        except json.JSONDecodeError:
            pytest.fail(f"Failed to parse output:\n{result.stdout}")

        if test_result['bug_detected']:
            pytest.fail(
                f"BUG DETECTED (Issue #418): Multiple failures accumulate leaked directories!\n\n"
                f"Cumulative Impact:\n"
                f"  - Number of clone failures: {test_result['num_failures']}\n"
                f"  - Leaked temp directories: {test_result['leaked_count']}\n"
                f"  - Before test: {test_result['before_count']} temp dirs\n"
                f"  - After test: {test_result['after_count']} temp dirs\n\n"
                f"Real-World Impact:\n"
                f"  - Users retrying failed commands leak multiple directories\n"
                f"  - CI/CD systems running many pdd commands accumulate leaks\n"
                f"  - Over time, disk space is gradually consumed\n"
                f"  - Can eventually cause 'No space left on device' errors\n\n"
                f"This demonstrates why proper resource cleanup is critical!"
            )
