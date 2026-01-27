"""
E2E Test for Issue #403: File Handle Resource Leak in SyncLock.acquire()

This test verifies the bug at a system level by simulating what happens when
a user runs a sync operation and interrupts it with Ctrl+C (KeyboardInterrupt).

The Bug:
- SyncLock.acquire() opens a file at line 183 without guaranteed cleanup
- The exception handler only catches (IOError, OSError) at line 196
- When KeyboardInterrupt or other non-IO exceptions occur, the file handle leaks
- In long-running processes, this accumulates and causes "Too many open files"

E2E Test Strategy:
- Use subprocess to run a Python script that:
  1. Acquires a SyncLock (opens file descriptor)
  2. Gets interrupted by KeyboardInterrupt during lock acquisition
  3. Checks if the file descriptor leaked using lsof or psutil
- This isolates the test and simulates real-world user behavior
- The test should FAIL on buggy code (leak detected) and PASS once fixed

User-Facing Impact:
- Users running `pdd sync` and pressing Ctrl+C
- Long-running processes that repeatedly acquire locks
- CI/CD pipelines with frequent interruptions
- Eventually leads to "OSError: [Errno 24] Too many open files"
"""

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import List, Dict, Any

import pytest


def get_project_root() -> Path:
    """Get the project root directory."""
    current = Path(__file__).parent.parent
    return current


def get_open_lock_files(pid: int) -> List[Dict[str, Any]]:
    """
    Get list of open .lock files for a given process using psutil.

    Returns a list of dicts with file info: {'path': str, 'fd': int}
    """
    try:
        import psutil
        process = psutil.Process(pid)
        lock_files = []

        # Get all open files
        for file in process.open_files():
            if file.path.endswith('.lock'):
                lock_files.append({
                    'path': file.path,
                    'fd': file.fd,
                })

        return lock_files
    except (psutil.NoSuchProcess, psutil.AccessDenied):
        return []


class TestFileHandleLeakE2E:
    """
    E2E tests for Issue #403: File handle resource leak in SyncLock.acquire()
    when interrupted by KeyboardInterrupt or other non-IO exceptions.
    """

    def test_synclock_keyboard_interrupt_leaks_file_handle(self, tmp_path: Path):
        """
        E2E Test: SyncLock interrupted by KeyboardInterrupt leaves file handle open.

        This test simulates the real-world scenario:
        1. User runs `pdd sync` which acquires a SyncLock
        2. User presses Ctrl+C during lock acquisition
        3. File handle should be closed, but due to the bug, it leaks

        Expected behavior (after fix):
        - File descriptor is closed even when KeyboardInterrupt occurs
        - No .lock files remain open after the exception

        Bug behavior (Issue #403):
        - File descriptor remains open after KeyboardInterrupt
        - The .lock file is listed in lsof output for the process
        - Multiple interruptions accumulate leaked file descriptors
        """
        project_root = get_project_root()

        # Create a test script that simulates the bug scenario
        test_script = f'''
import sys
import json
import os
import fcntl

# Add project root to path
sys.path.insert(0, "{project_root}")

from pdd.sync_determine_operation import SyncLock
from pathlib import Path

def check_open_lock_files():
    """Check for open .lock files using psutil."""
    try:
        import psutil
        process = psutil.Process(os.getpid())
        lock_files = []

        for file in process.open_files():
            if file.path.endswith('.lock'):
                lock_files.append({{'path': file.path, 'fd': file.fd}})

        return lock_files
    except Exception as e:
        return []

def simulate_interrupt_during_lock_acquisition():
    """Simulate KeyboardInterrupt during lock acquisition."""
    # Patch fcntl.flock to raise KeyboardInterrupt
    original_flock = fcntl.flock

    def interrupt_flock(fd, operation):
        # Raise KeyboardInterrupt to simulate Ctrl+C
        raise KeyboardInterrupt("User pressed Ctrl+C")

    fcntl.flock = interrupt_flock

    try:
        lock = SyncLock("test_interrupt", "python")
        try:
            lock.acquire()  # This should raise KeyboardInterrupt
        except KeyboardInterrupt:
            pass  # Expected - user pressed Ctrl+C
    finally:
        fcntl.flock = original_flock

    # Return the list of open .lock files
    return check_open_lock_files()

if __name__ == "__main__":
    # Check initial state
    initial_locks = check_open_lock_files()

    # Simulate interrupt during lock acquisition
    leaked_locks = simulate_interrupt_during_lock_acquisition()

    # Output results as JSON
    result = {{
        "initial_lock_count": len(initial_locks),
        "leaked_lock_count": len(leaked_locks),
        "leaked_files": leaked_locks,
        "bug_detected": len(leaked_locks) > 0
    }}

    print(json.dumps(result))
'''

        # Write the test script to a temp file
        script_file = tmp_path / "test_interrupt_leak.py"
        script_file.write_text(test_script)

        # Run the test script in a subprocess with proper environment
        env = os.environ.copy()
        env['PYTHONPATH'] = str(project_root)
        env['PDD_FORCE_LOCAL'] = '1'  # Prevent any real API calls

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

        # THE BUG CHECK: File handles should NOT leak after KeyboardInterrupt
        if test_result['bug_detected']:
            leaked_files = test_result['leaked_files']
            leaked_paths = [f['path'] for f in leaked_files]

            pytest.fail(
                f"BUG DETECTED (Issue #403): File handle leaked after KeyboardInterrupt!\n\n"
                f"Scenario:\n"
                f"  1. SyncLock.acquire() opens file at line 183: self.fd = open(self.lock_file, 'w')\n"
                f"  2. KeyboardInterrupt raised during fcntl.flock() at line 187\n"
                f"  3. Exception handler at line 196 only catches (IOError, OSError)\n"
                f"  4. File handle never closed - LEAKED!\n\n"
                f"Results:\n"
                f"  - Initial open .lock files: {test_result['initial_lock_count']}\n"
                f"  - Leaked .lock files: {test_result['leaked_lock_count']}\n"
                f"  - Leaked file paths:\n    " + "\n    ".join(leaked_paths) + "\n\n"
                f"Impact:\n"
                f"  - Users pressing Ctrl+C during 'pdd sync' leak file descriptors\n"
                f"  - Long-running processes accumulate leaked FDs\n"
                f"  - Eventually causes: OSError: [Errno 24] Too many open files\n\n"
                f"Root Cause:\n"
                f"  - The except (IOError, OSError) handler is too narrow\n"
                f"  - KeyboardInterrupt inherits from BaseException, not Exception\n"
                f"  - Need try-finally block to guarantee cleanup\n\n"
                f"Fix:\n"
                f"  Add nested try-finally block after line 183:\n"
                f"  self.fd = open(self.lock_file, 'w')\n"
                f"  try:\n"
                f"      # locking operations\n"
                f"  finally:\n"
                f"      # cleanup on ANY exception"
            )

    def test_synclock_runtime_error_leaks_file_handle(self, tmp_path: Path):
        """
        E2E Test: SyncLock interrupted by RuntimeError also leaks file handle.

        This test verifies that not just KeyboardInterrupt, but ANY exception
        that's not IOError/OSError will cause the leak.

        User-facing scenario:
        - Unexpected errors during lock operations (memory issues, system errors)
        - Third-party library exceptions during file operations
        - System resource exhaustion
        """
        project_root = get_project_root()

        test_script = f'''
import sys
import json
import os
import fcntl

sys.path.insert(0, "{project_root}")

from pdd.sync_determine_operation import SyncLock

def check_open_lock_files():
    try:
        import psutil
        process = psutil.Process(os.getpid())
        lock_files = []
        for file in process.open_files():
            if file.path.endswith('.lock'):
                lock_files.append({{'path': file.path, 'fd': file.fd}})
        return lock_files
    except Exception:
        return []

def simulate_runtime_error_during_lock():
    """Simulate RuntimeError during lock acquisition."""
    original_flock = fcntl.flock

    def error_flock(fd, operation):
        raise RuntimeError("Unexpected system error")

    fcntl.flock = error_flock

    try:
        lock = SyncLock("test_error", "python")
        try:
            lock.acquire()
        except RuntimeError:
            pass  # Expected
    finally:
        fcntl.flock = original_flock

    return check_open_lock_files()

if __name__ == "__main__":
    leaked_locks = simulate_runtime_error_during_lock()
    result = {{
        "leaked_lock_count": len(leaked_locks),
        "leaked_files": leaked_locks,
        "bug_detected": len(leaked_locks) > 0
    }}
    print(json.dumps(result))
'''

        script_file = tmp_path / "test_error_leak.py"
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
                f"BUG DETECTED (Issue #403): File handle leaked after RuntimeError!\n\n"
                f"This confirms the bug affects ALL non-IOError/OSError exceptions,\n"
                f"not just KeyboardInterrupt.\n\n"
                f"Leaked files: {test_result['leaked_lock_count']}\n"
                f"Paths: {[f['path'] for f in test_result['leaked_files']]}\n\n"
                f"The exception handler must catch ALL exceptions to prevent leaks."
            )

    def test_synclock_normal_operation_no_leak(self, tmp_path: Path):
        """
        E2E Test: Normal SyncLock operation should NOT leak file handles.

        This is a regression test to ensure:
        1. Normal lock acquisition and release works correctly
        2. No file handles remain open after release
        3. The fix doesn't break existing functionality
        """
        project_root = get_project_root()

        test_script = f'''
import sys
import json
import os

sys.path.insert(0, "{project_root}")

from pdd.sync_determine_operation import SyncLock

def check_open_lock_files():
    try:
        import psutil
        process = psutil.Process(os.getpid())
        lock_files = []
        for file in process.open_files():
            if file.path.endswith('.lock'):
                lock_files.append({{'path': file.path, 'fd': file.fd}})
        return lock_files
    except Exception:
        return []

if __name__ == "__main__":
    # Normal operation: acquire and release
    lock = SyncLock("test_normal", "python")

    # Check before acquire
    before = check_open_lock_files()

    # Acquire lock
    lock.acquire()
    during = check_open_lock_files()

    # Release lock
    lock.release()
    after = check_open_lock_files()

    result = {{
        "before_count": len(before),
        "during_count": len(during),
        "after_count": len(after),
        "leak_detected": len(after) > 0
    }}
    print(json.dumps(result))
'''

        script_file = tmp_path / "test_normal.py"
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

        # Normal operation should NOT leak
        assert not test_result['leak_detected'], (
            f"File handle leaked during normal operation!\n"
            f"Before acquire: {test_result['before_count']} files\n"
            f"During lock: {test_result['during_count']} files\n"
            f"After release: {test_result['after_count']} files\n\n"
            f"Expected: after_count = 0\n"
            f"This is a regression - normal operation should not leak."
        )

        # Verify lock was actually held during acquisition
        assert test_result['during_count'] >= 1, (
            f"Lock file was not opened during acquisition!\n"
            f"Expected at least 1 .lock file open during lock hold,\n"
            f"but found {test_result['during_count']}"
        )

    def test_synclock_context_manager_interrupted_leaks(self, tmp_path: Path):
        """
        E2E Test: SyncLock context manager interrupted also leaks.

        This tests the __enter__/__exit__ path which calls acquire()/release().
        Even with context manager (which should guarantee cleanup), if acquire()
        is interrupted before completion, the file handle leaks.
        """
        project_root = get_project_root()

        test_script = f'''
import sys
import json
import os
import fcntl

sys.path.insert(0, "{project_root}")

from pdd.sync_determine_operation import SyncLock

def check_open_lock_files():
    try:
        import psutil
        process = psutil.Process(os.getpid())
        lock_files = []
        for file in process.open_files():
            if file.path.endswith('.lock'):
                lock_files.append({{'path': file.path, 'fd': file.fd}})
        return lock_files
    except Exception:
        return []

if __name__ == "__main__":
    # Patch fcntl.flock to raise KeyboardInterrupt
    original_flock = fcntl.flock
    fcntl.flock = lambda fd, op: (_ for _ in ()).throw(KeyboardInterrupt())

    try:
        # Use context manager (with statement)
        with SyncLock("test_ctx", "python"):
            pass  # Should never reach here
    except KeyboardInterrupt:
        pass  # Expected
    finally:
        fcntl.flock = original_flock

    # Check for leaked files
    leaked = check_open_lock_files()
    result = {{
        "leaked_count": len(leaked),
        "bug_detected": len(leaked) > 0
    }}
    print(json.dumps(result))
'''

        script_file = tmp_path / "test_ctx_leak.py"
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
                f"BUG DETECTED (Issue #403): Context manager doesn't prevent leak!\n\n"
                f"Even when using 'with SyncLock(...):' context manager,\n"
                f"KeyboardInterrupt during acquire() leaves file handle open.\n\n"
                f"Leaked files: {test_result['leaked_count']}\n\n"
                f"The bug is in acquire() itself - it must use try-finally\n"
                f"for cleanup, not rely on __exit__ which never gets called\n"
                f"if __enter__ (acquire) raises."
            )
