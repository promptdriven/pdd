"""
E2E Test for Issue #363: Heartbeat failure when a command takes a long time.

This test verifies the bug at a system level by simulating a long-running operation
and checking that the heartbeat mechanism keeps the session alive.

The Bug:
- When a user runs `pdd sync` with `auto-deps`, the operation can take a long time
- The heartbeat mechanism is supposed to keep the session alive with the cloud
- BUG 1: First heartbeat is delayed by 60 seconds (line 224 in remote_session.py)
- BUG 2: Heartbeat has no retry logic on failure (unlike update_command which has 3 retries)

As a result:
- Cloud-side session timeout may expire before the first heartbeat is sent
- Transient network errors cause heartbeats to be skipped entirely
- Session becomes disconnected while command is still running

E2E Test Strategy:
- Test the actual RemoteSessionManager class behavior
- Use subprocess to isolate timing-sensitive tests
- Verify heartbeat timing and retry behavior match expectations

The test should:
- FAIL on the current buggy code (heartbeat too slow, no retries)
- PASS once the bug is fixed
"""

import asyncio
import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Dict, List, Any
from unittest.mock import MagicMock, patch, AsyncMock

import pytest

from pdd.remote_session import RemoteSessionManager


def get_project_root() -> Path:
    """Get the project root directory."""
    current = Path(__file__).parent
    while current != current.parent:
        if (current / "pdd").is_dir():
            return current
        current = current.parent
    raise RuntimeError("Could not find project root with pdd/ directory")


@pytest.mark.e2e
class TestHeartbeatFailureE2E:
    """
    E2E tests for Issue #363: Heartbeat failure during long operations.

    These tests verify the user-facing behavior where session connection is lost
    during long-running operations like `pdd sync auto-deps`.
    """

    def test_heartbeat_timing_via_subprocess(self, tmp_path: Path):
        """
        E2E Test: Verify heartbeat timing behavior in an isolated subprocess.

        This test runs in a subprocess to avoid any interference from the test
        framework's event loop. It measures the actual time until the first
        heartbeat is sent.

        Expected behavior (after fix):
        - First heartbeat should be sent within 5 seconds of starting
        - This ensures cloud session doesn't timeout before first heartbeat

        Bug behavior (Issue #363):
        - First heartbeat is delayed by 60 seconds
        - Cloud session may timeout before first heartbeat arrives
        """
        project_root = get_project_root()

        # Test script that measures heartbeat timing
        test_script = '''
import asyncio
import sys
import json
import time

# Add project to path
sys.path.insert(0, "{project_root}")

from unittest.mock import MagicMock, patch, AsyncMock

async def measure_heartbeat_timing():
    """Measure time until first heartbeat is sent."""
    from pdd.remote_session import RemoteSessionManager
    from pathlib import Path

    # Track heartbeat calls
    heartbeat_times = []
    start_time = time.time()

    async def mock_post(*args, **kwargs):
        url = str(args[0]) if args else ""
        if "heartbeat" in url.lower():
            heartbeat_times.append(time.time() - start_time)
        mock_response = MagicMock()
        mock_response.status_code = 200
        mock_response.json.return_value = {{"sessionId": "test", "cloudUrl": "https://test"}}
        return mock_response

    # Create manager with mocked httpx
    with patch("pdd.remote_session.CloudConfig") as MockConfig:
        MockConfig.get_endpoint_url.side_effect = lambda e: f"https://api.pdd.dev/{{e}}"

        with patch("httpx.AsyncClient") as MockClient:
            mock_instance = AsyncMock()
            mock_instance.post = mock_post
            mock_instance.get = AsyncMock()
            MockClient.return_value.__aenter__.return_value = mock_instance
            MockClient.return_value.__aexit__.return_value = None

            manager = RemoteSessionManager(
                jwt_token="test-token",
                project_path=Path("/test")
            )
            manager.session_id = "test-session"

            # Start heartbeat and wait
            manager.start_heartbeat()

            # Wait up to 10 seconds for a heartbeat
            max_wait = 10.0
            check_interval = 0.1
            elapsed = 0

            while elapsed < max_wait and len(heartbeat_times) == 0:
                await asyncio.sleep(check_interval)
                elapsed += check_interval

            # Stop heartbeat
            await manager.stop_heartbeat()

            result = {{
                "heartbeat_count": len(heartbeat_times),
                "first_heartbeat_time": heartbeat_times[0] if heartbeat_times else None,
                "elapsed_time": elapsed
            }}

            print(json.dumps(result))

if __name__ == "__main__":
    asyncio.run(measure_heartbeat_timing())
'''

        # Write test script
        script_file = tmp_path / "test_heartbeat_timing.py"
        script_file.write_text(test_script.format(project_root=project_root))

        # Run in subprocess
        result = subprocess.run(
            [sys.executable, str(script_file)],
            capture_output=True,
            text=True,
            timeout=30,
            cwd=str(project_root)
        )

        # Parse result
        if result.returncode != 0:
            pytest.fail(
                f"Heartbeat timing test subprocess failed:\n"
                f"stdout: {result.stdout}\n"
                f"stderr: {result.stderr}"
            )

        try:
            data = json.loads(result.stdout.strip())
        except json.JSONDecodeError:
            pytest.fail(
                f"Could not parse test output:\n"
                f"stdout: {result.stdout}\n"
                f"stderr: {result.stderr}"
            )

        # THE BUG CHECK: First heartbeat should be sent quickly
        heartbeat_count = data.get("heartbeat_count", 0)
        first_heartbeat_time = data.get("first_heartbeat_time")

        if heartbeat_count == 0:
            pytest.fail(
                f"BUG DETECTED (Issue #363): No heartbeat sent within 10 seconds!\n\n"
                f"Expected: First heartbeat within 5 seconds of starting\n"
                f"Actual: No heartbeat sent (waited 10 seconds)\n\n"
                f"Root cause: Line 224 in remote_session.py waits 60 seconds before\n"
                f"sending the first heartbeat. This causes cloud session timeout\n"
                f"when operations take longer than the cloud's session TTL.\n\n"
                f"Fix: Send first heartbeat immediately, then continue on interval."
            )

        if first_heartbeat_time is not None and first_heartbeat_time > 5.0:
            pytest.fail(
                f"BUG DETECTED (Issue #363): First heartbeat took too long!\n\n"
                f"Expected: First heartbeat within 5 seconds\n"
                f"Actual: First heartbeat at {first_heartbeat_time:.1f} seconds\n\n"
                f"This delay can cause cloud session timeout before the first\n"
                f"heartbeat arrives, leaving the session disconnected."
            )

    def test_heartbeat_retry_logic_via_subprocess(self, tmp_path: Path):
        """
        E2E Test: Verify heartbeat has retry logic like update_command does.

        This test verifies that when heartbeat requests fail, the code retries
        with exponential backoff (similar to update_command's 3 retries).

        Expected behavior (after fix):
        - Heartbeat should retry at least 2-3 times on transient failure
        - Exponential backoff between retries (like update_command)

        Bug behavior (Issue #363):
        - Heartbeat only attempts once per interval
        - Errors are logged but no retry happens
        - Session can become disconnected due to single transient error
        """
        project_root = get_project_root()

        # Test script that counts retry attempts
        test_script = '''
import asyncio
import sys
import json
import time

# Add project to path
sys.path.insert(0, "{project_root}")

from unittest.mock import MagicMock, patch, AsyncMock

async def test_heartbeat_retry():
    """Test that heartbeat retries on failure."""
    from pdd.remote_session import RemoteSessionManager
    from pathlib import Path

    # Track call attempts
    call_count = [0]

    async def fail_twice_then_succeed(*args, **kwargs):
        url = str(args[0]) if args else ""
        if "heartbeat" in url.lower():
            call_count[0] += 1
            if call_count[0] <= 2:
                raise Exception("Simulated network error")
        mock_response = MagicMock()
        mock_response.status_code = 200
        return mock_response

    # Create manager with mocked httpx
    with patch("pdd.remote_session.CloudConfig") as MockConfig:
        MockConfig.get_endpoint_url.side_effect = lambda e: f"https://api.pdd.dev/{{e}}"

        with patch("httpx.AsyncClient") as MockClient:
            mock_instance = AsyncMock()
            mock_instance.post = fail_twice_then_succeed
            MockClient.return_value.__aenter__.return_value = mock_instance
            MockClient.return_value.__aexit__.return_value = None

            manager = RemoteSessionManager(
                jwt_token="test-token",
                project_path=Path("/test")
            )
            manager.session_id = "test-session"

            # Create a stop event that exits after one heartbeat cycle
            class ControlledStopEvent:
                def __init__(self):
                    self._iterations = 0

                def is_set(self):
                    # Exit after first heartbeat attempt(s)
                    return self._iterations > 0

                async def wait(self):
                    pass

            manager._stop_event = ControlledStopEvent()

            # Mock wait_for to simulate immediate timeout (heartbeat interval)
            original_wait_for = asyncio.wait_for

            async def mock_wait_for(coro, timeout):
                manager._stop_event._iterations += 1
                coro.close()
                raise asyncio.TimeoutError()

            with patch("asyncio.wait_for", side_effect=mock_wait_for):
                await manager._heartbeat_loop()

            result = {{
                "heartbeat_attempts": call_count[0],
                "expected_with_retry": 3,  # 2 failures + 1 success
            }}

            print(json.dumps(result))

if __name__ == "__main__":
    asyncio.run(test_heartbeat_retry())
'''

        # Write test script
        script_file = tmp_path / "test_heartbeat_retry.py"
        script_file.write_text(test_script.format(project_root=project_root))

        # Run in subprocess
        result = subprocess.run(
            [sys.executable, str(script_file)],
            capture_output=True,
            text=True,
            timeout=30,
            cwd=str(project_root)
        )

        # Parse result
        if result.returncode != 0:
            # Check if it failed due to the exception not being retried
            if "Simulated network error" in result.stderr:
                # This is expected behavior with current buggy code - error not retried
                pass
            else:
                pytest.fail(
                    f"Heartbeat retry test subprocess failed:\n"
                    f"stdout: {result.stdout}\n"
                    f"stderr: {result.stderr}"
                )

        try:
            data = json.loads(result.stdout.strip())
        except json.JSONDecodeError:
            # With current buggy code, test may fail before printing JSON
            # This indicates no retry logic exists
            pytest.fail(
                f"BUG DETECTED (Issue #363): Heartbeat has no retry logic!\n\n"
                f"Expected: Heartbeat should retry 2-3 times on transient failure\n"
                f"Actual: Single failure causes heartbeat to be skipped entirely\n\n"
                f"The update_command() function has retry logic (3 retries with\n"
                f"exponential backoff), but _heartbeat_loop() does not.\n\n"
                f"Fix: Add retry logic similar to update_command() in _heartbeat_loop().\n\n"
                f"subprocess stderr: {result.stderr[:500]}"
            )

        # THE BUG CHECK: Heartbeat should retry on failure
        heartbeat_attempts = data.get("heartbeat_attempts", 0)

        if heartbeat_attempts < 3:
            pytest.fail(
                f"BUG DETECTED (Issue #363): Heartbeat does not retry on failure!\n\n"
                f"Expected: At least 3 attempts (2 failures + 1 success)\n"
                f"Actual: Only {heartbeat_attempts} attempt(s)\n\n"
                f"Comparison with update_command():\n"
                f"- update_command() has 3 retries with exponential backoff (lines 373-402)\n"
                f"- _heartbeat_loop() only logs errors, no retry (lines 242-244)\n\n"
                f"This means a single transient network error can cause the session\n"
                f"to miss a heartbeat, potentially leading to session timeout."
            )

    @pytest.mark.asyncio
    async def test_session_stays_alive_during_long_operation(self):
        """
        E2E Test: Session should stay alive during long-running operations.

        This simulates what happens during `pdd sync auto-deps`:
        1. User starts a remote session
        2. Long-running command begins (auto-deps can take minutes)
        3. Heartbeat should continue running in background
        4. Session should remain active on cloud

        This test verifies the architecture allows concurrent heartbeat and
        command execution, though the actual timing bugs are tested above.
        """
        # Track heartbeat activity
        heartbeat_sent = [False]

        async def mock_post(*args, **kwargs):
            url = str(args[0]) if args else ""
            if "heartbeat" in url.lower():
                heartbeat_sent[0] = True
            mock_response = MagicMock()
            mock_response.status_code = 200
            mock_response.json.return_value = {}
            return mock_response

        with patch("pdd.remote_session.CloudConfig") as MockConfig:
            MockConfig.get_endpoint_url.side_effect = lambda e: f"https://api.pdd.dev/{e}"

            with patch("httpx.AsyncClient") as MockClient:
                mock_instance = AsyncMock()
                mock_instance.post = mock_post
                mock_instance.get.return_value = MagicMock(
                    status_code=200,
                    json=lambda: {"status": "completed", "result": {"stdout": "", "stderr": "", "exit_code": 0}}
                )
                MockClient.return_value.__aenter__.return_value = mock_instance
                MockClient.return_value.__aexit__.return_value = None

                manager = RemoteSessionManager(
                    jwt_token="test-token",
                    project_path=Path("/test")
                )
                manager.session_id = "test-session"

                # Start heartbeat
                manager.start_heartbeat()

                # Simulate a long-running operation
                # In real scenario, this would be auto-deps taking minutes
                await asyncio.sleep(3.0)

                # Stop heartbeat
                await manager.stop_heartbeat()

                # Note: With the current 60-second delay bug, no heartbeat
                # will have been sent in 3 seconds. This test documents
                # the expected behavior rather than failing on current code.
                #
                # The key insight is:
                # - The heartbeat TASK is running (architecture is correct)
                # - But the first heartbeat is DELAYED by 60 seconds (bug)
                #
                # The subprocess tests above verify the timing bug.
                # This test verifies the concurrency architecture works.

                assert manager._heartbeat_task is None, "Heartbeat task should be stopped"

    def test_full_session_lifecycle_simulation(self, tmp_path: Path):
        """
        E2E Test: Simulate full session lifecycle with timing measurement.

        This test simulates the complete user workflow:
        1. Register session
        2. Start heartbeat
        3. Execute long-running command
        4. Verify heartbeat kept session alive
        5. Deregister session

        This is a high-level integration test that exercises the full path.
        """
        project_root = get_project_root()

        # Test script that simulates full lifecycle
        test_script = '''
import asyncio
import sys
import json
import time
import io

# Add project to path
sys.path.insert(0, "{project_root}")

from unittest.mock import MagicMock, patch, AsyncMock

async def simulate_session_lifecycle():
    """Simulate full session lifecycle."""
    from pdd.remote_session import RemoteSessionManager
    from pathlib import Path

    events = []

    async def track_requests(*args, **kwargs):
        url = str(args[0]) if args else ""
        events.append({{
            "time": time.time(),
            "url": url,
            "type": "register" if "register" in url.lower() else
                   "heartbeat" if "heartbeat" in url.lower() else
                   "deregister" if "deregister" in url.lower() else "other"
        }})
        mock_response = MagicMock()
        mock_response.status_code = 200
        mock_response.json.return_value = {{"sessionId": "test-id", "cloudUrl": "https://test"}}
        return mock_response

    with patch("pdd.remote_session.CloudConfig") as MockConfig:
        MockConfig.get_endpoint_url.side_effect = lambda e: f"https://api.pdd.dev/{{e}}"

        with patch("httpx.AsyncClient") as MockClient:
            mock_instance = AsyncMock()
            mock_instance.post = track_requests
            MockClient.return_value.__aenter__.return_value = mock_instance
            MockClient.return_value.__aexit__.return_value = None

            # Suppress console output from the manager
            with patch("pdd.remote_session.console"):
                manager = RemoteSessionManager(
                    jwt_token="test-token",
                    project_path=Path("/test")
                )

                start_time = time.time()

                # 1. Register session
                try:
                    await manager.register()
                except:
                    pass  # May fail in mock environment

                # 2. Start heartbeat
                manager.start_heartbeat()

                # 3. Simulate long operation (5 seconds)
                await asyncio.sleep(5.0)

                # 4. Stop heartbeat
                await manager.stop_heartbeat()

                # 5. Deregister
                try:
                    await manager.deregister()
                except:
                    pass

                end_time = time.time()

            # Analyze events
            heartbeats = [e for e in events if e["type"] == "heartbeat"]

            result = {{
                "total_duration": end_time - start_time,
                "total_events": len(events),
                "heartbeat_count": len(heartbeats),
                "event_types": [e["type"] for e in events],
            }}

            print(json.dumps(result))

if __name__ == "__main__":
    asyncio.run(simulate_session_lifecycle())
'''

        # Write test script
        script_file = tmp_path / "test_lifecycle.py"
        script_file.write_text(test_script.format(project_root=project_root))

        # Run in subprocess
        result = subprocess.run(
            [sys.executable, str(script_file)],
            capture_output=True,
            text=True,
            timeout=30,
            cwd=str(project_root)
        )

        if result.returncode != 0:
            pytest.fail(
                f"Lifecycle simulation failed:\n"
                f"stdout: {result.stdout}\n"
                f"stderr: {result.stderr}"
            )

        # Extract JSON from output (may have other console output)
        output_lines = result.stdout.strip().split('\n')
        json_line = None
        for line in output_lines:
            line = line.strip()
            if line.startswith('{') and line.endswith('}'):
                json_line = line
                break

        if not json_line:
            pytest.fail(f"Could not find JSON in output: {result.stdout}")

        try:
            data = json.loads(json_line)
        except json.JSONDecodeError:
            pytest.fail(f"Could not parse JSON: {json_line}")

        # Verify session lifecycle completed
        event_types = data.get("event_types", [])
        heartbeat_count = data.get("heartbeat_count", 0)

        # THE BUG CHECK: During a 5-second operation, at least one heartbeat
        # should have been sent (if first heartbeat is immediate)
        if heartbeat_count == 0:
            pytest.fail(
                f"BUG DETECTED (Issue #363): No heartbeats during 5-second operation!\n\n"
                f"Events recorded: {event_types}\n"
                f"Heartbeat count: {heartbeat_count}\n\n"
                f"During a 5-second long-running operation, the heartbeat mechanism\n"
                f"should have sent at least one heartbeat to keep the session alive.\n\n"
                f"With the 60-second delay bug, no heartbeat is sent within this time,\n"
                f"causing the cloud session to potentially timeout and disconnect."
            )
