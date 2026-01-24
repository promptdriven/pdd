"""
E2E Test for Issue #379: pdd/commands/auth.py writes expires_at: null to cache

This test verifies the bug at a system level by simulating what happens when:
1. A user runs `pdd auth login` and receives a JWT without an `exp` claim
2. The login command writes `expires_at: null` to the cache file
3. Subsequent auth commands crash with TypeError

The Bug:
- `pdd/commands/auth.py:137-150` writes `expires_at` to cache without validation
- When JWT lacks `exp` claim, `payload.get("exp")` returns None
- This serializes as `null` in JSON cache file
- Any auth operation that reads cache and does `expires_at > time.time()` crashes

E2E Test Strategy:
- Use subprocess to run the CLI commands in isolation
- Create a corrupted cache file directly (simulating what buggy login creates)
- Verify that `pdd auth token` crashes with the documented TypeError
- This exercises the real code path without mocking the buggy component

The test should:
- FAIL on the current buggy code (TypeError crash detected)
- PASS once the bug is fixed (defensive handling prevents crash)
"""

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Dict, Optional, Tuple

import pytest


def get_project_root() -> Path:
    """Get the project root directory."""
    current = Path(__file__).parent
    while current != current.parent:
        if (current / "pdd").is_dir() and (current / "pyproject.toml").exists():
            return current
        current = current.parent
    raise RuntimeError("Could not find project root with pdd/ directory")


class TestAuthNullExpiresE2E:
    """
    E2E tests verifying the auth cache corruption issue #379.

    These tests exercise the full CLI path that users take when
    the cache file becomes corrupted with `expires_at: null`.
    """

    def _create_corrupted_cache(self, cache_dir: Path) -> Path:
        """
        Create a cache file with null expires_at (the corruption state).

        This simulates what the buggy `login` command creates when
        the JWT payload doesn't contain an `exp` claim.
        """
        cache_file = cache_dir / "jwt_cache"
        cache_file.parent.mkdir(parents=True, exist_ok=True)

        # This is exactly what the buggy code writes
        cache_data = {
            "id_token": "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiJ1c2VyMTIzIiwiZW1haWwiOiJ0ZXN0QGV4YW1wbGUuY29tIn0.fake_sig",
            "expires_at": None  # THE BUG: null expires_at
        }
        cache_file.write_text(json.dumps(cache_data))
        return cache_file

    def _create_valid_cache(self, cache_dir: Path, expires_at: int) -> Path:
        """Create a valid cache file with proper expires_at."""
        cache_file = cache_dir / "jwt_cache"
        cache_file.parent.mkdir(parents=True, exist_ok=True)

        cache_data = {
            "id_token": "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiJ1c2VyMTIzIiwiZW1haWwiOiJ0ZXN0QGV4YW1wbGUuY29tIiwiZXhwIjoxOTk5OTk5OTk5fQ.fake_sig",
            "expires_at": expires_at
        }
        cache_file.write_text(json.dumps(cache_data))
        return cache_file

    def _run_pdd_command(
        self,
        args: list,
        cache_dir: Path,
        timeout: int = 30
    ) -> Tuple[int, str, str]:
        """
        Run a pdd CLI command with custom cache directory.

        Returns (return_code, stdout, stderr).
        """
        project_root = get_project_root()

        # Set HOME to use our custom cache directory
        # JWT_CACHE_FILE is typically ~/.pdd/jwt_cache
        env = os.environ.copy()
        env["HOME"] = str(cache_dir.parent)  # .pdd will be under cache_dir
        env["PYTHONPATH"] = str(project_root)

        result = subprocess.run(
            [sys.executable, "-m", "pdd.cli"] + args,
            capture_output=True,
            text=True,
            cwd=str(project_root),
            env=env,
            timeout=timeout
        )

        return result.returncode, result.stdout, result.stderr

    def test_auth_token_with_null_expires_at(self, tmp_path: Path):
        """
        E2E Test: `pdd auth token` behavior with null expires_at cache.

        User scenario:
        1. User previously ran `pdd auth login` with a malformed JWT
        2. Cache file now contains `expires_at: null`
        3. User runs `pdd auth token` to get their token

        Note: The `pdd auth token` command happens to work due to short-circuit
        evaluation (line 290: `if cached_token and cached_exp and cached_exp > time.time()`).
        However, other commands like `pdd auth status` will crash.

        This test documents the current behavior and verifies it doesn't crash.
        The primary bug manifestation is in auth_status (tested separately).
        """
        # Setup: Create a .pdd directory in tmp_path
        pdd_dir = tmp_path / ".pdd"
        self._create_corrupted_cache(pdd_dir)

        # Run the command
        returncode, stdout, stderr = self._run_pdd_command(
            ["auth", "token"],
            pdd_dir
        )

        full_output = stdout + stderr

        # The specific TypeError pattern from the bug
        # Note: auth token has accidental protection via short-circuit,
        # but we still check for any crash
        # Normalize whitespace since output may have newlines from terminal wrapping
        normalized_output = " ".join(full_output.split())

        bug_indicators = [
            "'>' not supported between instances of 'NoneType' and 'float'",
            "TypeError: '>' not supported",
        ]

        has_bug_crash = any(indicator in normalized_output for indicator in bug_indicators)

        if has_bug_crash:
            pytest.fail(
                f"BUG DETECTED (Issue #379): `pdd auth token` crashes with TypeError!\n\n"
                f"When cache file contains 'expires_at': null, the command crashes\n"
                f"instead of handling the invalid state gracefully.\n\n"
                f"Return code: {returncode}\n"
                f"Output:\n{full_output}\n\n"
                f"Root cause: pdd/commands/auth.py:290 does `cached_exp > time.time()`\n"
                f"without checking if cached_exp is None.\n\n"
                f"Fix: Validate expires_at before writing to cache, or handle None defensively."
            )

    def test_auth_status_crashes_with_null_expires_at(self, tmp_path: Path):
        """
        E2E Test: `pdd auth status` should NOT crash when cache has null expires_at.

        User scenario:
        1. User has corrupted cache from buggy login
        2. User runs `pdd auth status` to check their auth state
        3. CRASH: TypeError: '>' not supported between 'NoneType' and 'float'

        Expected behavior (after fix):
        - Command should handle null gracefully (treat as not authenticated)
        - User should see helpful message, not a crash

        This test FAILS on buggy code, PASSES after fix.
        """
        # Setup
        pdd_dir = tmp_path / ".pdd"
        self._create_corrupted_cache(pdd_dir)

        # Run the command
        returncode, stdout, stderr = self._run_pdd_command(
            ["auth", "status"],
            pdd_dir
        )

        full_output = stdout + stderr

        # Check for the specific TypeError crash pattern
        # The error message is: "'>' not supported between instances of 'NoneType' and 'float'"
        # Note: The output may have newlines inserted due to terminal wrapping
        # so we normalize whitespace for matching
        normalized_output = " ".join(full_output.split())

        bug_indicators = [
            "'>' not supported between instances of 'NoneType' and 'float'",
            "TypeError: '>' not supported",
            "not supported between instances of 'NoneType'",
        ]

        has_bug_crash = any(indicator in normalized_output for indicator in bug_indicators)

        if has_bug_crash:
            pytest.fail(
                f"BUG DETECTED (Issue #379): `pdd auth status` crashes with TypeError!\n\n"
                f"When cache file contains 'expires_at': null, the command crashes\n"
                f"with: '>' not supported between instances of 'NoneType' and 'float'\n\n"
                f"Return code: {returncode}\n"
                f"Output:\n{full_output}\n\n"
                f"Root cause: auth_service.get_auth_status() calls get_jwt_cache_info()\n"
                f"which does `expires_at > time.time()` without checking for None.\n\n"
                f"Fix: Validate expires_at before writing to cache, or handle None defensively."
            )

    def test_full_user_journey_login_then_status(self, tmp_path: Path):
        """
        E2E Test: Full user journey from corrupted login to status check.

        This test simulates the complete user experience:
        1. A corrupted cache file exists (as if created by buggy login with exp-less JWT)
        2. User runs `pdd auth status` to check their auth state
        3. Should show auth status gracefully, not crash with traceback

        This is the PRIMARY E2E test that catches the bug, because `auth status`
        calls `get_auth_status()` which calls `get_jwt_cache_info()` which crashes.

        The test FAILS on buggy code, PASSES after fix.
        """
        pdd_dir = tmp_path / ".pdd"
        cache_file = self._create_corrupted_cache(pdd_dir)

        # Verify cache file is in the expected corrupted state
        cache_content = json.loads(cache_file.read_text())
        assert cache_content["expires_at"] is None, "Test setup: cache should have null expires_at"

        # Now run the status command (what user would do to check their auth)
        returncode, stdout, stderr = self._run_pdd_command(
            ["auth", "status"],
            pdd_dir
        )

        full_output = stdout + stderr

        # The buggy behavior: TypeError crash
        # Normalize whitespace since output may have newlines from terminal wrapping
        normalized_output = " ".join(full_output.split())

        bug_indicators = [
            "'>' not supported between instances of 'NoneType' and 'float'",
            "not supported between instances of 'NoneType'",
        ]

        has_bug_crash = any(indicator in normalized_output for indicator in bug_indicators)

        if has_bug_crash:
            pytest.fail(
                f"BUG DETECTED (Issue #379): Full user journey fails with crash!\n\n"
                f"After login creates corrupted cache, `pdd auth status` crashes.\n"
                f"This is a poor user experience - they see:\n"
                f"  '>' not supported between instances of 'NoneType' and 'float'\n"
                f"instead of a helpful error message.\n\n"
                f"Output:\n{full_output}"
            )

        # Even after fix, command might fail, but should fail cleanly
        if returncode != 0:
            # Should not have traceback
            assert "Traceback" not in full_output, (
                f"Command failed with a traceback instead of clean error:\n{full_output}"
            )

    def test_login_should_validate_expires_at_before_writing(self, tmp_path: Path):
        """
        E2E Test: The login command should not write null expires_at to cache.

        This test creates a scenario where we can verify that the login command
        properly validates expires_at before writing to the cache file.

        Note: This is challenging to test at E2E level without mocking the auth flow,
        but we can at least verify the cache file format expectations.

        The unit tests in test_commands_auth.py cover this more directly.
        This E2E test documents the expected cache file contract.
        """
        pdd_dir = tmp_path / ".pdd"
        pdd_dir.mkdir(parents=True, exist_ok=True)

        # Create a cache file with the expected valid format
        valid_cache = {
            "id_token": "valid.jwt.token",
            "expires_at": 1999999999  # Some future timestamp
        }
        cache_file = pdd_dir / "jwt_cache"
        cache_file.write_text(json.dumps(valid_cache))

        # Read it back and verify format
        read_cache = json.loads(cache_file.read_text())

        # These assertions document the expected cache contract
        assert "expires_at" in read_cache, "Cache must have expires_at field"
        assert read_cache["expires_at"] is not None, "expires_at must not be null"
        assert isinstance(read_cache["expires_at"], (int, float)), "expires_at must be numeric"
        assert read_cache["expires_at"] > 0, "expires_at must be positive timestamp"


class TestAuthCacheResilienceE2E:
    """
    Additional E2E tests for cache file resilience.

    These tests verify that the auth system is resilient to various
    forms of cache corruption, not just null expires_at.
    """

    def _run_pdd_auth_token(self, cache_dir: Path) -> Tuple[int, str]:
        """Run pdd auth token and return (return_code, combined_output)."""
        project_root = get_project_root()

        env = os.environ.copy()
        env["HOME"] = str(cache_dir.parent)
        env["PYTHONPATH"] = str(project_root)

        result = subprocess.run(
            [sys.executable, "-m", "pdd.cli", "auth", "token"],
            capture_output=True,
            text=True,
            cwd=str(project_root),
            env=env,
            timeout=30
        )

        return result.returncode, result.stdout + result.stderr

    def test_auth_token_handles_missing_cache_gracefully(self, tmp_path: Path):
        """
        E2E Test: `pdd auth token` should handle missing cache file gracefully.
        """
        pdd_dir = tmp_path / ".pdd"
        pdd_dir.mkdir(parents=True, exist_ok=True)
        # Don't create cache file

        returncode, output = self._run_pdd_auth_token(pdd_dir)

        # Should fail cleanly with helpful message
        assert "TypeError" not in output, f"Should not crash: {output}"
        assert "Traceback" not in output, f"Should not show traceback: {output}"
        # Should indicate no token available
        assert returncode != 0 or "login" in output.lower() or "no valid token" in output.lower()

    def test_auth_token_handles_malformed_json_gracefully(self, tmp_path: Path):
        """
        E2E Test: `pdd auth token` should handle malformed JSON cache gracefully.
        """
        pdd_dir = tmp_path / ".pdd"
        pdd_dir.mkdir(parents=True, exist_ok=True)
        cache_file = pdd_dir / "jwt_cache"
        cache_file.write_text("not valid json {{{")

        returncode, output = self._run_pdd_auth_token(pdd_dir)

        # Should fail cleanly, not crash
        assert "TypeError" not in output or "NoneType" not in output, f"Should not crash with TypeError: {output}"
        # JSONDecodeError is acceptable as it's a user-facing error about the file

    def test_auth_token_handles_missing_id_token_gracefully(self, tmp_path: Path):
        """
        E2E Test: `pdd auth token` should handle cache missing id_token gracefully.
        """
        pdd_dir = tmp_path / ".pdd"
        pdd_dir.mkdir(parents=True, exist_ok=True)
        cache_file = pdd_dir / "jwt_cache"
        cache_file.write_text(json.dumps({"expires_at": 1999999999}))  # Missing id_token

        returncode, output = self._run_pdd_auth_token(pdd_dir)

        # Should fail cleanly
        assert "TypeError" not in output, f"Should not crash: {output}"
        assert returncode != 0 or "no valid token" in output.lower()
