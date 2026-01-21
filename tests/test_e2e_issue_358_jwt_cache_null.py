"""
E2E Test for Issue #358: _get_cached_jwt() crashes with TypeError when cache file has expires_at: null

This test exercises the full CLI path from `pdd auth status` to verify that when the JWT cache
file contains `expires_at: null`, the command handles it gracefully instead of crashing.

The bug: When the JWT cache file (~/.pdd/jwt_cache) contains `{"id_token": "...", "expires_at": null}`,
the auth functions crash with `TypeError: '>' not supported between instances of 'NoneType' and 'float'`
because `dict.get('key', default)` returns None when the key exists with value None, not the default.

Bug locations:
- pdd/get_jwt_token.py:137-139 - _get_cached_jwt()
- pdd/auth_service.py:39-41 - get_jwt_cache_info()
- pdd/auth_service.py:62-64 - get_cached_jwt()

This E2E test:
1. Creates a corrupted JWT cache file with `expires_at: null`
2. Runs `pdd auth status` through Click's CliRunner
3. Verifies the command handles the corrupted cache gracefully

The test should FAIL on buggy code (TypeError crash) and PASS once the fix is applied.

Issue: https://github.com/promptdriven/pdd/issues/358
"""

import json
import pytest
from pathlib import Path
from unittest.mock import patch
from click.testing import CliRunner


class TestJWTCacheNullE2E:
    """
    E2E tests for Issue #358: Verify CLI commands handle corrupted JWT cache files
    with expires_at: null gracefully instead of crashing.
    """

    def test_pdd_auth_status_handles_expires_at_null(self, tmp_path, monkeypatch):
        """
        E2E Test: `pdd auth status` should not crash when JWT cache has expires_at: null

        This test runs the full CLI path and verifies that when the JWT cache file
        contains `expires_at: null`, the auth status command handles it gracefully
        instead of crashing with TypeError.

        Expected behavior (after fix):
        - Command should treat the corrupted cache as invalid/expired
        - Command should print "Not authenticated" or similar
        - Command should NOT crash with TypeError

        Bug behavior (Issue #358):
        - Command crashes with: TypeError: '>' not supported between instances of
          'NoneType' and 'float'
        - User sees an unhelpful traceback instead of a proper error message
        """
        # 1. Create mock home directory with corrupted JWT cache
        mock_pdd_dir = tmp_path / ".pdd"
        mock_pdd_dir.mkdir(parents=True, exist_ok=True)
        mock_jwt_cache = mock_pdd_dir / "jwt_cache"

        # Create corrupted cache file with expires_at: null
        # This is the exact scenario described in Issue #358
        corrupted_cache = {
            "id_token": "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiJ0ZXN0In0.test",
            "expires_at": None  # JSON null -> Python None - THIS TRIGGERS THE BUG
        }
        mock_jwt_cache.write_text(json.dumps(corrupted_cache))

        # 2. Patch the JWT_CACHE_FILE constant in auth_service to use our mock
        import pdd.auth_service as auth_service
        import pdd.get_jwt_token as get_jwt_token

        original_auth_cache = auth_service.JWT_CACHE_FILE
        original_jwt_cache = get_jwt_token.JWT_CACHE_FILE

        try:
            auth_service.JWT_CACHE_FILE = mock_jwt_cache
            get_jwt_token.JWT_CACHE_FILE = mock_jwt_cache

            # 3. Run the CLI command
            from pdd import cli

            runner = CliRunner()
            # catch_exceptions=False would let the TypeError propagate
            # We want to catch it to verify the bug exists
            result = runner.invoke(cli.cli, ["auth", "status"], catch_exceptions=True)

            # 4. THE KEY ASSERTIONS

            # If the bug exists, result.exception will be TypeError
            if result.exception:
                exception_type = type(result.exception).__name__
                exception_msg = str(result.exception)

                # Check if this is the specific bug we're looking for
                if exception_type == "TypeError" and "NoneType" in exception_msg and "float" in exception_msg:
                    pytest.fail(
                        f"BUG DETECTED (Issue #358): `pdd auth status` crashes with corrupted JWT cache!\n\n"
                        f"Exception: {exception_type}: {exception_msg}\n\n"
                        f"The JWT cache file contained: {corrupted_cache}\n\n"
                        f"Root cause: dict.get('expires_at', 0) returns None when the key exists\n"
                        f"with value null, causing comparison `None > float` to fail.\n\n"
                        f"Expected: Command should handle corrupted cache gracefully and\n"
                        f"either treat it as expired or print an informative error message.\n\n"
                        f"Full traceback:\n{result.output}"
                    )
                else:
                    # Some other exception occurred - might be expected (like missing auth)
                    # or might be a different bug
                    pass

            # If we get here without the TypeError, the bug is fixed
            # The command should indicate not authenticated (since cache is invalid)
            # or successfully handle the corrupted cache
            assert result.exit_code in (0, 1), (
                f"Unexpected exit code: {result.exit_code}\n"
                f"Output: {result.output}\n"
                f"Exception: {result.exception}"
            )

            # The output should contain either success message or auth prompt
            # but NOT a traceback
            output_lower = result.output.lower()
            assert "traceback" not in output_lower, (
                f"Command produced a traceback instead of handling error gracefully:\n"
                f"{result.output}"
            )

        finally:
            # Restore original paths
            auth_service.JWT_CACHE_FILE = original_auth_cache
            get_jwt_token.JWT_CACHE_FILE = original_jwt_cache

    def test_pdd_auth_status_handles_expires_at_string(self, tmp_path, monkeypatch):
        """
        E2E Test: `pdd auth status` should handle expires_at with string value gracefully.

        This tests another edge case where expires_at contains a non-numeric string,
        which would also cause a TypeError on comparison.
        """
        # 1. Create mock home directory with corrupted JWT cache
        mock_pdd_dir = tmp_path / ".pdd"
        mock_pdd_dir.mkdir(parents=True, exist_ok=True)
        mock_jwt_cache = mock_pdd_dir / "jwt_cache"

        # Create cache with string expires_at
        corrupted_cache = {
            "id_token": "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiJ0ZXN0In0.test",
            "expires_at": "not_a_timestamp"  # Non-numeric string
        }
        mock_jwt_cache.write_text(json.dumps(corrupted_cache))

        # 2. Patch the JWT_CACHE_FILE constant
        import pdd.auth_service as auth_service
        import pdd.get_jwt_token as get_jwt_token

        original_auth_cache = auth_service.JWT_CACHE_FILE
        original_jwt_cache = get_jwt_token.JWT_CACHE_FILE

        try:
            auth_service.JWT_CACHE_FILE = mock_jwt_cache
            get_jwt_token.JWT_CACHE_FILE = mock_jwt_cache

            # 3. Run the CLI command
            from pdd import cli

            runner = CliRunner()
            result = runner.invoke(cli.cli, ["auth", "status"], catch_exceptions=True)

            # 4. Check for TypeError
            if result.exception:
                exception_type = type(result.exception).__name__
                exception_msg = str(result.exception)

                if exception_type == "TypeError" and "'str'" in exception_msg and "float" in exception_msg:
                    pytest.fail(
                        f"BUG DETECTED (Issue #358): `pdd auth status` crashes with string expires_at!\n\n"
                        f"Exception: {exception_type}: {exception_msg}\n\n"
                        f"The JWT cache file contained: {corrupted_cache}\n\n"
                        f"Expected: Command should handle corrupted cache gracefully."
                    )

            # Verify no traceback in output
            assert "traceback" not in result.output.lower(), (
                f"Command produced a traceback:\n{result.output}"
            )

        finally:
            auth_service.JWT_CACHE_FILE = original_auth_cache
            get_jwt_token.JWT_CACHE_FILE = original_jwt_cache

    def test_pdd_auth_token_handles_expires_at_null(self, tmp_path, monkeypatch):
        """
        E2E Test: `pdd auth token` should handle expires_at: null gracefully.

        The `pdd auth token` command also reads the JWT cache and should not crash
        when encountering a corrupted cache file.
        """
        # 1. Create corrupted cache
        mock_pdd_dir = tmp_path / ".pdd"
        mock_pdd_dir.mkdir(parents=True, exist_ok=True)
        mock_jwt_cache = mock_pdd_dir / "jwt_cache"

        corrupted_cache = {
            "id_token": "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiJ0ZXN0In0.test",
            "expires_at": None
        }
        mock_jwt_cache.write_text(json.dumps(corrupted_cache))

        # 2. Patch
        import pdd.auth_service as auth_service
        import pdd.get_jwt_token as get_jwt_token

        original_auth_cache = auth_service.JWT_CACHE_FILE
        original_jwt_cache = get_jwt_token.JWT_CACHE_FILE

        try:
            auth_service.JWT_CACHE_FILE = mock_jwt_cache
            get_jwt_token.JWT_CACHE_FILE = mock_jwt_cache

            # 3. Run the command
            from pdd import cli

            runner = CliRunner()
            result = runner.invoke(cli.cli, ["auth", "token"], catch_exceptions=True)

            # 4. Check for TypeError (the bug)
            if result.exception:
                exception_type = type(result.exception).__name__
                exception_msg = str(result.exception)

                if exception_type == "TypeError" and "NoneType" in exception_msg:
                    pytest.fail(
                        f"BUG DETECTED (Issue #358): `pdd auth token` crashes!\n\n"
                        f"Exception: {exception_type}: {exception_msg}\n\n"
                        f"Cache: {corrupted_cache}"
                    )

            # The command should either:
            # - Print "No valid token available" (because expires_at is invalid)
            # - Exit cleanly without a traceback
            assert "traceback" not in result.output.lower()

        finally:
            auth_service.JWT_CACHE_FILE = original_auth_cache
            get_jwt_token.JWT_CACHE_FILE = original_jwt_cache


class TestJWTCacheNullDirectFunction:
    """
    More targeted E2E tests that call the auth functions directly but exercise
    the full code path without mocking the comparison logic.

    These tests verify the user-facing behavior through the public API.
    """

    def test_get_auth_status_with_expires_at_null_e2e(self, tmp_path):
        """
        E2E Test: get_auth_status() should not crash with expires_at: null

        This calls the auth_service function that would be called by CLI commands
        and other code paths that check authentication status.
        """
        import pdd.auth_service as auth_service

        # Set up corrupted cache
        mock_pdd_dir = tmp_path / ".pdd"
        mock_pdd_dir.mkdir(parents=True, exist_ok=True)
        mock_jwt_cache = mock_pdd_dir / "jwt_cache"

        corrupted_cache = {
            "id_token": "test_token",
            "expires_at": None  # The bug trigger
        }
        mock_jwt_cache.write_text(json.dumps(corrupted_cache))

        original_cache = auth_service.JWT_CACHE_FILE
        try:
            auth_service.JWT_CACHE_FILE = mock_jwt_cache

            # This should NOT raise TypeError
            # BUG: Currently raises TypeError: '>' not supported between
            # instances of 'NoneType' and 'float'
            try:
                status = auth_service.get_auth_status()

                # If we get here, the bug is fixed
                # With invalid expires_at, should report not authenticated
                # (or authenticated=False, cached=False)
                assert status is not None, "get_auth_status should return a dict"

            except TypeError as e:
                if "'NoneType'" in str(e) and "float" in str(e):
                    pytest.fail(
                        f"BUG DETECTED (Issue #358): get_auth_status() crashes!\n\n"
                        f"TypeError: {e}\n\n"
                        f"The JWT cache had expires_at: null which caused:\n"
                        f"  cache.get('expires_at', 0) -> None (not 0!)\n"
                        f"  None > time.time() + 300 -> TypeError"
                    )
                raise  # Re-raise if it's a different TypeError

        finally:
            auth_service.JWT_CACHE_FILE = original_cache

    def test_get_cached_jwt_from_auth_service_with_null_e2e(self, tmp_path):
        """
        E2E Test: get_cached_jwt() from auth_service should not crash with expires_at: null
        """
        import pdd.auth_service as auth_service

        mock_pdd_dir = tmp_path / ".pdd"
        mock_pdd_dir.mkdir(parents=True, exist_ok=True)
        mock_jwt_cache = mock_pdd_dir / "jwt_cache"

        corrupted_cache = {
            "id_token": "test_token",
            "expires_at": None
        }
        mock_jwt_cache.write_text(json.dumps(corrupted_cache))

        original_cache = auth_service.JWT_CACHE_FILE
        try:
            auth_service.JWT_CACHE_FILE = mock_jwt_cache

            try:
                token = auth_service.get_cached_jwt()

                # If we get here, bug is fixed
                # With invalid expires_at, should return None
                assert token is None, "Should return None for invalid cache"

            except TypeError as e:
                if "'NoneType'" in str(e) and "float" in str(e):
                    pytest.fail(
                        f"BUG DETECTED (Issue #358): get_cached_jwt() crashes!\n\n"
                        f"TypeError: {e}"
                    )
                raise

        finally:
            auth_service.JWT_CACHE_FILE = original_cache

    def test_get_cached_jwt_from_jwt_module_with_null_e2e(self, tmp_path):
        """
        E2E Test: _get_cached_jwt() from get_jwt_token module should not crash
        """
        import pdd.get_jwt_token as jwt_module

        mock_pdd_dir = tmp_path / ".pdd"
        mock_pdd_dir.mkdir(parents=True, exist_ok=True)
        mock_jwt_cache = mock_pdd_dir / "jwt_cache"

        corrupted_cache = {
            "id_token": "test_token",
            "expires_at": None
        }
        mock_jwt_cache.write_text(json.dumps(corrupted_cache))

        original_cache = jwt_module.JWT_CACHE_FILE
        try:
            jwt_module.JWT_CACHE_FILE = mock_jwt_cache

            try:
                from pdd.get_jwt_token import _get_cached_jwt
                token = _get_cached_jwt()

                # If we get here, bug is fixed
                assert token is None, "Should return None for invalid cache"

            except TypeError as e:
                if "'NoneType'" in str(e) and "float" in str(e):
                    pytest.fail(
                        f"BUG DETECTED (Issue #358): _get_cached_jwt() crashes!\n\n"
                        f"TypeError: {e}\n\n"
                        f"This is the primary bug location (pdd/get_jwt_token.py:137-139)"
                    )
                raise

        finally:
            jwt_module.JWT_CACHE_FILE = original_cache
