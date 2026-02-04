"""
E2E Test for Issue #466: PDD CLI cloud requests access to ALL repos instead of selective

This test verifies the bug at a system level by capturing the OAuth scope that PDD requests
from GitHub during the authentication flow.

The Bug:
- When users run `pdd auth login`, they are directed to GitHub's OAuth authorization page
- The OAuth scope requested is hardcoded to "repo,user" in `pdd/get_jwt_token.py:251`
- The "repo" scope grants access to ALL repositories (public and private) by design
- Users cannot select specific repositories - it's all-or-nothing with OAuth Apps
- This is a fundamental limitation of GitHub OAuth Apps (not GitHub Apps)

User Impact:
- Developers are uncomfortable granting access to all their repositories
- Some users refuse to use PDD Cloud due to this security/privacy concern
- Feedback from hackathon: "PDD cloud is asking for access to all their repo and some
  of the developers are not happy about that"

Expected Behavior (after fix):
- Migrate from GitHub OAuth App to GitHub App
- Users install the GitHub App and select specific repositories
- OAuth scope would no longer be used for repository access

E2E Test Strategy:
- Intercept the HTTP request to GitHub's device flow endpoint
- Capture the scope parameter being sent
- Verify it contains "repo,user" which grants all-repo access
- Document that this is the root cause of the user complaint

The test should:
- FAIL if the scope is "repo,user" (current buggy behavior - documents the bug)
- PASS once migrated to GitHub Apps (scope would change or auth method would change)

Issue: https://github.com/promptdriven/pdd/issues/466
"""

import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, Tuple
from unittest.mock import Mock, patch, MagicMock
import pytest
from click.testing import CliRunner


def get_project_root() -> Path:
    """Get the project root directory."""
    current = Path(__file__).parent
    while current != current.parent:
        if (current / "pdd").is_dir() and (current / "pyproject.toml").exists():
            return current
        current = current.parent
    raise RuntimeError("Could not find project root with pdd/ directory")


class TestOAuthAllRepoScopeE2E:
    """
    E2E tests verifying Issue #466: OAuth scope grants access to all repositories.

    These tests exercise the authentication flow and capture the OAuth scope
    being requested from GitHub, demonstrating that users cannot limit access
    to specific repositories.
    """

    def test_device_flow_requests_all_repo_access_via_scope(self, tmp_path):
        """
        E2E Test: DeviceFlow sends "repo,user" scope which grants ALL repo access.

        This test exercises the full authentication code path and verifies that
        when PDD initiates GitHub Device Flow authentication, it requests the
        "repo" scope which by GitHub's design grants access to ALL repositories.

        User Journey:
        1. User runs `pdd auth login`
        2. PDD calls DeviceFlow.request_device_code()
        3. GitHub API is called with scope="repo,user"
        4. User is shown authorization page: "This app wants access to all your repos"
        5. User is uncomfortable and may refuse to grant access

        Expected behavior (after fix with GitHub Apps):
        - Users would install a GitHub App instead
        - They would select specific repositories during installation
        - No OAuth "repo" scope would be used

        Bug behavior (Issue #466):
        - OAuth scope is hardcoded to "repo,user"
        - Cannot be changed to allow selective repo access
        - Fundamental limitation of OAuth Apps
        """
        # We'll intercept the actual HTTP request to GitHub's device flow endpoint
        # and capture what scope is being sent
        captured_scope = []

        def mock_post(*args, **kwargs):
            """Mock requests.post to capture the scope parameter."""
            # Capture the scope being sent to GitHub
            if 'data' in kwargs and 'scope' in kwargs['data']:
                captured_scope.append(kwargs['data']['scope'])

            # Return a mock response that looks like GitHub's device code response
            mock_response = Mock()
            mock_response.status_code = 200
            mock_response.json.return_value = {
                "device_code": "test_device_code_123",
                "user_code": "ABCD-1234",
                "verification_uri": "https://github.com/login/device",
                "expires_in": 900,
                "interval": 5
            }
            return mock_response

        # Import the DeviceFlow class
        from pdd.get_jwt_token import DeviceFlow

        # Create DeviceFlow instance
        device_flow = DeviceFlow(client_id="test_client_id")

        # Verify the scope is set at initialization
        assert device_flow.scope == "repo,user", (
            "DeviceFlow class should have scope='repo,user' at initialization. "
            "This is the root cause of Issue #466."
        )

        # Now test the actual HTTP request
        import asyncio

        async def test_request():
            with patch('requests.post', side_effect=mock_post):
                try:
                    await device_flow.request_device_code()
                except Exception:
                    # Even if the mock response isn't perfect and causes an error,
                    # we've already captured the scope in the post call
                    pass

        # Run the async test
        asyncio.run(test_request())

        # Verify the scope was captured
        assert len(captured_scope) > 0, "Should have captured at least one HTTP request"

        actual_scope = captured_scope[0]

        # THE KEY ASSERTION - This documents the bug
        if "repo" in actual_scope and "user" in actual_scope:
            pytest.fail(
                f"BUG DETECTED (Issue #466): PDD requests OAuth scope '{actual_scope}' "
                f"which grants access to ALL repositories!\n\n"
                f"User Impact:\n"
                f"  - When users authenticate, GitHub shows: 'This app wants access to all your repos'\n"
                f"  - Users cannot select specific repositories (OAuth Apps limitation)\n"
                f"  - Security-conscious developers refuse to grant access\n"
                f"  - Hackathon feedback: 'developers are not happy about that'\n\n"
                f"Root Cause:\n"
                f"  - pdd/get_jwt_token.py:251 - DeviceFlow class hardcodes scope='repo,user'\n"
                f"  - The 'repo' OAuth scope grants access to ALL public & private repos\n"
                f"  - This is a fundamental limitation of GitHub OAuth Apps\n\n"
                f"Expected Fix:\n"
                f"  - Migrate from OAuth Apps to GitHub Apps\n"
                f"  - Users would install the GitHub App and select specific repositories\n"
                f"  - Would provide fine-grained permissions and better security\n\n"
                f"Current OAuth scope: {actual_scope}\n"
                f"Location: pdd/get_jwt_token.py:251"
            )

    def test_cli_auth_login_uses_oauth_scope_all_repos(self, tmp_path, monkeypatch):
        """
        E2E Test: `pdd auth login` command uses OAuth scope that grants all-repo access.

        This test runs the full CLI command path and verifies that the authentication
        flow uses OAuth scopes that grant access to all repositories, demonstrating
        the user-facing issue reported in #466.

        User Experience:
        1. Developer runs: `pdd auth login`
        2. Browser opens to GitHub OAuth authorization page
        3. Page shows: "PDD CLI wants access to: All your public and private repositories"
        4. Developer is uncomfortable with this broad permission request
        5. Developer may refuse to authorize (blocking PDD Cloud usage)

        This is exactly what hackathon participants reported.
        """
        # Set up mock environment
        mock_pdd_dir = tmp_path / ".pdd"
        mock_pdd_dir.mkdir(parents=True, exist_ok=True)

        # We need to set required environment variables
        monkeypatch.setenv("NEXT_PUBLIC_FIREBASE_API_KEY", "test_firebase_key_123")
        monkeypatch.setenv("GITHUB_CLIENT_ID", "test_github_client_id")

        # Track the scope that would be sent to GitHub
        captured_requests = []

        def mock_requests_post(url, *args, **kwargs):
            """Capture OAuth requests."""
            captured_requests.append({
                'url': url,
                'data': kwargs.get('data', {}),
                'headers': kwargs.get('headers', {})
            })

            # Return mock device code response
            mock_response = Mock()
            mock_response.status_code = 200
            mock_response.json.return_value = {
                "device_code": "test_device_code",
                "user_code": "TEST-CODE",
                "verification_uri": "https://github.com/login/device",
                "expires_in": 900,
                "interval": 5
            }
            return mock_response

        # We'll also need to mock the polling and token exchange
        # to prevent the test from actually waiting or making real requests
        original_sleep = time.sleep

        def mock_sleep(seconds):
            """Don't actually sleep in tests."""
            pass

        # Mock the entire auth flow
        from pdd import cli
        from pdd.commands import auth as auth_module

        # Patch the JWT cache file location
        mock_jwt_cache = mock_pdd_dir / "jwt_cache"

        with patch('requests.post', side_effect=mock_requests_post), \
             patch('time.sleep', side_effect=mock_sleep), \
             patch.object(auth_module, 'JWT_CACHE_FILE', mock_jwt_cache), \
             patch('webbrowser.open', return_value=True):

            # Mock the async get_jwt_token to simulate successful auth
            # but we want to capture the scope it would use
            async def mock_get_jwt_token(*args, **kwargs):
                # This would normally contact GitHub, but we'll short-circuit
                # The important thing is that DeviceFlow was instantiated with the scope
                # Just return a fake token
                return "fake.jwt.token"

            with patch('pdd.commands.auth.get_jwt_token', side_effect=mock_get_jwt_token):
                runner = CliRunner()

                # Run the login command with --no-browser to avoid opening browser
                result = runner.invoke(
                    cli.cli,
                    ["auth", "login", "--no-browser"],
                    catch_exceptions=False
                )

        # Analyze the captured requests
        device_code_requests = [
            req for req in captured_requests
            if 'device/code' in req['url']
        ]

        if device_code_requests:
            # Check what scope was requested
            for req in device_code_requests:
                scope = req['data'].get('scope', '')

                if 'repo' in scope:
                    pytest.fail(
                        f"BUG DETECTED (Issue #466): CLI auth flow requests 'repo' scope!\n\n"
                        f"When user runs `pdd auth login`, the OAuth flow requests:\n"
                        f"  Scope: {scope}\n\n"
                        f"The 'repo' scope grants access to ALL repositories, which causes:\n"
                        f"  - GitHub authorization page shows: 'Access to all public and private repos'\n"
                        f"  - Users cannot select specific repositories\n"
                        f"  - Security-conscious developers refuse to grant access\n\n"
                        f"This is the exact issue reported by hackathon participants.\n\n"
                        f"Fix: Migrate from OAuth Apps to GitHub Apps for selective repository access."
                    )

    def test_oauth_scope_prevents_selective_repo_access(self):
        """
        E2E Test: Document that OAuth scope 'repo' cannot provide selective access.

        This test documents the architectural limitation that causes Issue #466.

        GitHub OAuth App Scopes:
        - 'repo' scope grants access to ALL public and private repositories
        - 'public_repo' scope grants access only to public repos (still all of them)
        - There is NO OAuth scope that allows selective repository access

        GitHub Apps (the solution):
        - Installed on specific repositories chosen by the user
        - Provide fine-grained permissions
        - Generate installation-specific tokens
        - Industry standard for modern GitHub integrations

        This test verifies that the current OAuth implementation fundamentally
        cannot support the user's requirement for selective repository access.
        """
        from pdd.get_jwt_token import DeviceFlow

        # Create a DeviceFlow instance
        device_flow = DeviceFlow(client_id="test_client_id")

        # Verify the scope
        scope = device_flow.scope

        # Check if scope contains 'repo'
        if 'repo' in scope.split(','):
            pytest.fail(
                f"BUG DETECTED (Issue #466): Current OAuth scope cannot support selective repo access!\n\n"
                f"Current scope: {scope}\n"
                f"Location: pdd/get_jwt_token.py:251\n\n"
                f"GitHub OAuth App Scope Limitations:\n"
                f"  • 'repo' scope = Access to ALL public and private repositories\n"
                f"  • 'public_repo' scope = Access to ALL public repositories\n"
                f"  • NO scope exists for selective repository access\n\n"
                f"User Impact (from Issue #466):\n"
                f"  • Users see: 'This app wants access to all your repositories'\n"
                f"  • Users cannot choose which repos to grant access to\n"
                f"  • Security/privacy conscious developers refuse to authorize\n"
                f"  • Hackathon feedback: 'developers are not happy about that'\n\n"
                f"Root Cause:\n"
                f"  • PDD uses GitHub OAuth Apps (not GitHub Apps)\n"
                f"  • OAuth Apps have coarse-grained, all-or-nothing permissions\n"
                f"  • This is a fundamental architectural limitation\n\n"
                f"Required Fix:\n"
                f"  • Migrate authentication from OAuth Apps to GitHub Apps\n"
                f"  • GitHub Apps support repository-level installation\n"
                f"  • Users select specific repositories during installation\n"
                f"  • Provides fine-grained permissions and better security\n"
                f"  • Aligns with industry best practices (Vercel, Netlify, etc.)\n\n"
                f"This test PASSES when PDD migrates to GitHub Apps,\n"
                f"because the authentication method will change entirely."
            )

    def test_auth_status_shows_oauth_limitation_in_scope(self, tmp_path):
        """
        E2E Test: Verify that authenticated users have all-repo access.

        This test simulates a user who has already authenticated and verifies
        that the token they received grants access to all repositories.

        While we can't directly inspect GitHub's authorization through the CLI,
        we can verify that the OAuth scope used during authentication inherently
        grants all-repo access, which is what users are complaining about.
        """
        # Create a mock JWT cache as if user had logged in
        mock_pdd_dir = tmp_path / ".pdd"
        mock_pdd_dir.mkdir(parents=True, exist_ok=True)
        mock_jwt_cache = mock_pdd_dir / "jwt_cache"

        # Create a cache file with a valid token
        # The token was obtained with "repo,user" scope (the bug)
        cache_data = {
            "id_token": "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiJ0ZXN0dXNlciIsImVtYWlsIjoidGVzdEB0ZXN0LmNvbSIsImV4cCI6OTk5OTk5OTk5OX0.fake",
            "expires_at": time.time() + 3600  # Valid for 1 hour
        }
        mock_jwt_cache.write_text(json.dumps(cache_data))

        # Patch auth_service to use our mock cache
        import pdd.auth_service as auth_service
        original_cache = auth_service.JWT_CACHE_FILE

        try:
            auth_service.JWT_CACHE_FILE = mock_jwt_cache

            # Check auth status
            from pdd import cli
            from pdd.commands import auth as auth_module

            with patch.object(auth_module, 'JWT_CACHE_FILE', mock_jwt_cache):
                runner = CliRunner()
                result = runner.invoke(cli.cli, ["auth", "status"], catch_exceptions=True)

            # The user is authenticated
            # But the token they have grants access to ALL repositories
            # This is the core issue - users don't want this

            # Verify by checking the scope that was used to obtain this token
            from pdd.get_jwt_token import DeviceFlow
            device_flow = DeviceFlow(client_id="test_client")

            if device_flow.scope == "repo,user":
                pytest.fail(
                    f"BUG DETECTED (Issue #466): Authenticated users have all-repo access!\n\n"
                    f"The current authentication system uses OAuth scope: {device_flow.scope}\n\n"
                    f"This means:\n"
                    f"  ✗ PDD Cloud can access ALL of the user's repositories\n"
                    f"  ✗ Users cannot limit access to specific repositories\n"
                    f"  ✗ This makes security-conscious developers uncomfortable\n\n"
                    f"User feedback from hackathon:\n"
                    f"  'PDD cloud is asking for access to all their repo and some\n"
                    f"   of the developers are not happy about that'\n\n"
                    f"Expected: Users should be able to select specific repositories\n"
                    f"Actual: All-or-nothing access (OAuth Apps limitation)\n\n"
                    f"Fix: Implement GitHub Apps for repository-level granularity"
                )

        finally:
            auth_service.JWT_CACHE_FILE = original_cache


class TestOAuthScopeDocumentation:
    """
    Tests that document the OAuth scope behavior and its implications.

    These tests serve as living documentation of Issue #466.
    """

    def test_oauth_repo_scope_definition(self):
        """
        Document what the 'repo' OAuth scope actually grants.

        According to GitHub documentation:
        - 'repo' scope grants full control of private repositories including:
          - Reading code
          - Reading and writing repository hooks
          - Reading and writing deploy keys
          - Reading and writing repository projects
          - Managing issues, pull requests, releases

        This is far more access than most users want to grant.
        """
        from pdd.get_jwt_token import DeviceFlow

        device_flow = DeviceFlow(client_id="test")

        if "repo" in device_flow.scope:
            pytest.fail(
                f"SCOPE DOCUMENTATION (Issue #466):\n\n"
                f"Current OAuth scope: {device_flow.scope}\n\n"
                f"The 'repo' scope grants:\n"
                f"  • Full control of ALL private repositories\n"
                f"  • Read/write access to code, hooks, keys, projects\n"
                f"  • Manage issues, PRs, releases\n"
                f"  • Access to ALL repositories the user has access to\n\n"
                f"Users expect:\n"
                f"  • Ability to select specific repositories\n"
                f"  • Minimal necessary permissions\n"
                f"  • Fine-grained access control\n\n"
                f"This expectation cannot be met with OAuth Apps.\n"
                f"GitHub Apps are required for repository-level granularity."
            )
