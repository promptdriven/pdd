import json
import os
import sys
import time
from pathlib import Path
from unittest.mock import MagicMock, patch, AsyncMock

import pytest
from click.testing import CliRunner
from rich.console import Console

# Import the module under test
# We need to adjust sys.path or use relative imports depending on how tests are run.
# Assuming standard structure where we can import pdd.commands.auth
try:
    from pdd.commands.auth import auth_group, _decode_jwt_payload, _load_firebase_api_key
except ImportError:
    # Fallback or mock for environment where pdd is not installed
    auth_group = MagicMock()
    _decode_jwt_payload = MagicMock()
    _load_firebase_api_key = MagicMock()

# Mock exceptions from get_jwt_token since we can't import them if the file doesn't exist in test env
class MockAuthError(Exception): pass
class MockNetworkError(Exception): pass
class MockTokenError(Exception): pass
class MockUserCancelledError(Exception): pass
class MockRateLimitError(Exception): pass

@pytest.fixture(autouse=True)
def mock_console():
    """
    Patch the rich console to disable color and highlighting for easier assertions.
    This ensures that console.print() outputs plain text without ANSI codes.
    """
    test_console = Console(force_terminal=False, no_color=True, highlight=False, width=1000)
    with patch("pdd.commands.auth.console", test_console):
        yield test_console

@pytest.fixture
def mock_dependencies():
    """
    Fixture to mock all external dependencies of the auth module.
    This is critical for isolation.
    """
    with patch("pdd.commands.auth.get_jwt_token", new_callable=AsyncMock) as mock_get_token, \
         patch("pdd.commands.auth.get_auth_status") as mock_status, \
         patch("pdd.commands.auth.service_logout") as mock_logout, \
         patch("pdd.commands.auth.JWT_CACHE_FILE", new_callable=MagicMock) as mock_cache_file, \
         patch("pdd.commands.auth.AuthError", MockAuthError), \
         patch("pdd.commands.auth.NetworkError", MockNetworkError), \
         patch("pdd.commands.auth.TokenError", MockTokenError), \
         patch("pdd.commands.auth.UserCancelledError", MockUserCancelledError), \
         patch("pdd.commands.auth.RateLimitError", MockRateLimitError):
        
        # Setup default behaviors
        mock_cache_file.parent.exists.return_value = True
        mock_cache_file.exists.return_value = False
        
        yield {
            "get_jwt_token": mock_get_token,
            "get_auth_status": mock_status,
            "service_logout": mock_logout,
            "JWT_CACHE_FILE": mock_cache_file
        }

@pytest.fixture
def runner():
    return CliRunner()

@pytest.fixture
def mock_env_vars(monkeypatch):
    """Clear relevant env vars to ensure clean state."""
    monkeypatch.delenv("NEXT_PUBLIC_FIREBASE_API_KEY", raising=False)
    monkeypatch.delenv("GITHUB_CLIENT_ID", raising=False)
    monkeypatch.delenv("GITHUB_CLIENT_ID_LOCAL", raising=False)
    monkeypatch.delenv("PDD_ENV", raising=False)

# --- Helper Function Tests ---

def test_decode_jwt_payload_valid():
    """Test decoding a valid JWT payload part."""
    # {"sub": "1234567890", "name": "John Doe", "iat": 1516239022}
    # Base64Url encoded: eyJzdWIiOiIxMjM0NTY3ODkwIiwibmFtZSI6IkpvaG4gRG9lIiwiaWF0IjoxNTE2MjM5MDIyfQ
    token = "header.eyJzdWIiOiIxMjM0NTY3ODkwIiwibmFtZSI6IkpvaG4gRG9lIiwiaWF0IjoxNTE2MjM5MDIyfQ.signature"
    payload = _decode_jwt_payload(token)
    assert payload["sub"] == "1234567890"
    assert payload["name"] == "John Doe"

def test_decode_jwt_payload_invalid_format():
    """Test decoding a malformed token."""
    assert _decode_jwt_payload("not.a.valid.token") == {}
    assert _decode_jwt_payload("short") == {}

def test_load_firebase_api_key_env(monkeypatch):
    """Test loading API key from environment variable."""
    monkeypatch.setenv("NEXT_PUBLIC_FIREBASE_API_KEY", "env-key")
    assert _load_firebase_api_key() == "env-key"

def test_load_firebase_api_key_file(monkeypatch, tmp_path):
    """Test loading API key from .env file."""
    # Ensure env var doesn't interfere
    monkeypatch.delenv("NEXT_PUBLIC_FIREBASE_API_KEY", raising=False)
    
    monkeypatch.chdir(tmp_path)
    env_file = tmp_path / ".env"
    env_file.write_text('NEXT_PUBLIC_FIREBASE_API_KEY="file-key"', encoding="utf-8")
    
    assert _load_firebase_api_key() == "file-key"

# --- Login Command Tests ---

def test_login_success(runner, mock_dependencies, monkeypatch):
    """Test successful login flow."""
    monkeypatch.setenv("NEXT_PUBLIC_FIREBASE_API_KEY", "test-api-key")
    
    # Mock token return
    # Payload: {"exp": 1234567890} -> eyJleHAiOjEyMzQ1Njc4OTB9
    fake_token = "header.eyJleHAiOjEyMzQ1Njc4OTB9.sig"
    mock_dependencies["get_jwt_token"].return_value = fake_token
    
    result = runner.invoke(auth_group, ["login"])
    
    assert result.exit_code == 0
    assert "Successfully authenticated" in result.output
    
    # Verify cache write
    mock_dependencies["JWT_CACHE_FILE"].write_text.assert_called_once()
    call_args = mock_dependencies["JWT_CACHE_FILE"].write_text.call_args[0][0]
    saved_data = json.loads(call_args)
    assert saved_data["id_token"] == fake_token
    assert saved_data["expires_at"] == 1234567890

def test_login_missing_api_key(runner, mock_dependencies, mock_env_vars):
    """Test login fails when API key is missing."""
    # Use isolated_filesystem to avoid reading .env files from the project root
    with runner.isolated_filesystem():
        result = runner.invoke(auth_group, ["login"])

        assert result.exit_code == 1
        assert "NEXT_PUBLIC_FIREBASE_API_KEY not found" in result.output

def test_login_user_cancelled(runner, mock_dependencies, monkeypatch):
    """Test login handles user cancellation."""
    monkeypatch.setenv("NEXT_PUBLIC_FIREBASE_API_KEY", "key")
    mock_dependencies["get_jwt_token"].side_effect = MockUserCancelledError("Cancelled")
    
    result = runner.invoke(auth_group, ["login"])
    
    assert result.exit_code == 1
    assert "Authentication cancelled by user" in result.output

def test_login_network_error(runner, mock_dependencies, monkeypatch):
    """Test login handles network errors."""
    monkeypatch.setenv("NEXT_PUBLIC_FIREBASE_API_KEY", "key")
    mock_dependencies["get_jwt_token"].side_effect = MockNetworkError("Connection failed")
    
    result = runner.invoke(auth_group, ["login"])
    
    assert result.exit_code == 1
    assert "Network error: Connection failed" in result.output

# --- Status Command Tests ---

def test_status_not_authenticated(runner, mock_dependencies):
    """Test status when not authenticated."""
    mock_dependencies["get_auth_status"].return_value = {"authenticated": False}

    result = runner.invoke(auth_group, ["status"])

    # Status returns 0 even when not authenticated (informational, not an error)
    assert result.exit_code == 0
    assert "Not authenticated" in result.output

def test_status_authenticated(runner, mock_dependencies):
    """Test status when authenticated."""
    mock_dependencies["get_auth_status"].return_value = {"authenticated": True, "cached": True}
    mock_dependencies["JWT_CACHE_FILE"].exists.return_value = True
    
    # Mock reading the cache file
    # Payload: {"email": "test@example.com"} -> eyJlbWFpbCI6InRlc3RAZXhhbXBsZS5jb20ifQ==
    token = "header.eyJlbWFpbCI6InRlc3RAZXhhbXBsZS5jb20ifQ==.sig"
    mock_dependencies["JWT_CACHE_FILE"].read_text.return_value = json.dumps({
        "id_token": token
    })
    
    result = runner.invoke(auth_group, ["status"])
    
    assert result.exit_code == 0
    assert "Authenticated as: test@example.com" in result.output

def test_status_authenticated_corrupt_cache(runner, mock_dependencies):
    """Test status when authenticated but cache is unreadable."""
    mock_dependencies["get_auth_status"].return_value = {"authenticated": True, "cached": True}
    mock_dependencies["JWT_CACHE_FILE"].exists.return_value = True
    mock_dependencies["JWT_CACHE_FILE"].read_text.side_effect = Exception("Read error")
    
    result = runner.invoke(auth_group, ["status"])
    
    # Should still say authenticated, but username might be Unknown
    assert result.exit_code == 0
    assert "Authenticated as: Unknown" in result.output

# --- Logout Command Tests ---

def test_logout_success(runner, mock_dependencies):
    """Test successful logout."""
    mock_dependencies["service_logout"].return_value = (True, None)
    
    result = runner.invoke(auth_group, ["logout"])
    
    assert result.exit_code == 0
    assert "Logged out of PDD Cloud" in result.output

def test_logout_failure(runner, mock_dependencies):
    """Test logout failure."""
    mock_dependencies["service_logout"].return_value = (False, "Keyring error")
    
    result = runner.invoke(auth_group, ["logout"])
    
    assert result.exit_code == 0  # Code says it doesn't exit with 1
    assert "Failed to logout: Keyring error" in result.output

# --- Token Command Tests ---

def test_token_raw_success(runner, mock_dependencies):
    """Test getting raw token."""
    mock_dependencies["JWT_CACHE_FILE"].exists.return_value = True
    future_time = time.time() + 3600
    mock_dependencies["JWT_CACHE_FILE"].read_text.return_value = json.dumps({
        "id_token": "valid.token.sig",
        "expires_at": future_time
    })
    
    result = runner.invoke(auth_group, ["token"])
    
    assert result.exit_code == 0
    assert result.output.strip() == "valid.token.sig"

def test_token_json_success(runner, mock_dependencies):
    """Test getting token in JSON format."""
    mock_dependencies["JWT_CACHE_FILE"].exists.return_value = True
    future_time = time.time() + 3600
    mock_dependencies["JWT_CACHE_FILE"].read_text.return_value = json.dumps({
        "id_token": "valid.token.sig",
        "expires_at": future_time
    })
    
    result = runner.invoke(auth_group, ["token", "--format", "json"])
    
    assert result.exit_code == 0
    data = json.loads(result.output)
    assert data["token"] == "valid.token.sig"
    assert data["expires_at"] == future_time

def test_token_expired(runner, mock_dependencies):
    """Test token command when token is expired."""
    mock_dependencies["JWT_CACHE_FILE"].exists.return_value = True
    past_time = time.time() - 3600
    mock_dependencies["JWT_CACHE_FILE"].read_text.return_value = json.dumps({
        "id_token": "expired.token.sig",
        "expires_at": past_time
    })
    
    result = runner.invoke(auth_group, ["token"])
    
    assert result.exit_code == 1
    assert "No valid token available" in result.output

def test_token_no_cache(runner, mock_dependencies):
    """Test token command when no cache exists."""
    mock_dependencies["JWT_CACHE_FILE"].exists.return_value = False
    
    result = runner.invoke(auth_group, ["token"])
    
    assert result.exit_code == 1
    assert "No valid token available" in result.output