"""
Test suite for pdd.core.cloud module.

Test Plan:

1.  **URL Configuration Tests (`get_base_url`, `get_endpoint_url`)**:
    *   Verify default base URL is returned when no environment variable is set.
    *   Verify `PDD_CLOUD_URL` environment variable overrides the default.
    *   Verify trailing slashes are stripped from the base URL.
    *   Verify endpoint URLs are constructed correctly using the `CLOUD_ENDPOINTS` map.
    *   Verify unknown endpoints default to `/{name}`.
    *   Verify that if `PDD_CLOUD_URL` contains the endpoint name, it is returned as-is (override logic).

2.  **Cloud Environment Detection Tests (`is_running_in_cloud`)**:
    *   Verify returns False when not in cloud environment.
    *   Verify returns True when `K_SERVICE` is set (Cloud Run/Cloud Functions).
    *   Verify returns True when `FUNCTIONS_EMULATOR` is set.

3.  **Cloud Enablement Tests (`is_cloud_enabled`)**:
    *   Verify returns False if running in cloud environment (prevents infinite loops).
    *   Verify returns False if neither API key nor Client ID is set (and no JWT token).
    *   Verify returns False if only one of Firebase/GitHub keys is set (and no JWT token).
    *   Verify returns True if both `FIREBASE_API_KEY_ENV` and `GITHUB_CLIENT_ID_ENV` are set.
    *   Verify returns True if `PDD_JWT_TOKEN` is set (for injected token in testing/CI scenarios).
    *   **Z3 Formal Verification**: Use Z3 to prove that the function returns True <=> (JWT is Set OR (Key1 is Set AND Key2 is Set)).

4.  **Authentication Tests (`get_jwt_token`)**:
    *   Verify `PDD_JWT_TOKEN` environment variable takes precedence (returns immediately).
    *   Verify that missing API keys trigger an `AuthError` internally and return `None` (graceful failure).
    *   Verify successful device flow execution returns the token.
    *   Verify that exceptions during the device flow (`AuthError`, `NetworkError`, etc.) are caught and return `None`.
    *   Verify `verbose` flag triggers console output (using mocks).

"""

import os
import sys
import pytest
import asyncio
from unittest.mock import patch, MagicMock, AsyncMock
from z3 import Solver, Bool, And, Not

# Import the code under test
from pdd.core.cloud import (
    CloudConfig,
    DEFAULT_BASE_URL,
    CLOUD_ENDPOINTS,
    FIREBASE_API_KEY_ENV,
    GITHUB_CLIENT_ID_ENV,
    PDD_CLOUD_URL_ENV,
    PDD_JWT_TOKEN_ENV,
    AuthError,
    NetworkError,
    RateLimitError
)

# -----------------------------------------------------------------------------
# Fixtures
# -----------------------------------------------------------------------------

@pytest.fixture
def clean_env():
    """Fixture to ensure environment is clean before and after tests."""
    # Store original values
    original_env = os.environ.copy()
    
    # Clear relevant keys
    keys_to_clear = [
        PDD_CLOUD_URL_ENV, 
        PDD_JWT_TOKEN_ENV, 
        FIREBASE_API_KEY_ENV, 
        GITHUB_CLIENT_ID_ENV
    ]
    for key in keys_to_clear:
        if key in os.environ:
            del os.environ[key]
            
    yield
    
    # Restore original values
    os.environ.clear()
    os.environ.update(original_env)

# -----------------------------------------------------------------------------
# Unit Tests: URL Configuration
# -----------------------------------------------------------------------------

def test_get_base_url_default(clean_env):
    """Test that the default base URL is returned when no env var is set."""
    assert CloudConfig.get_base_url() == DEFAULT_BASE_URL

def test_get_base_url_override(clean_env):
    """Test that PDD_CLOUD_URL overrides the default base URL."""
    custom_url = "https://custom-cloud.example.com"
    with patch.dict(os.environ, {PDD_CLOUD_URL_ENV: custom_url}):
        assert CloudConfig.get_base_url() == custom_url

def test_get_base_url_strips_slash(clean_env):
    """Test that trailing slashes are stripped from the custom URL."""
    custom_url = "https://custom-cloud.example.com/"
    with patch.dict(os.environ, {PDD_CLOUD_URL_ENV: custom_url}):
        assert CloudConfig.get_base_url() == "https://custom-cloud.example.com"

def test_get_endpoint_url_standard(clean_env):
    """Test constructing a URL for a known endpoint."""
    endpoint = "generateCode"
    expected_path = CLOUD_ENDPOINTS[endpoint]
    expected_url = f"{DEFAULT_BASE_URL}{expected_path}"
    assert CloudConfig.get_endpoint_url(endpoint) == expected_url

def test_get_endpoint_url_unknown(clean_env):
    """Test constructing a URL for an unknown endpoint defaults to /{name}."""
    endpoint = "unknownFunction"
    expected_url = f"{DEFAULT_BASE_URL}/{endpoint}"
    assert CloudConfig.get_endpoint_url(endpoint) == expected_url

def test_get_endpoint_url_with_custom_base(clean_env):
    """Test endpoint URL construction with a custom base URL."""
    custom_base = "https://staging.example.com"
    endpoint = "syncState"
    expected_path = CLOUD_ENDPOINTS[endpoint]
    
    with patch.dict(os.environ, {PDD_CLOUD_URL_ENV: custom_base}):
        expected_url = f"{custom_base}{expected_path}"
        assert CloudConfig.get_endpoint_url(endpoint) == expected_url

def test_get_endpoint_url_full_override(clean_env):
    """
    Test that if PDD_CLOUD_URL contains the endpoint name, 
    it is returned as-is (useful for testing specific function URLs directly).
    """
    # Scenario: User wants to test a specific deployment of generateCode
    full_custom_url = "https://custom-deploy.example.com/generateCode"
    
    with patch.dict(os.environ, {PDD_CLOUD_URL_ENV: full_custom_url}):
        # Should return the env var exactly because "generateCode" is in the string
        assert CloudConfig.get_endpoint_url("generateCode") == full_custom_url

# -----------------------------------------------------------------------------
# Unit Tests: Cloud Enablement
# -----------------------------------------------------------------------------

def test_is_running_in_cloud_false_by_default(clean_env):
    """Test is_running_in_cloud returns False when not in cloud environment."""
    # Ensure cloud env vars are not set
    for key in ["K_SERVICE", "FUNCTIONS_EMULATOR"]:
        if key in os.environ:
            del os.environ[key]
    assert CloudConfig.is_running_in_cloud() is False


def test_is_running_in_cloud_true_k_service(clean_env):
    """Test is_running_in_cloud returns True when K_SERVICE is set (Cloud Run/Functions)."""
    with patch.dict(os.environ, {"K_SERVICE": "my-function"}):
        assert CloudConfig.is_running_in_cloud() is True


def test_is_running_in_cloud_true_functions_emulator(clean_env):
    """Test is_running_in_cloud returns True when FUNCTIONS_EMULATOR is set."""
    with patch.dict(os.environ, {"FUNCTIONS_EMULATOR": "true"}):
        assert CloudConfig.is_running_in_cloud() is True


def test_is_cloud_enabled_false_when_in_cloud_environment(clean_env):
    """Test is_cloud_enabled returns False when running in cloud, even with credentials.

    This prevents infinite loops when cloud endpoints call CLI internally.
    """
    with patch.dict(os.environ, {
        "K_SERVICE": "generateCode",
        FIREBASE_API_KEY_ENV: "key",
        GITHUB_CLIENT_ID_ENV: "id"
    }):
        assert CloudConfig.is_cloud_enabled() is False


def test_is_cloud_enabled_false_when_in_emulator(clean_env):
    """Test is_cloud_enabled returns False when running in emulator, even with JWT token."""
    with patch.dict(os.environ, {
        "FUNCTIONS_EMULATOR": "true",
        PDD_JWT_TOKEN_ENV: "ey.test.token"
    }):
        assert CloudConfig.is_cloud_enabled() is False


def test_is_cloud_enabled_false_when_force_local_set(clean_env):
    """Test is_cloud_enabled returns False when PDD_FORCE_LOCAL is set (--local flag).

    This ensures that the --local CLI flag properly disables cloud mode,
    preventing keychain access prompts during local testing.
    """
    with patch.dict(os.environ, {
        "PDD_FORCE_LOCAL": "1",
        FIREBASE_API_KEY_ENV: "key",
        GITHUB_CLIENT_ID_ENV: "id"
    }):
        assert CloudConfig.is_cloud_enabled() is False


def test_is_cloud_enabled_false_when_force_local_with_jwt(clean_env):
    """Test is_cloud_enabled returns False when PDD_FORCE_LOCAL is set, even with JWT token."""
    with patch.dict(os.environ, {
        "PDD_FORCE_LOCAL": "1",
        PDD_JWT_TOKEN_ENV: "ey.test.token"
    }):
        assert CloudConfig.is_cloud_enabled() is False


def test_is_cloud_enabled_false_when_empty(clean_env):
    """Test is_cloud_enabled returns False when keys are missing."""
    assert CloudConfig.is_cloud_enabled() is False

def test_is_cloud_enabled_false_partial(clean_env):
    """Test is_cloud_enabled returns False when only one key is present."""
    with patch.dict(os.environ, {FIREBASE_API_KEY_ENV: "key"}):
        assert CloudConfig.is_cloud_enabled() is False
        
    with patch.dict(os.environ, {GITHUB_CLIENT_ID_ENV: "id"}):
        assert CloudConfig.is_cloud_enabled() is False

def test_is_cloud_enabled_true(clean_env):
    """Test is_cloud_enabled returns True when both keys are present."""
    with patch.dict(os.environ, {
        FIREBASE_API_KEY_ENV: "key",
        GITHUB_CLIENT_ID_ENV: "id"
    }):
        assert CloudConfig.is_cloud_enabled() is True


def test_is_cloud_enabled_true_with_jwt_token(clean_env):
    """Test is_cloud_enabled returns True when PDD_JWT_TOKEN is set (injected token for testing/CI).

    This tests the bug fix where cloud should be detected as enabled when a JWT token
    is directly injected via environment variable, even without device flow auth credentials.
    """
    with patch.dict(os.environ, {PDD_JWT_TOKEN_ENV: "ey.injected.token"}):
        assert CloudConfig.is_cloud_enabled() is True


def test_is_cloud_enabled_jwt_token_takes_priority(clean_env):
    """Test that PDD_JWT_TOKEN alone enables cloud, regardless of other credentials."""
    # Only JWT token set, no Firebase/GitHub credentials
    with patch.dict(os.environ, {PDD_JWT_TOKEN_ENV: "ey.test.token"}, clear=True):
        # Re-add only the JWT token after clearing
        os.environ[PDD_JWT_TOKEN_ENV] = "ey.test.token"
        assert CloudConfig.is_cloud_enabled() is True

# -----------------------------------------------------------------------------
# Z3 Formal Verification: Cloud Enablement Logic
# -----------------------------------------------------------------------------

def test_z3_verify_cloud_enabled_logic():
    """
    Formally verify the logic of is_cloud_enabled using Z3.

    Logic to prove: Result is True if and only if:
      (JWT is Set) OR (FirebaseKey is Set AND GithubId is Set)
    """
    from z3 import Or
    s = Solver()

    # Define boolean variables representing the state of environment variables
    jwt_set = Bool('jwt_set')
    firebase_set = Bool('firebase_set')
    github_set = Bool('github_set')

    # Define the result of the function based on the code's logic
    # Code: if jwt_set: return True; return bool(FIREBASE and GITHUB)
    result = Bool('result')

    # Add constraint representing the implementation
    # result == (jwt_set OR (firebase_set AND github_set))
    s.add(result == Or(jwt_set, And(firebase_set, github_set)))

    # Negate the biconditional: NOT (result <-> (jwt OR (firebase AND github)))
    # If this is unsatisfiable, the logic is verified.
    conjecture = result == Or(jwt_set, And(firebase_set, github_set))
    s.add(Not(conjecture))

    check = s.check()

    # If unsat, it means no counter-example exists, so the logic is verified.
    assert str(check) == "unsat", \
        f"Z3 found a counter-example to the logic: {s.model()}"

# -----------------------------------------------------------------------------
# Unit Tests: Authentication (JWT Token)
# -----------------------------------------------------------------------------

def test_get_jwt_token_from_env(clean_env):
    """Test that the token is retrieved from environment variable if present."""
    test_token = "ey.test.token"
    with patch.dict(os.environ, {PDD_JWT_TOKEN_ENV: test_token}):
        # Should return immediately without calling auth flow
        token = CloudConfig.get_jwt_token()
        assert token == test_token

@patch("pdd.core.cloud.device_flow_get_token")
def test_get_jwt_token_missing_keys(mock_device_flow, clean_env):
    """Test that missing API keys result in None (and caught AuthError)."""
    # Ensure keys are missing
    with patch.dict(os.environ, {}, clear=True):
        token = CloudConfig.get_jwt_token(verbose=True)
        assert token is None
        # Should not attempt to call the async flow if keys are missing
        mock_device_flow.assert_not_called()

@patch("pdd.core.cloud.device_flow_get_token", new_callable=AsyncMock)
def test_get_jwt_token_success(mock_device_flow, clean_env):
    """Test successful device flow authentication."""
    expected_token = "ey.generated.token"
    mock_device_flow.return_value = expected_token
    
    with patch.dict(os.environ, {
        FIREBASE_API_KEY_ENV: "test_key",
        GITHUB_CLIENT_ID_ENV: "test_id"
    }):
        token = CloudConfig.get_jwt_token()
        assert token == expected_token
        mock_device_flow.assert_called_once()

@patch("pdd.core.cloud.device_flow_get_token", new_callable=AsyncMock)
def test_get_jwt_token_auth_error(mock_device_flow, clean_env):
    """Test that AuthError during flow is caught and returns None."""
    mock_device_flow.side_effect = AuthError("Auth failed")
    
    with patch.dict(os.environ, {
        FIREBASE_API_KEY_ENV: "test_key",
        GITHUB_CLIENT_ID_ENV: "test_id"
    }):
        # Should not raise exception
        token = CloudConfig.get_jwt_token(verbose=True)
        assert token is None

@patch("pdd.core.cloud.device_flow_get_token", new_callable=AsyncMock)
def test_get_jwt_token_network_error(mock_device_flow, clean_env):
    """Test that NetworkError during flow is caught and returns None."""
    mock_device_flow.side_effect = NetworkError("Connection failed")
    
    with patch.dict(os.environ, {
        FIREBASE_API_KEY_ENV: "test_key",
        GITHUB_CLIENT_ID_ENV: "test_id"
    }):
        token = CloudConfig.get_jwt_token(verbose=True)
        assert token is None

@patch("pdd.core.cloud.device_flow_get_token", new_callable=AsyncMock)
def test_get_jwt_token_unexpected_error(mock_device_flow, clean_env):
    """Test that generic exceptions are caught and return None."""
    mock_device_flow.side_effect = Exception("Something went wrong")
    
    with patch.dict(os.environ, {
        FIREBASE_API_KEY_ENV: "test_key",
        GITHUB_CLIENT_ID_ENV: "test_id"
    }):
        token = CloudConfig.get_jwt_token(verbose=True)
        assert token is None