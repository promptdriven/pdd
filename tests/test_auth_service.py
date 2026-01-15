"""
Test Plan for pdd.auth_service

1. **Constants Verification**:
   - Verify that constants (JWT_CACHE_FILE, KEYRING_SERVICE_NAME, KEYRING_USER_NAME) are defined correctly.
   - *Method*: Unit Test.

2. **get_jwt_cache_info**:
   - **Case 1: File does not exist**: Should return (False, None).
   - **Case 2: File exists but invalid JSON**: Should return (False, None).
   - **Case 3: File exists, valid JSON, but missing 'expires_at'**: Should return (False, None).
   - **Case 4: File exists, valid token, but expired**: Should return (False, None).
   - **Case 5: File exists, valid token, expires soon (within buffer)**: Should return (False, None) because of the 300s buffer.
   - **Case 6: File exists, valid token, expires in future**: Should return (True, expires_at).
   - *Method*: Unit Test with mocked file system (fs) or `tmp_path`. Z3 is not necessary here as the logic is simple arithmetic comparison.

3. **has_refresh_token**:
   - **Case 1: Keyring has token**: Should return True.
   - **Case 2: Keyring returns None**: Should return False.
   - **Case 3: ImportError on primary keyring**: Should try fallback.
   - **Case 4: Fallback keyring has token**: Should return True.
   - **Case 5: Fallback keyring fails/empty**: Should return False.
   - *Method*: Unit Test with mocked `keyring` module.

4. **clear_jwt_cache**:
   - **Case 1: File exists**: Should delete file and return (True, None).
   - **Case 2: File does not exist**: Should return (True, None).
   - **Case 3: Deletion fails (PermissionError/OSError)**: Should return (False, error_msg).
   - *Method*: Unit Test with mocked file system.

5. **clear_refresh_token**:
   - **Case 1: Keyring delete successful**: Should return (True, None).
   - **Case 2: Keyring delete raises "not found"**: Should return (True, None) (idempotency).
   - **Case 3: Keyring delete raises other error**: Should return (False, error_msg).
   - **Case 4: ImportError on primary, fallback succeeds**: Should return (True, None).
   - **Case 5: ImportError on both**: Should return (True, None).
   - *Method*: Unit Test with mocked `keyring`.

6. **get_auth_status**:
   - **Case 1: Valid JWT Cache**: Should return authenticated=True, cached=True.
   - **Case 2: Invalid JWT, Valid Refresh Token**: Should return authenticated=True, cached=False.
   - **Case 3: Invalid JWT, No Refresh Token**: Should return authenticated=False.
   - *Method*: Unit Test mocking `get_jwt_cache_info` and `has_refresh_token`.

7. **logout**:
   - **Case 1: Both succeed**: Returns (True, None).
   - **Case 2: JWT clear fails**: Returns (False, error_msg).
   - **Case 3: Refresh clear fails**: Returns (False, error_msg).
   - **Case 4: Both fail**: Returns (False, combined_error_msg).
   - *Method*: Unit Test mocking `clear_jwt_cache` and `clear_refresh_token`.

8. **get_cached_jwt**:
   - **Case 1: File does not exist**: Should return None.
   - **Case 2: File exists but invalid JSON**: Should return None.
   - **Case 3: File exists, valid JSON, but missing token keys**: Should return None.
   - **Case 4: File exists, valid token, but expired**: Should return None.
   - **Case 5: File exists, valid token, expires soon (within buffer)**: Should return None.
   - **Case 6: File exists, valid token with 'id_token' key**: Should return token.
   - **Case 7: File exists, valid token with legacy 'jwt' key**: Should return token.
   - **Case 8: Both 'id_token' and 'jwt' exist**: Should prefer 'id_token'.
   - *Method*: Unit Test with mocked file system.

9. **Z3 Formal Verification**:
   - While the logic is mostly IO-bound, we can verify the temporal logic of `get_jwt_cache_info` to ensure the buffer logic (current_time + 300) holds for all possible timestamps.
   - We can also verify the state machine logic of `get_auth_status` (e.g., if cached is True, authenticated MUST be True).
"""

import json
import time
import sys
from unittest.mock import MagicMock, patch, mock_open
import pytest
from z3 import Solver, Real, Bool, Implies, And, Or, Not, sat

# Import the code under test
# Adjusting path to ensure import works regardless of where test is run
import pdd.auth_service as auth_service

# --- Fixtures ---

@pytest.fixture
def mock_home(tmp_path):
    """Mock JWT_CACHE_FILE to use a temporary directory.

    Note: We patch the constant directly because it's evaluated at module import time,
    so patching Path.home() after import has no effect.
    """
    mock_cache_file = tmp_path / ".pdd" / "jwt_cache"
    with patch.object(auth_service, 'JWT_CACHE_FILE', mock_cache_file):
        yield tmp_path

@pytest.fixture
def mock_keyring():
    """Mock the keyring module."""
    with patch.dict(sys.modules, {"keyring": MagicMock()}):
        yield sys.modules["keyring"]

# --- Unit Tests ---

def test_constants():
    """Verify module constants."""
    assert auth_service.KEYRING_SERVICE_NAME == "firebase-auth-PDD CLI"
    assert auth_service.KEYRING_USER_NAME == "refresh_token"
    # We can't easily assert the exact path of JWT_CACHE_FILE without mocking home during import,
    # but we can check the suffix.
    assert auth_service.JWT_CACHE_FILE.name == "jwt_cache"

# --- get_jwt_cache_info Tests ---

def test_get_jwt_cache_info_no_file(mock_home):
    """Should return (False, None) if cache file does not exist."""
    # Ensure file doesn't exist
    cache_file = mock_home / ".pdd" / "jwt_cache"
    if cache_file.exists():
        cache_file.unlink()
    
    is_valid, expires_at = auth_service.get_jwt_cache_info()
    assert is_valid is False
    assert expires_at is None

def test_get_jwt_cache_info_invalid_json(mock_home):
    """Should return (False, None) if file contains invalid JSON."""
    cache_file = mock_home / ".pdd" / "jwt_cache"
    cache_file.parent.mkdir(parents=True, exist_ok=True)
    cache_file.write_text("{invalid_json")

    is_valid, expires_at = auth_service.get_jwt_cache_info()
    assert is_valid is False
    assert expires_at is None

def test_get_jwt_cache_info_missing_key(mock_home):
    """Should return (False, None) if JSON is valid but missing 'expires_at'."""
    cache_file = mock_home / ".pdd" / "jwt_cache"
    cache_file.parent.mkdir(parents=True, exist_ok=True)
    cache_file.write_text(json.dumps({"some_other_key": 123}))

    is_valid, expires_at = auth_service.get_jwt_cache_info()
    assert is_valid is False
    assert expires_at is None

def test_get_jwt_cache_info_expired(mock_home):
    """Should return (False, None) if token is expired."""
    cache_file = mock_home / ".pdd" / "jwt_cache"
    cache_file.parent.mkdir(parents=True, exist_ok=True)
    
    # Expired 1 second ago
    past_time = time.time() - 1
    cache_file.write_text(json.dumps({"expires_at": past_time}))

    is_valid, expires_at = auth_service.get_jwt_cache_info()
    assert is_valid is False
    assert expires_at is None

def test_get_jwt_cache_info_within_buffer(mock_home):
    """Should return (False, None) if token expires within the 300s buffer."""
    cache_file = mock_home / ".pdd" / "jwt_cache"
    cache_file.parent.mkdir(parents=True, exist_ok=True)
    
    # Expires in 200 seconds (less than 300s buffer)
    future_time = time.time() + 200
    cache_file.write_text(json.dumps({"expires_at": future_time}))

    is_valid, expires_at = auth_service.get_jwt_cache_info()
    assert is_valid is False
    assert expires_at is None

def test_get_jwt_cache_info_valid(mock_home):
    """Should return (True, expires_at) if token is valid and outside buffer."""
    cache_file = mock_home / ".pdd" / "jwt_cache"
    cache_file.parent.mkdir(parents=True, exist_ok=True)

    # Expires in 600 seconds (more than 300s buffer)
    future_time = time.time() + 600
    cache_file.write_text(json.dumps({"expires_at": future_time}))

    is_valid, expires_at = auth_service.get_jwt_cache_info()
    assert is_valid is True
    assert expires_at == future_time

# --- get_cached_jwt Tests ---

def test_get_cached_jwt_no_file(mock_home):
    """Should return None if cache file does not exist."""
    cache_file = mock_home / ".pdd" / "jwt_cache"
    if cache_file.exists():
        cache_file.unlink()

    token = auth_service.get_cached_jwt()
    assert token is None

def test_get_cached_jwt_invalid_json(mock_home):
    """Should return None if file contains invalid JSON."""
    cache_file = mock_home / ".pdd" / "jwt_cache"
    cache_file.parent.mkdir(parents=True, exist_ok=True)
    cache_file.write_text("{invalid_json")

    token = auth_service.get_cached_jwt()
    assert token is None

def test_get_cached_jwt_missing_token_key(mock_home):
    """Should return None if JSON is valid but missing token keys."""
    cache_file = mock_home / ".pdd" / "jwt_cache"
    cache_file.parent.mkdir(parents=True, exist_ok=True)
    future_time = time.time() + 600
    cache_file.write_text(json.dumps({"expires_at": future_time, "some_other_key": "value"}))

    token = auth_service.get_cached_jwt()
    assert token is None

def test_get_cached_jwt_expired(mock_home):
    """Should return None if token is expired."""
    cache_file = mock_home / ".pdd" / "jwt_cache"
    cache_file.parent.mkdir(parents=True, exist_ok=True)

    # Expired 1 second ago
    past_time = time.time() - 1
    cache_file.write_text(json.dumps({
        "expires_at": past_time,
        "id_token": "expired_token"
    }))

    token = auth_service.get_cached_jwt()
    assert token is None

def test_get_cached_jwt_within_buffer(mock_home):
    """Should return None if token expires within the 300s buffer."""
    cache_file = mock_home / ".pdd" / "jwt_cache"
    cache_file.parent.mkdir(parents=True, exist_ok=True)

    # Expires in 200 seconds (less than 300s buffer)
    future_time = time.time() + 200
    cache_file.write_text(json.dumps({
        "expires_at": future_time,
        "id_token": "almost_expired_token"
    }))

    token = auth_service.get_cached_jwt()
    assert token is None

def test_get_cached_jwt_valid_id_token(mock_home):
    """Should return token when using 'id_token' key (new format)."""
    cache_file = mock_home / ".pdd" / "jwt_cache"
    cache_file.parent.mkdir(parents=True, exist_ok=True)

    # Expires in 600 seconds (more than 300s buffer)
    future_time = time.time() + 600
    expected_token = "valid_id_token_abc123"
    cache_file.write_text(json.dumps({
        "expires_at": future_time,
        "id_token": expected_token
    }))

    token = auth_service.get_cached_jwt()
    assert token == expected_token

def test_get_cached_jwt_valid_legacy_jwt(mock_home):
    """Should return token when using legacy 'jwt' key for backwards compatibility."""
    cache_file = mock_home / ".pdd" / "jwt_cache"
    cache_file.parent.mkdir(parents=True, exist_ok=True)

    # Expires in 600 seconds (more than 300s buffer)
    future_time = time.time() + 600
    expected_token = "legacy_jwt_token_xyz789"
    cache_file.write_text(json.dumps({
        "expires_at": future_time,
        "jwt": expected_token
    }))

    token = auth_service.get_cached_jwt()
    assert token == expected_token

def test_get_cached_jwt_prefers_id_token_over_jwt(mock_home):
    """Should prefer 'id_token' over 'jwt' if both exist."""
    cache_file = mock_home / ".pdd" / "jwt_cache"
    cache_file.parent.mkdir(parents=True, exist_ok=True)

    future_time = time.time() + 600
    cache_file.write_text(json.dumps({
        "expires_at": future_time,
        "id_token": "preferred_token",
        "jwt": "legacy_token"
    }))

    token = auth_service.get_cached_jwt()
    assert token == "preferred_token"

# --- has_refresh_token Tests ---

def test_has_refresh_token_exists(mock_keyring):
    """Should return True if keyring has password."""
    mock_keyring.get_password.return_value = "some_token"
    assert auth_service.has_refresh_token() is True
    mock_keyring.get_password.assert_called_with(
        auth_service.KEYRING_SERVICE_NAME, 
        auth_service.KEYRING_USER_NAME
    )

def test_has_refresh_token_none(mock_keyring):
    """Should return False if keyring returns None."""
    mock_keyring.get_password.return_value = None
    assert auth_service.has_refresh_token() is False

def test_has_refresh_token_import_error():
    """Should return False if keyring import fails and no fallback available."""
    # Remove keyring from sys.modules to force re-import
    saved_keyring = sys.modules.pop('keyring', None)
    saved_keyrings = sys.modules.pop('keyrings', None)
    saved_keyrings_alt = sys.modules.pop('keyrings.alt', None)
    saved_keyrings_alt_file = sys.modules.pop('keyrings.alt.file', None)

    try:
        # Mock builtins.__import__ to raise ImportError for keyring-related imports
        original_import = __builtins__['__import__'] if isinstance(__builtins__, dict) else __builtins__.__import__

        def import_mock(name, *args, **kwargs):
            if name == 'keyring' or name.startswith('keyrings'):
                raise ImportError(f"No module named '{name}'")
            return original_import(name, *args, **kwargs)

        with patch('builtins.__import__', side_effect=import_mock):
            # When both keyring and keyrings.alt.file are unavailable, should return False
            result = auth_service.has_refresh_token()
            assert result is False
    finally:
        # Restore original modules
        if saved_keyring:
            sys.modules['keyring'] = saved_keyring
        if saved_keyrings:
            sys.modules['keyrings'] = saved_keyrings
        if saved_keyrings_alt:
            sys.modules['keyrings.alt'] = saved_keyrings_alt
        if saved_keyrings_alt_file:
            sys.modules['keyrings.alt.file'] = saved_keyrings_alt_file

# --- clear_jwt_cache Tests ---

def test_clear_jwt_cache_success(mock_home):
    """Should delete file and return success."""
    cache_file = mock_home / ".pdd" / "jwt_cache"
    cache_file.parent.mkdir(parents=True, exist_ok=True)
    cache_file.touch()
    
    success, error = auth_service.clear_jwt_cache()
    assert success is True
    assert error is None
    assert not cache_file.exists()

def test_clear_jwt_cache_no_file(mock_home):
    """Should return success if file doesn't exist."""
    success, error = auth_service.clear_jwt_cache()
    assert success is True
    assert error is None

def test_clear_jwt_cache_error(mock_home):
    """Should return error if deletion fails."""
    cache_file = mock_home / ".pdd" / "jwt_cache"
    cache_file.parent.mkdir(parents=True, exist_ok=True)
    cache_file.touch()
    
    # Mock unlink to raise exception
    with patch.object(type(cache_file), 'unlink', side_effect=PermissionError("Access denied")):
        # We need to ensure auth_service uses our mocked path object or the logic hits it.
        # Since auth_service.JWT_CACHE_FILE is a global constant initialized at import time,
        # we need to patch that constant.
        with patch('pdd.auth_service.JWT_CACHE_FILE', cache_file):
             success, error = auth_service.clear_jwt_cache()
             assert success is False
             assert "Access denied" in error

# --- clear_refresh_token Tests ---

def test_clear_refresh_token_success(mock_keyring):
    """Should delete password and return success."""
    success, error = auth_service.clear_refresh_token()
    assert success is True
    assert error is None
    mock_keyring.delete_password.assert_called_once()

def test_clear_refresh_token_not_found(mock_keyring):
    """Should ignore 'not found' errors."""
    mock_keyring.delete_password.side_effect = Exception("Password not found in keyring")
    success, error = auth_service.clear_refresh_token()
    assert success is True
    assert error is None

def test_clear_refresh_token_other_error(mock_keyring):
    """Should return error for other exceptions."""
    mock_keyring.delete_password.side_effect = Exception("System error")
    success, error = auth_service.clear_refresh_token()
    assert success is False
    assert "System error" in error

# --- get_auth_status Tests ---

@patch('pdd.auth_service.get_jwt_cache_info')
@patch('pdd.auth_service.has_refresh_token')
def test_get_auth_status_cached(mock_has_refresh, mock_get_jwt):
    """Should return cached status if JWT is valid."""
    mock_get_jwt.return_value = (True, 1234567890.0)
    
    status = auth_service.get_auth_status()
    
    assert status['authenticated'] is True
    assert status['cached'] is True
    assert status['expires_at'] == 1234567890.0
    # Should not check refresh token if cache is valid (optimization check)
    # Note: The code doesn't explicitly forbid it, but usually it's an `if/else` or early return.
    # Looking at code: it returns early.
    mock_has_refresh.assert_not_called()

@patch('pdd.auth_service.get_jwt_cache_info')
@patch('pdd.auth_service.has_refresh_token')
def test_get_auth_status_refresh_only(mock_has_refresh, mock_get_jwt):
    """Should return authenticated but not cached if only refresh token exists."""
    mock_get_jwt.return_value = (False, None)
    mock_has_refresh.return_value = True
    
    status = auth_service.get_auth_status()
    
    assert status['authenticated'] is True
    assert status['cached'] is False
    assert status['expires_at'] is None

@patch('pdd.auth_service.get_jwt_cache_info')
@patch('pdd.auth_service.has_refresh_token')
def test_get_auth_status_unauthenticated(mock_has_refresh, mock_get_jwt):
    """Should return unauthenticated if neither exists."""
    mock_get_jwt.return_value = (False, None)
    mock_has_refresh.return_value = False
    
    status = auth_service.get_auth_status()
    
    assert status['authenticated'] is False
    assert status['cached'] is False
    assert status['expires_at'] is None

# --- logout Tests ---

@patch('pdd.auth_service.clear_jwt_cache')
@patch('pdd.auth_service.clear_refresh_token')
def test_logout_success(mock_clear_refresh, mock_clear_jwt):
    """Should return success if both clears succeed."""
    mock_clear_jwt.return_value = (True, None)
    mock_clear_refresh.return_value = (True, None)
    
    success, error = auth_service.logout()
    
    assert success is True
    assert error is None
    mock_clear_jwt.assert_called_once()
    mock_clear_refresh.assert_called_once()

@patch('pdd.auth_service.clear_jwt_cache')
@patch('pdd.auth_service.clear_refresh_token')
def test_logout_partial_failure(mock_clear_refresh, mock_clear_jwt):
    """Should return failure if one fails."""
    mock_clear_jwt.return_value = (False, "JWT Error")
    mock_clear_refresh.return_value = (True, None)
    
    success, error = auth_service.logout()
    
    assert success is False
    assert "JWT Error" in error

@patch('pdd.auth_service.clear_jwt_cache')
@patch('pdd.auth_service.clear_refresh_token')
def test_logout_total_failure(mock_clear_refresh, mock_clear_jwt):
    """Should combine errors if both fail."""
    mock_clear_jwt.return_value = (False, "JWT Error")
    mock_clear_refresh.return_value = (False, "Refresh Error")
    
    success, error = auth_service.logout()
    
    assert success is False
    assert "JWT Error" in error
    assert "Refresh Error" in error
    assert "; " in error

# --- Z3 Formal Verification ---

def test_z3_jwt_expiration_logic():
    """
    Formal verification of the JWT expiration logic using Z3.
    
    Logic to verify: 
    is_valid <=> expires_at > current_time + 300
    """
    s = Solver()
    
    # Variables
    expires_at = Real('expires_at')
    current_time = Real('current_time')
    is_valid = Bool('is_valid')
    
    # The logic implemented in the code:
    # if expires_at > time.time() + 300: return True
    # else: return False
    implementation_logic = (is_valid == (expires_at > current_time + 300))
    
    s.add(implementation_logic)
    
    # Property 1: If the token expires in exactly 300 seconds, it is INVALID.
    # We want to prove: (expires_at == current_time + 300) => Not(is_valid)
    # We negate the property and check for unsatisfiability (counter-example).
    s.push()
    s.add(expires_at == current_time + 300)
    s.add(is_valid)  # Assert it IS valid (negation of Not(is_valid))
    # Code: if expires_at > time.time() + 300
    # Case: expires_at = 1300, time = 1000. 1300 > 1300 is False.
    # So is_valid should be False.
    # If we assert is_valid is True, s.check() should be unsat.
    from z3 import unsat
    assert s.check() == unsat, f"Found counter-example for boundary condition: {s.model()}"
    s.pop()
    
    # Property 2: If token expires in 301 seconds, it is VALID.
    s.push()
    s.add(expires_at == current_time + 301)
    s.add(Not(is_valid)) # Negation of property
    if s.check() == sat:
        pytest.fail(f"Found counter-example for valid condition: {s.model()}")
    s.pop()

def test_z3_auth_status_state_machine():
    """
    Formal verification of the get_auth_status state logic.
    
    States:
    - Cache Valid (CV)
    - Refresh Token Exists (RT)
    
    Outputs:
    - Authenticated (Auth)
    - Cached (Cached)
    """
    s = Solver()
    
    CV = Bool('Cache_Valid')
    RT = Bool('Refresh_Token_Exists')
    Auth = Bool('Authenticated')
    Cached = Bool('Cached')
    
    # Logic from get_auth_status:
    # if CV: Auth=True, Cached=True
    # elif RT: Auth=True, Cached=False
    # else: Auth=False, Cached=False
    
    logic = And(
        Implies(CV, And(Auth, Cached)),
        Implies(And(Not(CV), RT), And(Auth, Not(Cached))),
        Implies(And(Not(CV), Not(RT)), And(Not(Auth), Not(Cached)))
    )
    
    s.add(logic)
    
    # Property 1: It is impossible to be Cached but not Authenticated.
    # Verify: Cached => Auth
    # Negation: Cached AND Not(Auth)
    s.push()
    s.add(Cached, Not(Auth))
    if s.check() == sat:
        pytest.fail("Found state where Cached=True but Authenticated=False")
    s.pop()
    
    # Property 2: It is impossible to be Cached if Cache is not Valid.
    # Verify: Cached => CV
    # Negation: Cached AND Not(CV)
    s.push()
    s.add(Cached, Not(CV))
    if s.check() == sat:
        pytest.fail("Found state where Cached=True but Cache_Valid=False")
    s.pop()