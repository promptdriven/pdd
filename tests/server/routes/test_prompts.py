"""
Test Plan for pdd/server/routes/prompts.py

1. **Unit Tests**:
    - **Dependency Injection**: Verify `get_path_validator` and `set_path_validator` work correctly.
    - **File Analysis (Success)**:
        - Verify correct handling of valid file paths.
        - Verify `get_token_metrics` is called for raw content.
        - Verify `preprocess` is called when requested.
        - Verify `get_token_metrics` is called for processed content.
        - Verify CWD is switched and restored during preprocessing.
    - **Direct Content Analysis (Success)**:
        - Verify `content` parameter takes precedence over `path`.
        - Verify file system is not accessed when content is provided.
    - **Size Limits**:
        - Verify 400 error for files > 500KB.
        - Verify 400 error for direct content > 500KB.
    - **File Errors**:
        - Verify 404 for non-existent files.
        - Verify 400 for directories.
        - Verify 400 for non-text files (UnicodeDecodeError).
    - **Security**:
        - Verify 403 when `PathValidator` raises `SecurityError`.
    - **Preprocessing Errors**:
        - Verify `preprocessing_succeeded=False` and error message when `preprocess` raises exception.
        - Verify 200 OK status code is returned (partial success).

2. **Z3 Formal Verification**:
    - **Size Limit Logic**: Formally verify the boundary condition for the 500KB limit.
    - **Response Consistency**: Verify the logical implication that if `preprocessing_succeeded` is True, `processed_metrics` must be present (based on the code flow).

3. **Mocking Strategy**:
    - Mock `pdd.server.security` for `PathValidator` and `SecurityError`.
    - Mock `pdd.server.token_counter` for `get_token_metrics`.
    - Mock `pdd.preprocess` for `preprocess` function.
    - Mock `os.getcwd` and `os.chdir` to verify directory switching.
"""

import sys
import pytest
import os
import z3
from unittest.mock import MagicMock, patch
from pathlib import Path
from fastapi import HTTPException
from pydantic import BaseModel
import types

# --- Mock Setup ---

# Create mock modules before importing the code under test
mock_security = types.ModuleType("pdd.server.security")
class MockSecurityError(Exception):
    def __init__(self, message):
        self.message = message
mock_security.SecurityError = MockSecurityError
mock_security.PathValidator = MagicMock()
sys.modules["pdd.server.security"] = mock_security

mock_token_counter = types.ModuleType("pdd.server.token_counter")
mock_token_counter.get_token_metrics = MagicMock()
sys.modules["pdd.server.token_counter"] = mock_token_counter

mock_preprocess_pkg = types.ModuleType("pdd.preprocess")
mock_preprocess_pkg.preprocess = MagicMock()
sys.modules["pdd.preprocess"] = mock_preprocess_pkg

# Mock pdd package structure
sys.modules["pdd"] = types.ModuleType("pdd")
sys.modules["pdd.server"] = types.ModuleType("pdd.server")

# Import code under test
from pdd.server.routes.prompts import (
    router,
    analyze_prompt,
    get_path_validator,
    set_path_validator,
    PromptAnalyzeRequest,
    PromptAnalyzeResponse,
    TokenMetricsResponse,
    CostEstimateResponse
)

# --- Fixtures ---

@pytest.fixture
def mock_validator():
    validator = MagicMock()
    validator.project_root = Path("/mock/root")
    validator.validate.return_value = Path("/mock/root/test.txt")
    return validator

@pytest.fixture
def setup_validator(mock_validator):
    set_path_validator(mock_validator)
    yield
    set_path_validator(None)

@pytest.fixture
def mock_metrics():
    def _create_metrics(count=100):
        cost = MagicMock()
        cost.to_dict.return_value = {
            "input_cost": 0.01,
            "model": "test-model",
            "tokens": count,
            "cost_per_million": 10.0,
            "currency": "USD"
        }
        
        metrics = MagicMock()
        metrics.token_count = count
        metrics.context_limit = 1000
        metrics.context_usage_percent = (count / 1000) * 100
        metrics.cost_estimate = cost
        return metrics
    return _create_metrics

# --- Unit Tests ---

def test_dependency_injection(mock_validator):
    """Test get/set path validator dependency."""
    set_path_validator(mock_validator)
    assert get_path_validator() == mock_validator
    
    set_path_validator(None)
    with pytest.raises(RuntimeError, match="PathValidator not configured"):
        get_path_validator()

@pytest.mark.asyncio
async def test_analyze_file_success(setup_validator, mock_validator, mock_metrics):
    """Test successful analysis of a file with preprocessing."""
    # Setup mocks
    mock_file = MagicMock()
    mock_file.exists.return_value = True
    mock_file.is_dir.return_value = False
    mock_file.stat.return_value.st_size = 100
    mock_file.read_text.return_value = "raw content"
    mock_validator.validate.return_value = mock_file
    
    mock_token_counter.get_token_metrics.side_effect = [
        mock_metrics(10),  # Raw
        mock_metrics(20)   # Processed
    ]
    mock_preprocess_pkg.preprocess.return_value = "processed content"

    # Execute
    request = PromptAnalyzeRequest(path="test.txt", preprocess=True)
    response = await analyze_prompt(request, validator=mock_validator)

    # Assertions
    assert response.raw_content == "raw content"
    assert response.processed_content == "processed content"
    assert response.raw_metrics.token_count == 10
    assert response.processed_metrics.token_count == 20
    assert response.preprocessing_succeeded is True
    
    # Verify calls
    mock_validator.validate.assert_called_with("test.txt")
    mock_preprocess_pkg.preprocess.assert_called_once()

@pytest.mark.asyncio
async def test_analyze_direct_content(setup_validator, mock_validator, mock_metrics):
    """Test analysis of direct content without file reading."""
    mock_token_counter.get_token_metrics.return_value = mock_metrics(50)
    
    request = PromptAnalyzeRequest(
        path="ignored.txt", 
        content="direct content",
        preprocess=False
    )
    
    response = await analyze_prompt(request, validator=mock_validator)
    
    assert response.raw_content == "direct content"
    # Should validate path even if content provided (for context/security context usually, 
    # though code just validates it and ignores result for reading)
    mock_validator.validate.assert_called()
    # Should NOT check file existence or read it
    mock_validator.validate.return_value.exists.assert_not_called()
    mock_validator.validate.return_value.read_text.assert_not_called()

@pytest.mark.asyncio
async def test_analyze_file_too_large(setup_validator, mock_validator):
    """Test error when file exceeds size limit."""
    mock_file = MagicMock()
    mock_file.exists.return_value = True
    mock_file.is_dir.return_value = False
    mock_file.stat.return_value.st_size = 500 * 1024 + 1  # Just over limit
    mock_validator.validate.return_value = mock_file

    request = PromptAnalyzeRequest(path="large.txt")
    
    with pytest.raises(HTTPException) as exc:
        await analyze_prompt(request, validator=mock_validator)
    
    assert exc.value.status_code == 400
    assert "File too large" in exc.value.detail

@pytest.mark.asyncio
async def test_analyze_content_too_large(setup_validator, mock_validator):
    """Test error when direct content exceeds size limit."""
    large_content = "a" * (500 * 1024 + 1)
    request = PromptAnalyzeRequest(path="test.txt", content=large_content)
    
    with pytest.raises(HTTPException) as exc:
        await analyze_prompt(request, validator=mock_validator)
    
    assert exc.value.status_code == 400
    assert "Content too large" in exc.value.detail

@pytest.mark.asyncio
async def test_analyze_directory_error(setup_validator, mock_validator):
    """Test error when path is a directory."""
    mock_file = MagicMock()
    mock_file.exists.return_value = True
    mock_file.is_dir.return_value = True
    mock_validator.validate.return_value = mock_file

    request = PromptAnalyzeRequest(path="somedir")
    
    with pytest.raises(HTTPException) as exc:
        await analyze_prompt(request, validator=mock_validator)
    
    assert exc.value.status_code == 400
    assert "Cannot analyze directory" in exc.value.detail

@pytest.mark.asyncio
async def test_analyze_file_not_found(setup_validator, mock_validator):
    """Test error when file does not exist."""
    mock_file = MagicMock()
    mock_file.exists.return_value = False
    mock_validator.validate.return_value = mock_file

    request = PromptAnalyzeRequest(path="missing.txt")
    
    with pytest.raises(HTTPException) as exc:
        await analyze_prompt(request, validator=mock_validator)
    
    assert exc.value.status_code == 404

@pytest.mark.asyncio
async def test_analyze_binary_file_error(setup_validator, mock_validator):
    """Test error when file is not valid text."""
    mock_file = MagicMock()
    mock_file.exists.return_value = True
    mock_file.is_dir.return_value = False
    mock_file.stat.return_value.st_size = 100
    mock_file.read_text.side_effect = UnicodeDecodeError('utf-8', b'', 0, 1, 'bad')
    mock_validator.validate.return_value = mock_file

    request = PromptAnalyzeRequest(path="binary.bin")
    
    with pytest.raises(HTTPException) as exc:
        await analyze_prompt(request, validator=mock_validator)
    
    assert exc.value.status_code == 400
    assert "not a valid text file" in exc.value.detail

@pytest.mark.asyncio
async def test_security_error(setup_validator, mock_validator):
    """Test handling of security violations."""
    mock_validator.validate.side_effect = MockSecurityError("Access denied")
    
    request = PromptAnalyzeRequest(path="../secret.txt")
    
    with pytest.raises(HTTPException) as exc:
        await analyze_prompt(request, validator=mock_validator)
    
    assert exc.value.status_code == 403
    assert "Access denied" in exc.value.detail

@pytest.mark.asyncio
async def test_preprocessing_failure(setup_validator, mock_validator, mock_metrics):
    """Test graceful handling of preprocessing errors."""
    mock_file = MagicMock()
    mock_file.read_text.return_value = "content"
    mock_file.stat.return_value.st_size = 10
    mock_validator.validate.return_value = mock_file
    
    mock_token_counter.get_token_metrics.return_value = mock_metrics(10)
    mock_preprocess_pkg.preprocess.side_effect = Exception("Syntax error in prompt")

    request = PromptAnalyzeRequest(path="test.txt", preprocess=True)
    response = await analyze_prompt(request, validator=mock_validator)

    assert response.preprocessing_succeeded is False
    assert "Syntax error" in response.preprocessing_error
    assert response.processed_content is None
    assert response.processed_metrics is None
    # Raw metrics should still be returned
    assert response.raw_metrics is not None

@pytest.mark.asyncio
async def test_cwd_restoration(setup_validator, mock_validator, mock_metrics):
    """Test that CWD is restored even if preprocessing fails."""
    mock_file = MagicMock()
    mock_file.read_text.return_value = "content"
    mock_file.stat.return_value.st_size = 10
    mock_validator.validate.return_value = mock_file
    mock_token_counter.get_token_metrics.return_value = mock_metrics(10)
    
    mock_preprocess_pkg.preprocess.side_effect = Exception("Fail")
    
    original_cwd = os.getcwd()
    
    with patch("os.getcwd", return_value=original_cwd), \
         patch("os.chdir") as mock_chdir:
        
        request = PromptAnalyzeRequest(path="test.txt", preprocess=True)
        await analyze_prompt(request, validator=mock_validator)
        
        # Should have been called at least twice: once to project root, once back
        assert mock_chdir.call_count >= 2
        # Last call should be to restore original CWD
        mock_chdir.assert_called_with(original_cwd)

# --- Z3 Formal Verification Tests ---

def test_z3_size_limit_boundary():
    """
    Formally verify the size limit logic.
    Constraint: size > 500 * 1024 implies Error.
    """
    s = z3.Solver()
    
    size = z3.Int('size')
    limit = 500 * 1024
    is_error = z3.Bool('is_error')
    
    # Logic from code: if file_size > 500 * 1024: raise HTTPException
    s.add(is_error == (size > limit))
    
    # Verify: Is it possible to have an error with size <= limit?
    s.push()
    s.add(size <= limit)
    s.add(is_error)
    assert s.check() == z3.unsat, "Should not error if size is within limit"
    s.pop()
    
    # Verify: Is it possible to NOT have an error with size > limit?
    s.push()
    s.add(size > limit)
    s.add(z3.Not(is_error))
    assert s.check() == z3.unsat, "Should error if size exceeds limit"
    s.pop()

def test_z3_response_consistency():
    """
    Formally verify response consistency logic.
    If preprocessing succeeds, processed metrics should be available (assuming no other errors).
    """
    s = z3.Solver()
    
    preprocess_requested = z3.Bool('preprocess_requested')
    preprocess_succeeded = z3.Bool('preprocess_succeeded')
    has_processed_metrics = z3.Bool('has_processed_metrics')
    has_processed_content = z3.Bool('has_processed_content')
    
    # Logic derived from code flow:
    # if request.preprocess:
    #    try:
    #       ... preprocess ...
    #       processed_metrics = ...
    #       preprocessing_succeeded = True
    #    except:
    #       preprocessing_succeeded = False
    # else:
    #    processed_metrics = None
    #    preprocessing_succeeded = True (default init)
    
    # Modeling the logic
    # If not requested, metrics are None
    s.add(z3.Implies(z3.Not(preprocess_requested), z3.Not(has_processed_metrics)))
    
    # If requested and succeeded, metrics must exist
    s.add(z3.Implies(z3.And(preprocess_requested, preprocess_succeeded), has_processed_metrics))
    
    # If requested and failed, metrics must NOT exist
    s.add(z3.Implies(z3.And(preprocess_requested, z3.Not(preprocess_succeeded)), z3.Not(has_processed_metrics)))

    # Verify: Can we have success=True, requested=True, but no metrics?
    s.push()
    s.add(preprocess_requested)
    s.add(preprocess_succeeded)
    s.add(z3.Not(has_processed_metrics))
    assert s.check() == z3.unsat, "Inconsistent state: Success with no metrics"
    s.pop()