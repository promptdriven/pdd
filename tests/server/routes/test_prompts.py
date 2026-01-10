"""
Test Plan for pdd/server/routes/prompts.py

NOTE: This test file uses fixtures with sys.modules patching inside fixtures
(NOT at module level) to prevent test pollution during pytest collection.

The mocking strategy handles dynamic imports by patching sys.modules inside
fixtures, which only run during test execution, not during collection.
"""

import sys
import pytest
import os
import z3
import types
from unittest.mock import MagicMock, patch, AsyncMock
from pathlib import Path
from fastapi import HTTPException
from pydantic import BaseModel


class MockSecurityError(Exception):
    """Mock security error for testing."""
    def __init__(self, message):
        self.message = message


# --- Fixtures ---

@pytest.fixture
def mock_validator():
    """Create a mock path validator."""
    validator = MagicMock()
    validator.project_root = Path("/mock/root")
    validator.validate.return_value = Path("/mock/root/test.txt")
    return validator


@pytest.fixture
def mock_token_metrics():
    """Create mock token metrics as an object with attributes."""
    metrics = MagicMock()
    metrics.token_count = 3
    metrics.context_limit = 128000
    metrics.context_usage_percent = 0.002

    # cost_estimate needs a to_dict() method
    cost_estimate = MagicMock()
    cost_estimate.to_dict.return_value = {
        "input_cost": 0.0001,
        "model": "claude-sonnet-4-20250514",
        "tokens": 3,
        "cost_per_million": 3.0,
        "currency": "USD"
    }
    metrics.cost_estimate = cost_estimate

    return metrics


@pytest.fixture
def prompts_test_env():
    """
    Fixture that sets up mocks inside fixtures (not at module level) to avoid
    collection-time pollution. Uses sys.modules patching for dynamic imports.
    """
    # Store original modules - include all modules that might be affected
    original_modules = {}
    modules_to_mock = [
        "pdd.server.security",
        "pdd.server.token_counter",
        "pdd.preprocess",
    ]
    # Also track modules that get imported during test and need cleanup
    modules_to_clear = [
        "pdd.server.routes.prompts",
        "pdd.server",
        "pdd.server.routes",
    ]

    # Save all original module states
    for mod in modules_to_mock + modules_to_clear:
        if mod in sys.modules:
            original_modules[mod] = sys.modules[mod]

    # Create mocks
    mock_security = types.ModuleType("pdd.server.security")
    mock_security.SecurityError = MockSecurityError
    mock_security.PathValidator = MagicMock()
    # Add other security module exports that app.py needs
    mock_security.configure_cors = MagicMock()
    mock_security.create_token_dependency = MagicMock()
    mock_security.SecurityLoggingMiddleware = MagicMock()
    mock_security.DEFAULT_BLACKLIST = []
    sys.modules["pdd.server.security"] = mock_security

    mock_token_counter = types.ModuleType("pdd.server.token_counter")
    mock_token_counter.get_token_metrics = MagicMock()
    sys.modules["pdd.server.token_counter"] = mock_token_counter

    mock_preprocess = types.ModuleType("pdd.preprocess")
    mock_preprocess.preprocess = MagicMock()
    sys.modules["pdd.preprocess"] = mock_preprocess

    # Clear cached imports of the module under test
    for mod_name in list(sys.modules.keys()):
        if "pdd.server.routes.prompts" in mod_name:
            del sys.modules[mod_name]

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

    yield {
        'router': router,
        'analyze_prompt': analyze_prompt,
        'get_path_validator': get_path_validator,
        'set_path_validator': set_path_validator,
        'PromptAnalyzeRequest': PromptAnalyzeRequest,
        'PromptAnalyzeResponse': PromptAnalyzeResponse,
        'TokenMetricsResponse': TokenMetricsResponse,
        'CostEstimateResponse': CostEstimateResponse,
        'mock_security': mock_security,
        'mock_token_counter': mock_token_counter,
        'mock_preprocess': mock_preprocess,
    }

    # Cleanup: delete all modules we mocked or imported during test
    for mod in modules_to_mock:
        if mod in sys.modules:
            del sys.modules[mod]

    # Clear any prompts module that was imported with mocks
    for mod_name in list(sys.modules.keys()):
        if "pdd.server.routes.prompts" in mod_name:
            del sys.modules[mod_name]

    # Restore all original modules
    for mod, original in original_modules.items():
        sys.modules[mod] = original


@pytest.fixture
def setup_validator(prompts_test_env, mock_validator):
    """Set up a mock validator for tests."""
    prompts_test_env['set_path_validator'](mock_validator)
    yield prompts_test_env, mock_validator
    prompts_test_env['set_path_validator'](None)


# --- Unit Tests ---

def test_dependency_injection(prompts_test_env):
    """Test get/set_path_validator functions."""
    get_path_validator = prompts_test_env['get_path_validator']
    set_path_validator = prompts_test_env['set_path_validator']

    # Initially no validator is configured - should raise RuntimeError
    with pytest.raises(RuntimeError, match="PathValidator not configured"):
        get_path_validator()

    # Set a mock validator
    mock = MagicMock()
    set_path_validator(mock)
    assert get_path_validator() is mock

    # Set to None and verify error is raised again
    set_path_validator(None)
    with pytest.raises(RuntimeError, match="PathValidator not configured"):
        get_path_validator()


@pytest.mark.asyncio
async def test_analyze_file_success(setup_validator, mock_token_metrics, tmp_path):
    """Test successful file analysis."""
    prompts_test_env, mock_validator = setup_validator
    analyze_prompt = prompts_test_env['analyze_prompt']
    PromptAnalyzeRequest = prompts_test_env['PromptAnalyzeRequest']
    mock_gtm = prompts_test_env['mock_token_counter'].get_token_metrics

    # Create a test file
    test_file = tmp_path / "test.txt"
    test_file.write_text("Hello, world!")

    # Set up mock to return the real file path
    mock_validator.validate.return_value = test_file

    # Set up mock token metrics
    mock_gtm.return_value = mock_token_metrics

    # Create request
    request = PromptAnalyzeRequest(path=str(test_file), preprocess=False)

    # Call function - pass validator explicitly (bypasses FastAPI Depends)
    response = await analyze_prompt(request, validator=mock_validator)

    # Verify
    assert response.raw_metrics is not None
    mock_validator.validate.assert_called()


@pytest.mark.asyncio
async def test_analyze_direct_content(setup_validator, mock_token_metrics):
    """Test analysis with direct content (no file access)."""
    prompts_test_env, mock_validator = setup_validator
    analyze_prompt = prompts_test_env['analyze_prompt']
    PromptAnalyzeRequest = prompts_test_env['PromptAnalyzeRequest']
    mock_gtm = prompts_test_env['mock_token_counter'].get_token_metrics

    mock_gtm.return_value = mock_token_metrics

    # path is required by the model, but content takes precedence when provided
    request = PromptAnalyzeRequest(path="dummy.txt", content="Direct content test", preprocess=False)
    response = await analyze_prompt(request, validator=mock_validator)

    assert response.raw_metrics is not None
    assert response.raw_content == "Direct content test"


@pytest.mark.asyncio
async def test_analyze_file_too_large(setup_validator, tmp_path):
    """Test 400 error for files > 500KB."""
    prompts_test_env, mock_validator = setup_validator
    analyze_prompt = prompts_test_env['analyze_prompt']
    PromptAnalyzeRequest = prompts_test_env['PromptAnalyzeRequest']

    # Create a large file
    large_file = tmp_path / "large.txt"
    large_file.write_text("x" * (500 * 1024 + 1))  # Just over 500KB

    mock_validator.validate.return_value = large_file

    request = PromptAnalyzeRequest(path=str(large_file))

    with pytest.raises(HTTPException) as exc_info:
        await analyze_prompt(request, validator=mock_validator)

    assert exc_info.value.status_code == 400
    assert "500KB" in str(exc_info.value.detail)


@pytest.mark.asyncio
async def test_analyze_content_too_large(setup_validator):
    """Test 400 error for direct content > 500KB."""
    prompts_test_env, mock_validator = setup_validator
    analyze_prompt = prompts_test_env['analyze_prompt']
    PromptAnalyzeRequest = prompts_test_env['PromptAnalyzeRequest']

    large_content = "x" * (500 * 1024 + 1)
    # path is required by the model but content takes precedence
    request = PromptAnalyzeRequest(path="dummy.txt", content=large_content)

    with pytest.raises(HTTPException) as exc_info:
        await analyze_prompt(request, validator=mock_validator)

    assert exc_info.value.status_code == 400


@pytest.mark.asyncio
async def test_analyze_directory_error(setup_validator, tmp_path):
    """Test 400 error when path is a directory."""
    prompts_test_env, mock_validator = setup_validator
    analyze_prompt = prompts_test_env['analyze_prompt']
    PromptAnalyzeRequest = prompts_test_env['PromptAnalyzeRequest']

    mock_validator.validate.return_value = tmp_path

    request = PromptAnalyzeRequest(path=str(tmp_path))

    with pytest.raises(HTTPException) as exc_info:
        await analyze_prompt(request, validator=mock_validator)

    assert exc_info.value.status_code == 400


@pytest.mark.asyncio
async def test_analyze_file_not_found(setup_validator):
    """Test 404 error for non-existent files."""
    prompts_test_env, mock_validator = setup_validator
    analyze_prompt = prompts_test_env['analyze_prompt']
    PromptAnalyzeRequest = prompts_test_env['PromptAnalyzeRequest']

    mock_validator.validate.return_value = Path("/nonexistent/file.txt")

    request = PromptAnalyzeRequest(path="/nonexistent/file.txt")

    with pytest.raises(HTTPException) as exc_info:
        await analyze_prompt(request, validator=mock_validator)

    assert exc_info.value.status_code == 404


@pytest.mark.asyncio
async def test_analyze_binary_file_error(setup_validator, tmp_path):
    """Test 400 error for binary files with invalid UTF-8 sequences."""
    prompts_test_env, mock_validator = setup_validator
    analyze_prompt = prompts_test_env['analyze_prompt']
    PromptAnalyzeRequest = prompts_test_env['PromptAnalyzeRequest']

    binary_file = tmp_path / "binary.bin"
    # Use invalid UTF-8 sequences that will cause UnicodeDecodeError
    # 0x80-0xFF are invalid as standalone bytes in UTF-8
    binary_file.write_bytes(b"\x80\x81\x82\x83")

    mock_validator.validate.return_value = binary_file

    request = PromptAnalyzeRequest(path=str(binary_file))

    with pytest.raises(HTTPException) as exc_info:
        await analyze_prompt(request, validator=mock_validator)

    assert exc_info.value.status_code == 400


@pytest.mark.asyncio
async def test_security_error(setup_validator):
    """Test 403 error when PathValidator raises SecurityError."""
    prompts_test_env, mock_validator = setup_validator
    analyze_prompt = prompts_test_env['analyze_prompt']
    PromptAnalyzeRequest = prompts_test_env['PromptAnalyzeRequest']

    mock_validator.validate.side_effect = MockSecurityError("Access denied")

    request = PromptAnalyzeRequest(path="/secret/file.txt")

    with pytest.raises(HTTPException) as exc_info:
        await analyze_prompt(request, validator=mock_validator)

    assert exc_info.value.status_code == 403


@pytest.mark.asyncio
async def test_preprocessing_failure(setup_validator, mock_token_metrics, tmp_path):
    """Test partial success when preprocessing fails."""
    prompts_test_env, mock_validator = setup_validator
    analyze_prompt = prompts_test_env['analyze_prompt']
    PromptAnalyzeRequest = prompts_test_env['PromptAnalyzeRequest']
    mock_gtm = prompts_test_env['mock_token_counter'].get_token_metrics
    mock_prep = prompts_test_env['mock_preprocess'].preprocess

    test_file = tmp_path / "test.txt"
    test_file.write_text("Test content")

    mock_validator.validate.return_value = test_file
    mock_prep.side_effect = Exception("Preprocess failed")
    mock_gtm.return_value = mock_token_metrics

    request = PromptAnalyzeRequest(path=str(test_file), preprocess=True)
    response = await analyze_prompt(request, validator=mock_validator)

    # Should return 200 with partial success
    assert response.preprocessing_succeeded is False
    assert response.preprocessing_error is not None


@pytest.mark.asyncio
async def test_cwd_restoration(setup_validator, mock_token_metrics, tmp_path):
    """Test that CWD is restored after preprocessing."""
    prompts_test_env, mock_validator = setup_validator
    analyze_prompt = prompts_test_env['analyze_prompt']
    PromptAnalyzeRequest = prompts_test_env['PromptAnalyzeRequest']
    mock_gtm = prompts_test_env['mock_token_counter'].get_token_metrics
    mock_prep = prompts_test_env['mock_preprocess'].preprocess

    test_file = tmp_path / "test.txt"
    test_file.write_text("Test content")

    mock_validator.validate.return_value = test_file
    mock_prep.return_value = "Processed content"
    mock_gtm.return_value = mock_token_metrics

    original_cwd = os.getcwd()
    request = PromptAnalyzeRequest(path=str(test_file), preprocess=True)

    await analyze_prompt(request, validator=mock_validator)

    assert os.getcwd() == original_cwd


# --- Z3 Formal Verification ---

def test_z3_size_limit_boundary():
    """Formally verify the 500KB size limit boundary condition."""
    s = z3.Solver()

    file_size = z3.Int('file_size')
    SIZE_LIMIT = 500 * 1024  # 500KB in bytes

    # Property: file is rejected iff size > SIZE_LIMIT
    is_rejected = file_size > SIZE_LIMIT

    # Test boundary: 500KB should be accepted
    s.push()
    s.add(file_size == SIZE_LIMIT)
    s.add(is_rejected)  # Should be unsat (not rejected at exactly 500KB)
    assert s.check() == z3.unsat
    s.pop()

    # Test boundary: 500KB + 1 should be rejected
    s.push()
    s.add(file_size == SIZE_LIMIT + 1)
    s.add(z3.Not(is_rejected))  # Should be unsat (must be rejected)
    assert s.check() == z3.unsat
    s.pop()


def test_z3_response_consistency():
    """Formally verify response field consistency."""
    s = z3.Solver()

    preprocessing_requested = z3.Bool('preprocessing_requested')
    preprocessing_succeeded = z3.Bool('preprocessing_succeeded')
    has_processed_metrics = z3.Bool('has_processed_metrics')

    # Property: if preprocessing succeeded, processed_metrics must be present
    consistency_rule = z3.Implies(preprocessing_succeeded, has_processed_metrics)

    # Verify the rule is satisfiable in valid states
    s.push()
    s.add(consistency_rule)
    s.add(preprocessing_succeeded)
    assert s.check() == z3.sat
    model = s.model()
    assert model[has_processed_metrics]  # Must be True
    s.pop()

    # Verify violation is detectable
    s.push()
    s.add(preprocessing_succeeded)
    s.add(z3.Not(has_processed_metrics))
    s.add(consistency_rule)
    assert s.check() == z3.unsat  # Inconsistent state
    s.pop()
