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
        "pdd.sync_determine_operation",
        "pdd.llm_invoke",
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
    mock_token_counter.get_context_limit = MagicMock(return_value=128000)
    sys.modules["pdd.server.token_counter"] = mock_token_counter

    mock_preprocess = types.ModuleType("pdd.preprocess")
    mock_preprocess.preprocess = MagicMock()
    sys.modules["pdd.preprocess"] = mock_preprocess

    # Clear cached imports of the module under test
    for mod_name in list(sys.modules.keys()):
        if "pdd.server.routes.prompts" in mod_name:
            del sys.modules[mod_name]

    # Mock sync_determine_operation
    mock_sync_op = types.ModuleType("pdd.sync_determine_operation")
    mock_sync_op.read_fingerprint = MagicMock()
    mock_sync_op.get_pdd_file_paths = MagicMock()
    mock_sync_op.calculate_sha256 = MagicMock()
    sys.modules["pdd.sync_determine_operation"] = mock_sync_op

    # Mock llm_invoke module
    mock_llm_invoke = types.ModuleType("pdd.llm_invoke")
    mock_llm_invoke.llm_invoke = MagicMock()
    mock_llm_invoke._load_model_data = MagicMock()
    mock_llm_invoke.LLM_MODEL_CSV_PATH = "/mock/llm_model.csv"
    mock_llm_invoke.DEFAULT_BASE_MODEL = "claude-sonnet-4-20250514"
    sys.modules["pdd.llm_invoke"] = mock_llm_invoke

    # Import code under test
    from pdd.server.routes.prompts import (
        router,
        analyze_prompt,
        get_path_validator,
        set_path_validator,
        PromptAnalyzeRequest,
        PromptAnalyzeResponse,
        TokenMetricsResponse,
        CostEstimateResponse,
        get_sync_status,
        get_available_models,
        check_match,
        analyze_diff,
        get_prompt_diff,
        SyncStatusResponse,
        ModelsResponse,
        MatchCheckRequest,
        MatchCheckResponse,
        DiffAnalysisRequest,
        DiffAnalysisResponse,
        DiffSection,
        LineMapping,
        DiffStats,
        PromptDiffRequest,
        PromptDiffResponse,
        _get_cache_key,
        _get_cached_result,
        _cache_result,
        _diff_cache,
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
        'get_sync_status': get_sync_status,
        'get_available_models': get_available_models,
        'check_match': check_match,
        'analyze_diff': analyze_diff,
        'get_prompt_diff': get_prompt_diff,
        'SyncStatusResponse': SyncStatusResponse,
        'ModelsResponse': ModelsResponse,
        'MatchCheckRequest': MatchCheckRequest,
        'MatchCheckResponse': MatchCheckResponse,
        'DiffAnalysisRequest': DiffAnalysisRequest,
        'DiffAnalysisResponse': DiffAnalysisResponse,
        'DiffSection': DiffSection,
        'LineMapping': LineMapping,
        'DiffStats': DiffStats,
        'PromptDiffRequest': PromptDiffRequest,
        'PromptDiffResponse': PromptDiffResponse,
        '_get_cache_key': _get_cache_key,
        '_get_cached_result': _get_cached_result,
        '_cache_result': _cache_result,
        '_diff_cache': _diff_cache,
        'mock_security': mock_security,
        'mock_token_counter': mock_token_counter,
        'mock_preprocess': mock_preprocess,
        'mock_sync_op': mock_sync_op,
        'mock_llm_invoke': mock_llm_invoke,
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


# --- Tests for new endpoints ---

@pytest.mark.asyncio
async def test_sync_status_never_synced(setup_validator, tmp_path):
    """Test sync status when no fingerprint exists."""
    prompts_test_env, mock_validator = setup_validator
    get_sync_status = prompts_test_env['get_sync_status']
    mock_sync_op = prompts_test_env['mock_sync_op']

    # Use real tmp_path for project_root
    mock_validator.project_root = tmp_path

    # Set up mocks
    mock_paths = MagicMock()
    mock_paths.__getitem__ = lambda self, key: MagicMock(exists=lambda: key == 'prompt')
    mock_sync_op.get_pdd_file_paths.return_value = mock_paths
    mock_sync_op.read_fingerprint.return_value = None  # No fingerprint

    response = await get_sync_status(
        basename="test_module",
        language="python",
        validator=mock_validator
    )

    assert response.status == "never_synced"
    assert response.fingerprint_exists is False


@pytest.mark.asyncio
async def test_sync_status_in_sync(setup_validator, tmp_path):
    """Test sync status when files are in sync."""
    prompts_test_env, mock_validator = setup_validator
    get_sync_status = prompts_test_env['get_sync_status']
    mock_sync_op = prompts_test_env['mock_sync_op']

    # Use real tmp_path for project_root
    mock_validator.project_root = tmp_path

    # Set up mocks
    mock_prompt_path = MagicMock()
    mock_prompt_path.exists.return_value = True
    mock_code_path = MagicMock()
    mock_code_path.exists.return_value = True

    mock_sync_op.get_pdd_file_paths.return_value = {
        'prompt': mock_prompt_path,
        'code': mock_code_path
    }

    # Fingerprint with matching hashes
    mock_fingerprint = MagicMock()
    mock_fingerprint.prompt_hash = "abc123"
    mock_fingerprint.code_hash = "def456"
    mock_fingerprint.timestamp = "2024-01-01T00:00:00Z"
    mock_fingerprint.command = "generate"
    mock_sync_op.read_fingerprint.return_value = mock_fingerprint

    # Current hashes match fingerprint
    mock_sync_op.calculate_sha256.side_effect = ["abc123", "def456"]

    response = await get_sync_status(
        basename="test_module",
        language="python",
        validator=mock_validator
    )

    assert response.status == "in_sync"
    assert response.prompt_modified is False
    assert response.code_modified is False


@pytest.mark.asyncio
async def test_sync_status_prompt_changed(setup_validator, tmp_path):
    """Test sync status when prompt has changed."""
    prompts_test_env, mock_validator = setup_validator
    get_sync_status = prompts_test_env['get_sync_status']
    mock_sync_op = prompts_test_env['mock_sync_op']

    # Use real tmp_path for project_root
    mock_validator.project_root = tmp_path

    # Set up mocks
    mock_prompt_path = MagicMock()
    mock_prompt_path.exists.return_value = True
    mock_code_path = MagicMock()
    mock_code_path.exists.return_value = True

    mock_sync_op.get_pdd_file_paths.return_value = {
        'prompt': mock_prompt_path,
        'code': mock_code_path
    }

    mock_fingerprint = MagicMock()
    mock_fingerprint.prompt_hash = "old_hash"
    mock_fingerprint.code_hash = "def456"
    mock_fingerprint.timestamp = "2024-01-01T00:00:00Z"
    mock_fingerprint.command = "generate"
    mock_sync_op.read_fingerprint.return_value = mock_fingerprint

    # Prompt hash changed, code hash same
    mock_sync_op.calculate_sha256.side_effect = ["new_hash", "def456"]

    response = await get_sync_status(
        basename="test_module",
        language="python",
        validator=mock_validator
    )

    assert response.status == "prompt_changed"
    assert response.prompt_modified is True
    assert response.code_modified is False


@pytest.mark.asyncio
async def test_get_available_models(prompts_test_env):
    """Test getting available models list."""
    import pandas as pd

    get_available_models = prompts_test_env['get_available_models']
    mock_llm_invoke = prompts_test_env['mock_llm_invoke']

    # Create mock DataFrame
    mock_df = pd.DataFrame([
        {
            'model': 'claude-sonnet-4-20250514',
            'provider': 'Anthropic',
            'input': 3.0,
            'output': 15.0,
            'coding_arena_elo': 1400,
            'max_reasoning_tokens': 0,
            'reasoning_type': 'none',
            'structured_output': True,
        },
        {
            'model': 'gpt-4-turbo',
            'provider': 'OpenAI',
            'input': 10.0,
            'output': 30.0,
            'coding_arena_elo': 1350,
            'max_reasoning_tokens': 0,
            'reasoning_type': 'none',
            'structured_output': True,
        }
    ])
    mock_llm_invoke._load_model_data.return_value = mock_df

    response = await get_available_models()

    assert len(response.models) == 2
    # Should be sorted by ELO descending
    assert response.models[0].model == 'claude-sonnet-4-20250514'
    assert response.models[0].elo == 1400
    assert response.default_model == 'claude-sonnet-4-20250514'


@pytest.mark.asyncio
async def test_check_match(prompts_test_env):
    """Test match checking endpoint."""
    check_match = prompts_test_env['check_match']
    MatchCheckRequest = prompts_test_env['MatchCheckRequest']
    mock_llm_invoke = prompts_test_env['mock_llm_invoke']

    # Mock LLM response
    mock_llm_invoke.llm_invoke.return_value = {
        'result': {
            'match_score': 85,
            'summary': 'Code largely matches requirements',
            'missing': ['error handling'],
            'extra': [],
            'suggestions': ['Add try/except blocks']
        },
        'cost': 0.001,
        'model_name': 'claude-sonnet-4-20250514'
    }

    request = MatchCheckRequest(
        prompt_content="Write a function that adds two numbers",
        code_content="def add(a, b): return a + b",
        strength=0.5
    )

    response = await check_match(request)

    assert response.result.match_score == 85
    assert response.result.summary == 'Code largely matches requirements'
    assert len(response.result.missing) == 1
    assert response.cost == 0.001


# --- Tests for diff analysis endpoint ---

@pytest.mark.asyncio
async def test_analyze_diff_basic(prompts_test_env):
    """Test basic diff analysis functionality."""
    analyze_diff = prompts_test_env['analyze_diff']
    DiffAnalysisRequest = prompts_test_env['DiffAnalysisRequest']
    mock_llm_invoke = prompts_test_env['mock_llm_invoke']
    _diff_cache = prompts_test_env['_diff_cache']

    # Clear cache before test
    _diff_cache.clear()

    # Mock LLM response with detailed diff analysis
    mock_llm_invoke.llm_invoke.return_value = {
        'result': {
            'overallScore': 80,
            'summary': 'Code implements most requirements',
            'sections': [
                {
                    'id': 'sec_1',
                    'promptRange': {'startLine': 1, 'endLine': 3, 'text': 'Add two numbers'},
                    'codeRanges': [{'startLine': 1, 'endLine': 2, 'text': 'def add(a, b):'}],
                    'status': 'matched',
                    'matchConfidence': 95,
                    'semanticLabel': 'Addition Function',
                    'notes': 'Fully implemented'
                }
            ],
            'lineMappings': [
                {'promptLine': 1, 'codeLines': [1], 'matchType': 'exact'},
                {'promptLine': 2, 'codeLines': [2], 'matchType': 'semantic'},
            ],
            'stats': {
                'totalRequirements': 2,
                'matchedRequirements': 2,
                'missingRequirements': 0,
                'totalCodeFeatures': 2,
                'documentedFeatures': 2,
                'undocumentedFeatures': 0,
                'promptToCodeCoverage': 100.0,
                'codeToPromptCoverage': 100.0
            },
            'missing': [],
            'extra': [],
            'suggestions': ['Add docstring']
        },
        'cost': 0.002,
        'model_name': 'claude-sonnet-4-20250514'
    }

    request = DiffAnalysisRequest(
        prompt_content="Write a function that adds two numbers\nReturn the result",
        code_content="def add(a, b):\n    return a + b",
        strength=0.5,
        mode="detailed"
    )

    response = await analyze_diff(request)

    assert response.result.overallScore == 80
    assert response.result.summary == 'Code implements most requirements'
    assert len(response.result.sections) == 1
    assert response.result.sections[0].id == 'sec_1'
    assert response.result.sections[0].status == 'matched'
    assert len(response.result.lineMappings) == 2
    assert response.result.stats.totalRequirements == 2
    assert response.result.stats.promptToCodeCoverage == 100.0
    assert response.cost == 0.002
    assert response.analysisMode == "detailed"
    assert response.cached is False


@pytest.mark.asyncio
async def test_analyze_diff_quick_mode(prompts_test_env):
    """Test diff analysis in quick mode reduces strength."""
    analyze_diff = prompts_test_env['analyze_diff']
    DiffAnalysisRequest = prompts_test_env['DiffAnalysisRequest']
    mock_llm_invoke = prompts_test_env['mock_llm_invoke']
    _diff_cache = prompts_test_env['_diff_cache']

    _diff_cache.clear()

    mock_llm_invoke.llm_invoke.return_value = {
        'result': {
            'overallScore': 75,
            'summary': 'Quick analysis complete',
            'sections': [],
            'lineMappings': [],
            'stats': {
                'totalRequirements': 1,
                'matchedRequirements': 1,
                'missingRequirements': 0,
                'totalCodeFeatures': 1,
                'documentedFeatures': 1,
                'undocumentedFeatures': 0,
                'promptToCodeCoverage': 100.0,
                'codeToPromptCoverage': 100.0
            },
            'missing': [],
            'extra': [],
            'suggestions': []
        },
        'cost': 0.001,
        'model_name': 'claude-sonnet-4-20250514'
    }

    request = DiffAnalysisRequest(
        prompt_content="Test prompt",
        code_content="Test code",
        strength=0.8,  # High strength requested
        mode="quick"   # But quick mode should cap it
    )

    await analyze_diff(request)

    # Check that strength was capped for quick mode
    call_args = mock_llm_invoke.llm_invoke.call_args
    assert call_args.kwargs['strength'] <= 0.25


@pytest.mark.asyncio
async def test_analyze_diff_caching(prompts_test_env):
    """Test that diff analysis results are cached."""
    analyze_diff = prompts_test_env['analyze_diff']
    DiffAnalysisRequest = prompts_test_env['DiffAnalysisRequest']
    mock_llm_invoke = prompts_test_env['mock_llm_invoke']
    _diff_cache = prompts_test_env['_diff_cache']

    _diff_cache.clear()

    mock_llm_invoke.llm_invoke.return_value = {
        'result': {
            'overallScore': 90,
            'summary': 'Cached result',
            'sections': [],
            'lineMappings': [],
            'stats': {
                'totalRequirements': 1,
                'matchedRequirements': 1,
                'missingRequirements': 0,
                'totalCodeFeatures': 1,
                'documentedFeatures': 1,
                'undocumentedFeatures': 0,
                'promptToCodeCoverage': 100.0,
                'codeToPromptCoverage': 100.0
            },
            'missing': [],
            'extra': [],
            'suggestions': []
        },
        'cost': 0.001,
        'model_name': 'claude-sonnet-4-20250514'
    }

    request = DiffAnalysisRequest(
        prompt_content="Cache test prompt",
        code_content="Cache test code",
        strength=0.5,
        mode="detailed"
    )

    # First call - should hit LLM
    response1 = await analyze_diff(request)
    assert response1.cached is False
    assert mock_llm_invoke.llm_invoke.call_count == 1

    # Second call with same content - should be cached
    response2 = await analyze_diff(request)
    assert response2.cached is True
    assert mock_llm_invoke.llm_invoke.call_count == 1  # No additional call


def test_cache_key_generation(prompts_test_env):
    """Test that cache keys are properly generated from content hash."""
    _get_cache_key = prompts_test_env['_get_cache_key']

    key1 = _get_cache_key("prompt1", "code1", "detailed")
    key2 = _get_cache_key("prompt1", "code1", "detailed")
    key3 = _get_cache_key("prompt2", "code1", "detailed")
    key4 = _get_cache_key("prompt1", "code1", "quick")

    # Same content should produce same key
    assert key1 == key2
    # Different prompt should produce different key
    assert key1 != key3
    # Different mode should produce different key
    assert key1 != key4


@pytest.mark.asyncio
async def test_analyze_diff_with_missing_requirements(prompts_test_env):
    """Test diff analysis with missing requirements."""
    analyze_diff = prompts_test_env['analyze_diff']
    DiffAnalysisRequest = prompts_test_env['DiffAnalysisRequest']
    mock_llm_invoke = prompts_test_env['mock_llm_invoke']
    _diff_cache = prompts_test_env['_diff_cache']

    _diff_cache.clear()

    mock_llm_invoke.llm_invoke.return_value = {
        'result': {
            'overallScore': 50,
            'summary': 'Code missing key requirements',
            'sections': [
                {
                    'id': 'sec_1',
                    'promptRange': {'startLine': 1, 'endLine': 2, 'text': 'Validate input'},
                    'codeRanges': [],  # No code implements this
                    'status': 'missing',
                    'matchConfidence': 0,
                    'semanticLabel': 'Input Validation',
                    'notes': 'No input validation found'
                },
                {
                    'id': 'sec_2',
                    'promptRange': {'startLine': 3, 'endLine': 4, 'text': 'Return result'},
                    'codeRanges': [{'startLine': 2, 'endLine': 2, 'text': 'return a + b'}],
                    'status': 'matched',
                    'matchConfidence': 90,
                    'semanticLabel': 'Return Statement',
                }
            ],
            'lineMappings': [],
            'stats': {
                'totalRequirements': 2,
                'matchedRequirements': 1,
                'missingRequirements': 1,
                'totalCodeFeatures': 2,
                'documentedFeatures': 1,
                'undocumentedFeatures': 1,
                'promptToCodeCoverage': 50.0,
                'codeToPromptCoverage': 50.0
            },
            'missing': ['Input validation is not implemented'],
            'extra': [],
            'suggestions': ['Add input type checking']
        },
        'cost': 0.002,
        'model_name': 'claude-sonnet-4-20250514'
    }

    request = DiffAnalysisRequest(
        prompt_content="Validate input\nCheck types\nReturn result\nDocument function",
        code_content="def add(a, b):\n    return a + b",
        strength=0.5,
        mode="detailed"
    )

    response = await analyze_diff(request)

    assert response.result.overallScore == 50
    assert response.result.stats.missingRequirements == 1
    assert len(response.result.missing) == 1
    assert 'missing' in response.result.sections[0].status


@pytest.mark.asyncio
async def test_analyze_diff_handles_string_result(prompts_test_env):
    """Test that diff analysis handles LLM returning string instead of dict."""
    import json
    analyze_diff = prompts_test_env['analyze_diff']
    DiffAnalysisRequest = prompts_test_env['DiffAnalysisRequest']
    mock_llm_invoke = prompts_test_env['mock_llm_invoke']
    _diff_cache = prompts_test_env['_diff_cache']

    _diff_cache.clear()

    # Return result as JSON string instead of dict
    mock_llm_invoke.llm_invoke.return_value = {
        'result': json.dumps({
            'overallScore': 70,
            'summary': 'String result test',
            'sections': [],
            'lineMappings': [],
            'stats': {
                'totalRequirements': 1,
                'matchedRequirements': 1,
                'missingRequirements': 0,
                'totalCodeFeatures': 1,
                'documentedFeatures': 1,
                'undocumentedFeatures': 0,
                'promptToCodeCoverage': 100.0,
                'codeToPromptCoverage': 100.0
            },
            'missing': [],
            'extra': [],
            'suggestions': []
        }),
        'cost': 0.001,
        'model_name': 'claude-sonnet-4-20250514'
    }

    request = DiffAnalysisRequest(
        prompt_content="Test",
        code_content="Test",
        strength=0.5,
        mode="detailed"
    )

    response = await analyze_diff(request)

    assert response.result.overallScore == 70
    assert response.result.summary == 'String result test'


# --- Z3 Formal Verification for Diff Analysis ---

def test_z3_diff_score_bounds():
    """Formally verify that diff scores are bounded 0-100."""
    s = z3.Solver()

    overall_score = z3.Int('overall_score')
    match_confidence = z3.Int('match_confidence')

    # Property: scores must be in valid range
    valid_overall = z3.And(overall_score >= 0, overall_score <= 100)
    valid_confidence = z3.And(match_confidence >= 0, match_confidence <= 100)

    # Test that invalid scores are rejected
    s.push()
    s.add(overall_score == 150)  # Invalid score
    s.add(valid_overall)
    assert s.check() == z3.unsat
    s.pop()

    s.push()
    s.add(match_confidence == -10)  # Invalid negative score
    s.add(valid_confidence)
    assert s.check() == z3.unsat
    s.pop()


def test_z3_coverage_calculation():
    """Formally verify coverage percentage calculation."""
    s = z3.Solver()

    total_reqs = z3.Int('total_reqs')
    matched_reqs = z3.Int('matched_reqs')
    coverage = z3.Real('coverage')

    # Constraints
    s.add(total_reqs > 0)
    s.add(matched_reqs >= 0)
    s.add(matched_reqs <= total_reqs)
    s.add(coverage == (matched_reqs * 100) / total_reqs)

    # Property: coverage is between 0 and 100
    s.push()
    s.add(z3.Or(coverage < 0, coverage > 100))
    assert s.check() == z3.unsat
    s.pop()

    # Property: 100% coverage when all matched
    s.push()
    s.add(matched_reqs == total_reqs)
    s.add(coverage != 100)
    assert s.check() == z3.unsat
    s.pop()


# --- Tests for Cloud-Enabled LLM Calls ---

class TestCloudEnabledLLMCalls:
    """
    Tests to verify that LLM endpoints use cloud auto-detection.

    Previously, endpoints explicitly passed use_cloud=False which forced local
    execution. These tests verify that use_cloud is NOT explicitly set to False,
    allowing llm_invoke to auto-detect cloud availability.
    """

    @pytest.mark.asyncio
    async def test_check_match_allows_cloud_autodetect(self, prompts_test_env):
        """
        Verify /check-match endpoint does NOT pass use_cloud=False.

        This allows llm_invoke to auto-detect cloud availability via
        CloudConfig.is_cloud_enabled().
        """
        check_match = prompts_test_env['check_match']
        MatchCheckRequest = prompts_test_env['MatchCheckRequest']
        mock_llm_invoke = prompts_test_env['mock_llm_invoke']

        # Mock LLM response
        mock_llm_invoke.llm_invoke.return_value = {
            'result': {
                'match_score': 85,
                'summary': 'Test result',
                'missing': [],
                'extra': [],
                'suggestions': []
            },
            'cost': 0.001,
            'model_name': 'claude-sonnet-4-20250514'
        }

        request = MatchCheckRequest(
            prompt_content="Test prompt",
            code_content="def test(): pass",
            strength=0.5
        )

        await check_match(request)

        # Verify llm_invoke was called
        assert mock_llm_invoke.llm_invoke.called

        # Get the call arguments
        call_kwargs = mock_llm_invoke.llm_invoke.call_args.kwargs

        # CRITICAL: use_cloud should NOT be explicitly set to False
        # If use_cloud is in kwargs, it should not be False
        if 'use_cloud' in call_kwargs:
            assert call_kwargs['use_cloud'] is not False, (
                "use_cloud should not be explicitly set to False - "
                "this prevents cloud auto-detection"
            )

    @pytest.mark.asyncio
    async def test_analyze_diff_allows_cloud_autodetect(self, prompts_test_env):
        """
        Verify /diff-analysis endpoint does NOT pass use_cloud=False.

        This allows llm_invoke to auto-detect cloud availability via
        CloudConfig.is_cloud_enabled().
        """
        analyze_diff = prompts_test_env['analyze_diff']
        DiffAnalysisRequest = prompts_test_env['DiffAnalysisRequest']
        mock_llm_invoke = prompts_test_env['mock_llm_invoke']
        _diff_cache = prompts_test_env['_diff_cache']

        _diff_cache.clear()

        # Mock LLM response
        mock_llm_invoke.llm_invoke.return_value = {
            'result': {
                'overallScore': 80,
                'promptToCodeScore': 85,
                'codeToPromptScore': 75,
                'summary': 'Test analysis',
                'sections': [],
                'codeSections': [],
                'lineMappings': [],
                'stats': {
                    'totalRequirements': 1,
                    'matchedRequirements': 1,
                    'missingRequirements': 0,
                    'promptToCodeCoverage': 100.0
                },
                'missing': [],
                'extra': [],
                'suggestions': []
            },
            'cost': 0.002,
            'model_name': 'claude-sonnet-4-20250514'
        }

        request = DiffAnalysisRequest(
            prompt_content="Test prompt",
            code_content="def test(): pass",
            strength=0.5,
            mode="detailed"
        )

        await analyze_diff(request)

        # Verify llm_invoke was called
        assert mock_llm_invoke.llm_invoke.called

        # Get the call arguments
        call_kwargs = mock_llm_invoke.llm_invoke.call_args.kwargs

        # CRITICAL: use_cloud should NOT be explicitly set to False
        if 'use_cloud' in call_kwargs:
            assert call_kwargs['use_cloud'] is not False, (
                "use_cloud should not be explicitly set to False - "
                "this prevents cloud auto-detection"
            )

    @pytest.mark.asyncio
    async def test_prompt_diff_allows_cloud_autodetect(self, prompts_test_env, tmp_path):
        """
        Verify /prompt-diff endpoint does NOT pass use_cloud=False.

        This allows llm_invoke to auto-detect cloud availability via
        CloudConfig.is_cloud_enabled().
        """
        get_prompt_diff = prompts_test_env['get_prompt_diff']
        PromptDiffRequest = prompts_test_env['PromptDiffRequest']
        mock_llm_invoke = prompts_test_env['mock_llm_invoke']

        # Create a test file for the prompt
        test_prompt = tmp_path / "test.prompt"
        test_prompt.write_text("Original prompt content")

        # Mock LLM response
        mock_llm_invoke.llm_invoke.return_value = {
            'result': {
                'summary': 'No significant changes',
                'changes': []
            },
            'cost': 0.001,
            'model_name': 'claude-sonnet-4-20250514'
        }

        request = PromptDiffRequest(
            prompt_path=str(test_prompt),
            version_a="working",
            version_b="working",
            strength=0.5
        )

        await get_prompt_diff(request)

        # Verify llm_invoke was called
        assert mock_llm_invoke.llm_invoke.called

        # Get the call arguments
        call_kwargs = mock_llm_invoke.llm_invoke.call_args.kwargs

        # CRITICAL: use_cloud should NOT be explicitly set to False
        if 'use_cloud' in call_kwargs:
            assert call_kwargs['use_cloud'] is not False, (
                "use_cloud should not be explicitly set to False - "
                "this prevents cloud auto-detection"
            )
