"""Tests for model_tester.py — CSV loading, key resolution, cost calculation, error classification."""

import os
import pytest
from unittest.mock import MagicMock, patch

from pdd import model_tester


# ---------------------------------------------------------------------------
# Tests for _resolve_api_key
# ---------------------------------------------------------------------------

def test_resolve_api_key_empty_key_name():
    """No api_key configured returns None with status message."""
    row = {"api_key": ""}
    key, status = model_tester._resolve_api_key(row)
    assert key is None
    assert "no key configured" in status


def test_resolve_api_key_found_in_env(monkeypatch):
    """Key found in os.environ returns the value."""
    monkeypatch.setenv("TEST_API_KEY", "sk-abc123")
    row = {"api_key": "TEST_API_KEY"}
    key, status = model_tester._resolve_api_key(row)
    assert key == "sk-abc123"
    assert "Found" in status
    assert "TEST_API_KEY" in status


def test_resolve_api_key_not_found(monkeypatch):
    """Key not in any source returns None with 'Not found'."""
    monkeypatch.delenv("MISSING_KEY", raising=False)
    row = {"api_key": "MISSING_KEY"}
    with patch.dict("sys.modules", {"dotenv": None}):
        key, status = model_tester._resolve_api_key(row)
    assert key is None
    assert "Not found" in status


def test_resolve_api_key_strips_whitespace(monkeypatch):
    """Key value is stripped of leading/trailing whitespace."""
    monkeypatch.setenv("PADDED_KEY", "  sk-test  ")
    row = {"api_key": "PADDED_KEY"}
    key, _ = model_tester._resolve_api_key(row)
    assert key == "sk-test"


# ---------------------------------------------------------------------------
# Tests for _resolve_base_url
# ---------------------------------------------------------------------------

def test_resolve_base_url_explicit():
    """Explicit base_url in row is returned directly."""
    row = {"base_url": "https://custom.api.com/v1"}
    assert model_tester._resolve_base_url(row) == "https://custom.api.com/v1"


def test_resolve_base_url_empty():
    """Empty base_url for non-local model returns None."""
    row = {"base_url": "", "model": "anthropic/claude", "provider": "Anthropic"}
    assert model_tester._resolve_base_url(row) is None


def test_resolve_base_url_lm_studio_model(monkeypatch):
    """LM Studio model gets default localhost URL."""
    monkeypatch.delenv("LM_STUDIO_API_BASE", raising=False)
    row = {"base_url": "", "model": "lm_studio/my-model", "provider": "lm_studio"}
    result = model_tester._resolve_base_url(row)
    assert result == "http://localhost:1234/v1"


def test_resolve_base_url_lm_studio_custom_env(monkeypatch):
    """LM Studio respects LM_STUDIO_API_BASE env var."""
    monkeypatch.setenv("LM_STUDIO_API_BASE", "http://remote:5000/v1")
    row = {"base_url": "", "model": "lm_studio/model", "provider": "lm_studio"}
    assert model_tester._resolve_base_url(row) == "http://remote:5000/v1"


# ---------------------------------------------------------------------------
# Tests for _calculate_cost
# ---------------------------------------------------------------------------

def test_calculate_cost_basic():
    """Cost calculation with known token counts and prices."""
    # 100 prompt tokens at $3/M + 50 completion tokens at $15/M
    cost = model_tester._calculate_cost(100, 50, 3.0, 15.0)
    expected = (100 * 3.0 + 50 * 15.0) / 1_000_000.0
    assert abs(cost - expected) < 1e-10


def test_calculate_cost_zero():
    """Zero tokens or zero prices produce zero cost."""
    assert model_tester._calculate_cost(0, 0, 3.0, 15.0) == 0.0
    assert model_tester._calculate_cost(100, 100, 0.0, 0.0) == 0.0


# ---------------------------------------------------------------------------
# Tests for _classify_error
# ---------------------------------------------------------------------------

def test_classify_error_auth():
    """Authentication-related errors are classified correctly."""
    exc = Exception("401 Unauthorized - invalid api key")
    result = model_tester._classify_error(exc)
    assert "Authentication error" in result


def test_classify_error_connection_refused():
    """Connection refused errors suggest local server issue."""
    exc = ConnectionError("Connection refused")
    result = model_tester._classify_error(exc)
    assert "Connection refused" in result


def test_classify_error_not_found():
    """404 / model not found errors classified correctly."""
    exc = Exception("404 Model does not exist")
    result = model_tester._classify_error(exc)
    assert "Model not found" in result


def test_classify_error_timeout():
    """Timeout errors classified correctly."""
    exc = TimeoutError("Request timed out after 30s")
    result = model_tester._classify_error(exc)
    assert "timed out" in result


def test_classify_error_rate_limit():
    """Rate limit errors classified correctly."""
    exc = Exception("429 Rate limit exceeded")
    result = model_tester._classify_error(exc)
    assert "Rate limited" in result


def test_classify_error_generic():
    """Unknown errors fall through to generic classification."""
    exc = ValueError("Something unexpected")
    result = model_tester._classify_error(exc)
    assert "ValueError" in result
    assert "Something unexpected" in result


# ---------------------------------------------------------------------------
# Tests for _run_test
# ---------------------------------------------------------------------------

@patch("litellm.completion")
def test_run_test_success(mock_completion, monkeypatch):
    """Successful litellm call returns success dict with tokens and cost."""
    monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-test")

    usage = MagicMock()
    usage.prompt_tokens = 10
    usage.completion_tokens = 5
    response = MagicMock()
    response.usage = usage
    mock_completion.return_value = response

    row = {"model": "anthropic/claude", "api_key": "ANTHROPIC_API_KEY",
           "input": 3.0, "output": 15.0}
    result = model_tester._run_test(row)

    assert result["success"] is True
    assert result["error"] is None
    assert result["tokens"]["prompt"] == 10
    assert result["tokens"]["completion"] == 5
    assert result["cost"] > 0
    assert result["duration_s"] >= 0


@patch("litellm.completion")
def test_run_test_failure(mock_completion, monkeypatch):
    """Failed litellm call returns failure dict with classified error."""
    monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-test")
    mock_completion.side_effect = Exception("401 Unauthorized")

    row = {"model": "anthropic/claude", "api_key": "ANTHROPIC_API_KEY",
           "input": 3.0, "output": 15.0}
    result = model_tester._run_test(row)

    assert result["success"] is False
    assert result["cost"] == 0.0
    assert result["tokens"] is None
    assert "Authentication error" in result["error"]


# ---------------------------------------------------------------------------
# Tests for _load_user_csv
# ---------------------------------------------------------------------------

@patch("pdd.model_tester.Path")
def test_load_user_csv_missing_file(mock_path):
    """Returns None when CSV file doesn't exist."""
    mock_home = MagicMock()
    mock_csv = MagicMock()
    mock_csv.is_file.return_value = False
    mock_home.__truediv__ = MagicMock(return_value=MagicMock(__truediv__=MagicMock(return_value=mock_csv)))
    mock_path.home.return_value = mock_home

    result = model_tester._load_user_csv()
    assert result is None


def test_load_user_csv_valid(tmp_path):
    """Returns DataFrame for a valid CSV with required columns."""
    csv_content = "provider,model,api_key,input,output\nAnthropic,claude,ANTHROPIC_API_KEY,3.0,15.0\n"
    csv_file = tmp_path / ".pdd" / "llm_model.csv"
    csv_file.parent.mkdir(parents=True)
    csv_file.write_text(csv_content)

    with patch.object(model_tester.Path, "home", return_value=tmp_path):
        df = model_tester._load_user_csv()

    assert df is not None
    assert len(df) == 1
    assert df.iloc[0]["provider"] == "Anthropic"


def test_load_user_csv_missing_columns(tmp_path):
    """Returns None when required columns are missing."""
    csv_content = "name,value\nfoo,bar\n"
    csv_file = tmp_path / ".pdd" / "llm_model.csv"
    csv_file.parent.mkdir(parents=True)
    csv_file.write_text(csv_content)

    with patch.object(model_tester.Path, "home", return_value=tmp_path):
        df = model_tester._load_user_csv()

    assert df is None
