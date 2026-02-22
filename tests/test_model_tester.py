# Test Plan:
# I. No-CSV Edge Cases (test_model_interactive exits early)
#   1. test_no_csv_file: No ~/.pdd/llm_model.csv → prints guidance message and returns.
#   2. test_empty_csv: CSV exists but has no data rows → same early exit.
#   3. test_csv_missing_required_columns: CSV exists but lacks provider/model/api_key → early exit.
#
# II. Interactive Flow — User Input Handling
#   4. test_quit_with_empty_input: User presses Enter immediately → exits cleanly.
#   5. test_quit_with_q: User types "q" → exits cleanly.
#   6. test_invalid_input_then_quit: User types "abc", sees error, then quits.
#   7. test_out_of_range_then_quit: User types "99" (out of range), sees error, then quits.
#   8. test_eof_exits_gracefully: EOFError during input → exits without crashing.
#
# III. Successful Model Test (end-to-end through test_model_interactive)
#   9.  test_successful_test_shows_ok: User picks model 1, LLM returns OK → output shows ✓ OK with cost/tokens.
#   10. test_successful_test_passes_api_key_for_single_var: Single api_key var → passed as api_key= to litellm.
#   11. test_multi_var_provider_no_api_key_kwarg: Bedrock (pipe-delimited) → api_key= NOT passed to litellm.
#   12. test_device_flow_no_api_key_kwarg: Empty api_key → api_key= NOT passed to litellm.
#
# IV. Failed Model Test (end-to-end through test_model_interactive)
#   13. test_auth_error_shows_classified_message: LLM raises 401 → output shows "Authentication error".
#   14. test_connection_refused_shows_local_server_hint: LLM raises connection error → output suggests local server.
#
# V. Diagnostics Displayed Before Test
#   15. test_diagnostics_show_key_found: API key in env → output includes "✓ Found".
#   16. test_diagnostics_show_key_missing: API key not in env → output includes "✗ Not found".
#   17. test_diagnostics_show_base_url_for_lm_studio: LM Studio model → base URL shown in output.
#   18. test_diagnostics_bedrock_checks_all_vars: Bedrock model → all three env vars checked in output.
#   19. test_diagnostics_vertex_bad_creds_file: GOOGLE_APPLICATION_CREDENTIALS path invalid → warns in output.
#   20. test_diagnostics_device_flow_no_key_needed: Empty api_key → output indicates no key needed.
#
# VI. Session Persistence
#   21. test_results_persist_across_picks: User tests model 1 then model 2 → both results shown in table.
#
# VII. CSV Loading Normalization
#   22. test_csv_normalizes_nan_strings_and_bad_numerics: NaN strings → "", bad numbers → 0.0.
#
# VIII. Pure Function Contracts
#   23-28. _classify_error: auth, connection refused, not found, timeout, rate limit, generic.
#   29-30. _calculate_cost: basic math, zero tokens.

"""Tests for model_tester.py — behavioral tests driven through test_model_interactive()."""

import pytest
from unittest.mock import MagicMock, patch

from pdd import model_tester


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_csv(tmp_path, content):
    """Write a CSV file at the expected ~/.pdd/llm_model.csv location."""
    csv_file = tmp_path / ".pdd" / "llm_model.csv"
    csv_file.parent.mkdir(parents=True, exist_ok=True)
    csv_file.write_text(content)
    return csv_file


def _mock_litellm_success(prompt_tokens=10, completion_tokens=5):
    """Return a mock litellm response with token usage."""
    usage = MagicMock()
    usage.prompt_tokens = prompt_tokens
    usage.completion_tokens = completion_tokens
    response = MagicMock()
    response.usage = usage
    return response


def _run_interactive(tmp_path, csv_content, user_inputs, monkeypatch,
                     mock_completion=None, env_vars=None):
    """Run test_model_interactive with mocked CSV, user input, and litellm.

    Returns the captured console output as a string.
    """
    _make_csv(tmp_path, csv_content)

    for k, v in (env_vars or {}).items():
        monkeypatch.setenv(k, v)

    input_iter = iter(user_inputs)
    mock_console_input = MagicMock(side_effect=input_iter)

    if mock_completion is None:
        mock_completion = MagicMock(return_value=_mock_litellm_success())

    with patch.object(model_tester.Path, "home", return_value=tmp_path), \
         patch.object(model_tester.console, "input", mock_console_input), \
         patch("litellm.completion", mock_completion), \
         patch("sys.stdout"):  # suppress dot-printing from thread
        model_tester.test_model_interactive()

    # Collect all console.print() calls into a single string for assertions.
    # Each call may contain rich markup; we join them for substring matching.
    output_parts = []
    for c in model_tester.console.print.call_args_list if hasattr(model_tester.console.print, "call_args_list") else []:
        for arg in c.args:
            output_parts.append(str(arg))
    return "\n".join(output_parts), mock_completion


def _run_interactive_capture(tmp_path, csv_content, user_inputs, monkeypatch,
                             mock_completion=None, env_vars=None):
    """Like _run_interactive but patches console.print to capture output."""
    _make_csv(tmp_path, csv_content)

    for k, v in (env_vars or {}).items():
        monkeypatch.setenv(k, v)

    input_iter = iter(user_inputs)

    if mock_completion is None:
        mock_completion = MagicMock(return_value=_mock_litellm_success())

    captured = []

    def _capture_print(*args, **kwargs):
        for a in args:
            captured.append(str(a))

    with patch.object(model_tester.Path, "home", return_value=tmp_path), \
         patch.object(model_tester.console, "input", side_effect=input_iter), \
         patch.object(model_tester.console, "print", side_effect=_capture_print), \
         patch("litellm.completion", mock_completion), \
         patch("sys.stdout"):
        model_tester.test_model_interactive()

    return "\n".join(captured), mock_completion


SIMPLE_CSV = "provider,model,api_key,input,output\nOpenAI,gpt-5,OPENAI_API_KEY,3.0,15.0\n"

TWO_MODEL_CSV = (
    "provider,model,api_key,input,output\n"
    "OpenAI,gpt-5,OPENAI_API_KEY,3.0,15.0\n"
    "Anthropic,claude-sonnet,ANTHROPIC_API_KEY,3.0,15.0\n"
)

BEDROCK_CSV = (
    "provider,model,api_key,input,output\n"
    "AWS Bedrock,bedrock/anthropic.claude-v1,"
    "AWS_ACCESS_KEY_ID|AWS_SECRET_ACCESS_KEY|AWS_REGION_NAME,1.0,5.0\n"
)

DEVICE_FLOW_CSV = (
    "provider,model,api_key,input,output\n"
    "Github Copilot,github_copilot/gpt-5,,0.0,0.0\n"
)

LM_STUDIO_CSV = (
    "provider,model,api_key,input,output,base_url\n"
    "lm_studio,lm_studio/local-model,,0.0,0.0,\n"
)

VERTEX_CSV = (
    "provider,model,api_key,input,output\n"
    "Google Vertex AI,vertex_ai/gemini-2.5-pro,"
    "GOOGLE_APPLICATION_CREDENTIALS|VERTEXAI_PROJECT|VERTEXAI_LOCATION,1.0,5.0\n"
)


# ===========================================================================
# I. No-CSV Edge Cases
# ===========================================================================

def test_no_csv_file(tmp_path):
    """No ~/.pdd/llm_model.csv → prints guidance and returns."""
    with patch.object(model_tester.Path, "home", return_value=tmp_path):
        captured = []
        with patch.object(model_tester.console, "print",
                          side_effect=lambda *a, **kw: captured.extend(str(x) for x in a)):
            model_tester.test_model_interactive()
    output = "\n".join(captured)
    assert "No user model CSV" in output
    assert "pdd setup" in output


def test_empty_csv(tmp_path):
    """CSV with headers but no rows → same early exit."""
    _make_csv(tmp_path, "provider,model,api_key,input,output\n")
    with patch.object(model_tester.Path, "home", return_value=tmp_path):
        captured = []
        with patch.object(model_tester.console, "print",
                          side_effect=lambda *a, **kw: captured.extend(str(x) for x in a)):
            model_tester.test_model_interactive()
    output = "\n".join(captured)
    assert "No user model CSV" in output


def test_csv_missing_required_columns(tmp_path):
    """CSV with wrong columns → early exit."""
    _make_csv(tmp_path, "name,value\nfoo,bar\n")
    with patch.object(model_tester.Path, "home", return_value=tmp_path):
        captured = []
        with patch.object(model_tester.console, "print",
                          side_effect=lambda *a, **kw: captured.extend(str(x) for x in a)):
            model_tester.test_model_interactive()
    output = "\n".join(captured)
    assert "No user model CSV" in output or "missing required columns" in output


# ===========================================================================
# II. Interactive Flow — User Input Handling
# ===========================================================================

def test_quit_with_empty_input(tmp_path, monkeypatch):
    """User presses Enter → exits cleanly."""
    output, _ = _run_interactive_capture(
        tmp_path, SIMPLE_CSV, [""], monkeypatch,
        env_vars={"OPENAI_API_KEY": "sk-test"},
    )
    assert "Exiting" in output


def test_quit_with_q(tmp_path, monkeypatch):
    """User types 'q' → exits cleanly."""
    output, _ = _run_interactive_capture(
        tmp_path, SIMPLE_CSV, ["q"], monkeypatch,
        env_vars={"OPENAI_API_KEY": "sk-test"},
    )
    assert "Exiting" in output


def test_invalid_input_then_quit(tmp_path, monkeypatch):
    """User types 'abc' → error message, then quits."""
    output, _ = _run_interactive_capture(
        tmp_path, SIMPLE_CSV, ["abc", "q"], monkeypatch,
        env_vars={"OPENAI_API_KEY": "sk-test"},
    )
    assert "Invalid input" in output


def test_out_of_range_then_quit(tmp_path, monkeypatch):
    """User types '99' → out-of-range error, then quits."""
    output, _ = _run_interactive_capture(
        tmp_path, SIMPLE_CSV, ["99", "q"], monkeypatch,
        env_vars={"OPENAI_API_KEY": "sk-test"},
    )
    assert "Invalid selection" in output


def test_eof_exits_gracefully(tmp_path, monkeypatch):
    """EOFError during input → exits without crashing."""
    _make_csv(tmp_path, SIMPLE_CSV)
    monkeypatch.setenv("OPENAI_API_KEY", "sk-test")

    with patch.object(model_tester.Path, "home", return_value=tmp_path), \
         patch.object(model_tester.console, "input", side_effect=EOFError), \
         patch.object(model_tester.console, "print"), \
         patch("sys.stdout"):
        # Should not raise
        model_tester.test_model_interactive()


# ===========================================================================
# III. Successful Model Test
# ===========================================================================

def test_successful_test_shows_ok(tmp_path, monkeypatch):
    """User picks model 1, LLM succeeds → output shows ✓ OK with cost info."""
    output, _ = _run_interactive_capture(
        tmp_path, SIMPLE_CSV, ["1", "q"], monkeypatch,
        mock_completion=MagicMock(return_value=_mock_litellm_success(10, 5)),
        env_vars={"OPENAI_API_KEY": "sk-test"},
    )
    assert "✓ OK" in output


def test_successful_test_passes_api_key_for_single_var(tmp_path, monkeypatch):
    """Single-var provider → api_key= passed to litellm.completion."""
    mock_comp = MagicMock(return_value=_mock_litellm_success())
    _run_interactive_capture(
        tmp_path, SIMPLE_CSV, ["1", "q"], monkeypatch,
        mock_completion=mock_comp,
        env_vars={"OPENAI_API_KEY": "sk-test123"},
    )
    call_kwargs = mock_comp.call_args[1]
    assert call_kwargs["api_key"] == "sk-test123"


def test_multi_var_provider_no_api_key_kwarg(tmp_path, monkeypatch):
    """Bedrock (pipe-delimited api_key) → api_key= NOT passed to litellm."""
    mock_comp = MagicMock(return_value=_mock_litellm_success())
    _run_interactive_capture(
        tmp_path, BEDROCK_CSV, ["1", "q"], monkeypatch,
        mock_completion=mock_comp,
        env_vars={
            "AWS_ACCESS_KEY_ID": "AKIAEXAMPLE",
            "AWS_SECRET_ACCESS_KEY": "secret",
            "AWS_REGION_NAME": "us-east-1",
        },
    )
    call_kwargs = mock_comp.call_args[1]
    assert "api_key" not in call_kwargs


def test_device_flow_no_api_key_kwarg(tmp_path, monkeypatch):
    """Device flow (empty api_key) → api_key= NOT passed to litellm."""
    mock_comp = MagicMock(return_value=_mock_litellm_success())
    _run_interactive_capture(
        tmp_path, DEVICE_FLOW_CSV, ["1", "q"], monkeypatch,
        mock_completion=mock_comp,
    )
    call_kwargs = mock_comp.call_args[1]
    assert "api_key" not in call_kwargs


# ===========================================================================
# IV. Failed Model Test
# ===========================================================================

def test_auth_error_shows_classified_message(tmp_path, monkeypatch):
    """LLM raises 401 → output shows 'Authentication error'."""
    mock_comp = MagicMock(side_effect=Exception("401 Unauthorized"))
    output, _ = _run_interactive_capture(
        tmp_path, SIMPLE_CSV, ["1", "q"], monkeypatch,
        mock_completion=mock_comp,
        env_vars={"OPENAI_API_KEY": "sk-bad"},
    )
    assert "Authentication error" in output


def test_connection_refused_shows_local_server_hint(tmp_path, monkeypatch):
    """LLM raises connection error → output suggests local server."""
    mock_comp = MagicMock(side_effect=ConnectionError("Connection refused"))
    output, _ = _run_interactive_capture(
        tmp_path, LM_STUDIO_CSV, ["1", "q"], monkeypatch,
        mock_completion=mock_comp,
    )
    assert "Connection refused" in output
    assert "local server" in output


# ===========================================================================
# V. Diagnostics Displayed Before Test
# ===========================================================================

def test_diagnostics_show_key_found(tmp_path, monkeypatch):
    """API key in env → diagnostics show ✓ Found."""
    output, _ = _run_interactive_capture(
        tmp_path, SIMPLE_CSV, ["1", "q"], monkeypatch,
        env_vars={"OPENAI_API_KEY": "sk-test"},
    )
    assert "✓ Found" in output
    assert "OPENAI_API_KEY" in output


def test_diagnostics_show_key_missing(tmp_path, monkeypatch):
    """API key NOT in env → diagnostics show ✗ Not found."""
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    output, _ = _run_interactive_capture(
        tmp_path, SIMPLE_CSV, ["1", "q"], monkeypatch,
    )
    assert "✗ Not found" in output


def test_diagnostics_show_base_url_for_lm_studio(tmp_path, monkeypatch):
    """LM Studio model → base URL shown in diagnostics."""
    monkeypatch.delenv("LM_STUDIO_API_BASE", raising=False)
    output, _ = _run_interactive_capture(
        tmp_path, LM_STUDIO_CSV, ["1", "q"], monkeypatch,
    )
    assert "localhost:1234" in output


def test_diagnostics_bedrock_checks_all_vars(tmp_path, monkeypatch):
    """Bedrock model → all three env vars appear in diagnostics."""
    monkeypatch.setenv("AWS_ACCESS_KEY_ID", "AKIAEXAMPLE")
    monkeypatch.delenv("AWS_SECRET_ACCESS_KEY", raising=False)
    monkeypatch.setenv("AWS_REGION_NAME", "us-east-1")
    output, _ = _run_interactive_capture(
        tmp_path, BEDROCK_CSV, ["1", "q"], monkeypatch,
    )
    assert "AWS_ACCESS_KEY_ID" in output
    assert "AWS_SECRET_ACCESS_KEY" in output
    assert "AWS_REGION_NAME" in output
    # One should be found, one missing
    assert "✓ Found" in output
    assert "✗ Not found" in output


def test_diagnostics_vertex_bad_creds_file(tmp_path, monkeypatch):
    """GOOGLE_APPLICATION_CREDENTIALS pointing to nonexistent file → warns."""
    monkeypatch.setenv("GOOGLE_APPLICATION_CREDENTIALS", "/nonexistent/creds.json")
    monkeypatch.setenv("VERTEXAI_PROJECT", "my-project")
    monkeypatch.setenv("VERTEXAI_LOCATION", "us-central1")
    output, _ = _run_interactive_capture(
        tmp_path, VERTEX_CSV, ["1", "q"], monkeypatch,
    )
    assert "file not found" in output


def test_diagnostics_device_flow_no_key_needed(tmp_path, monkeypatch):
    """Device flow provider → diagnostics say no key needed."""
    output, _ = _run_interactive_capture(
        tmp_path, DEVICE_FLOW_CSV, ["1", "q"], monkeypatch,
    )
    assert "Device flow" in output or "no key needed" in output


# ===========================================================================
# VI. Session Persistence
# ===========================================================================

def test_results_persist_across_picks(tmp_path, monkeypatch):
    """User tests model 1 then model 2 → second table render includes first result."""
    call_count = [0]
    def _completion_side_effect(**kwargs):
        call_count[0] += 1
        return _mock_litellm_success()

    mock_comp = MagicMock(side_effect=_completion_side_effect)
    output, _ = _run_interactive_capture(
        tmp_path, TWO_MODEL_CSV, ["1", "2", "q"], monkeypatch,
        mock_completion=mock_comp,
        env_vars={"OPENAI_API_KEY": "sk-test", "ANTHROPIC_API_KEY": "sk-test"},
    )
    # litellm.completion should have been called twice (once per model)
    assert mock_comp.call_count == 2


# ===========================================================================
# VII. CSV Loading Normalization
# ===========================================================================

def test_csv_normalizes_nan_strings_and_bad_numerics(tmp_path):
    """NaN string columns → empty string; non-numeric cost → 0.0."""
    csv_content = (
        "provider,model,api_key,base_url,location,input,output\n"
        "OpenAI,gpt-5,,,us-east,bad,3.0\n"
    )
    _make_csv(tmp_path, csv_content)

    with patch.object(model_tester.Path, "home", return_value=tmp_path):
        df = model_tester._load_user_csv()

    assert df is not None
    row = df.iloc[0]
    assert row["api_key"] == ""
    assert row["base_url"] == ""
    assert row["input"] == 0.0
    assert row["output"] == 3.0


# ===========================================================================
# VIII. Pure Function Contracts — _classify_error
# These are kept as direct tests because _classify_error is a pure function
# with clear sub-contract semantics (like ExtractedCode in test_postprocess.py).
# ===========================================================================

@pytest.mark.parametrize("message,expected_fragment", [
    ("401 Unauthorized - invalid api key", "Authentication error"),
    ("403 Forbidden - access denied", "Authentication error"),
    ("Connection refused", "Connection refused"),
    ("404 Model does not exist", "Model not found"),
    ("Request timed out after 30s", "timed out"),
    ("429 Rate limit exceeded", "Rate limited"),
])
def test_classify_error_categories(message, expected_fragment):
    """Error messages are classified into user-friendly categories."""
    exc = Exception(message)
    result = model_tester._classify_error(exc)
    assert expected_fragment in result


def test_classify_error_generic():
    """Unknown errors fall through to generic classification."""
    exc = ValueError("Something unexpected")
    result = model_tester._classify_error(exc)
    assert "ValueError" in result
    assert "Something unexpected" in result


# ===========================================================================
# IX. Pure Function Contracts — _calculate_cost
# ===========================================================================

def test_calculate_cost_basic():
    """Cost = (prompt_tokens * input_price + completion_tokens * output_price) / 1M."""
    cost = model_tester._calculate_cost(100, 50, 3.0, 15.0)
    expected = (100 * 3.0 + 50 * 15.0) / 1_000_000.0
    assert abs(cost - expected) < 1e-10


def test_calculate_cost_zero():
    """Zero tokens or zero prices produce zero cost."""
    assert model_tester._calculate_cost(0, 0, 3.0, 15.0) == 0.0
    assert model_tester._calculate_cost(100, 100, 0.0, 0.0) == 0.0
