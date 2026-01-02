import pytest
import json
import os
from unittest.mock import patch, MagicMock
import streamlit as st

# Fix import path
from ui.streamlit_app import get_severity_color, call_lint_api, render_finding, main

# --- Unit Tests ---

def test_get_severity_color():
    """Tests the color mapping helper function."""
    assert get_severity_color("error") == "red"
    assert get_severity_color("ERROR") == "red"
    assert get_severity_color("warning") == "orange"
    assert get_severity_color("info") == "blue"
    assert get_severity_color("critical") == "grey"  # Default case

@patch("requests.post")
def test_call_lint_api_success(mock_post):
    """Tests successful API communication."""
    mock_response = MagicMock()
    mock_response.status_code = 200
    # Correct structure matching LintReport
    expected_response = {
        "filename": "test.txt",
        "summary": {
            "score": 85,
            "issue_counts": {"error": 0, "warn": 0, "info": 0},
            "token_count_estimate": 100
        },
        "findings": []
    }
    mock_response.json.return_value = expected_response
    mock_post.return_value = mock_response

    result = call_lint_api("test content", False)
    
    assert result == expected_response
    mock_post.assert_called_once()
    # Verify payload matching api_main schema
    args, kwargs = mock_post.call_args
    assert kwargs['json']['prompt_text'] == "test content"
    assert kwargs['json']['options']['resolve_includes'] is False

@patch("requests.post")
@patch("streamlit.error")
def test_call_lint_api_connection_error(mock_st_error, mock_post):
    """Tests API behavior when the backend is down."""
    import requests
    mock_post.side_effect = requests.exceptions.ConnectionError()

    result = call_lint_api("test content", True)
    
    assert result is None
    mock_st_error.assert_called_once()
    assert "Could not connect" in mock_st_error.call_args[0][0]

@patch("streamlit.error")
@patch("streamlit.warning")
@patch("streamlit.info")
@patch("streamlit.markdown")
@patch("streamlit.code")
def test_render_finding_error(mock_code, mock_markdown, mock_info, mock_warning, mock_error):
    """Tests rendering of an error-level finding."""
    # We need to mock the context manager behavior of st.error/warning/info
    mock_error.return_value.__enter__.return_value = MagicMock()
    
    finding = {
        "rule_id": "P001",
        "title": "Too Long",
        "severity": "error",
        "message": "Prompt exceeds limit",
        "evidence": {"line_start": 1, "line_end": 2},
        "suggested_edits": [{"kind": "replace", "snippet": "Shorten it"}]
    }
    
    render_finding(finding)
    
    mock_error.assert_called_once()
    assert "[P001] Too Long" in mock_error.call_args[0][0]
    # Check if markdown was called for message and lines
    assert mock_markdown.called
    
    # Check for Line(s) rendering
    markdown_calls = [args[0] for args, _ in mock_markdown.call_args_list]
    assert any("Line(s):" in call for call in markdown_calls), "Line numbers not rendered"
    
    # Check for Suggested Edit rendering
    # It might use st.markdown or st.code
    assert any("Suggested Edit:" in call for call in markdown_calls), "Suggested Edit header not rendered"
    assert mock_code.called, "Suggested edit code block not rendered"

@patch("streamlit.info")
@patch("streamlit.markdown")
def test_render_finding_missing_fields(mock_markdown, mock_info):
    """Tests rendering when some finding fields are missing (robustness)."""
    mock_info.return_value.__enter__.return_value = MagicMock()
    
    finding = {
        "severity": "info"
        # rule_id, title, message, etc. are missing
    }
    
    render_finding(finding)
    
    mock_info.assert_called_once()
    assert "[N/A] Untitled Issue" in mock_info.call_args[0][0]

def test_api_url_config():
    """Verifies that the API_URL can be influenced by environment variables."""
    with patch.dict(os.environ, {"PDD_API_URL": "http://test-api:9000/lint"}):
        import importlib
        import ui.streamlit_app
        importlib.reload(ui.streamlit_app)
        assert ui.streamlit_app.API_URL == "http://test-api:9000/lint"

@patch("ui.streamlit_app.call_lint_api")
@patch("streamlit.metric")
@patch("streamlit.button")
@patch("streamlit.text_area")
@patch("streamlit.title")
@patch("streamlit.markdown")
@patch("streamlit.header")
@patch("streamlit.subheader")
@patch("streamlit.columns")
@patch("streamlit.divider")
@patch("streamlit.sidebar")
@patch("streamlit.file_uploader")
@patch("streamlit.spinner")
@patch("streamlit.download_button")
def test_main_flow(mock_download, mock_spinner, mock_uploader, mock_sidebar, mock_divider, mock_columns, mock_subheader, mock_header, mock_markdown, mock_title, mock_text_area, mock_button, mock_metric, mock_call_api):
    """
    Tests the main application flow, ensuring that the score is correctly parsed
    from the nested 'summary' object in the API response.
    """
    # Setup mocks
    mock_button.return_value = True # Simulate "Lint Prompt" button click
    mock_text_area.return_value = "Test prompt content"
    
    # Mock columns to return 4 separate mocks
    col1, col2, col3, col4 = MagicMock(), MagicMock(), MagicMock(), MagicMock()
    mock_columns.return_value = (col1, col2, col3, col4)
    
    # Mock API response with nested summary structure
    api_response = {
        "filename": "test.txt",
        "summary": {
            "score": 92,
            "issue_counts": {"error": 1, "warn": 2, "info": 0},
            "token_count_estimate": 150
        },
        "findings": [
            {"severity": "error", "message": "err"},
            {"severity": "warning", "message": "warn1"},
            {"severity": "warning", "message": "warn2"}
        ]
    }
    mock_call_api.return_value = api_response
    
    # Run main
    main()
    
    # Verify API was called
    mock_call_api.assert_called_with("Test prompt content", False)
    
    calls = mock_metric.call_args_list
    score_call = next((c for c in calls if c[0][0] == "Overall Score"), None)
    
    assert score_call is not None, "Overall Score metric was not displayed"
    assert score_call[0][1] == "92/100", f"Expected score '92/100' but got '{score_call[0][1]}'. This confirms the bug."

    # Also check token count logic
    token_call = next((c for c in calls if c[0][0] == "Est. Tokens"), None)
    if token_call:
        assert str(token_call[0][1]) == "150", f"Expected tokens '150' but got '{token_call[0][1]}'"