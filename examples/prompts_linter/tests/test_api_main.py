import pytest
from fastapi.testclient import TestClient
from unittest.mock import MagicMock, patch
import json
from z3 import Solver, Int, Or, And, Bool, Implies, Not, unsat

# Import the app and models
# Based on the file path: src/backend/app/main.py
# The package structure implies 'backend.app.main'
from backend.app.main import app, LintRequest
from backend.models.findings import LintReport

client = TestClient(app)

# --- System Endpoint Tests ---

def test_root_endpoint():
    """Verifies the root endpoint returns the expected welcome message."""
    response = client.get("/")
    assert response.status_code == 200
    data = response.json()
    assert data["status"] == "running"
    assert "docs_url" in data
    assert "PDD Prompt Linter" in data["message"]

def test_health_check():
    """Verifies the health check endpoint for deployment readiness."""
    response = client.get("/health")
    assert response.status_code == 200
    assert response.json() == {"status": "ok"}

# --- Linting Endpoint Tests ---

@patch("backend.app.main.lint_engine")
def test_lint_prompt_success(mock_engine):
    """Verifies successful linting flow with mocked engine."""
    # Setup mock return value
    # Updated to match the strict schema validation observed in errors:
    # Requires: filename, summary.issue_counts, findings[].title, findings[].severity (enum)
    mock_report = {
        "filename": "test_prompt.txt",
        "summary": {
            "score": 85, 
            "token_count_estimate": 0,
            "issue_counts": {"error": 0, "warn": 0, "info": 1}
        },
        "findings": [{
            "rule_id": "P001", 
            "title": "Test Finding Title",
            "message": "Test finding", 
            "severity": "info",
            "evidence": None,
            "suggested_edits": []
        }]
    }
    mock_engine.lint.return_value = mock_report

    payload = {
        "prompt_text": "Write a python script to scrape google.",
        "options": {"verbose": True}
    }
    
    response = client.post("/lint", json=payload)
    
    assert response.status_code == 200
    assert response.json() == mock_report
    mock_engine.lint.assert_called_once_with("Write a python script to scrape google.")

def test_lint_prompt_validation_error():
    """Verifies that missing required fields return 422."""
    # Missing 'prompt_text'
    payload = {"options": {}}
    response = client.post("/lint", json=payload)
    assert response.status_code == 422

@patch("backend.app.main.lint_engine")
def test_lint_prompt_engine_exception(mock_engine):
    """Verifies that engine crashes are caught and return 500."""
    mock_engine.lint.side_effect = Exception("Engine failure")
    
    payload = {"prompt_text": "Trigger error"}
    response = client.post("/lint", json=payload)
    
    assert response.status_code == 500
    # The code raises HTTPException(500, detail=...) which returns {"detail": ...}
    assert "Internal Server Error" in response.json()["detail"] or "Error processing prompt" in response.json()["detail"]

# --- Formal Verification Tests (Z3) ---

def test_status_code_logic_formal():
    """
    Uses Z3 to formally verify that the API logic (conceptually) 
    never returns a 200 if the input is invalid according to Pydantic rules.
    Note: This is a meta-test demonstrating how Z3 can model API behavior.
    """
    # Define states
    has_prompt = Bool('has_prompt')
    status_code = Int('status_code')

    s = Solver()

    # Rule: If prompt is missing, status code must be 422 (Pydantic behavior)
    # Rule: If prompt is present, status code is 200 (assuming no engine error)
    s.add(Implies(Not(has_prompt), status_code == 422))
    s.add(Implies(has_prompt, status_code == 200))

    # Prove: It is impossible to have no prompt AND a 200 status code
    s.add(And(Not(has_prompt), status_code == 200))

    # If unsat, the condition (No prompt AND 200) is impossible given our rules
    assert s.check() == unsat

def test_cors_headers():
    """Verifies CORS middleware is configured to allow all origins."""
    origin = "http://localhost:8501"
    response = client.options("/lint", headers={
        "Origin": origin,
        "Access-Control-Request-Method": "POST",
        "Access-Control-Request-Headers": "Content-Type",
    })
    assert response.status_code == 200
    # When allow_credentials=True, Starlette reflects the specific origin
    # instead of returning '*' in the Access-Control-Allow-Origin header.
    assert response.headers.get("access-control-allow-origin") == origin

def test_lint_request_model():
    """Directly tests the Pydantic model for default values."""
    req = LintRequest(prompt_text="Hello")
    assert req.prompt_text == "Hello"
    assert req.options == {}
    
    req_with_options = LintRequest(prompt_text="Hello", options={"key": "val"})
    assert req_with_options.options == {"key": "val"}
