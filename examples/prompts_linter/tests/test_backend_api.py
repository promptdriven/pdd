import sys
import os
import pytest
from unittest.mock import patch, MagicMock
from fastapi.testclient import TestClient
from pydantic import ValidationError, BaseModel

# --- Path Setup ---
# Adjust path to import the module under test
# The file path provided is .../src/backend/backend_api.py
# We need to add the directory containing 'src' to sys.path
current_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(current_dir, '..'))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

# Import the app from the module under test
# Note: The prompt indicates the module name is 'backend_api'
from src.backend.backend_api import app, LintRequest

# --- Fixtures ---

@pytest.fixture
def client():
    """
    Fixture to provide a TestClient for the FastAPI app.
    """
    return TestClient(app)

@pytest.fixture
def mock_report():
    """
    Fixture to provide a mock Report object structure.
    """
    mock_r = MagicMock()
    mock_r.score = 85
    mock_r.summary = "Test Summary"
    mock_r.issues = []
    mock_r.filepath = "test.txt"
    mock_r.llm_analysis = None
    return mock_r

# --- Tests ---

def test_health_check(client):
    """
    Test the GET /health endpoint.
    """
    response = client.get("/health")
    assert response.status_code == 200
    assert response.json() == {"status": "ok"}

def test_lint_endpoint_basic_success(client):
    """
    Test POST /lint with valid content and default config.
    """
    # Mock the pipeline function to avoid running actual linting logic
    with patch("src.backend.backend_api.lint_text") as mock_lint:
        # Setup the mock return value
        mock_report_instance = MagicMock()
        mock_report_instance.score = 100
        mock_report_instance.summary = "Perfect"
        mock_report_instance.issues = []
        # Fix: Ensure required fields for Report model are present and valid types
        mock_report_instance.filepath = "test_prompt.txt"
        mock_report_instance.llm_analysis = None

        mock_lint.return_value = mock_report_instance

        payload = {"content": "Simple prompt"}
        response = client.post("/lint", json=payload)

        assert response.status_code == 200
        # Verify the response structure based on our mock
        data = response.json()
        assert data["score"] == 100
        assert data["summary"] == "Perfect"
        
        # Verify lint_text was called with correct args
        mock_lint.assert_called_once()
        call_args = mock_lint.call_args
        assert call_args.kwargs['text'] == "Simple prompt"

def test_lint_endpoint_with_config(client):
    """
    Test POST /lint with custom configuration.
    """
    with patch("src.backend.backend_api.lint_text") as mock_lint:
        # Mock return
        mock_report_instance = MagicMock()
        mock_report_instance.score = 50
        mock_report_instance.summary = "Configured"
        mock_report_instance.issues = []
        # Fix: Ensure required fields for Report model are present and valid types
        mock_report_instance.filepath = "test_prompt.txt"
        mock_report_instance.llm_analysis = None
        
        mock_lint.return_value = mock_report_instance

        payload = {
            "content": "Prompt",
            "config": {
                "use_llm": False,
                "weights": {"modularity": 10}
            }
        }
        
        response = client.post("/lint", json=payload)
        
        assert response.status_code == 200
        
        # Verify config was passed correctly
        mock_lint.assert_called_once()
        _, kwargs = mock_lint.call_args
        # The code converts the dict to a LintConfig object
        config_arg = kwargs['config']
        assert config_arg.use_llm is False
        assert config_arg.weights == {"modularity": 10}

def test_lint_endpoint_missing_content(client):
    """
    Test POST /lint fails when 'content' is missing (Pydantic validation).
    """
    payload = {"config": {}} # Missing 'content'
    response = client.post("/lint", json=payload)
    
    assert response.status_code == 422
    errors = response.json()["detail"]
    assert any(err["loc"] == ["body", "content"] for err in errors)

def test_lint_endpoint_invalid_config_structure(client):
    """
    Test POST /lint fails when 'config' is not a dict (Pydantic validation).
    """
    payload = {
        "content": "Prompt",
        "config": "this is a string not a dict"
    }
    response = client.post("/lint", json=payload)
    
    assert response.status_code == 422
    errors = response.json()["detail"]
    assert any(err["loc"] == ["body", "config"] for err in errors)

def test_lint_endpoint_invalid_config_parameters(client):
    """
    Test POST /lint fails when config parameters are invalid for LintConfig.
    The code explicitly catches ValidationError during LintConfig creation and raises 400.
    """
    # We need to patch LintConfig to raise a ValidationError
    with patch("src.backend.backend_api.LintConfig") as MockLintConfig:
        # Fix: Generate a real ValidationError instead of manually constructing one.
        # Manual construction is fragile and version-dependent (Pydantic v1 vs v2).
        class FailModel(BaseModel):
            param: int
        
        real_error = None
        try:
            FailModel(param="invalid")
        except ValidationError as e:
            real_error = e
        
        MockLintConfig.side_effect = real_error

        payload = {
            "content": "Prompt",
            "config": {"bad_param": "value"}
        }
        
        response = client.post("/lint", json=payload)
        
        assert response.status_code == 400
        assert "Invalid configuration parameters" in response.json()["detail"]

def test_lint_endpoint_internal_error(client):
    """
    Test POST /lint handles unexpected exceptions from the pipeline with 500.
    """
    with patch("src.backend.backend_api.lint_text") as mock_lint:
        # Simulate an unexpected crash in the pipeline
        mock_lint.side_effect = Exception("Unexpected pipeline failure")
        
        # We also need to ensure LintConfig creation succeeds
        with patch("src.backend.backend_api.LintConfig"):
            payload = {"content": "Prompt"}
            response = client.post("/lint", json=payload)
            
            assert response.status_code == 500
            assert "An error occurred while processing the prompt" in response.json()["detail"]
            assert "Unexpected pipeline failure" in response.json()["detail"]

def test_lint_request_model():
    """
    Unit test for the LintRequest Pydantic model directly.
    """
    # Valid case
    req = LintRequest(content="abc", config={"a": 1})
    assert req.content == "abc"
    assert req.config == {"a": 1}

    # Default config
    req = LintRequest(content="abc")
    assert req.content == "abc"
    assert req.config == {}

    # Missing content
    try:
        LintRequest(config={})
        assert False, "Should have raised ValidationError"
    except ValidationError as e:
        assert "content" in str(e)