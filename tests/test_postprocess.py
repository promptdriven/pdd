import pytest
from unittest.mock import patch, mock_open
from postprocess import postprocess
from rich.console import Console

# Mock environment variable
@pytest.fixture(autouse=True)
def mock_env_var():
    with patch.dict('os.environ', {'PDD_PATH': '/mock/path'}):
        yield

# Mock console to capture output
@pytest.fixture
def mock_console(monkeypatch):
    mock_console = Console(file=None)
    monkeypatch.setattr("postprocess.console", mock_console)
    return mock_console

# Mock functions and classes
@pytest.fixture
def mock_dependencies(monkeypatch):
    monkeypatch.setattr("postprocess.postprocess_0", lambda x, y: "Mocked postprocess_0 output")
    monkeypatch.setattr("postprocess.llm_selector", lambda x, y: (None, lambda z: len(z), 0.01, 0.02))
    monkeypatch.setattr("postprocess.PromptTemplate", lambda template, input_variables: None)
    monkeypatch.setattr("postprocess.JsonOutputParser", lambda pydantic_object: None)
    monkeypatch.setattr("langchain_core.prompts.PromptTemplate.format", lambda self, **kwargs: "Mocked prompt")

def test_postprocess_strength_zero(mock_dependencies):
    result, cost = postprocess("Test input", "python", strength=0)
    assert result == "Mocked postprocess_0 output"
    assert cost == 0.0

def test_postprocess_normal_execution(mock_dependencies, mock_console):
    with patch("builtins.open", mock_open(read_data="Mock prompt template")):
        with patch("postprocess.chain.invoke") as mock_invoke:
            mock_invoke.return_value = {"extracted_code": "def test():\n    pass"}
            result, cost = postprocess("Test input", "python")
    
    assert "def test():" in result
    assert cost > 0

def test_postprocess_missing_pdd_path():
    with patch.dict('os.environ', clear=True):
        with pytest.raises(ValueError, match="PDD_PATH environment variable is not set"):
            postprocess("Test input", "python")

def test_postprocess_error_handling(mock_dependencies, mock_console):
    with patch("builtins.open", mock_open(read_data="Mock prompt template")):
        with patch("postprocess.chain.invoke", side_effect=Exception("Test error")):
            result, cost = postprocess("Test input", "python")
    
    assert result == ""
    assert cost == 0.0

def test_postprocess_remove_backticks(mock_dependencies, mock_console):
    with patch("builtins.open", mock_open(read_data="Mock prompt template")):
        with patch("postprocess.chain.invoke") as mock_invoke:
            mock_invoke.return_value = {"extracted_code": "```python\ndef test():\n    pass\n```"}
            result, cost = postprocess("Test input", "python")
    
    assert result == "def test():\n    pass"
    assert "```" not in result

def test_postprocess_missing_extracted_code(mock_dependencies, mock_console):
    with patch("builtins.open", mock_open(read_data="Mock prompt template")):
        with patch("postprocess.chain.invoke") as mock_invoke:
            mock_invoke.return_value = {}
            result, cost = postprocess("Test input", "python")
    
    assert "Error: No extracted code found in the output" in result
