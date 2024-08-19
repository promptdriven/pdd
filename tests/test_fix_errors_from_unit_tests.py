import pytest
from unittest.mock import patch, mock_open
from fix_errors_from_unit_tests import fix_errors_from_unit_tests

# Mock data
MOCK_UNIT_TEST = "def test_example(): assert True"
MOCK_CODE = "def example(): return True"
MOCK_ERROR = "AssertionError: Test failed"
MOCK_STRENGTH = 0.7
MOCK_TEMPERATURE = 0.5

# Mock prompt content
MOCK_PROMPT_CONTENT = "Mock prompt content"

# Mock LLM response
MOCK_LLM_RESPONSE = """
# Fixed Code

Here's the fixed code:

```python
def example():
    return True
```

# Fixed Unit Test

Here's the fixed unit test:

```python
def test_example():
    assert example() == True
```
"""

MOCK_JSON_RESPONSE = {
    "update_unit_test": True,
    "update_code": False,
    "fixed_unit_test": "def test_example():\n    assert example() == True",
    "fixed_code": "def example():\n    return True"
}

@pytest.fixture
def mock_environment():
    with patch.dict('os.environ', {'PDD_PATH': '/mock/path'}):
        yield

@pytest.fixture
def mock_file_open():
    with patch('builtins.open', mock_open(read_data=MOCK_PROMPT_CONTENT)):
        yield

@pytest.fixture
def mock_llm_selector():
    with patch('fix_errors_from_unit_tests.llm_selector') as mock:
        mock.return_value = (
            lambda x: MOCK_LLM_RESPONSE,  # Mock LLM
            lambda x: len(x),  # Mock token counter
            0.01,  # Mock input cost
            0.02   # Mock output cost
        )
        yield mock

@pytest.fixture
def mock_json_parser():
    with patch('fix_errors_from_unit_tests.JsonOutputParser') as mock:
        mock_parser = mock.return_value
        mock_parser.parse.return_value = MOCK_JSON_RESPONSE
        yield mock_parser

def test_fix_errors_from_unit_tests_success(mock_environment, mock_file_open, mock_llm_selector, mock_json_parser):
    result = fix_errors_from_unit_tests(MOCK_UNIT_TEST, MOCK_CODE, MOCK_ERROR, MOCK_STRENGTH, MOCK_TEMPERATURE)
    
    assert isinstance(result, tuple)
    assert len(result) == 5
    update_unit_test, update_code, fixed_unit_test, fixed_code, total_cost = result
    
    assert update_unit_test == True
    assert update_code == False
    assert fixed_unit_test == "def test_example():\n    assert example() == True"
    assert fixed_code == "def example():\n    return True"
    assert isinstance(total_cost, float)
    assert total_cost > 0

def test_fix_errors_from_unit_tests_missing_pdd_path():
    with patch.dict('os.environ', clear=True):
        result = fix_errors_from_unit_tests(MOCK_UNIT_TEST, MOCK_CODE, MOCK_ERROR, MOCK_STRENGTH, MOCK_TEMPERATURE)
    
    assert result == (False, False, '', '', 0.0)

def test_fix_errors_from_unit_tests_file_not_found(mock_environment):
    with patch('builtins.open', side_effect=FileNotFoundError):
        result = fix_errors_from_unit_tests(MOCK_UNIT_TEST, MOCK_CODE, MOCK_ERROR, MOCK_STRENGTH, MOCK_TEMPERATURE)
    
    assert result == (False, False, '', '', 0.0)
