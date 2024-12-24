import pytest
from pdd.trace import trace
from unittest.mock import patch, MagicMock

# Test data
SAMPLE_CODE = """def hello():
    print("Hello, World!")
    return True"""

SAMPLE_PROMPT = """Create a function that prints "Hello, World!"
Here's the implementation:
def hello():
    print("Hello, World!")
    return True"""

@pytest.fixture
def mock_llm_responses():
    trace_response = {
        'result': 'The matching line is: print("Hello, World!")',
        'cost': 0.001,
        'model_name': 'gpt-3.5-turbo'
    }
    
    extract_response = {
        'result': MagicMock(prompt_line='print("Hello, World!")'),
        'cost': 0.001,
        'model_name': 'gpt-3.5-turbo'
    }
    
    return trace_response, extract_response

@pytest.fixture
def mock_prompt_templates():
    return "Test prompt template"

def test_successful_trace(mock_llm_responses, mock_prompt_templates):
    """
    Test successful trace operation.
    Expected line mapping:
    SAMPLE_CODE line 2: print("Hello, World!")
    maps to
    SAMPLE_PROMPT line 4: print("Hello, World!")
    """
    with patch('pdd.trace.load_prompt_template', return_value=mock_prompt_templates), \
         patch('pdd.trace.llm_invoke', side_effect=mock_llm_responses):
        
        result, cost, model = trace(
            code_file=SAMPLE_CODE,
            code_line=2,
            prompt_file=SAMPLE_PROMPT,
            strength=0.5,
            temperature=0,
            verbose=False
        )
        
        assert result == 4  # Line number in SAMPLE_PROMPT (print statement)
        assert cost == 0.002  # Sum of both LLM calls
        assert model == 'gpt-3.5-turbo'

def test_invalid_code_line():
    result, cost, model = trace(
        code_file=SAMPLE_CODE,
        code_line=10,  # Invalid line number
        prompt_file=SAMPLE_PROMPT,
        verbose=False
    )
    
    assert result is None
    assert cost == 0.0
    assert model == ""

def test_empty_inputs():
    result, cost, model = trace(
        code_file="",
        code_line=1,
        prompt_file="",
        verbose=False
    )
    
    assert result is None
    assert cost == 0.0
    assert model == ""

@pytest.mark.parametrize("code_line", [0, -1])
def test_invalid_line_numbers(code_line):
    result, cost, model = trace(
        code_file=SAMPLE_CODE,
        code_line=code_line,
        prompt_file=SAMPLE_PROMPT,
        verbose=False
    )
    
    assert result is None
    assert cost == 0.0
    assert model == ""

def test_verbose_output(mock_llm_responses, mock_prompt_templates, capsys):
    with patch('pdd.trace.load_prompt_template', return_value=mock_prompt_templates), \
         patch('pdd.trace.llm_invoke', side_effect=mock_llm_responses):
        
        trace(
            code_file=SAMPLE_CODE,
            code_line=2,
            prompt_file=SAMPLE_PROMPT,
            verbose=True
        )
        
        captured = capsys.readouterr()
        assert "Running trace analysis" in captured.out
        assert "Extracting prompt line" in captured.out

def test_failed_prompt_template_load():
    with patch('pdd.trace.load_prompt_template', return_value=None):
        result, cost, model = trace(
            code_file=SAMPLE_CODE,
            code_line=2,
            prompt_file=SAMPLE_PROMPT,
            verbose=False
        )
        
        assert result is None
        assert cost == 0.0
        assert model == ""

def test_llm_invoke_error(mock_prompt_templates):
    with patch('pdd.trace.load_prompt_template', return_value=mock_prompt_templates), \
         patch('pdd.trace.llm_invoke', side_effect=Exception("LLM Error")):
        
        result, cost, model = trace(
            code_file=SAMPLE_CODE,
            code_line=2,
            prompt_file=SAMPLE_PROMPT,
            verbose=False
        )
        
        assert result is None
        assert cost == 0.0
        assert model == ""