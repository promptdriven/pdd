import pytest
from unittest.mock import patch, mock_open, MagicMock
from pdd.trace import trace
from fuzzywuzzy import process

# Sample data for tests
SAMPLE_CODE_FILE = """
def foo():
    print("Hello, World!")
    return True
"""

SAMPLE_PROMPT_FILE = """
Line 1: Initialize variables
Line 2: Call foo function
Line 3: Print greeting
Line 4: Return success
"""

# Mocked responses
MOCK_TRACE_OUTPUT = "Extracted line from trace LLM"
MOCK_EXTRACTED_LINE = "Line 3: Print greeting"
MOCK_PROMPT_LINE_NUMBER = 3
MOCK_MODEL_NAME = "mock-model"
MOCK_TOTAL_COST = 0.000001  # Adjusted to a more realistic value

@pytest.fixture
def mock_environment():
    with patch.dict('os.environ', {'PDD_PATH': '/fake/path'}):
        yield

@pytest.fixture
def mock_open_files():
    mock_trace_prompt = "Trace LLM prompt content"
    mock_extract_prompt = "Extract promptline LLM prompt content"
    m = mock_open()
    def side_effect(file, *args, **kwargs):
        if 'trace_LLM.prompt' in file:
            return mock_open(read_data=mock_trace_prompt).return_value
        elif 'extract_promptline_LLM.prompt' in file:
            return mock_open(read_data=mock_extract_prompt).return_value
        else:
            raise FileNotFoundError(f"No such file: {file}")
    m.side_effect = side_effect
    with patch('builtins.open', m):
        yield m

@pytest.fixture
def mock_preprocess():
    with patch('pdd.trace.preprocess', return_value="Preprocessed prompt") as mock:
        yield mock

@pytest.fixture
def mock_llm_selector():
    mock_llm = MagicMock()
    token_counter = MagicMock(side_effect=lambda x: len(x.split()))
    return_patch = patch('pdd.trace.llm_selector', return_value=(
        mock_llm, token_counter, 0.000001, 0.000002, MOCK_MODEL_NAME
    ))
    mock_llm_selector = return_patch.start()
    yield mock_llm_selector
    return_patch.stop()

@pytest.fixture
def mock_trace_chain_invoke():
    with patch('langchain_core.prompts.prompt.PromptTemplate.from_template') as mock_prompt_template:
        mock_chain = MagicMock()
        mock_chain.invoke.return_value = MOCK_TRACE_OUTPUT
        mock_prompt_template.return_value.__or__.return_value.__or__.return_value = mock_chain
        yield mock_prompt_template

@pytest.fixture
def mock_extract_chain_invoke():
    with patch('langchain_core.prompts.prompt.PromptTemplate.from_template') as mock_prompt_template:
        mock_chain = MagicMock()
        mock_chain.invoke.return_value = MOCK_EXTRACTED_LINE
        mock_prompt_template.return_value.__or__.return_value.__or__.return_value = mock_chain
        yield mock_prompt_template

@pytest.fixture
def mock_fuzzywuzzy_process():
    def mock_extractOne(query, choices, score_cutoff=0):
        for idx, choice in enumerate(choices):
            if query.lower() in choice.lower():
                return (choice, 100, idx)
        return None
    with patch('pdd.trace.process.extractOne', side_effect=mock_extractOne) as mock:
        yield mock

def test_trace_success(mock_environment, mock_open_files, mock_preprocess, mock_llm_selector, mock_trace_chain_invoke, mock_extract_chain_invoke, mock_fuzzywuzzy_process):
    result = trace(
        code_file=SAMPLE_CODE_FILE,
        code_line=2,
        prompt_file=SAMPLE_PROMPT_FILE,
        strength=0.7,
        temperature=0.3
    )
    assert result[0] == MOCK_PROMPT_LINE_NUMBER
    assert abs(result[1] - MOCK_TOTAL_COST) < 1e-6  # Allow for small floating-point differences
    assert result[2] == MOCK_MODEL_NAME

def test_trace_missing_pdd_path(mock_open_files, mock_preprocess, mock_llm_selector, mock_fuzzywuzzy_process):
    with patch.dict('os.environ', {}, clear=True):
        with pytest.raises(ValueError) as excinfo:
            trace(
                code_file=SAMPLE_CODE_FILE,
                code_line=2,
                prompt_file=SAMPLE_PROMPT_FILE
            )
        assert "PDD_PATH environment variable is not set" in str(excinfo.value)

def test_trace_missing_trace_prompt_file(mock_environment, mock_preprocess, mock_llm_selector, mock_fuzzywuzzy_process):
    with patch('builtins.open', side_effect=FileNotFoundError("No such file: trace_LLM.prompt")):
        with pytest.raises(FileNotFoundError) as excinfo:
            trace(
                code_file=SAMPLE_CODE_FILE,
                code_line=2,
                prompt_file=SAMPLE_PROMPT_FILE
            )
        assert "No such file: trace_LLM.prompt" in str(excinfo.value)

def test_trace_missing_extract_prompt_file(mock_environment, mock_preprocess, mock_llm_selector, mock_fuzzywuzzy_process):
    def side_effect(file, *args, **kwargs):
        if 'trace_LLM.prompt' in file:
            return mock_open(read_data="Trace LLM prompt content")()
        else:
            raise FileNotFoundError(f"No such file: {file}")
    
    with patch('builtins.open', side_effect=side_effect):
        with pytest.raises(FileNotFoundError) as excinfo:
            trace(
                code_file=SAMPLE_CODE_FILE,
                code_line=2,
                prompt_file=SAMPLE_PROMPT_FILE
            )
        assert "No such file: extract_promptline_LLM.prompt" in str(excinfo.value)

def test_trace_invalid_code_line(mock_environment, mock_open_files, mock_preprocess, mock_llm_selector, mock_fuzzywuzzy_process):
    invalid_code_line = 10  # Out of range
    with pytest.raises(ValueError) as excinfo:
        trace(
            code_file=SAMPLE_CODE_FILE,
            code_line=invalid_code_line,
            prompt_file=SAMPLE_PROMPT_FILE
        )
    assert f"Invalid code_line: {invalid_code_line}. File has {len(SAMPLE_CODE_FILE.splitlines())} lines." in str(excinfo.value)

def test_trace_no_matching_line(mock_environment, mock_open_files, mock_preprocess, mock_llm_selector, mock_trace_chain_invoke, mock_extract_chain_invoke):
    with patch('pdd.trace.process.extractOne', return_value=None):
        with pytest.raises(ValueError) as excinfo:
            trace(
                code_file=SAMPLE_CODE_FILE,
                code_line=2,
                prompt_file=SAMPLE_PROMPT_FILE
            )
        assert "Could not find a matching line in the prompt file" in str(excinfo.value)

def test_trace_llm_exception(mock_environment, mock_open_files, mock_preprocess, mock_llm_selector, mock_fuzzywuzzy_process):
    with patch('langchain_core.prompts.prompt.PromptTemplate.from_template') as mock_prompt_template:
        mock_chain = MagicMock()
        mock_chain.invoke.side_effect = Exception("LLM invocation failed")
        mock_prompt_template.return_value.__or__.return_value.__or__.return_value = mock_chain
        with pytest.raises(Exception) as excinfo:
            trace(
                code_file=SAMPLE_CODE_FILE,
                code_line=2,
                prompt_file=SAMPLE_PROMPT_FILE
            )
        assert "LLM invocation failed" in str(excinfo.value)

def test_trace_invalid_strength_value(mock_environment, mock_open_files, mock_preprocess, mock_fuzzywuzzy_process):
    with patch('pdd.trace.llm_selector', side_effect=ValueError("Invalid strength value")):
        with pytest.raises(ValueError) as excinfo:
            trace(
                code_file=SAMPLE_CODE_FILE,
                code_line=2,
                prompt_file=SAMPLE_PROMPT_FILE,
                strength=1.5  # Invalid strength
            )
        assert "Invalid strength value" in str(excinfo.value)

def test_trace_default_parameters(mock_environment, mock_open_files, mock_preprocess, mock_llm_selector, mock_trace_chain_invoke, mock_extract_chain_invoke, mock_fuzzywuzzy_process):
    result = trace(
        code_file=SAMPLE_CODE_FILE,
        code_line=2,
        prompt_file=SAMPLE_PROMPT_FILE
    )
    assert result[0] == MOCK_PROMPT_LINE_NUMBER
    assert abs(result[1] - MOCK_TOTAL_COST) < 1e-6  # Allow for small floating-point differences
    assert result[2] == MOCK_MODEL_NAME

def test_trace_cost_computation(mock_environment, mock_open_files, mock_preprocess, mock_llm_selector, mock_trace_chain_invoke, mock_extract_chain_invoke, mock_fuzzywuzzy_process):
    with patch('pdd.trace.llm_selector') as mock_selector:
        mock_llm = MagicMock()
        token_counter = MagicMock(side_effect=lambda x: len(x.split()))
        mock_selector.return_value = (mock_llm, token_counter, 0.000001, 0.000002, MOCK_MODEL_NAME)
        
        result = trace(
            code_file=SAMPLE_CODE_FILE,
            code_line=2,
            prompt_file=SAMPLE_PROMPT_FILE,
            strength=0.7,
            temperature=0.3
        )
        
        # Calculate expected cost
        token_count_trace = len(SAMPLE_CODE_FILE.split()) + len(SAMPLE_PROMPT_FILE.split())
        cost_trace = (0.000001 * token_count_trace) / 1_000_000
        
        token_count_extract = len(MOCK_TRACE_OUTPUT.split())
        cost_extract = (0.000001 * token_count_extract) / 1_000_000
        
        total_expected_cost = cost_trace + cost_extract
        
        assert result[0] == MOCK_PROMPT_LINE_NUMBER
        assert abs(result[1] - total_expected_cost) < 1e-12  # Allow for small floating-point differences
        assert result[2] == MOCK_MODEL_NAME
