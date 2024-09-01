import pytest
from unittest.mock import patch, mock_open
from pdd.context_generator import context_generator

@pytest.fixture
def mock_environment():
    with patch.dict('os.environ', {'PDD_PATH': '/mock/path'}):
        yield

@pytest.fixture
def mock_file_content():
    return "Mock example generator prompt content"

@pytest.fixture
def mock_llm_selector():
    return (
        lambda *args, **kwargs: (
            "mock_llm",
            lambda x: len(x),
            0.001,
            0.002,
            "mock_model"
        )
    )

@pytest.fixture
def mock_chain_run():
    return lambda **kwargs: "Mock generated output"

def test_context_generator_success(mock_environment, mock_file_content, mock_llm_selector, mock_chain_run):
    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        with patch('pdd.context_generator.preprocess', side_effect=lambda x, **kwargs: x):
            with patch('pdd.context_generator.llm_selector', mock_llm_selector):
                with patch('pdd.context_generator.LLMChain') as mock_llm_chain:
                    mock_llm_chain.return_value.run = mock_chain_run
                    with patch('pdd.context_generator.unfinished_prompt', return_value=(None, True, 0, None)):
                        with patch('pdd.context_generator.postprocess', return_value=("Postprocessed output", 0.001)):
                            result = context_generator("test_module", "test_prompt", "python", 0.5, 0.0)
                            
                            assert isinstance(result, tuple)
                            assert len(result) == 3
                            assert isinstance(result[0], str)
                            assert isinstance(result[1], float)
                            assert isinstance(result[2], str)
                            assert result[0] == "Postprocessed output"
                            assert result[2] == "mock_model"

def test_context_generator_unfinished_prompt(mock_environment, mock_file_content, mock_llm_selector, mock_chain_run):
    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        with patch('pdd.context_generator.preprocess', side_effect=lambda x, **kwargs: x):
            with patch('pdd.context_generator.llm_selector', mock_llm_selector):
                with patch('pdd.context_generator.LLMChain') as mock_llm_chain:
                    mock_llm_chain.return_value.run = mock_chain_run
                    with patch('pdd.context_generator.unfinished_prompt', return_value=(None, False, 0.001, None)):
                        with patch('pdd.context_generator.continue_generation', return_value=("Continued output", 0.002, None)):
                            with patch('pdd.context_generator.postprocess', return_value=("Postprocessed output", 0.001)):
                                result = context_generator("test_module", "test_prompt", "python", 0.5, 0.0)
                                
                                assert isinstance(result, tuple)
                                assert len(result) == 3
                                assert isinstance(result[0], str)
                                assert isinstance(result[1], float)
                                assert isinstance(result[2], str)
                                assert result[0] == "Postprocessed output"
                                assert result[2] == "mock_model"

def test_context_generator_missing_env_variable():
    with pytest.raises(ValueError, match="PDD_PATH environment variable is not set"):
        context_generator("test_module", "test_prompt")

def test_context_generator_file_not_found(mock_environment):
    with patch('builtins.open', side_effect=FileNotFoundError):
        result = context_generator("test_module", "test_prompt")
        assert result == ("", 0.0, "")

def test_context_generator_exception_handling(mock_environment, mock_file_content):
    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        with patch('pdd.context_generator.preprocess', side_effect=Exception("Mocked error")):
            result = context_generator("test_module", "test_prompt")
            assert result == ("", 0.0, "")