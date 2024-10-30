# tests/test_fix_code_module_errors.py

import os
import pytest
from unittest.mock import patch, mock_open, MagicMock
from pdd.fix_code_module_errors import fix_code_module_errors, FixOutput

@pytest.fixture
def mock_pdd_path(monkeypatch):
    """Fixture to mock the PDD_PATH environment variable."""
    monkeypatch.setenv('PDD_PATH', '/fake/path')

@pytest.fixture
def mock_prompt_files():
    """Fixture to mock the content of prompt files."""
    fix_prompt_content = "Fix the following code errors:\n{program}\n{prompt}\n{code}\n{errors}"
    extract_prompt_content = "Extract the fixes from the following response:\n{program_code_fix}\n{program}\n{code}"

    mock_files = {
        '/fake/path/prompts/fix_code_module_errors_LLM.prompt': fix_prompt_content,
        '/fake/path/prompts/extract_program_code_fix_LLM.prompt': extract_prompt_content,
    }

    def _mock_open(file, mode='r', *args, **kwargs):
        if str(file) in mock_files:
            return mock_open(read_data=mock_files[str(file)])(file, mode)
        else:
            raise FileNotFoundError(f"No such file or directory: '{file}'")

    return _mock_open

@pytest.fixture
def mock_llm_selector():
    """Fixture to mock the llm_selector function."""
    with patch('pdd.fix_code_module_errors.llm_selector') as mock_selector:
        mock_selector.return_value = (
            MagicMock(),   # llm
            MagicMock(side_effect=lambda x: 1000),  # token_counter returns 1000 tokens
            0.02,          # input_cost per million tokens
            0.03,          # output_cost per million tokens
            "mock-model"   # model_name
        )
        yield mock_selector

@pytest.fixture
def mock_json_parser():
    """Fixture to mock the JsonOutputParser."""
    with patch('pdd.fix_code_module_errors.JsonOutputParser') as mock_parser:
        parser_instance = mock_parser.return_value
        parser_instance.parse.return_value = FixOutput(
            update_program=True,
            update_code=True,
            fixed_program="print('Fixed Program')",
            fixed_code="print('Fixed Code')"
        )
        yield mock_parser

@pytest.fixture
def mock_chain_invoke(mock_json_parser):
    """Fixture to mock the chain.invoke method."""
    with patch('pdd.fix_code_module_errors.PromptTemplate') as mock_prompt_template:
        # Create mock chains
        mock_fix_chain = MagicMock()
        mock_extract_chain = MagicMock()
        
        # Configure the first chain
        mock_fix_chain.invoke.return_value = "Fixed Code Analysis"
        
        # Configure the second chain
        mock_result = FixOutput(
            update_program=True,
            update_code=True,
            fixed_program="print('Fixed Program')",
            fixed_code="print('Fixed Code')"
        )
        mock_extract_chain.invoke.return_value = mock_result
        
        # Configure PromptTemplate
        mock_prompt_template.from_template.side_effect = [mock_fix_chain, mock_extract_chain]
        
        yield mock_fix_chain, mock_extract_chain

def test_fix_code_module_errors_success(mock_pdd_path, mock_prompt_files, mock_llm_selector, mock_chain_invoke):
    """Test the successful execution of fix_code_module_errors."""
    mock_open_fn = mock_prompt_files
    with patch("builtins.open", mock_open_fn):
        fix_chain, extract_chain = mock_chain_invoke
        update_program, update_code, fixed_program, fixed_code, total_cost, model_name = fix_code_module_errors(
            program="original_program_code",
            prompt="original_prompt",
            code="original_code",
            errors="original_errors",
            strength=0.5,
            temperature=0.7
        )

        # Assertions for returned values
        assert isinstance(update_program, bool), "update_program should be a boolean"
        assert update_program is True, "update_program should be True"
        assert isinstance(update_code, bool), "update_code should be a boolean"
        assert update_code is True, "update_code should be True"
        assert isinstance(fixed_program, str), "fixed_program should be a string"
        assert fixed_program == "print('Fixed Program')", "fixed_program has unexpected value"
        assert isinstance(fixed_code, str), "fixed_code should be a string"
        assert fixed_code == "print('Fixed Code')", "fixed_code has unexpected value"
        assert isinstance(total_cost, float), "total_cost should be a float"
        assert total_cost == (1000 / 1_000_000) * 0.02 + (1000 / 1_000_000) * 0.03, "total_cost has unexpected value"
        assert isinstance(model_name, str), "model_name should be a string"
        assert model_name == "mock-model", "model_name has unexpected value"

def test_fix_code_module_errors_missing_pdd_path(monkeypatch):
    """Test behavior when PDD_PATH environment variable is missing."""
    monkeypatch.delenv('PDD_PATH', raising=False)

    with pytest.raises(ValueError) as exc_info:
        fix_code_module_errors(
            program="program",
            prompt="prompt",
            code="code",
            errors="errors",
            strength=0.5
        )
    assert "PDD_PATH environment variable not set" in str(exc_info.value)

def test_fix_code_module_errors_missing_prompt_files(mock_pdd_path, mock_prompt_files, mock_llm_selector, mock_chain_invoke):
    """Test behavior when prompt files are missing."""
    # Modify mock_open to raise FileNotFoundError for prompt files
    def _missing_mock_open(file, mode='r', *args, **kwargs):
        raise FileNotFoundError(f"No such file or directory: '{file}'")

    with patch("builtins.open", _missing_mock_open):
        with pytest.raises(FileNotFoundError):
            fix_code_module_errors(
                program="program",
                prompt="prompt",
                code="code",
                errors="errors",
                strength=0.5
            )

def test_fix_code_module_errors_invalid_strength(mock_pdd_path, mock_prompt_files, mock_llm_selector, mock_chain_invoke):
    """Test behavior with invalid strength values."""
    # Test strength below 0
    with pytest.raises(ValueError):
        fix_code_module_errors(
            program="program",
            prompt="prompt",
            code="code",
            errors="errors",
            strength=-0.1
        )

    # Test strength above 1
    with pytest.raises(ValueError):
        fix_code_module_errors(
            program="program",
            prompt="prompt",
            code="code",
            errors="errors",
            strength=1.1
        )

def test_fix_code_module_errors_invalid_temperature(mock_pdd_path, mock_prompt_files, mock_llm_selector, mock_chain_invoke):
    """Test behavior with invalid temperature values."""
    # Test temperature below 0
    with pytest.raises(ValueError):
        fix_code_module_errors(
            program="program",
            prompt="prompt",
            code="code",
            errors="errors",
            strength=0.5,
            temperature=-0.5
        )

    # Test temperature above a reasonable upper bound, e.g., 1
    with pytest.raises(ValueError):
        fix_code_module_errors(
            program="program",
            prompt="prompt",
            code="code",
            errors="errors",
            strength=0.5,
            temperature=1.5
        )

def test_fix_code_module_errors_llm_selector_failure(mock_pdd_path, mock_prompt_files):
    """Test behavior when llm_selector raises an exception."""
    with patch("builtins.open", mock_prompt_files):
        with patch('pdd.fix_code_module_errors.llm_selector', 
                side_effect=Exception("LLM Selector Error")):
            with pytest.raises(Exception) as exc_info:
                fix_code_module_errors(
                    program="program",
                    prompt="prompt",
                    code="code",
                    errors="errors",
                    strength=0.5
                )
            assert "LLM Selector Error" in str(exc_info.value)

def test_fix_code_module_errors_chain_invoke_failure(mock_pdd_path, mock_prompt_files, mock_llm_selector):
    """Test behavior when chain.invoke raises an exception."""
    with patch("builtins.open", mock_prompt_files):
        with patch('pdd.fix_code_module_errors.PromptTemplate') as mock_prompt_template:
            mock_chain = MagicMock()
            mock_chain.invoke.side_effect = Exception("Chain Invoke Error")
            mock_chain.__or__ = MagicMock(return_value=mock_chain)
            
            mock_prompt_template.from_template.return_value = mock_chain
            
            with pytest.raises(Exception) as exc_info:
                fix_code_module_errors(
                    program="program",
                    prompt="prompt",
                    code="code",
                    errors="errors",
                    strength=0.5
                )
            assert "Chain Invoke Error" in str(exc_info.value)

def test_fix_code_module_errors_empty_inputs(mock_pdd_path, mock_prompt_files, mock_llm_selector, mock_chain_invoke):
    """Test behavior when inputs are empty strings."""
    mock_open_fn = mock_prompt_files
    with patch("builtins.open", mock_open_fn):
        fix_chain, extract_chain = mock_chain_invoke
        update_program, update_code, fixed_program, fixed_code, total_cost, model_name = fix_code_module_errors(
            program="",
            prompt="",
            code="",
            errors="",
            strength=0.5,
            temperature=0.7
        )

        # Assert that the function still returns expected values
        assert update_program is True
        assert update_code is True
        assert fixed_program == "print('Fixed Program')"
        assert fixed_code == "print('Fixed Code')"
        assert total_cost == (1000 / 1_000_000) * 0.02 + (1000 / 1_000_000) * 0.03
        assert model_name == "mock-model"
