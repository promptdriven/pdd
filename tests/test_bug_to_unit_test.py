import os
import pytest
from unittest.mock import patch, mock_open, Mock
from pdd.bug_to_unit_test import bug_to_unit_test

@pytest.fixture
def valid_inputs():
    return {
        "current_output": "2",
        "desired_output": "4",
        "prompt_used_to_generate_the_code": "create a function that adds two numbers in python",
        "code_under_test": "def add(a, b):\n    return a + b",
        "program_used_to_run_code_under_test": "python add.py",
        "strength": 0.5,
        "temperature": 0.7,
        "language": "python"
    }

@pytest.fixture
def mock_prompt_content():
    return "Generate a unit test for the provided code."

@pytest.fixture
def mock_unit_test_output():
    return (
        "import pytest\n"
        "from pdd.bug_to_unit_test import add\n\n"
        "def test_add_positive_numbers():\n"
        "    assert add(2, 3) == 5\n\n"
        "def test_add_negative_numbers():\n"
        "    assert add(-2, -3) == -5\n\n"
        "def test_add_zero():\n"
        "    assert add(0, 0) == 0\n"
    )

@patch.dict(os.environ, {"PDD_PATH": "/fake/path"})
def test_bug_to_unit_test_valid_input(valid_inputs, mock_prompt_content, mock_unit_test_output):
    with patch("builtins.open", mock_open(read_data=mock_prompt_content)) as mocked_file:
        with patch("pdd.bug_to_unit_test.preprocess.preprocess", return_value=mock_prompt_content) as mock_preprocess:
            with patch("pdd.bug_to_unit_test.llm_selector.llm_selector") as mock_llm_selector:
                mock_llm = Mock()
                mock_llm.invoke.side_effect = lambda x: mock_unit_test_output
                mock_llm_selector.return_value = (mock_llm, lambda x: len(x), 0.02, 0.03, "gpt-4")

                with patch("pdd.unfinished_prompt.unfinished_prompt", return_value=("", True, 0.0, "gpt-4")) as mock_unfinished:
                    with patch("pdd.continue_generation.continue_generation", return_value=("", 0.0, "")) as mock_continue:
                        with patch("pdd.postprocess.postprocess", return_value=(mock_unit_test_output, 0.01)) as mock_postprocess:
                            result, total_cost, model_name = bug_to_unit_test(**valid_inputs)

                            # Assertions
                            assert result == mock_unit_test_output
                            expected_cost = (
                                (len(valid_inputs["prompt_used_to_generate_the_code"]) * 0.02 / 1_000_000) +
                                (len(mock_unit_test_output) * 0.03 / 1_000_000) +
                                0.01
                            )
                            assert total_cost == pytest.approx(expected_cost)
                            assert model_name == "gpt-4"

                            # Verify file was read correctly
                            mocked_file.assert_called_once_with(
                                os.path.join("/fake/path", "prompts", "bug_to_unit_test_LLM.prompt"),
                                'r'
                            )

@patch.dict(os.environ, {}, clear=True)
def test_bug_to_unit_test_missing_pdd_path(valid_inputs):
    with pytest.raises(ValueError) as exc_info:
        bug_to_unit_test(**valid_inputs)
    assert "PDD_PATH environment variable is not set" in str(exc_info.value)

@patch.dict(os.environ, {"PDD_PATH": "/fake/path"})
def test_bug_to_unit_test_missing_prompt_file(valid_inputs):
    with patch("builtins.open", mock_open()) as mocked_file:
        mocked_file.side_effect = FileNotFoundError("Prompt file not found.")
        with pytest.raises(FileNotFoundError) as exc_info:
            bug_to_unit_test(**valid_inputs)
        assert "Prompt file not found." in str(exc_info.value)

@patch.dict(os.environ, {"PDD_PATH": "/fake/path"})
def test_bug_to_unit_test_empty_inputs():
    empty_inputs = {
        "current_output": "",
        "desired_output": "",
        "prompt_used_to_generate_the_code": "",
        "code_under_test": "",
        "program_used_to_run_code_under_test": "",
        "strength": 0.0,
        "temperature": 0.0,
        "language": ""
    }
    
    with patch("builtins.open", mock_open(read_data="")) as mocked_file:
        with patch("pdd.bug_to_unit_test.preprocess.preprocess", return_value="") as mock_preprocess:
            with patch("pdd.bug_to_unit_test.llm_selector.llm_selector") as mock_llm_selector:
                mock_llm = Mock()
                mock_llm.invoke.side_effect = lambda x: ""
                mock_llm_selector.return_value = (mock_llm, lambda x: 0, 0.0, 0.0, "gpt-4")
                
                with patch("pdd.unfinished_prompt.unfinished_prompt", return_value=("", True, 0.0, "gpt-4")) as mock_unfinished:
                    with patch("pdd.continue_generation.continue_generation", return_value=("", 0.0, "")) as mock_continue:
                        with patch("pdd.postprocess.postprocess", return_value=("", 0.0)) as mock_postprocess:
                            result, total_cost, model_name = bug_to_unit_test(**empty_inputs)
                            
                            assert result == ""
                            assert total_cost == 0.0
                            assert model_name == "gpt-4"

@patch.dict(os.environ, {"PDD_PATH": "/fake/path"})
def test_bug_to_unit_test_llm_error(valid_inputs, mock_prompt_content):
    with patch("builtins.open", mock_open(read_data=mock_prompt_content)) as mocked_file:
        with patch("pdd.bug_to_unit_test.preprocess.preprocess", return_value=mock_prompt_content) as mock_preprocess:
            with patch("pdd.bug_to_unit_test.llm_selector.llm_selector", side_effect=Exception("LLM service failed.")) as mock_llm_selector:
                with pytest.raises(Exception) as exc_info:
                    bug_to_unit_test(**valid_inputs)
                assert "LLM service failed." in str(exc_info.value)

@patch.dict(os.environ, {"PDD_PATH": "/fake/path"})
def test_bug_to_unit_test_continue_generation(valid_inputs, mock_prompt_content, mock_unit_test_output):
    with patch("builtins.open", mock_open(read_data=mock_prompt_content)) as mocked_file:
        with patch("pdd.bug_to_unit_test.preprocess.preprocess", return_value=mock_prompt_content) as mock_preprocess:
            with patch("pdd.bug_to_unit_test.llm_selector.llm_selector") as mock_llm_selector:
                mock_llm = Mock()
                mock_llm.invoke.side_effect = lambda x: mock_unit_test_output
                mock_llm_selector.return_value = (mock_llm, lambda x: len(x), 0.02, 0.03, "gpt-4")

                with patch("pdd.unfinished_prompt.unfinished_prompt", return_value=("Reasoning incomplete", False, 0.005, "gpt-4")) as mock_unfinished:
                    with patch("pdd.continue_generation.continue_generation", return_value=("Completed unit test.", 0.002, "gpt-4")) as mock_continue:
                        with patch("pdd.postprocess.postprocess", return_value=("Completed unit test.", 0.002)) as mock_postprocess:
                            result, total_cost, model_name = bug_to_unit_test(**valid_inputs)
                            
                            assert result == "Completed unit test."
                            expected_cost = (
                                (len(valid_inputs["prompt_used_to_generate_the_code"]) * 0.02 / 1_000_000) +
                                (len(mock_unit_test_output) * 0.03 / 1_000_000) +
                                0.005 + 0.002
                            )
                            assert total_cost == pytest.approx(expected_cost)
                            assert model_name == "gpt-4"

@patch.dict(os.environ, {"PDD_PATH": "/fake/path"})
def test_bug_to_unit_test_postprocess(valid_inputs, mock_prompt_content, mock_unit_test_output):
    with patch("builtins.open", mock_open(read_data=mock_prompt_content)) as mocked_file:
        with patch("pdd.bug_to_unit_test.preprocess.preprocess", return_value=mock_prompt_content) as mock_preprocess:
            with patch("pdd.bug_to_unit_test.llm_selector.llm_selector") as mock_llm_selector:
                mock_llm = Mock()
                mock_llm.invoke.side_effect = lambda x: mock_unit_test_output
                mock_llm_selector.return_value = (mock_llm, lambda x: len(x), 0.02, 0.03, "gpt-4")

                with patch("pdd.unfinished_prompt.unfinished_prompt", return_value=("", True, 0.0, "gpt-4")) as mock_unfinished:
                    with patch("pdd.continue_generation.continue_generation", return_value=("", 0.0, "")) as mock_continue:
                        with patch("pdd.postprocess.postprocess", return_value=(mock_unit_test_output, 0.01)) as mock_postprocess:
                            result, total_cost, model_name = bug_to_unit_test(**valid_inputs)
                            
                            assert result == mock_unit_test_output
                            expected_cost = (
                                (len(valid_inputs["prompt_used_to_generate_the_code"]) * 0.02 / 1_000_000) +
                                (len(mock_unit_test_output) * 0.03 / 1_000_000) +
                                0.01
                            )
                            assert total_cost == pytest.approx(expected_cost)
                            assert model_name == "gpt-4"
