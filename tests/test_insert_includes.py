# test_insert_includes.py
# Place this file in the "tests" directory alongside your "pdd" package.
#
# This set of pytest unit tests covers a range of scenarios to validate the
# behavior of the insert_includes function. It uses Python's unittest.mock
# to patch dependencies such as load_prompt_template, auto_include, and
# llm_invoke, ensuring that no actual network/file calls are made and that
# behavior can be tested in isolation.

import pytest
from unittest.mock import patch, mock_open, MagicMock

# Import the function under test from pdd.insert_includes (same name as file)
from pdd.insert_includes import insert_includes

@pytest.fixture
def mock_llm_response():
    """
    Returns a minimal, valid LLM response with included cost, model_name, and result.
    """
    return {
        'cost': 0.01,
        'model_name': 'mock-model',
        'result': type('MockResult', (), {'output_prompt': 'Updated Prompt with Dependencies'}),
    }

@pytest.fixture
def mock_auto_include_response():
    """
    Returns a typical response from auto_include used in standard operation.
    """
    return (
        "Some dependencies text",
        "full_path,file_summary,date\npath/to/something.py,example summary,2023-01-01\n",
        0.02,
        "auto-include-model"
    )

@pytest.mark.parametrize("verbose_flag", [True, False])
@patch("pdd.insert_includes.load_prompt_template")
@patch("pdd.insert_includes.preprocess")
@patch("pdd.insert_includes.auto_include")
@patch("pdd.insert_includes.llm_invoke")
def test_insert_includes_success(
    mock_llm_invoke,
    mock_auto_include,
    mock_preprocess,
    mock_load_prompt_template,
    verbose_flag,
    mock_llm_response,
    mock_auto_include_response
):
    """
    Tests successful scenario where:
      1) insert_includes_LLM.prompt is available
      2) CSV file is found
      3) auto_include returns valid dependency info
      4) llm_invoke returns a valid structured response
    Checks return values correctness.
    """
    # Setup mocks
    mock_load_prompt_template.return_value = "prompt template content"
    mock_preprocess.return_value = "processed insert_includes_LLM prompt"
    mock_auto_include.return_value = mock_auto_include_response
    mock_llm_invoke.return_value = mock_llm_response

    # Provide a dummy CSV file content
    m_open = mock_open(read_data="full_path,file_summary,date\n")
    with patch("builtins.open", m_open):
        output_prompt, csv_output, total_cost, model_name = insert_includes(
            input_prompt="Some input prompt",
            directory_path="./test_dir",
            csv_filename="output/dependencies.csv",
            strength=0.7,
            temperature=0.5,
            verbose=verbose_flag
        )

    # Assertions
    assert output_prompt == "Updated Prompt with Dependencies"
    assert "path/to/something.py" in csv_output
    # total_cost is sum of auto_include cost (0.02) and llm_invoke cost (0.01)
    assert abs(total_cost - 0.03) < 1e-9
    assert model_name == "mock-model"


@patch("pdd.insert_includes.load_prompt_template", return_value=None)
def test_insert_includes_missing_prompt_template(mock_load_prompt_template):
    """
    Tests that a ValueError is raised when the insert_includes_LLM.prompt
    template cannot be loaded.
    """
    with pytest.raises(ValueError, match="Failed to load insert_includes_LLM.prompt template"):
        insert_includes(
            input_prompt="Some input prompt",
            directory_path="./test_dir",
            csv_filename="output/dependencies.csv",
            strength=0.7,
            temperature=0.5,
            verbose=False
        )


@patch("pdd.insert_includes.load_prompt_template", return_value="template content")
@patch("pdd.insert_includes.preprocess", return_value="processed template")
@patch("pdd.insert_includes.auto_include")
@patch("pdd.insert_includes.llm_invoke")
def test_insert_includes_missing_csv_file(
    mock_llm_invoke,
    mock_auto_include,
    mock_preprocess,
    mock_load_prompt_template,
    mock_llm_response,
    mock_auto_include_response,
    tmp_path
):
    """
    Tests behavior when the CSV file is missing. 
    The code should create a new CSV file and not raise an error.
    """
    # Arrange
    mock_auto_include.return_value = mock_auto_include_response
    mock_llm_invoke.return_value = mock_llm_response

    # We give a CSV filename that doesn't exist in the tmp_path
    csv_path = tmp_path / "non_existent.csv"

    # Act
    output_prompt, csv_output, total_cost, model_name = insert_includes(
        input_prompt="Some input prompt",
        directory_path="./test_dir",
        csv_filename=str(csv_path),
        strength=0.7,
        temperature=0.5,
        verbose=True
    )

    # Assert
    assert output_prompt == "Updated Prompt with Dependencies"
    assert "full_path,file_summary,date" in csv_output
    assert total_cost > 0
    assert model_name == "mock-model"
    # Confirm file was created
    assert csv_path.exists(), "CSV file was not created even though it was missing."


@patch("pdd.insert_includes.load_prompt_template", return_value="template content")
@patch("pdd.insert_includes.preprocess", return_value="processed template")
@patch("pdd.insert_includes.auto_include")
@patch("pdd.insert_includes.llm_invoke", return_value=None)
def test_insert_includes_invalid_llm_response(
    mock_llm_invoke,
    mock_auto_include,
    mock_preprocess,
    mock_load_prompt_template
):
    """
    Tests that a ValueError is raised when llm_invoke does not return a valid
    response dict or 'result' key is missing.
    """
    # auto_include mock, does not matter for this test
    mock_auto_include.return_value = ("deps", "csv\n", 0.0, "auto-include-model")

    m_open = mock_open(read_data="full_path,file_summary,date\n")
    with patch("builtins.open", m_open):
        with pytest.raises(ValueError, match="Failed to get valid response from LLM model"):
            insert_includes(
                input_prompt="Some input prompt",
                directory_path="./test_dir",
                csv_filename="output/dependencies.csv",
                strength=0.7,
                temperature=0.5,
                verbose=False
            )


@patch("pdd.insert_includes.load_prompt_template", return_value="template content")
@patch("pdd.insert_includes.preprocess", return_value="processed template")
@patch("pdd.insert_includes.auto_include", side_effect=Exception("auto_include error"))
def test_insert_includes_auto_include_exception(
    mock_auto_include,
    mock_preprocess,
    mock_load_prompt_template
):
    """
    Tests that an exception in auto_include is properly captured and re-raised.
    """
    m_open = mock_open(read_data="full_path,file_summary,date\n")
    with patch("builtins.open", m_open):
        with pytest.raises(Exception, match="auto_include error"):
            insert_includes(
                input_prompt="Some input prompt",
                directory_path="./test_dir",
                csv_filename="output/dependencies.csv",
                strength=0.7,
                temperature=0.5,
                verbose=False
            )