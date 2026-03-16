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
from pdd.insert_includes import insert_includes, InsertIncludesOutput

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


# =============================================================================
# NEW TESTS: Prompt-spec coverage for insert_includes requirements
# =============================================================================


# ---------------------------------------------------------------------------
# Req 1: Load and preprocess insert_includes_LLM.prompt
# ---------------------------------------------------------------------------

class TestReq1LoadAndPreprocess:
    """Requirement 1: Load insert_includes_LLM.prompt and preprocess it."""

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include", return_value=("<update><include>f.py</include></update>", "csv", 0.0, "m"))
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="raw template")
    def test_loads_correct_template(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        csv_path = tmp_path / "deps.csv"
        insert_includes("prompt", "dir", str(csv_path))
        mock_lpt.assert_called_once_with("insert_includes_LLM")

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include", return_value=("<update><include>f.py</include></update>", "csv", 0.0, "m"))
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="raw template")
    def test_preprocesses_with_correct_args(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        csv_path = tmp_path / "deps.csv"
        insert_includes("prompt", "dir", str(csv_path))
        mock_pp.assert_called_once_with(
            "raw template",
            recursive=False,
            double_curly_brackets=True,
            exclude_keys=["actual_prompt_to_update", "actual_dependencies_to_insert"],
        )


# ---------------------------------------------------------------------------
# Req 2: Read CSV file / create if missing (with correct header)
# ---------------------------------------------------------------------------

class TestReq2CsvHandling:
    """Requirement 2: Read CSV, create with header if it doesn't exist."""

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include", return_value=("", "csv_out", 0.0, "m"))
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_creates_csv_with_correct_header(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        csv_path = tmp_path / "nonexistent.csv"
        assert not csv_path.exists()
        insert_includes("prompt", "dir", str(csv_path))
        assert csv_path.exists()
        content = csv_path.read_text()
        assert content.startswith("full_path,file_summary,key_exports,dependencies,content_hash")

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include", return_value=("", "csv_out", 0.0, "m"))
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_reads_existing_csv_and_passes_to_auto_include(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        csv_path = tmp_path / "deps.csv"
        csv_path.write_text("full_path,file_summary,key_exports,dependencies,content_hash\nfile.py,summary,exports,deps,hash\n")
        insert_includes("prompt", "dir", str(csv_path))
        call_kwargs = mock_ai.call_args[1]
        assert "file.py" in call_kwargs["csv_file"]


# ---------------------------------------------------------------------------
# Req 3: Call auto_include correctly
# ---------------------------------------------------------------------------

class TestReq3AutoInclude:
    """Requirement 3: Call auto_include and get (include_directives, csv_output, total_cost, model_name)."""

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include")
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_auto_include_called_with_all_params(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        mock_ai.return_value = ("", "csv_out", 0.0, "model")
        csv_path = tmp_path / "deps.csv"

        def callback(c, t): pass

        insert_includes(
            input_prompt="my prompt",
            directory_path="context/*.py",
            csv_filename=str(csv_path),
            prompt_filename="prompts/test.prompt",
            strength=0.8,
            temperature=0.1,
            time=0.5,
            verbose=True,
            progress_callback=callback,
        )

        kwargs = mock_ai.call_args[1]
        assert kwargs["input_prompt"] == "my prompt"
        assert kwargs["directory_path"] == "context/*.py"
        assert kwargs["prompt_filename"] == "prompts/test.prompt"
        assert kwargs["strength"] == 0.8
        assert kwargs["temperature"] == 0.1
        assert kwargs["time"] == 0.5
        assert kwargs["verbose"] is True
        assert kwargs["progress_callback"] is callback

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include")
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_csv_output_returned_from_auto_include(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        expected_csv = "full_path,file_summary,key_exports,dependencies,content_hash\nf.py,s,e,d,h\n"
        mock_ai.return_value = ("", expected_csv, 0.0, "model")
        csv_path = tmp_path / "deps.csv"

        _, csv_output, _, _ = insert_includes("prompt", "dir", str(csv_path))
        assert csv_output == expected_csv


# ---------------------------------------------------------------------------
# Req 4: Apply <update> blocks deterministically
# ---------------------------------------------------------------------------

class TestReq4UpdateBlocks:
    """Requirement 4: <update> blocks replace existing <include> tags by file path, no LLM."""

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include")
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_update_replaces_existing_include(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        input_prompt = "Start\n<include>utils.py</include>\nEnd"
        update_directive = "<update><include select='def:helper'>utils.py</include></update>"
        mock_ai.return_value = (update_directive, "csv", 0.02, "auto-model")
        csv_path = tmp_path / "deps.csv"

        output_prompt, _, _, _ = insert_includes(input_prompt, "dir", str(csv_path))

        assert "<include select='def:helper'>utils.py</include>" in output_prompt
        assert "Start" in output_prompt
        assert "End" in output_prompt

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include")
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_update_replaces_include_with_existing_attributes(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        """Existing <include> tags with attributes should still be matched by file path."""
        input_prompt = "Before\n<include select='old'>utils.py</include>\nAfter"
        update_directive = "<update><include select='new_selector'>utils.py</include></update>"
        mock_ai.return_value = (update_directive, "csv", 0.01, "model")
        csv_path = tmp_path / "deps.csv"

        output_prompt, _, _, _ = insert_includes(input_prompt, "dir", str(csv_path))

        assert "select='new_selector'" in output_prompt
        assert "select='old'" not in output_prompt

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include")
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_multiple_update_blocks(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        input_prompt = "<include>a.py</include>\n<include>b.py</include>"
        directives = (
            "<update><include select='x'>a.py</include></update>\n"
            "<update><include select='y'>b.py</include></update>"
        )
        mock_ai.return_value = (directives, "csv", 0.01, "model")
        csv_path = tmp_path / "deps.csv"

        output_prompt, _, _, _ = insert_includes(input_prompt, "dir", str(csv_path))

        assert "select='x'" in output_prompt
        assert "select='y'" in output_prompt

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include")
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_multiline_update_block_uses_only_include_tag(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        """Multi-line update blocks should only inject the <include> tag, not extra content."""
        input_prompt = "Before\n<include>utils.py</include>\nAfter"
        # A multi-line update block with a comment before the include
        update_directive = "<update><!-- selector added -->\n<include select='def:helper'>utils.py</include></update>"
        mock_ai.return_value = (update_directive, "csv", 0.01, "model")
        csv_path = tmp_path / "deps.csv"

        output_prompt, _, _, _ = insert_includes(input_prompt, "dir", str(csv_path))

        # The include tag should be updated
        assert "<include select='def:helper'>utils.py</include>" in output_prompt
        # The extra comment line should NOT be injected into the prompt
        assert "<!-- selector added -->" not in output_prompt


# ---------------------------------------------------------------------------
# Req 5: If <new> blocks remain, invoke LLM
# ---------------------------------------------------------------------------

class TestReq5NewBlocksLLM:
    """Requirement 5: <new> blocks trigger LLM call with insert_includes_LLM."""

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include")
    @patch("pdd.insert_includes.preprocess", return_value="processed template")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_new_blocks_trigger_llm(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        directives = "<new><include>new_dep.py</include></new>"
        mock_ai.return_value = (directives, "csv", 0.02, "auto-model")
        mock_llm.return_value = {
            "cost": 0.01,
            "model_name": "mock-model",
            "result": InsertIncludesOutput(output_prompt="LLM placed new includes"),
        }
        csv_path = tmp_path / "deps.csv"

        output_prompt, _, total_cost, model_name = insert_includes("prompt", "dir", str(csv_path))

        mock_llm.assert_called_once()
        assert model_name == "mock-model"
        assert abs(total_cost - 0.03) < 1e-9  # 0.02 + 0.01

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include")
    @patch("pdd.insert_includes.preprocess", return_value="processed template")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_llm_receives_correct_input_json(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        input_prompt = "original prompt\n<include>existing.py</include>"
        directives = (
            "<update><include select='fn'>existing.py</include></update>\n"
            "<new><include>brand_new.py</include></new>"
        )
        mock_ai.return_value = (directives, "csv", 0.02, "model")
        mock_llm.return_value = {
            "cost": 0.01,
            "model_name": "m",
            "result": InsertIncludesOutput(output_prompt="done"),
        }
        csv_path = tmp_path / "deps.csv"

        insert_includes(input_prompt, "dir", str(csv_path))

        call_kwargs = mock_llm.call_args[1]
        input_json = call_kwargs["input_json"]
        # actual_prompt_to_update should have updates already applied
        assert "select='fn'" in input_json["actual_prompt_to_update"]
        # actual_dependencies_to_insert should contain only <new> blocks
        assert "<new>" in input_json["actual_dependencies_to_insert"]
        assert "<update>" not in input_json["actual_dependencies_to_insert"]

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include")
    @patch("pdd.insert_includes.preprocess", return_value="processed template")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_llm_passes_through_parameters(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        directives = "<new><include>dep.py</include></new>"
        mock_ai.return_value = (directives, "csv", 0.0, "model")
        mock_llm.return_value = {
            "cost": 0.01,
            "model_name": "m",
            "result": InsertIncludesOutput(output_prompt="done"),
        }
        csv_path = tmp_path / "deps.csv"

        insert_includes("prompt", "dir", str(csv_path), strength=0.9, temperature=0.3, time=0.7, verbose=True)

        call_kwargs = mock_llm.call_args[1]
        assert call_kwargs["strength"] == 0.9
        assert call_kwargs["temperature"] == 0.3
        assert call_kwargs["time"] == 0.7
        assert call_kwargs["verbose"] is True


# ---------------------------------------------------------------------------
# Req 6: No <new> blocks → skip LLM
# ---------------------------------------------------------------------------

class TestReq6SkipLLM:
    """Requirement 6: If no <new> blocks exist, skip LLM and use updated prompt."""

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include")
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_update_only_skips_llm(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        input_prompt = "prompt\n<include>file.py</include>"
        update_directive = "<update><include select='fn'>file.py</include></update>"
        mock_ai.return_value = (update_directive, "csv", 0.05, "auto-model")
        csv_path = tmp_path / "deps.csv"

        output_prompt, csv_output, total_cost, model_name = insert_includes(
            input_prompt, "dir", str(csv_path)
        )

        mock_llm.assert_not_called()
        assert total_cost == 0.05
        assert model_name == "auto-model"
        assert "select='fn'" in output_prompt

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include")
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_empty_directives_skips_llm(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        """When auto_include returns empty directives, no LLM call needed."""
        mock_ai.return_value = ("", "csv", 0.01, "auto-model")
        csv_path = tmp_path / "deps.csv"

        output_prompt, _, total_cost, model_name = insert_includes("my prompt", "dir", str(csv_path))

        mock_llm.assert_not_called()
        assert output_prompt == "my prompt"
        assert total_cost == 0.01
        assert model_name == "auto-model"


# ---------------------------------------------------------------------------
# Req 7: Return tuple shape
# ---------------------------------------------------------------------------

class TestReq7ReturnTuple:
    """Requirement 7: Return (output_prompt, csv_output, total_cost, model_name)."""

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include")
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_return_types(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        mock_ai.return_value = ("<new><include>f.py</include></new>", "csv_data", 0.05, "model-x")
        mock_llm.return_value = {
            "cost": 0.01,
            "model_name": "mock-model",
            "result": InsertIncludesOutput(output_prompt="done"),
        }
        csv_path = tmp_path / "deps.csv"

        result = insert_includes("prompt", "dir", str(csv_path))

        assert isinstance(result, tuple)
        assert len(result) == 4
        output_prompt, csv_output, total_cost, model_name = result
        assert isinstance(output_prompt, str)
        assert isinstance(csv_output, str)
        assert isinstance(total_cost, float)
        assert isinstance(model_name, str)

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include")
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_cost_is_sum_of_auto_include_and_llm(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        mock_ai.return_value = ("<new><include>f.py</include></new>", "csv", 0.05, "m")
        mock_llm.return_value = {
            "cost": 0.03,
            "model_name": "llm-model",
            "result": InsertIncludesOutput(output_prompt="done"),
        }
        csv_path = tmp_path / "deps.csv"

        _, _, total_cost, _ = insert_includes("prompt", "dir", str(csv_path))
        assert abs(total_cost - 0.08) < 1e-9


# ---------------------------------------------------------------------------
# Edge cases
# ---------------------------------------------------------------------------

class TestEdgeCases:
    """Edge cases and robustness tests."""

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include")
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_update_block_with_no_matching_include_is_noop(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        """An <update> block referencing a file not in the prompt should not crash."""
        input_prompt = "prompt without includes"
        update_directive = "<update><include select='fn'>nonexistent.py</include></update>"
        mock_ai.return_value = (update_directive, "csv", 0.01, "model")
        csv_path = tmp_path / "deps.csv"

        output_prompt, _, _, _ = insert_includes(input_prompt, "dir", str(csv_path))
        assert output_prompt == "prompt without includes"
        mock_llm.assert_not_called()

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include")
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_mixed_update_and_new_blocks(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        """Both <update> and <new> blocks: updates applied first, then LLM places new ones."""
        input_prompt = "prompt\n<include>existing.py</include>"
        directives = (
            "<update><include select='fn'>existing.py</include></update>\n"
            "<new><include>brand_new.py</include></new>"
        )
        mock_ai.return_value = (directives, "csv", 0.02, "model")
        mock_llm.return_value = {
            "cost": 0.01,
            "model_name": "mock-model",
            "result": InsertIncludesOutput(output_prompt="final prompt"),
        }
        csv_path = tmp_path / "deps.csv"

        output_prompt, _, total_cost, model_name = insert_includes(input_prompt, "dir", str(csv_path))

        mock_llm.assert_called_once()
        assert abs(total_cost - 0.03) < 1e-9

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include", return_value=("", "csv", 0.0, "m"))
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_default_parameters(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        """Default values for optional parameters should work."""
        csv_path = tmp_path / "deps.csv"
        insert_includes("prompt", "dir", str(csv_path))

        kwargs = mock_ai.call_args[1]
        assert kwargs["prompt_filename"] is None
        assert kwargs["progress_callback"] is None

    @patch("pdd.insert_includes.llm_invoke")
    @patch("pdd.insert_includes.auto_include")
    @patch("pdd.insert_includes.preprocess", return_value="processed")
    @patch("pdd.insert_includes.load_prompt_template", return_value="template")
    def test_raw_dependencies_without_tags_triggers_llm(self, mock_lpt, mock_pp, mock_ai, mock_llm, tmp_path):
        """If auto_include returns raw text (no <new>/<update> tags), treat as new and call LLM."""
        mock_ai.return_value = ("some raw dependency text", "csv", 0.01, "model")
        mock_llm.return_value = {
            "cost": 0.01,
            "model_name": "mock-model",
            "result": InsertIncludesOutput(output_prompt="done"),
        }
        csv_path = tmp_path / "deps.csv"

        insert_includes("prompt", "dir", str(csv_path))

        mock_llm.assert_called_once()
