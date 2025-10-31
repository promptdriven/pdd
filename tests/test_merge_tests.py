import sys
import os
import pytest
from unittest.mock import patch, MagicMock

# Add the project root to the Python path to allow importing 'pdd'
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from pdd.merge_tests import merge_with_existing_test
from pdd import EXTRACTION_STRENGTH, DEFAULT_TIME

class TestMergeWithExistingTest:
    # Define a set of valid inputs to be reused across tests
    @pytest.fixture
    def valid_inputs(self):
        return {
            "existing_test": "def test_one(): assert 1 == 1",
            "new_test_case": "def test_two(): assert 2 == 2",
            "language": "python",
            "strength": 0.5,
            "temperature": 0.1,
            "time_budget": DEFAULT_TIME,
            "verbose": False
        }

    @patch('pdd.merge_tests.load_prompt_template')
    @patch('pdd.merge_tests.preprocess')
    @patch('pdd.merge_tests.llm_invoke')
    @patch('pdd.merge_tests.postprocess')
    def test_successful_merge(self, mock_postprocess, mock_llm_invoke, mock_preprocess, mock_load_prompt, valid_inputs):
        """
        Test the successful execution path of merge_with_existing_test.
        """
        # --- Arrange ---
        mock_load_prompt.return_value = "merge_template"
        mock_preprocess.return_value = "processed_merge_template"
        mock_llm_invoke.return_value = {
            'result': 'raw_merged_code',
            'cost': 0.01,
            'model_name': 'test-merge-model'
        }
        mock_postprocess.return_value = ('final_merged_code', 0.005, 'postprocess-model')

        # --- Act ---
        result, cost, model_name = merge_with_existing_test(**valid_inputs)

        # --- Assert ---
        assert result == 'final_merged_code'
        assert cost == 0.01 + 0.005  # Total cost should be sum of llm_invoke and postprocess
        assert model_name == 'test-merge-model' # The original model name should be returned

        mock_load_prompt.assert_called_once_with("merge_tests")
        mock_preprocess.assert_called_once_with("merge_template", recursive=False, double_curly_brackets=False)
        
        expected_input_json = {
            "existing_test_file": valid_inputs["existing_test"],
            "new_test_case": valid_inputs["new_test_case"],
            "language": valid_inputs["language"]
        }
        mock_llm_invoke.assert_called_once_with(
            prompt="processed_merge_template",
            input_json=expected_input_json,
            strength=valid_inputs["strength"],
            temperature=valid_inputs["temperature"],
            time=valid_inputs["time_budget"],
            verbose=valid_inputs["verbose"]
        )
        mock_postprocess.assert_called_once_with(
            'raw_merged_code',
            language=valid_inputs["language"],
            strength=EXTRACTION_STRENGTH,
            temperature=valid_inputs["temperature"],
            time=valid_inputs["time_budget"],
            verbose=valid_inputs["verbose"]
        )

    def test_input_validation_empty_strings(self, valid_inputs):
        """
        Test that the function raises ValueError for empty string inputs.
        """
        for key in ["existing_test", "new_test_case", "language"]:
            with pytest.raises(ValueError, match="must be non-empty strings"):
                invalid_inputs = valid_inputs.copy()
                invalid_inputs[key] = ""
                merge_with_existing_test(**invalid_inputs)

    def test_input_validation_strength(self, valid_inputs):
        """
        Test that the function raises ValueError for out-of-range strength values.
        """
        with pytest.raises(ValueError, match="Strength must be between 0.0 and 1.0."):
            invalid_inputs = valid_inputs.copy()
            invalid_inputs["strength"] = -0.1
            merge_with_existing_test(**invalid_inputs)
        
        with pytest.raises(ValueError, match="Strength must be between 0.0 and 1.0."):
            invalid_inputs = valid_inputs.copy()
            invalid_inputs["strength"] = 1.1
            merge_with_existing_test(**invalid_inputs)

    def test_input_validation_temperature(self, valid_inputs):
        """
        Test that the function raises ValueError for out-of-range temperature values.
        """
        with pytest.raises(ValueError, match="Temperature must be between 0.0 and 2.0."):
            invalid_inputs = valid_inputs.copy()
            invalid_inputs["temperature"] = -0.1
            merge_with_existing_test(**invalid_inputs)

        with pytest.raises(ValueError, match="Temperature must be between 0.0 and 2.0."):
            invalid_inputs = valid_inputs.copy()
            invalid_inputs["temperature"] = 2.1
            merge_with_existing_test(**invalid_inputs)

    @patch('pdd.merge_tests.load_prompt_template', return_value=None)
    def test_template_load_failure(self, mock_load_prompt, valid_inputs):
        """
        Test that a ValueError is raised if the prompt template fails to load.
        """
        with pytest.raises(ValueError, match="Failed to load 'merge_tests' prompt template."):
            merge_with_existing_test(**valid_inputs)

    @patch('pdd.merge_tests.load_prompt_template', return_value="template")
    @patch('pdd.merge_tests.preprocess', return_value="processed")
    @patch('pdd.merge_tests.llm_invoke', return_value={'result': ' ', 'cost': 0, 'model_name': 'm'})
    def test_llm_empty_result_failure(self, mock_llm, mock_preprocess, mock_load, valid_inputs):
        """
        Test that a ValueError is raised if the LLM returns an empty or whitespace-only result.
        """
        with pytest.raises(ValueError, match="LLM returned an empty result during merge operation."):
            merge_with_existing_test(**valid_inputs)