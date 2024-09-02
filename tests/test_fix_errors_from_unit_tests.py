import pytest
import os
from unittest.mock import patch, mock_open
from pdd.fix_errors_from_unit_tests import fix_errors_from_unit_tests

@pytest.fixture
def mock_environment():
    with patch.dict(os.environ, {'PDD_PATH': '/mock/path'}):
        yield

@pytest.fixture
def mock_file_contents():
    return {
        '/mock/path/prompts/fix_errors_from_unit_tests_LLM.prompt': 'Mock fix errors prompt',
        '/mock/path/prompts/extract_unit_code_fix_LLM.prompt': 'Mock extract fix prompt',
        'error_file.log': 'Existing errors'
    }

@pytest.fixture
def mock_llm_selector():
    with patch('pdd.fix_errors_from_unit_tests.llm_selector') as mock:
        mock.return_value = (
            lambda x: 'LLM output',  # mock LLM
            lambda x: 100,  # mock token counter
            0.01,  # mock input cost
            0.02,  # mock output cost
            'GPT-3.5-turbo'  # mock model name
        )
        yield mock

@pytest.fixture
def mock_preprocess():
    with patch('pdd.fix_errors_from_unit_tests.preprocess') as mock:
        mock.return_value = 'Preprocessed prompt'
        yield mock

def test_fix_errors_from_unit_tests_success(mock_environment, mock_file_contents, mock_llm_selector, mock_preprocess):
    with patch('builtins.open', mock_open(read_data='Mock file content')) as mock_file:
        def side_effect(filename, mode):
            if filename in mock_file_contents:
                return mock_open(read_data=mock_file_contents[filename])(filename, mode)
            return mock_open()(filename, mode)
        
        mock_file.side_effect = side_effect

        with patch('pdd.fix_errors_from_unit_tests.JsonOutputParser') as mock_parser:
            mock_parser.return_value.parse.return_value = {
                'update_unit_test': True,
                'update_code': True,
                'fixed_unit_test': 'Fixed unit test',
                'fixed_code': 'Fixed code'
            }

            result = fix_errors_from_unit_tests(
                unit_test='def test_example(): assert True',
                code='def example(): return True',
                prompt='Write a function that returns True',
                error='AssertionError',
                error_file='error_file.log',
                strength=0.7,
                temperature=0.5
            )

            assert result[0] == True  # update_unit_test
            assert result[1] == True  # update_code
            assert result[2] == 'Fixed unit test'
            assert result[3] == 'Fixed code'
            assert isinstance(result[4], float)  # total_cost
            assert result[5] == 'GPT-3.5-turbo'  # model_name

def test_fix_errors_from_unit_tests_file_not_found(mock_environment, mock_llm_selector, mock_preprocess):
    with patch('builtins.open', side_effect=FileNotFoundError):
        result = fix_errors_from_unit_tests(
            unit_test='def test_example(): assert True',
            code='def example(): return True',
            prompt='Write a function that returns True',
            error='AssertionError',
            error_file='non_existent_file.log',
            strength=0.7,
            temperature=0.5
        )

        assert result == (False, False, '', '', 0.0, '')

def test_fix_errors_from_unit_tests_missing_env_var():
    with patch.dict(os.environ, clear=True):
        result = fix_errors_from_unit_tests(
            unit_test='def test_example(): assert True',
            code='def example(): return True',
            prompt='Write a function that returns True',
            error='AssertionError',
            error_file='error_file.log',
            strength=0.7,
            temperature=0.5
        )

        assert result == (False, False, '', '', 0.0, '')

def test_fix_errors_from_unit_tests_io_error(mock_environment, mock_file_contents, mock_llm_selector, mock_preprocess):
    with patch('builtins.open', side_effect=IOError):
        result = fix_errors_from_unit_tests(
            unit_test='def test_example(): assert True',
            code='def example(): return True',
            prompt='Write a function that returns True',
            error='AssertionError',
            error_file='error_file.log',
            strength=0.7,
            temperature=0.5
        )

        assert result == (False, False, '', '', 0.0, '')