import pytest
from unittest.mock import patch, mock_open
from pdd.fix_errors_from_unit_tests import fix_errors_from_unit_tests

@pytest.fixture
def mock_environment():
    with patch.dict('os.environ', {'PDD_PATH': '/mock/path'}):
        yield

@pytest.fixture
def mock_file_contents():
    return {
        '/mock/path/prompts/fix_errors_from_unit_tests_LLM.prompt': 'Mock fix errors prompt',
        '/mock/path/prompts/extract_unit_code_fix_LLM.prompt': 'Mock extract fix prompt',
        'error_file.log': 'Existing error log content'
    }

@pytest.fixture
def mock_llm_selector():
    with patch('pdd.fix_errors_from_unit_tests.llm_selector') as mock:
        mock.return_value = (
            lambda x: 'LLM response',  # Mock LLM
            lambda x: 100,  # Mock token counter
            0.01,  # Mock input cost
            0.02   # Mock output cost
        )
        yield mock

@pytest.fixture
def mock_file_open(mock_file_contents):
    def mock_open_file(filename, mode='r'):
        content = mock_file_contents.get(filename, '')
        return mock_open(read_data=content)(filename, mode)
    return mock_open_file

def test_fix_errors_from_unit_tests_success(mock_environment, mock_file_contents, mock_llm_selector, mock_file_open):
    with patch('builtins.open', mock_file_open):
        with patch('pdd.fix_errors_from_unit_tests.PromptTemplate.from_template') as mock_prompt:
            mock_prompt.return_value.format.return_value = 'Formatted prompt'
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

def test_fix_errors_from_unit_tests_file_error(mock_environment, mock_file_contents, mock_llm_selector):
    with patch('builtins.open', side_effect=IOError("Mock IO Error")):
        result = fix_errors_from_unit_tests(
            unit_test='def test_example(): assert True',
            code='def example(): return True',
            error='AssertionError',
            error_file='error_file.log',
            strength=0.7,
            temperature=0.5
        )
        
        assert result == (False, False, '', '', 0.0)

def test_fix_errors_from_unit_tests_missing_env_var():
    with patch.dict('os.environ', clear=True):
        result = fix_errors_from_unit_tests(
            unit_test='def test_example(): assert True',
            code='def example(): return True',
            error='AssertionError',
            error_file='error_file.log',
            strength=0.7,
            temperature=0.5
        )
        
        assert result == (False, False, '', '', 0.0)