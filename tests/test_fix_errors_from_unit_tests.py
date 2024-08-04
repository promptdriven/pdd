import unittest
from unittest.mock import patch, mock_open, MagicMock
import os
import sys

# Add the path to the directory containing the fix_errors_from_unit_tests.py file
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'pdd')))
from fix_errors_from_unit_tests import fix_errors_from_unit_tests, FixResult

class TestFixErrorsFromUnitTests(unittest.TestCase):

    @patch('builtins.open', new_callable=mock_open, read_data='mocked prompt content')
    @patch('os.getenv')
    @patch('fix_errors_from_unit_tests.llm_selector')
    @patch('fix_errors_from_unit_tests.tiktoken.get_encoding')
    @patch('fix_errors_from_unit_tests.PromptTemplate')
    @patch('fix_errors_from_unit_tests.StrOutputParser')
    @patch('fix_errors_from_unit_tests.PydanticOutputParser')
    @patch('fix_errors_from_unit_tests.set_llm_cache')
    def test_fix_errors_from_unit_tests(self, mock_set_llm_cache, mock_pydantic_output_parser,
                                        mock_str_output_parser, mock_prompt_template,
                                        mock_get_encoding, mock_llm_selector, mock_getenv, mock_open):
        # Mocking the necessary components
        mock_llm_selector.return_value = (MagicMock(), 0.01, 0.02)
        mock_get_encoding.return_value.encode.return_value = [1, 2, 3, 4, 5]
        
        # Create mock chain
        mock_chain = MagicMock()
        mock_chain.invoke.return_value = """
        Update unit test: True
        Update code: True
        
        def test_example():
            assert example() == 2
        
        def example():
            return 2
        """
        
        # Make PromptTemplate.from_template return a MagicMock that can be chained
        mock_template = MagicMock()
        mock_template.__or__.return_value.__or__.return_value = mock_chain
        mock_prompt_template.from_template.return_value = mock_template
        
        # Make StrOutputParser return a MagicMock that can be chained
        mock_str_parser = MagicMock()
        mock_str_parser.__or__.return_value = mock_chain
        mock_str_output_parser.return_value = mock_str_parser

        # Define test inputs
        unit_test = 'def test_example(): assert 1 == 1'
        code = 'def example(): return 1'
        error = 'AssertionError'
        strength = 0.5

        # Call the function under test
        update_unit_test, update_code, fixed_unit_test, fixed_code = fix_errors_from_unit_tests(unit_test, code, error, strength)

        # Assertions to ensure the function behaves as expected
        self.assertTrue(update_unit_test)
        self.assertTrue(update_code)
        self.assertEqual(fixed_unit_test, 'def test_example():\n    assert example() == 2')
        self.assertEqual(fixed_code, 'def example():\n    return 2')

        # Ensure the mocks were called as expected
        mock_open.assert_called()
        mock_getenv.assert_called_with('PDD_PATH', '.')  # Updated assertion
        mock_llm_selector.assert_called()
        mock_get_encoding.assert_called_with("cl100k_base")
        mock_prompt_template.from_template.assert_called()
        mock_chain.invoke.assert_called()

if __name__ == '__main__':
    unittest.main()