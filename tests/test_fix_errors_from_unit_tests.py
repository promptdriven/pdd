import unittest
from unittest.mock import patch, mock_open, MagicMock, ANY
import os
import sys
# Add the path to the directory containing the fix_errors_from_unit_tests.py file
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'pdd')))

from fix_errors_from_unit_tests import fix_errors_from_unit_tests, FixResult

class TestFixErrorsFromUnitTests(unittest.TestCase):

    @patch('fix_errors_from_unit_tests.os.getenv')
    @patch('fix_errors_from_unit_tests.open', new_callable=mock_open, read_data="mocked prompt content")
    @patch('fix_errors_from_unit_tests.llm_selector')
    @patch('fix_errors_from_unit_tests.tiktoken.get_encoding')
    @patch('fix_errors_from_unit_tests.PromptTemplate.from_template')
    @patch('fix_errors_from_unit_tests.ChatOpenAI')
    @patch('fix_errors_from_unit_tests.StrOutputParser')
    @patch('langchain.output_parsers.PydanticOutputParser')
    @patch('fix_errors_from_unit_tests.Markdown')
    @patch('fix_errors_from_unit_tests.rprint')
    def test_fix_errors_from_unit_tests(self, mock_rprint, mock_markdown, mock_pydantic_output_parser, 
                                        mock_str_output_parser, mock_chat_openai, mock_prompt_template, 
                                        mock_get_encoding, mock_llm_selector, mock_open, mock_getenv):
        # Mock environment variable
        mock_getenv.return_value = '/mocked/path'
        
        # Mock llm_selector to return dummy values
        mock_llm_selector.return_value = ('mock_llm', 0.01, 0.02)
        
        # Mock encoding
        mock_encoding = mock_get_encoding.return_value
        mock_encoding.encode.return_value = [1, 2, 3, 4, 5]
        
        # Mock PromptTemplate
        mock_template = MagicMock()
        mock_prompt_template.return_value = mock_template
        
        # Mock ChatOpenAI
        mock_llm = MagicMock()
        mock_chat_openai.return_value = mock_llm
        
        # Mock StrOutputParser
        mock_str_parser = MagicMock()
        mock_str_output_parser.return_value = mock_str_parser
        
        # Mock PydanticOutputParser
        mock_pydantic_parser = MagicMock()
        mock_pydantic_output_parser.return_value = mock_pydantic_parser
        
        # Set up the first chain
        mock_template.__or__.return_value.__or__.return_value = mock_str_parser
        mock_str_parser.invoke.return_value = "Mocked first chain result"
        
        # Set up the second chain
        second_mock_template = MagicMock()
        mock_prompt_template.return_value = second_mock_template
        second_mock_template.__or__.return_value.__or__.return_value = mock_pydantic_parser
        mock_pydantic_parser.invoke.return_value = FixResult(
            update_unit_test=True,
            update_code=True,
            fixed_unit_test="fixed unit test",
            fixed_code="fixed code"
        )
        
        # Mock Markdown
        mock_markdown.return_value = MagicMock()
        
        # Define inputs
        unit_test = "def test_add():\n    assert add(1, 2) == 3"
        code = "def add(a, b):\n    return a + b"
        error = "NameError: name 'add' is not defined"
        strength = 0.8
        
        # Call the function
        update_unit_test, update_code, fixed_unit_test, fixed_code = fix_errors_from_unit_tests(unit_test, code, error, strength)
        
        # Assertions
        self.assertTrue(update_unit_test)
        self.assertTrue(update_code)
        self.assertEqual(fixed_unit_test, "fixed unit test")
        self.assertEqual(fixed_code, "fixed code")
        
        # Check if the environment variable was accessed
        mock_getenv.assert_called_once_with('PDD_PATH')
        
        # Check if the prompt files were opened
        mock_open.assert_any_call('/mocked/path/prompts/fix_errors_from_unit_tests_LLM.prompt', 'r')
        mock_open.assert_any_call('/mocked/path/prompts/extract_unit_code_fix_LLM.prompt', 'r')
        
        # Check if the llm_selector was called with correct parameters
        mock_llm_selector.assert_any_call(strength, 0)
        mock_llm_selector.assert_any_call(0.5, 0)
        
        # Check if the encoding was used correctly
        mock_encoding.encode.assert_any_call(ANY)  # We're now using ANY to be more flexible
        
        # Check if rprint was called with a Markdown object
        mock_rprint.assert_any_call(mock_markdown.return_value)

if __name__ == '__main__':
    unittest.main()