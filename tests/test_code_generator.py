import unittest
from unittest.mock import patch, MagicMock
import sys
import os

# Add the path to the directory containing the code_generator.py file
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'pdd')))

from code_generator import code_generator

class TestCodeGenerator(unittest.TestCase):

    @patch('code_generator.preprocess')
    @patch('code_generator.llm_selector')
    @patch('code_generator.PromptTemplate')
    @patch('code_generator.postprocess')
    @patch('code_generator.tiktoken.get_encoding')
    @patch('code_generator.print')
    def test_code_generator(self, mock_print, mock_get_encoding, mock_postprocess, mock_prompt_template, mock_llm_selector, mock_preprocess):
        # Mock the necessary functions and objects
        mock_preprocess.return_value = "Processed prompt"
        mock_llm = MagicMock()
        mock_llm_selector.return_value = (mock_llm, 0.01, 0.02)
        mock_chain = MagicMock()
        mock_chain.invoke.return_value = "Model output"
        mock_prompt_template.from_template.return_value.__or__.return_value.__or__.return_value = mock_chain
        mock_postprocess.return_value = "Runnable code"
        mock_get_encoding.return_value.encode.return_value = [1] * 100  # Simulate 100 tokens

        # Test the code_generator function
        result = code_generator("test_prompt.txt", "python", 0.8)

        # Assertions
        self.assertEqual(result, "Runnable code")
        mock_preprocess.assert_called_once_with("test_prompt.txt")
        mock_llm_selector.assert_called_once_with(0.8, 0)
        mock_prompt_template.from_template.assert_called_once_with("Processed prompt")
        mock_postprocess.assert_called_once_with("Model output", "python")

        # Check if the print function was called with the expected arguments
        mock_print.assert_any_call("[bold green]Running the model...[/bold green]")
        mock_print.assert_any_call("Token count in prompt: 100")
        mock_print.assert_any_call("Estimated cost: $0.000001")

    @patch('code_generator.preprocess')
    @patch('code_generator.print')
    def test_code_generator_file_not_found(self, mock_print, mock_preprocess):
        # Simulate a FileNotFoundError in preprocess
        mock_preprocess.side_effect = FileNotFoundError("File not found")

        # Test the code_generator function with a non-existent file
        result = code_generator("non_existent_file.txt", "python", 0.8)

        # Assertions
        self.assertEqual(result, "")
        mock_preprocess.assert_called_once_with("non_existent_file.txt")
        mock_print.assert_called_with("[bold red]Error:[/bold red] File not found")

if __name__ == '__main__':
    unittest.main()