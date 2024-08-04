import unittest
import os
from pathlib import Path
from unittest.mock import patch, mock_open
from staging.pdd.test_generator import test_generator

class TestTestGenerator(unittest.TestCase):

    @patch('staging.pdd.test_generator.llm_selector')
    @patch('staging.pdd.test_generator.PromptTemplate')
    @patch('staging.pdd.test_generator.StrOutputParser')
    @patch('staging.pdd.test_generator.tiktoken')
    @patch('staging.pdd.test_generator.postprocess')
    def test_test_generator(self, mock_postprocess, mock_tiktoken, mock_str_output_parser, mock_prompt_template, mock_llm_selector):
        # Mock environment variable
        with patch.dict(os.environ, {'PDD_PATH': '/fake/path'}):
            # Mock file reads
            mock_prompt_content = "Test prompt content"
            mock_code_content = "Test code content"
            
            def mock_file_read(filename, *args, **kwargs):
                if filename == "test_prompt.txt":
                    return mock_open(read_data=mock_prompt_content)()
                else:
                    return mock_open(read_data=mock_code_content)()
            
            with patch('builtins.open', side_effect=mock_file_read):
                # Mock LLM selector
                mock_llm = unittest.mock.MagicMock()
                mock_llm_selector.return_value = (mock_llm, 0.01, 0.02)

                # Mock PromptTemplate
                mock_prompt = unittest.mock.MagicMock()
                mock_prompt_template.from_template.return_value = mock_prompt

                # Mock StrOutputParser
                mock_parser = unittest.mock.MagicMock()
                mock_str_output_parser.return_value = mock_parser

                # Mock tiktoken
                mock_encoding = unittest.mock.MagicMock()
                mock_encoding.encode.return_value = [1, 2, 3]  # 3 tokens
                mock_tiktoken.get_encoding.return_value = mock_encoding

                # Mock chain invocation
                mock_chain = unittest.mock.MagicMock()
                mock_chain.invoke.return_value = "Generated test content"
                mock_prompt.__or__.return_value.__or__.return_value = mock_chain

                # Mock postprocess
                mock_postprocess.return_value = "Processed test content"

                # Call the function
                result = test_generator(
                    prompt_file="test_prompt.txt",
                    code_file="/fake/path/code.py",
                    strength=0.7,
                    language="python",
                    test_directory="/fake/path/tests"
                )

                # Assertions
                self.assertEqual(result, "Processed test content")
                mock_llm_selector.assert_called_once_with(0.7, temperature=0)
                mock_prompt_template.from_template.assert_called_once()
                mock_chain.invoke.assert_called_once_with({
                    "prompt_that_generated_code": "test_prompt.txt",
                    "code": mock_code_content,
                    "test_directory": "/fake/path/tests",
                    "language": "python",
                    "code_directory": "/fake/path"
                })
                mock_postprocess.assert_called_once_with("Generated test content", "python")

if __name__ == '__main__':
    unittest.main()