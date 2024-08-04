import unittest
import os
import pandas as pd
from unittest.mock import patch, MagicMock
from staging.pdd.llm_selector import llm_selector, instantiate_llm

class TestLLMSelector(unittest.TestCase):

    @patch('staging.pdd.llm_selector.pd.read_csv')
    @patch('staging.pdd.llm_selector.os.getenv')
    @patch('staging.pdd.llm_selector.instantiate_llm')
    def test_llm_selector(self, mock_instantiate_llm, mock_getenv, mock_read_csv):
        # Mock environment variables
        mock_getenv.side_effect = lambda x, default=None: {
            'PDD_MODEL_DEFAULT': 'gpt-4o-mini',
            'PDD_PATH': '/mock/path'
        }.get(x, default)

        # Mock CSV data
        mock_csv_data = pd.DataFrame({
            'model': ['gpt-4o-mini', 'gpt-3.5-turbo', 'gpt-4'],
            'provider': ['OpenAI', 'OpenAI', 'OpenAI'],
            'input': [0.01, 0.0015, 0.03],
            'output': [0.03, 0.002, 0.06],
            'coding_arena_elo': [1500, 1300, 1700]
        })
        mock_read_csv.return_value = mock_csv_data

        # Mock instantiate_llm
        mock_llm = MagicMock()
        mock_instantiate_llm.return_value = mock_llm

        # Test cases
        test_cases = [
            (0.3, 0.5, 'gpt-3.5-turbo'),  # Lower strength
            (0.5, 0.5, 'gpt-4o-mini'),    # Base model
            (0.7, 0.5, 'gpt-4'),          # Higher strength
        ]

        for strength, temperature, expected_model in test_cases:
            with self.subTest(strength=strength, temperature=temperature):
                llm, input_cost, output_cost = llm_selector(strength, temperature)

                self.assertEqual(llm, mock_llm)
                mock_instantiate_llm.assert_called_with('OpenAI', expected_model, temperature)

                expected_row = mock_csv_data[mock_csv_data['model'] == expected_model].iloc[0]
                self.assertEqual(input_cost, expected_row['input'])
                self.assertEqual(output_cost, expected_row['output'])

    def test_instantiate_llm(self):
        with patch('staging.pdd.llm_selector.ChatOpenAI') as mock_openai, \
             patch('staging.pdd.llm_selector.ChatGoogleGenerativeAI') as mock_google, \
             patch('staging.pdd.llm_selector.ChatAnthropic') as mock_anthropic:

            instantiate_llm('OpenAI', 'gpt-4', 0.7)
            mock_openai.assert_called_once_with(model='gpt-4', temperature=0.7)

            instantiate_llm('Google', 'gemini-pro', 0.5)
            mock_google.assert_called_once_with(model='gemini-pro', temperature=0.5)

            instantiate_llm('Anthropic', 'claude-2', 0.3)
            mock_anthropic.assert_called_once_with(model='claude-2', temperature=0.3)

            with self.assertRaises(ValueError):
                instantiate_llm('Unknown', 'model', 0.5)

if __name__ == '__main__':
    unittest.main()