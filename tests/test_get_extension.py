import unittest
import os
import pandas as pd
from unittest.mock import patch
from staging.pdd.get_extension import get_extension

class TestGetExtension(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        # Create a mock CSV file for testing
        cls.test_csv_content = pd.DataFrame({
            'language': ['Python', 'Java', 'C++'],
            'extension': ['.py', '.java', '.cpp']
        })
        cls.test_csv_path = 'test_language_format.csv'
        cls.test_csv_content.to_csv(cls.test_csv_path, index=False)

    @classmethod
    def tearDownClass(cls):
        # Remove the mock CSV file
        os.remove(cls.test_csv_path)

    def setUp(self):
        # Ensure PDD_PATH is not set at the start of each test
        os.environ.pop('PDD_PATH', None)

    @patch('os.path.join')
    @patch('pandas.read_csv')
    def test_get_extension_valid_language(self, mock_read_csv, mock_join):
        os.environ['PDD_PATH'] = '/mock/path'
        mock_join.return_value = self.test_csv_path
        mock_read_csv.return_value = self.test_csv_content

        self.assertEqual(get_extension('Python'), '.py')
        self.assertEqual(get_extension('JAVA'), '.java')
        self.assertEqual(get_extension('c++'), '.cpp')

        os.environ.pop('PDD_PATH', None)

    @patch('os.path.join')
    @patch('pandas.read_csv')
    def test_get_extension_invalid_language(self, mock_read_csv, mock_join):
        os.environ['PDD_PATH'] = '/mock/path'
        mock_join.return_value = self.test_csv_path
        mock_read_csv.return_value = self.test_csv_content

        self.assertEqual(get_extension('Ruby'), '')

        os.environ.pop('PDD_PATH', None)

    def test_get_extension_no_environment_variable(self):
        with self.assertRaises(ValueError):
            get_extension('Python')

    @patch('os.path.join')
    def test_get_extension_file_not_found(self, mock_join):
        os.environ['PDD_PATH'] = '/mock/path'
        mock_join.return_value = 'non_existent_file.csv'
        
        with self.assertRaises(FileNotFoundError):
            get_extension('Python')

        os.environ.pop('PDD_PATH', None)

if __name__ == '__main__':
    unittest.main()