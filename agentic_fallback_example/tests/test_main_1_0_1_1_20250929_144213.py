import unittest
import os
import sys

# Add the src directory to the Python path to allow for absolute imports
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))

from main import create_user_greeting

class TestMain(unittest.TestCase):
    def test_create_user_greeting(self):
        """
        This test will fail because main.py calls get_greeting with wrong keywords.
        The resulting TypeError is captured in error.log.
        """
        # This call will raise the TypeError we want to fix.
        create_user_greeting()

if __name__ == '__main__':
    unittest.main()
