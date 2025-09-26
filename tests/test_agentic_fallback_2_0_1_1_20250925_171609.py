# tests/test_agentic_fallback.py
import unittest
from agentic_test import calculate_sum

class TestAgenticFallback(unittest.TestCase):
    def test_calculate_sum(self):
        self.assertEqual(calculate_sum([1, 2, 3, 4, 5]), 15)

if __name__ == '__main__':
    unittest.main()
