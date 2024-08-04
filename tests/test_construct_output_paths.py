# Certainly! I'll create a unit test for the `construct_output_paths` function. The test will be placed in the 'staging/tests' directory, and it will test the function located in the 'staging/pdd' directory. Here's the unit test in Python:

# ```python
import unittest
import os
import sys

# Add the path to the directory containing the function to be tested
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'pdd')))

# Import the function to be tested
from construct_output_paths import construct_output_paths

class TestConstructOutputPaths(unittest.TestCase):

    def test_default_paths(self):
        runnable, example = construct_output_paths('context_generator', '.py', None, None)
        self.assertEqual(runnable, 'context_generator.py')
        self.assertEqual(example, 'context_generator_example.py')

    def test_example_directory_path(self):
        runnable, example = construct_output_paths('context_generator', '.py', None, 'context/')
        self.assertEqual(runnable, 'context_generator.py')
        self.assertEqual(example, os.path.join('context', 'context_generator_example.py'))

    def test_both_directory_paths(self):
        runnable, example = construct_output_paths('context_generator', '.py', 'pdd/', 'context/')
        self.assertEqual(runnable, os.path.join('pdd', 'context_generator.py'))
        self.assertEqual(example, os.path.join('context', 'context_generator_example.py'))

    def test_runnable_file_path(self):
        runnable, example = construct_output_paths('pdd', '.prompt', 'pdd/pdd_v1.py', None)
        self.assertEqual(runnable, 'pdd/pdd_v1.py')
        self.assertEqual(example, 'pdd_example.prompt')

    def test_different_extensions(self):
        runnable, example = construct_output_paths('test', '.txt', 'output/file.dat', 'examples/ex.log')
        self.assertEqual(runnable, 'output/file.dat')
        self.assertEqual(example, 'examples/ex.log')

    def test_absolute_paths(self):
        runnable, example = construct_output_paths('abs_test', '.py', '/tmp/runnable/', '/tmp/example/')
        self.assertEqual(runnable, os.path.join('/tmp/runnable', 'abs_test.py'))
        self.assertEqual(example, os.path.join('/tmp/example', 'abs_test_example.py'))

if __name__ == '__main__':
    unittest.main()
# ```

# This unit test covers various scenarios:

# 1. Default paths (no output paths provided)
# 2. Example directory path provided
# 3. Both runnable and example directory paths provided
# 4. Runnable file path provided
# 5. Different file extensions and paths
# 6. Absolute paths

# To run this test:

# 1. Save the `construct_output_paths` function in a file named `construct_output_paths.py` in the 'staging/pdd' directory.
# 2. Save this test file as `test_construct_output_paths.py` in the 'staging/tests' directory.
# 3. Run the test using the command: `python -m unittest staging/tests/test_construct_output_paths.py`

# This test suite ensures that the `construct_output_paths` function handles various input scenarios correctly and produces the expected output paths for both runnable and example files.