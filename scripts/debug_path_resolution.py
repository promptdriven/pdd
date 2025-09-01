#!/usr/bin/env python3
"""Debug script to debug path resolution issue"""

import sys
import os
from pathlib import Path

# Add pdd to path
sys.path.insert(0, 'pdd')

from sync_determine_operation import get_pdd_file_paths

# Test in a directory with .pddrc
os.makedirs('test_debug', exist_ok=True)
os.chdir('test_debug')

# Create .pddrc
pddrc_content = """version: "1.0"
contexts:
  regression:
    paths: ["**"]
    defaults:
      test_output_path: "tests/"
      example_output_path: "examples/"
"""

with open('.pddrc', 'w') as f:
    f.write(pddrc_content)

# Create directories
os.makedirs('prompts', exist_ok=True)
os.makedirs('tests', exist_ok=True)
os.makedirs('examples', exist_ok=True)

# Test 1: When prompt doesn't exist
print("Test 1: Prompt doesn't exist")
paths = get_pdd_file_paths('simple_math', 'python', 'prompts')
print(f"  test path: {paths['test']}")
print(f"  is tests/test_simple_math.py: {str(paths['test']) == 'tests/test_simple_math.py'}")

# Test 2: When prompt exists
print("\nTest 2: Prompt exists")
with open('prompts/simple_math_python.prompt', 'w') as f:
    f.write("Create add function")
    
paths = get_pdd_file_paths('simple_math', 'python', 'prompts')
print(f"  test path: {paths['test']}")
print(f"  is tests/test_simple_math.py: {str(paths['test']) == 'tests/test_simple_math.py'}")

# Clean up
os.chdir('..')
