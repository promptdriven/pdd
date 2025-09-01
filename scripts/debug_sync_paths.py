#!/usr/bin/env python3
"""Debug sync path resolution with debug logging"""

import sys
import os
import logging

# Set up logging
logging.basicConfig(level=logging.DEBUG, format='%(levelname)s - %(message)s')

# Add pdd to path
sys.path.insert(0, '.')

from pdd.sync_determine_operation import get_pdd_file_paths

# Test in the sync regression directory
test_dir = "staging/sync_regression_20250802_204235"
if os.path.exists(test_dir):
    os.chdir(test_dir)
    
    print("Current directory:", os.getcwd())
    print("\n[TEST] Testing get_pdd_file_paths in sync regression directory")
    
    paths = get_pdd_file_paths('simple_math', 'python', 'prompts')
    
    print("\nReturned paths:")
    for key, path in paths.items():
        print(f"  {key}: {path}")
    
    print(f"\nTest path is correct: {str(paths['test']) == 'tests/test_simple_math.py'}")
    
    os.chdir("../..")
else:
    print(f"Test directory {test_dir} not found")
