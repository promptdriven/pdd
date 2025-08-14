#!/usr/bin/env python3
"""Test to understand construct_paths return values"""

import sys
import os
from pathlib import Path
import json

# Add pdd to path
sys.path.insert(0, 'pdd')

from pdd.construct_paths import construct_paths

# Test in a directory with .pddrc
os.makedirs('test_debug2', exist_ok=True)
os.chdir('test_debug2')

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
os.makedirs('tests', exist_ok=True)
os.makedirs('examples', exist_ok=True)

# Call construct_paths with empty inputs (like the fallback does)
print("Calling construct_paths with empty inputs for sync command...")
resolved_config, input_strings, output_paths, language = construct_paths(
    input_file_paths={},
    force=True,
    quiet=True,
    command="sync",
    command_options={"basename": "simple_math", "language": "python"}
)

print("\nresolved_config:")
for key, value in resolved_config.items():
    if 'path' in key:
        print(f"  {key}: {value}")

print("\noutput_paths:")
for key, value in output_paths.items():
    print(f"  {key}: {value}")

# Clean up
os.chdir('..')