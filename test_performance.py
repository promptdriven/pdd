#!/usr/bin/env python3
"""Test script to measure _scan_risky_placeholders performance"""

import time
import sys
sys.path.insert(0, '/tmp/pdd_job_70Yc2BCByrU78eYp9SBn_moqp6eyr')

from pdd.preprocess import _scan_risky_placeholders

# Read the test file
with open("large_test.prompt", "r") as f:
    text = f.read()

# Count lines and estimate placeholders
num_lines = text.count("\n")
print(f"Test file: {num_lines} lines, ~{len(text)} characters")

# Measure the performance
start_time = time.time()
single_brace, template_brace = _scan_risky_placeholders(text)
end_time = time.time()

elapsed = end_time - start_time
print(f"Found {len(single_brace)} single-brace placeholders")
print(f"Found {len(template_brace)} template-brace placeholders")
print(f"Time elapsed: {elapsed:.3f} seconds")

# Show a few examples
if single_brace:
    print(f"\nFirst few placeholders:")
    for i, (line_no, placeholder) in enumerate(single_brace[:5]):
        print(f"  Line {line_no}: {placeholder}")
