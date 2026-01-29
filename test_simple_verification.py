#!/usr/bin/env python3
"""Simple test to verify the fix for issue #430 works"""

import sys
from pathlib import Path

# Read the sync_orchestration.py file
sync_file = Path("pdd/sync_orchestration.py")
content = sync_file.read_text()

# Find the auto-fix success block
auto_fix_marker = "# Auto-fix worked! Save run report and continue"
continue_marker = "continue  # Skip crash_main, move to next operation"

# Find the positions
auto_fix_pos = content.find(auto_fix_marker)
continue_pos = content.find(continue_marker, auto_fix_pos)

if auto_fix_pos == -1 or continue_pos == -1:
    print("ERROR: Could not find auto-fix code block")
    sys.exit(1)

# Extract the code between these markers
code_block = content[auto_fix_pos:continue_pos]

# Check if the fix is present
has_append = "operations_completed.append('crash')" in code_block
has_fingerprint = "_save_fingerprint_atomic(basename, language, 'crash'" in code_block

print("Verification Results:")
print(f"  operations_completed.append('crash') present: {has_append}")
print(f"  _save_fingerprint_atomic call present: {has_fingerprint}")

if has_append and has_fingerprint:
    print("\n✅ Fix is correctly applied!")
    sys.exit(0)
else:
    print("\n❌ Fix is NOT correctly applied!")
    if not has_append:
        print("  Missing: operations_completed.append('crash')")
    if not has_fingerprint:
        print("  Missing: _save_fingerprint_atomic call")
    sys.exit(1)
