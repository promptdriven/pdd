#!/usr/bin/env python3
"""
Verification script for issue #392 fix.
Runs the tests and reports if they pass.
"""
import subprocess
import sys

def main():
    # Run the tests
    result = subprocess.run(
        ["pytest", "tests/test_e2e_issue_392_change_keyerror.py", "-v"],
        capture_output=True,
        text=True
    )

    print(result.stdout)
    print(result.stderr, file=sys.stderr)

    # Exit with the same code as pytest
    sys.exit(result.returncode)

if __name__ == "__main__":
    main()
