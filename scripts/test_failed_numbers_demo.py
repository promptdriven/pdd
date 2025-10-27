#!/usr/bin/env python3
"""
Demo script to test the failed test number extraction functionality.
This creates mock test outputs to verify the parsing works correctly.
"""

from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).parent.parent))

from scripts.run_all_tests_with_results import TestRunner


def test_failed_number_extraction():
    """Test that we can extract test numbers from pytest output."""
    
    # Sample pytest output with test numbers
    sample_output = """
============================= test session starts ==============================
collected 10 items

tests/test_regression.py::test_case[1] PASSED                          [ 10%]
tests/test_regression.py::test_case[2] PASSED                          [ 20%]
tests/test_regression.py::test_case[3] FAILED                          [ 30%]
tests/test_regression.py::test_case[4] PASSED                          [ 40%]
tests/test_regression.py::test_case[5] FAILED                          [ 50%]
tests/test_unit.py::test_basic PASSED                                  [ 60%]
tests/test_unit.py::test_advanced FAILED                               [ 70%]

=================================== FAILURES ===================================
_________________________ test_case[3] _________________________
AssertionError: Expected 5, got 3
_________________________ test_case[5] _________________________
ValueError: Invalid input
_________________________ test_advanced _________________________
RuntimeError: Something went wrong

=========================== short test summary info ============================
FAILED tests/test_regression.py::test_case[3] - AssertionError: Expected 5, got 3
FAILED tests/test_regression.py::test_case[5] - ValueError: Invalid input
FAILED tests/test_unit.py::test_advanced - RuntimeError: Something went wrong
========================= 7 passed, 3 failed, 0 skipped in 5.23s =============
"""
    
    runner = TestRunner(Path.cwd())
    passed, failed, skipped, failures = runner._parse_pytest_output(sample_output)
    
    print("=" * 60)
    print("PARSING TEST RESULTS")
    print("=" * 60)
    print(f"Passed: {passed}")
    print(f"Failed: {failed}")
    print(f"Skipped: {skipped}")
    print(f"Failures detected: {len(failures)}")
    
    print("\n" + "=" * 60)
    print("FAILED TESTS DETAILS")
    print("=" * 60)
    
    for i, failure in enumerate(failures, 1):
        print(f"\n{i}. Test: {failure['test']}")
        if failure.get('test_number'):
            print(f"   Test Number: {failure['test_number']}")
        print(f"   Error: {failure['error'][:100]}...")
    
    # Extract just the test numbers
    test_numbers = [f['test_number'] for f in failures if f.get('test_number')]
    
    print("\n" + "=" * 60)
    print("FAILED TEST NUMBERS")
    print("=" * 60)
    if test_numbers:
        print(f"Numbers: {', '.join(test_numbers)}")
        print("\nTo rerun:")
        for num in test_numbers:
            print(f"  make regression TEST_NUM={num}")
    else:
        print("No numbered tests failed")
    
    # Verify expected results
    assert passed == 7, f"Expected 7 passed, got {passed}"
    assert failed == 3, f"Expected 3 failed, got {failed}"
    assert len(failures) == 3, f"Expected 3 failures, got {len(failures)}"
    assert '3' in test_numbers, "Expected test number 3 in failures"
    assert '5' in test_numbers, "Expected test number 5 in failures"
    
    print("\n" + "=" * 60)
    print("ALL ASSERTIONS PASSED")
    print("=" * 60)


if __name__ == "__main__":
    test_failed_number_extraction()

