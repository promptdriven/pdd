from __future__ import annotations

import os
import sys

# Ensure the parent directory is in the path so we can import pdd
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from pdd.pytest_slicer import PytestSlicer


def run_example() -> None:
    """Demonstrate PytestSlicer extracting a test and its dependencies."""
    test_source = """
import pytest

def helper_func(x):
    return x + 1

@pytest.fixture
def my_fixture():
    return 42

def test_something(my_fixture):
    assert helper_func(my_fixture) == 43

def test_other():
    assert 1 == 1
"""

    slicer = PytestSlicer(test_source, file_path="tests/test_demo.py")

    print("Slicing 'test_something'...")
    try:
        sliced_code, manifest = slicer.slice(["test_something"])

        print("\n--- Sliced Code ---")
        print(sliced_code)

        print("\n--- Manifest ---")
        print(f"Selected Tests: {manifest.selected_tests}")
        print(f"Included Fixtures: {manifest.included_fixtures}")
        print(f"Included Helpers: {manifest.included_helpers}")
        print(f"Source Hashes: {manifest.source_hashes}")

    except Exception as exc:
        print(f"Error during slicing: {exc}")
        sys.exit(1)


if __name__ == "__main__":
    run_example()
    print("\nSTEP_COMPLETE:example_generate")
