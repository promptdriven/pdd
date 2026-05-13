import os
import sys


def run_example() -> None:
    """
    Demonstrates how setup.py is conceptually used in Python packaging.

    Note: This is an illustrative example. In practice, you would run these
    commands directly in your shell, not through a Python script.
    """
    print("pdd-cli setup.py conceptual example")
    print("====================================")
    print("The setup.py file defines the package metadata, dependencies, and entry points")
    print("for the pdd-cli application using setuptools.\n")

    print("Common ways to use setup.py (from the command line in the project root):")
    print("  1. Install in editable mode for development:")
    print("     pip install -e .")
    print("  2. Build the package (source distribution and wheel):")
    print("     python -m build")
    print("  3. Install dependencies and dev dependencies:")
    print("     pip install -e \".[dev]\"")
    print("\nThe setup.py configures:")
    print("  - Package name: pdd-cli")
    print("  - Entry point: 'pdd' command line tool")
    print("  - Dependencies: litellm, click, PyYAML, GitPython, etc.")
    print("  - Package data: Includes prompts, csv data files, and templates")


if __name__ == '__main__':
    run_example()