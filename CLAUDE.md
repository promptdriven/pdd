# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands
- Install dependencies: `pip install -e .` or `pip install -r requirements.txt`
- Run all tests: `pytest -vv tests/` 
- Run single test: `pytest -vv tests/test_module_name.py`
- Test with coverage: `make coverage`
- Generate module: `make generate MODULE=module_name`
- Fix module: `make fix MODULE=module_name`
- Crash fix: `make crash MODULE=module_name`
- Regression tests: `make regression`
- Lint check: `pylint **/*.py`

## Code Style
- Python 3.11+, follow PEP 8 conventions
- Type hints required (import from typing module)
- Imports: standard lib � third-party � local (alphabetically)
- Functions must have docstrings with triple quotes
- Error handling with custom exceptions when appropriate
- Comprehensive test coverage expected for new functionality
- Uses pydantic for data validation (v2)
- Click library for CLI commands
- Langchain for LLM interactions