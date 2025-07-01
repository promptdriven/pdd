# PDD Tutorials

This document provides step-by-step tutorials for common tasks in the PDD workflow.

## How to Create a New Test Case

Adding a new test case is a great way to improve the robustness of PDD. This guide will walk you through the process.

### 1. Prerequisite: Ensure Existing Tests Pass

Before adding a new test, ensure that all existing test cases are passing in your local repository. If other tests are failing, it can be difficult to tell if a new failure is caused by your changes or by an existing issue.

To run all tests, activate the conda environment and run `pytest` from the root of the project:

```bash
conda activate pdd
pytest
```

### 2. Locate or Create the Correct Test File

PDD's tests follow the project's module structure. For a module `pdd/my_module.py`, the corresponding tests should be in `tests/test_my_module.py`.

Figure out which module of PDD you want to test and find the corresponding test file. If one doesn't exist, you'll need to create it.

> **Example**: If you want to add a test case for a test that specifically/primarily calls `pdd/fix_error_loop.py`, you would add your test to `tests/test_fix_error_loop.py`.

### 3. Write Your Test

PDD uses the `pytest` framework for all tests. Test functions should be named using the `test_` prefix.

Here is a basic test structure:

```python
import pytest
from pdd import my_module # Import the module you are testing

def test_my_function_with_specific_case():
    # 1. Setup any variables or data needed for the test
    input_data = "some_value"
    expected_output = "expected_result"

    # 2. Call the function you are testing
    actual_output = my_module.my_function(input_data)

    # 3. Assert that the result is what you expect
    assert actual_output == expected_output
```

#### Mocking and Fixtures

For more complex scenarios, you will need to "mock" parts of the code, like calls to an LLM or functions that read from files. PDD tests use `unittest.mock.patch` for mocking and `pytest` fixtures for setting up reusable test components.

Here's an example of how to use mocking:

```python
from unittest.mock import patch

def test_function_with_external_call():
    # Use 'patch' to replace a function with a mock
    with patch('pdd.my_module.external_function') as mock_external_function:
        # Configure the mock to return a specific value
        mock_external_function.return_value = "mocked_value"

        # Now when my_function calls external_function, it will get the mocked value
        result = my_module.my_function()

        assert result == "mocked_value"
```

### 4. Handling Test Data

For tests that require more extensive data (like files or structured inputs), PDD follows a convention of placing this data in subdirectories within the `tests/` folder. For example, if you are testing a function that processes a set of files, you might create a directory like `tests/data_for_my_test/scenario_1/` and place your input files there.

Your test would then read from this directory:

```python
import os

def test_with_data_files():
    # Path to the test data
    test_data_path = os.path.join(os.path.dirname(__file__), 'data_for_my_test', 'scenario_1')
    input_file_path = os.path.join(test_data_path, 'input.txt')

    with open(input_file_path, 'r') as f:
        content = f.read()

    # ... rest of the test logic
```

### 5. Running Your New Test

Once you have written your test, you can run it specifically to make sure it works as expected.

To run a single test file:
```bash
pytest tests/test_my_module.py
```

To run a single test function within a file:
```bash
pytest tests/test_my_module.py::test_my_function_with_specific_case
```

After you've confirmed your new test passes, run the full test suite again to ensure your changes haven't broken anything else.

```bash
pytest
```