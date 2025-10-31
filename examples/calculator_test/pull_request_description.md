## Feature: Incremental Test Appending for `pdd test` and `pdd bug` Commands

### Issue Addressed
This pull request addresses the need for `pdd test` and `pdd bug` commands to automatically append new tests to existing test files, rather than overwriting them or creating new, separate files for each test generation. This enhances the incremental development workflow and improves test coverage management.

Closes #102

### Description of Changes

This implementation modifies the `pdd test` and `pdd bug` commands to support incremental test generation. When new tests are generated, they are intelligently appended to an existing test file if one is specified (or detected), ensuring that previously written tests are preserved and new test cases are integrated seamlessly.

Key changes include:
-   **`pdd test`**: When used with `--existing-tests` and `--merge` options (or when `pdd sync` implicitly calls it), new tests generated to improve coverage are appended to the specified existing test file.
-   **`pdd bug`**: New unit tests generated from bug reports are now appended to the target test file, allowing for continuous expansion of the test suite without manual merging.
-   **`pdd sync`**: The `sync` command, which orchestrates the PDD workflow including test generation, now respects this incremental appending behavior for both `test` and `bug` operations.

### Testing

The new functionality was tested using the `examples/calculator_test` scenario.

**Steps to reproduce and verify:**

1.  **Initial Test Generation:**
    ```bash
    pdd test --output examples/calculator_test/test_calculator.py examples/calculator_test/calculator_python.prompt examples/calculator_test/calculator.py
    ```
    (This creates `test_calculator.py` with initial tests.)

2.  **Simulate Bug and Generate Bug Test:**
    *   Introduce a bug in `examples/calculator_test/calculator.py` (e.g., change `add` to `return a - b`).
    *   Ensure `examples/calculator_test/program_to_run_calculator.py`, `examples/calculator_test/current_output.txt`, and `examples/calculator_test/desired_output.txt` are set up as described in the example's `README.md`.
    *   Run `pdd bug`:
        ```bash
        pdd bug --output examples/calculator_test/test_calculator.py examples/calculator_test/calculator_python.prompt examples/calculator_test/calculator.py examples/calculator_test/program_to_run_calculator.py examples/calculator_test/current_output.txt examples/calculator_test/desired_output.txt
        ```
        (This command now appends the bug test to `test_calculator.py`.)

3.  **Enhance Coverage (Incremental `pdd test`):**
    *   (Optional: Generate a real `coverage.xml` by running tests.)
    *   Run `pdd test` with `--merge`:
        ```bash
        pdd test --coverage-report examples/calculator_test/coverage.xml --existing-tests examples/calculator_test/test_calculator.py --merge --target-coverage 95.0 examples/calculator_test/calculator_python.prompt examples/calculator_test/calculator.py
        ```
        (This appends additional tests to `test_calculator.py` if coverage needs improvement.)

4.  **Verify with `pdd sync`:**
    ```bash
    pdd --force sync examples/calculator_test/calculator
    ```
    (This runs the full workflow, confirming `sync` respects the appending behavior.)

### Benefits

-   **Improved Workflow:** Developers can incrementally add tests without manually merging files.
-   **Better Coverage Management:** Easier to enhance test coverage over time by appending new test cases.
-   **Reduced Manual Effort:** Automates the integration of new tests, saving time and reducing errors.
-   **Consistency:** Ensures `pdd sync` maintains a consistent and growing test suite.
