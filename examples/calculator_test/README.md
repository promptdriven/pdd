## Calculator Test Example

This example demonstrates the `pdd test`, `pdd bug`, and `pdd sync` commands, focusing on how tests are appended incrementally.

### Setup

All commands should be run from the project root directory (`/Users/caijiamin/Desktop/pdd_my_branch/pdd`).

### Step 1: Generate Initial Unit Tests

Run the following command to generate the initial unit tests:

```bash
pdd test examples/calculator_test/calculator_python.prompt examples/calculator_test/calculator.py  \
  --output examples/calculator_test/test_calculator.py
```

This will create `examples/calculator_test/test_calculator.py` with basic tests for `add` and `subtract`.



```bash
pdd test examples/calculator_test/calculator_python.prompt examples/calculator_test/calculator.py  \
  --output examples/calculator_test/test_calculator.py \
  --merge --existing-tests examples/calculator_test/test_calculator.py

```

### Step 2: Simulate a Bug and Generate a New Test with `pdd bug`

First, let's introduce a bug in `examples/calculator_test/calculator.py` (e.g., modify the `add` function to be incorrect). Then, create `current_output.txt` and `desired_output.txt` files in the `examples/calculator_test` directory to define the bug.

After that, run `pdd bug` to generate a new test case for the bug:

```bash
pdd bug --output examples/calculator_test/test_calculator_bug.py examples/calculator_test/calculator_python.prompt examples/calculator_test/calculator.py examples/calculator_test/program_to_run_calculator.py examples/calculator_test/current_output.txt examples/calculator_test/desired_output.txt
```

This will create `examples/calculator_test/test_calculator_bug.py` with a test case specifically for the bug.

### Step 3: Enhance Coverage with `pdd test --coverage-report --existing-tests --merge`

To demonstrate incremental test generation, you would typically run your tests, generate a coverage report, and then use `pdd test` to add more tests to improve coverage. For this example, we'll simulate this by directly using the `--merge` option.

```bash
pdd test --coverage-report examples/calculator_test/coverage.xml --existing-tests examples/calculator_test/test_calculator.py --merge --target-coverage 95.0 examples/calculator_test/calculator_python.prompt examples/calculator_test/calculator.py
```

This command will analyze `examples/calculator_test/calculator.py` and `examples/calculator_test/test_calculator.py`, and if there are uncovered lines, it will append new tests to `examples/calculator_test/test_calculator.py` to increase coverage.

### Step 4: Verify with `pdd sync`

Finally, run `pdd sync` to see how it handles existing tests and potentially generates new ones or fixes issues. `pdd sync` should also append to existing test files.

```bash
pdd --force sync examples/calculator_test/calculator
```

This command will run the full PDD workflow, including test generation and fixing, and should respect the existing `examples/calculator_test/test_calculator.py` by appending to it if necessary.