## Calculator Test Example

This example demonstrates the `pdd test`, `pdd bug`, and `pdd sync` commands, focusing on how tests are appended incrementally.

### Setup

All commands should be run from the project root directory (`/Users/caijiamin/Desktop/pdd_my_branch/pdd`).

### Example 1: Append new test using pdd test command

Run the following command to generate the initial unit tests:

```bash
pdd test examples/calculator_test/calculator_python.prompt examples/calculator_test/calculator.py  \
  --output examples/calculator_test/test_calculator.py
```

This will create `examples/calculator_test/test_calculator.py` with basic tests for `add` and `subtract`.

Run the following command to merge new test with the existing test

```bash
pdd test examples/calculator_test/calculator_python.prompt examples/calculator_test/calculator.py  \
  --output examples/calculator_test/test_calculator.py \
  --merge --existing-tests examples/calculator_test/test_calculator.py

```

### Example 2: Simulate a Bug and Generate a New Test with `pdd bug`

First, let's introduce a bug in `examples/calculator_test/calculator.py` (e.g., modify the `add` function to be incorrect). Then, create `current_output.txt` and `desired_output.txt` files in the `examples/calculator_test` directory to define the bug.

After that, run `pdd bug` to generate a new test case for the bug:

```bash
pdd bug --output examples/calculator_test/test_caculator.py \
 examples/calculator_test/calculator_python.prompt \
 examples/calculator_test/calculator.py \
 examples/calculator_test/program_to_run_calculator.py \
 examples/calculator_test/current_output.txt \
 examples/calculator_test/desired_output.txt
```

This will create `examples/calculator_test/test_calculator_bug.py` with a test case specifically for the bug.



