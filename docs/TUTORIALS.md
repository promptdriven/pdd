# PDD Tutorials

This document provides step-by-step tutorials for common tasks in the PDD workflow.

See also:
- Prompting Guide: pdd/docs/prompting_guide.md
- PDD Doctrine: pdd/docs/prompt-driven-development-doctrine.md

## Issue-Driven Development Tutorial

This tutorial walks through implementing a GitHub issue using PDD.

### Prerequisites

- **PDD installed**: `pdd --version`
- **GitHub CLI**: `brew install gh && gh auth login`
- **One Agentic CLI** - Install at least one:
  - **Claude Code**: `npm install -g @anthropic-ai/claude-code` (requires `ANTHROPIC_API_KEY`)
  - **Gemini CLI**: `npm install -g @google/gemini-cli` (requires `GOOGLE_API_KEY`)
  - **Codex CLI**: `npm install -g @openai/codex` (requires `OPENAI_API_KEY`)

### Method 1: Using the Web Interface

1. **Start PDD Connect**
   ```bash
   pdd connect
   ```

2. **Run the Command**
   - Use the command execution interface to run:
     - `pdd change https://github.com/myorg/myrepo/issues/123` (for features)
     - `pdd bug https://github.com/myorg/myrepo/issues/123` (for bugs)

3. **Monitor Progress**
   - Watch the agentic workflow progress through each step
   - Answer any clarifying questions posted to the GitHub issue

4. **Review the PR**
   - PDD creates a draft PR automatically
   - Review the changes in GitHub
   - Request human review when ready

### Method 2: Using the CLI

1. **Implement a Feature Request**
   ```bash
   pdd change https://github.com/myorg/myrepo/issues/123
   ```

2. **Handle Clarifying Questions**
   - If PDD needs clarification, it will post questions to the issue
   - Answer them in the GitHub issue comments
   - Run `pdd change` again to resume

3. **Review the Generated PR**
   - Open the PR link provided by PDD
   - Review the changes
   - Run `pdd sync` on modified prompts to regenerate code if needed

### Method 3: Fixing a Bug Report

1. **Create Failing Tests**
   ```bash
   pdd bug https://github.com/myorg/myrepo/issues/456
   ```
   This analyzes the bug and creates failing tests.

2. **Fix the Tests**
   ```bash
   pdd fix https://github.com/myorg/myrepo/issues/456
   ```
   This iteratively fixes the code until tests pass.

3. **Review and Merge**
   - The PR is updated with the fix
   - Review and merge when ready

### Method 4: Generating Tests (UI, CLI, or API)

1. **Create a GitHub Issue**
   - Describe what needs to be tested:
     - **Web UI**: Webpage URL, screenshots, expected behaviors
     - **CLI**: Commands to test, expected outputs
     - **API**: Endpoints to test, HTTP methods, expected responses
   - Include examples of expected behavior
   - Specify what elements/interactions/responses should be verified

2. **Generate Tests**
   ```bash
   pdd test https://github.com/myorg/myrepo/issues/789
   ```
   This analyzes the target and creates comprehensive tests (Playwright for web, pytest for CLI, pytest+requests for API).

3. **Handle Clarifying Questions**
   - If PDD needs more information (e.g., credentials, test environment setup, API authentication), it posts questions to the issue
   - Answer them in the GitHub issue comments
   - Run `pdd test` again to resume

4. **Review the Generated Tests**
   - The PR contains tests for the specified target:
     - **Web UI**: Playwright tests
     - **CLI**: pytest with subprocess
     - **API**: pytest with requests/httpx
   - Review and adjust tests as needed

5. **Fix Any Issues Found**
   ```bash
   pdd fix https://github.com/myorg/myrepo/issues/789
   ```
   Use this if tests reveal bugs that need fixing.

### Tips

- **Resume from anywhere**: Workflow state is saved to GitHub, so you can continue on any machine
- **Cost budgeting**: Use `--budget` flag to limit spending on complex issues
- **Skip steps**: If a step hangs, check the GitHub issue for clarifying questions

---

## How to Create a New Test Case

Adding a new test case is a great way to improve the robustness of PDD. This guide will walk you through the process of creating **unit tests** - low-level tests that focus on testing individual functions and modules for robustness and functionality.

> **Note**: This section covers unit tests. For high-level integration testing that validates entire workflows, see the [regression tests section](#how-to-create-a-new-regression-test) below.

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

## How to Create a New Regression Test

Regression tests are high-level integration tests that validate the entire PDD workflow by testing multiple components working together. Unlike unit tests (which test individual functions in isolation), regression tests simulate real-world usage scenarios and ensure that the complete system functions correctly.

### Key Differences: Unit Tests vs Regression Tests

- **Unit Tests**: Low-level, test specific module functions for robustness and functionality
- **Regression Tests**: High-level, test multiple parts of the system working together in realistic scenarios

Both types of tests must pass for the codebase to be considered stable.

### 1. Running Existing Regression Tests

Before creating new regression tests, familiarize yourself with the existing test suite:

#### Run All Regression Tests
```bash
make regression
```

#### Run a Specific Regression Test
```bash
make regression TEST_NUM=1
```

This runs only test case #1 (the 'generate' command test). Test numbers correspond to the numbered sections in `tests/regression.sh`.

#### Check Test Results
After running regression tests, check the output directory for:
- Log files with detailed execution information
- Cost tracking files showing API usage
- Generated test artifacts

#### View Past Regression Test Results
To see results from previous regression test runs, look in the `staging/` directory. Each regression test run creates a timestamped folder (e.g., `staging/regression_20240115_143022/`) containing all the artifacts and logs from that test run.

### 2. Understanding the Regression Test Structure

The regression tests are defined in `tests/regression.sh` and follow this structure:

```bash
# Test case structure
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "N" ]; then
  log "N. Testing 'command_name' command"
  
  # Setup test data
  # Run PDD command
  # Validate outputs
  # Check expected files exist
  
  # Optional: Test variations (flags, options, etc.)
  log "Na. Testing 'command_name' with specific options"
  # Additional test scenarios
fi
```

### 3. Step-by-Step Guide to Adding a New Regression Test

#### Step 1: Plan Your Test Scenario

Choose a realistic workflow scenario that tests multiple PDD components. Examples:
- Testing a new command with various options
- Testing command interactions (e.g., generate → test → fix)
- Testing error handling and recovery scenarios

#### Step 2: Add Your Test Case

1. **Choose a test number**: Find the next available number in `tests/regression.sh`
2. **Add the test block**: Insert your test case in the appropriate location

```bash
# XX. Your New Test (replace XX with actual test number)
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "XX" ]; then
  log "XX. Testing 'your_new_feature' command"
  
  # Setup phase - create any needed test files
  echo "Test input data" > "test_input.txt"
  
  # Run the command being tested
  run_pdd_command your_new_feature --output "output.txt" "input.txt"
  
  # Validate the output
  check_exists "output.txt" "'your_new_feature' output"
  
  # Additional validation (content checks, behavior verification)
  if grep -q "expected_content" "output.txt"; then
    log "Output contains expected content"
  else
    log_error "Output missing expected content"
    exit 1
  fi
fi
```

#### Step 3: Use Helper Functions

The regression test framework provides several helper functions:

- `run_pdd_command`: Execute PDD commands with automatic logging and error handling
- `run_pdd_command_noexit`: Same as above but doesn't exit on failure
- `run_pdd_expect_fail`: Expects the command to fail (for error testing)
- `check_exists`: Validates that a file exists and is not empty
- `check_not_exists`: Validates that a file should not exist
- `log`: Outputs informational messages
- `log_error`: Outputs error messages

#### Step 4: Test Data Management

Create test data files as needed:

```bash
# Create test files in the regression directory
cat << EOF > "test_prompt.prompt"
Your test prompt content here
EOF

# Create directories for complex scenarios
mkdir -p "test_scenario/input"
mkdir -p "test_scenario/output"
```

**Important Note**: The regression test framework automatically creates a timestamped regression folder for each test run. All test files are created within this folder by default. However, if you need to create files that cannot be placed in the regression folder (due to specific path requirements), you should output them to the `output/` directory instead:

```bash
# For files that need to be in a specific location outside the regression folder
OUTPUT_DIR="$PDD_BASE_DIR/output"
mkdir -p "$OUTPUT_DIR"
echo "Special output file" > "$OUTPUT_DIR/special_file.txt"
```

#### Step 5: Handle Test Variations

Test different scenarios within your test case:

```bash
# XX. Your New Test (replace XX with actual test number)
if [ "$TARGET_TEST" = "all" ] || [ "$TARGET_TEST" = "XX" ]; then
  log "XX. Testing 'your_new_feature' command"
  
  # Basic functionality
  run_pdd_command your_new_feature --output "basic_output.txt" "input.txt"
  check_exists "basic_output.txt" "'your_new_feature' basic output"
  
  # XXa. Test with additional options
  log "XXa. Testing 'your_new_feature' with --advanced-option"
  run_pdd_command your_new_feature --advanced-option --output "advanced_output.txt" "input.txt"
  check_exists "advanced_output.txt" "'your_new_feature' advanced output"
  
  # XXb. Test error handling
  log "XXb. Testing 'your_new_feature' error handling"
  run_pdd_expect_fail your_new_feature --output "error_output.txt" "nonexistent_input.txt"
fi
```

### 4. Best Practices for Regression Tests

#### Test Isolation
- Each test should be independent and not rely on previous tests
- Clean up temporary files if needed
- Use unique file names to avoid conflicts

#### Comprehensive Coverage
- Test the happy path (normal usage)
- Test edge cases and error conditions
- Test different command options and flags
- Test file input/output scenarios

#### Clear Logging
- Use descriptive log messages
- Log what you're testing and why
- Include validation steps in logs

#### Error Handling
- Use appropriate helper functions (`run_pdd_expect_fail` for expected failures)
- Provide clear error messages when validations fail
- Don't let tests continue if critical validations fail

### 5. Testing Your New Regression Test

#### Test Locally
```bash
# Run only your new test (replace XX with your actual test number)
make regression TEST_NUM=XX

# Run all tests to ensure no regressions
make regression
```

#### Validate Test Output
- Check that log files contain expected information
- Verify that test files are created and cleaned up properly
- Ensure cost tracking is working correctly

#### Test Different Scenarios
- Test with different environment variables
- Test with different PDD configurations
- Test both local and cloud execution modes

### 6. Common Patterns in Regression Tests

#### File Generation and Validation
```bash
# Generate a file and validate its contents
run_pdd_command generate --output "$OUTPUT_FILE" "$INPUT_PROMPT"
check_exists "$OUTPUT_FILE" "Generated output"
grep -q "expected_function" "$OUTPUT_FILE" || (log_error "Missing expected function"; exit 1)
```

#### Command Chaining
```bash
# Test multiple commands working together
run_pdd_command generate --output "code.py" "prompt.prompt"
run_pdd_command test --output "test_code.py" "prompt.prompt" "code.py"
run_pdd_command fix --output-test "fixed_test.py" --output-code "fixed_code.py" "prompt.prompt" "code.py" "test_code.py" "error.log"
```

#### Environment Testing
```bash
# Test environment variable behavior
export PDD_SOME_OPTION="test_value"
run_pdd_command some_command --output "env_output.txt" "input.txt"
unset PDD_SOME_OPTION
```

### 7. Final Validation

Before submitting your regression test:

1. **Run the full test suite**: `make regression`
2. **Verify all tests pass**: Check that your new test doesn't break existing functionality
3. **Test edge cases**: Ensure your test handles various scenarios gracefully
4. **Review logs**: Confirm that logging is clear and helpful for debugging

Remember: Regression tests are crucial for maintaining system stability. They should catch breaking changes and ensure that the PDD workflow continues to function correctly as the codebase evolves.

## Method 4: Generating Architecture from a PRD (GitHub Issue)

Instead of manually writing `architecture.json`, you can point `pdd generate` at a GitHub issue containing your PRD. An 11-step agentic workflow will analyze the PRD, research the tech stack, generate `architecture.json`, create `.pddrc` configuration, and produce prompt files for each module.

### Prerequisites

1. `gh` CLI installed and authenticated (`gh auth login`)
2. A GitHub issue containing your PRD (title, goals, features, tech stack)

### Steps

1. **Create a GitHub issue** with your PRD content:
   - Title: Project name or feature area
   - Body: Goals, key features, non-functional requirements, tech stack preferences

2. **Run the agentic generate command**:
   ```bash
   pdd generate https://github.com/myorg/myrepo/issues/42
   ```

3. **Monitor progress**: The workflow posts step-by-step progress as issue comments:
   - Analyzes your PRD for features and tech stack
   - Researches documentation and best practices
   - Designs the module breakdown with dependency ordering
   - Generates `architecture.json` and `.pddrc` configuration
   - Creates prompt files for each module
   - Validates completeness, sync configuration, and dependencies

4. **Review the output**: The workflow produces:
   - `architecture.json` - Module definitions with priorities and dependencies
   - `architecture_diagram.html` - Interactive Mermaid visualization
   - `.pddrc` - Project configuration with context-specific paths
   - `prompts/*.prompt` - Prompt files for each module (unless `--skip-prompts`)

5. **Run sync on generated prompts** (prompts are already generated):
   ```bash
   pdd sync my_module
   ```

### Resuming a Failed Run

If the workflow stops (e.g., PRD needs clarification):
1. Add clarifications as comments on the GitHub issue
2. Re-run `pdd generate <issue-url>` — it resumes from the last completed step

### Tips

- Write detailed PRDs: The more specific your requirements, the better the architecture
- Include tech stack preferences explicitly (e.g., "FastAPI + PostgreSQL" vs. leaving it ambiguous)
- Review the generated `architecture.json` before generating individual module prompts
- The `context_urls` field in each module entry provides documentation links for code generation

## Method 5: Syncing Modules from a GitHub Issue

If you have a GitHub issue describing a feature or bug, you can use `pdd sync` to automatically identify and sync all affected modules:

```bash
pdd sync https://github.com/myorg/myrepo/issues/42
```

### How it works

1. Fetches the issue content (title, description, and comments)
2. Identifies which modules need syncing using an LLM
3. Validates the dependency graph
4. Runs `pdd sync` on each module in dependency order (parallelizing where possible)

### With or without `architecture.json`

- If your project has an `architecture.json`, the LLM uses it to identify affected modules and their dependencies
- If your project only has prompt files in `prompts/`, the system scans for `*_<Language>.prompt` files to build a module catalog and uses `<include>` tags to infer dependencies

### Prerequisites

1. `gh` CLI installed and authenticated (`gh auth login`)
2. Prompt files in your `prompts/` directory

### Example workflow

```bash
# Someone files an issue about improving the calculator module
# Run agentic sync to update affected modules
pdd sync https://github.com/myorg/myrepo/issues/99

# The command will:
# - Analyze the issue
# - Identify that calculator_python.prompt and its dependents need sync
# - Run pdd sync on each in the correct order
```
