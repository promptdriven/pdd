# PDD (Prompt-Driven Development) Command Line Interface

PDD is a versatile tool for generating code, examples, unit tests, and managing prompt files through various features like splitting large prompt files into smaller ones.

## Prompt File Naming Convention

Prompt files in PDD follow this specific naming format:
```
<basename>_<language>.prompt
```
Where:
- `<basename>` is the base name of the file or project
- `<language>` is the programming language or context of the prompt file

Examples:
- `pdd_cli_python.prompt` (basename: pdd_cli, language: python)
- `Makefile_makefile.prompt` (basename: Makefile, language: makefile)
- `setup_bash.prompt` (basename: setup, language: bash)

## Basic Usage

```
python pdd/pdd.py [GLOBAL OPTIONS] COMMAND [OPTIONS] [ARGS]...
```

## Global Options

These options can be used with any command:

- `--force`: Overwrite existing files without asking for confirmation.
- `--strength`: Set the strength of the AI model (default is 0.5).
- `--temperature`: Set the temperature of the AI model (default is 0.0).
- `--verbose`: Increase output verbosity for more detailed information.
- `--quiet`: Decrease output verbosity for minimal information.
- `--output-cost PATH_TO_CSV_FILE`: Enable cost tracking and output a CSV file with usage details.

## Output Cost Tracking

PDD includes a global feature for tracking and reporting the cost of operations. When enabled, it generates a CSV file with usage details for each command execution.

### Usage

To enable cost tracking, use the `--output-cost` option with any command:

```
pdd --output-cost PATH_TO_CSV_FILE [COMMAND] [OPTIONS] [ARGS]...
```

The `PATH_TO_CSV_FILE` should be the desired location and filename for the CSV output.

### CSV Output

The generated CSV file includes the following columns:
- timestamp: The date and time of the command execution
- model: The AI model used for the operation
- command: The PDD command that was executed
- cost: The estimated cost of the operation
- input_files: A list of input files involved in the operation
- output_files: A list of output files generated or modified by the operation

This comprehensive output allows for detailed tracking of not only the cost and type of operations but also the specific files involved in each PDD command execution.

### Environment Variable

You can set a default location for the cost output CSV file using the environment variable:

- **`PDD_OUTPUT_COST_PATH`**: Default path for the cost tracking CSV file.

If this environment variable is set, the CSV file will be saved to the specified path by default, unless overridden by the `--output-cost` option. For example, if `PDD_OUTPUT_COST_PATH=/path/to/cost/reports/`, the CSV file will be saved in that directory with a default filename.

## Commands

Here are the main commands:

### 1. Generate

Create runnable code from a prompt file.

```
pdd generate [GLOBAL OPTIONS] [OPTIONS] PROMPT_FILE
```

Options:
- `--output LOCATION`: Specify where to save the generated code. The default file name is `<basename>.<language_file_extension>`. If an environment variable `PDD_GENERATE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

### 2. Example

Create an example file from an existing code file.

```
pdd example [GLOBAL OPTIONS] [OPTIONS] CODE_FILE
```

Options:
- `--output LOCATION`: Specify where to save the generated example code. The default file name is `<basename>_example.<language_file_extension>`. If an environment variable `PDD_EXAMPLE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

### 3. Test

Generate a unit test file for a given code file and its corresponding prompt file.

```
pdd test [GLOBAL OPTIONS] [OPTIONS] CODE_FILE PROMPT_FILE
```

Options:
- `--output LOCATION`: Specify where to save the generated test file. The default file name is `test_<basename>.<language_file_extension>`. If an environment variable `PDD_TEST_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--language`: Specify the programming language. Defaults to the language specified by the prompt file name.

### 4. Preprocess

Preprocess prompt files and save the results.

```
pdd preprocess [GLOBAL OPTIONS] [OPTIONS] PROMPT_FILE
```

Options:
- `--output LOCATION`: Specify where to save the preprocessed prompt file. The default file name is `<basename>_<language>_preprocessed.prompt`. If an environment variable `PDD_PREPROCESS_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--xml`: Automatically insert XML delimiters for long and complex prompt files to structure the content better.

### 5. Fix

Fix errors in code and unit tests based on error messages.

```
pdd fix [GLOBAL OPTIONS] [OPTIONS] UNIT_TEST_FILE CODE_FILE ERROR_FILE
```

Options:
- `--output-test LOCATION`: Specify where to save the fixed unit test file. The default file name is `test_<basename>_fixed.<language_file_extension>`. If an environment variable `PDD_FIX_TEST_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--output-code LOCATION`: Specify where to save the fixed code file. The default file name is `<basename>_fixed.<language_file_extension>`. If an environment variable `PDD_FIX_CODE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--loop`: Enable iterative fixing process.
  - `--verification-program PATH`: Specify the path to a Python program that verifies if the code still runs correctly.
  - `--max-attempts INT`: Set the maximum number of fix attempts before giving up (default is 3).
  - `--budget FLOAT`: Set the maximum cost allowed for the fixing process (default is $5.0).

When the `--loop` option is used, the fix command will attempt to fix errors through multiple iterations. It will use the specified verification program to check if the code runs correctly after each fix attempt. The process will continue until either the errors are fixed, the maximum number of attempts is reached, or the budget is exhausted.

Outputs when using `--loop`:
- Success status (boolean)
- Final unit test file contents
- Final code file contents
- Total number of fix attempts made
- Total cost of all fix attempts

### 6. Split

Split large complex prompt files into smaller, more manageable prompt files.

```
pdd split [GLOBAL OPTIONS] [OPTIONS] INPUT_PROMPT INPUT_CODE EXAMPLE_CODE
```

Options:
- `--output-sub LOCATION`: Specify where to save the generated sub-prompt file. The default file name is `sub_<basename>.prompt`. If an environment variable `PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--output-modified LOCATION`: Specify where to save the modified prompt file. The default file name is `modified_<basename>.prompt`. If an environment variable `PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

The `EXAMPLE_CODE` input serves as the interface to the sub-module prompt file that will be generated.

### 7. Change

Modify an input prompt file based on a change prompt and the corresponding input code.

```
pdd change [GLOBAL OPTIONS] [OPTIONS] INPUT_PROMPT INPUT_CODE CHANGE_PROMPT
```

Options:
- `--output LOCATION`: Specify where to save the modified prompt file. The default file name is `modified_<basename>.prompt`. If an environment variable `PDD_CHANGE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

This command takes three inputs:
- `INPUT_PROMPT`: A string containing the prompt file that will be modified.
- `INPUT_CODE`: A string containing the code that was generated from the input prompt file.
- `CHANGE_PROMPT`: A string containing the instructions on how to modify the input prompt file.

The command produces one output:
- `MODIFIED_PROMPT`: A string containing the modified prompt file that was changed based on the change prompt.

### 8. Update

Update the original prompt file based on the original code and the modified code.

```
pdd update [GLOBAL OPTIONS] [OPTIONS] INPUT_PROMPT INPUT_CODE MODIFIED_CODE
```

Options:
- `--output LOCATION`: Specify where to save the modified prompt file. The default file name is `modified_<basename>.prompt`. If an environment variable `PDD_UPDATE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

This command takes three inputs:
- `INPUT_PROMPT`: A string containing the prompt file that generated the original code.
- `INPUT_CODE`: A string containing the original code that was generated from the input prompt file.
- `MODIFIED_CODE`: A string containing the code that was modified by the user.

The command produces one output:
- `MODIFIED_PROMPT`: A string containing the modified prompt file that will generate the modified code.

## Output Location Specification

For all commands that generate or modify files, the `--output` option (or its variant, such as `--output-sub` or `--output-modified` for the `split` command) allows flexible specification of the output location:

1. **Filename only**: If you provide just a filename (e.g., `--output result.py`), the file will be created in the current working directory.
2. **Full path**: If you provide a full path (e.g., `--output /home/user/projects/result.py`), the file will be created at that exact location.
3. **Directory**: If you provide a directory name (e.g., `--output ./generated/`), a file with an automatically generated name will be created in that directory.
4. **Environment Variable**: If the `--output` option is not provided, and an environment variable specific to the command is set, PDD will use the path specified by this variable. Otherwise, it will use default naming conventions and save the file in the current working directory.
5. **No Output Location**: If no output location is specified and no environment variable is set, the file will be saved in the current working directory with a default name given the command.

## Multi-Command Chaining

PDD supports multi-command chaining, allowing you to execute multiple commands in a single line. Commands will be executed in the order they are specified.

Basic syntax for multi-command chaining:
```
pdd [GLOBAL OPTIONS] COMMAND1 [OPTIONS] [ARGS]... [COMMAND2 [OPTIONS] [ARGS]...]...
```

This feature enables you to perform complex workflows efficiently. Here's an example of multi-command chaining:

```
pdd --output-cost usage.csv generate --output src/app.py app.prompt test --output tests/test_app.py src/app.py app.prompt example --output examples/app_example.py src/app.py
```

This command chain will:
1. Enable cost tracking and save the results to `usage.csv`
2. Generate code from `app.prompt` and save it to `src/app.py`
3. Create a test file for the generated code and save it to `tests/test_app.py`
4. Create an example file based on the generated code and save it to `examples/app_example.py`

## Getting Help

PDD provides comprehensive help features:

1. **General Help**:
   ```
   pdd --help
   ```
   Displays a list of available commands and options.

2. **Command-Specific Help**:
   ```
   pdd COMMAND --help
   ```
   Provides detailed help for a specific command, including available options and usage examples.

## Additional Features

- **Tab Completion**: PDD supports tab completion for commands and options in compatible shells. You can install tab completion by running:
  ```
  pdd --install-completion
  ```
- **Colorized Output**: PDD provides colorized output for better readability in compatible terminals.
- **Progress Indicators**: For long-running operations, PDD includes progress indicators to keep you informed of the task's status.

## Environment Variables for Output Paths

You can set environment variables to define default output paths for each command, reducing the need to specify output locations in the command line. The following environment variables are supported:

- **`PDD_GENERATE_OUTPUT_PATH`**: Default path for the `generate` command.
- **`PDD_EXAMPLE_OUTPUT_PATH`**: Default path for the `example` command.
- **`PDD_TEST_OUTPUT_PATH`**: Default path for the `test` command.
- **`PDD_PREPROCESS_OUTPUT_PATH`**: Default path for the `preprocess` command.
- **`PDD_FIX_TEST_OUTPUT_PATH`**: Default path for the fixed unit test files in the `fix` command.
- **`PDD_FIX_CODE_OUTPUT_PATH`**: Default path for the fixed code files in the `fix` command.
- **`PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH`**: Default path for the sub-prompts generated by the `split` command.
- **`PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH`**: Default path for the modified prompts generated by the `split` command.
- **`PDD_CHANGE_OUTPUT_PATH`**: Default path for the modified prompts generated by the `change` command.
- **`PDD_UPDATE_OUTPUT_PATH`**: Default path for the updated prompts generated by the `update` command.
- **`PDD_OUTPUT_COST_PATH`**: Default path for the cost tracking CSV file.

## Examples of Common Workflows

1. Preprocess a prompt file, generate code, create an example, and generate tests (using multi-command chaining):
```
pdd preprocess --output preprocessed/ --temperature 0.0 app_python.prompt generate --output src/app.py --temperature 0.0 preprocessed/app_python_preprocessed.prompt example --output examples/ --temperature 0.0 src/app.py test --output tests/ --language python --temperature 0.0 src/app.py app_python.prompt
```

2. Generate code and create examples for multiple prompt files (using multi-command chaining):
```
pdd generate --output src/api.py --temperature 0.0 api_python.prompt generate --output src/db.py --temperature 0.0 database_sql.prompt example --output examples/api_usage.py --temperature 0.0 src/api.py example --output examples/db_usage.py --temperature 0.0 src/db.py
```

3. Preprocess a prompt file and view the diff:
```
pdd preprocess --output preprocessed/app_python_preprocessed.prompt --diff --temperature 0.0 app_python.prompt
```

4. Preprocess a prompt file with XML delimiters inserted:
```
pdd preprocess --output preprocessed/app_python_preprocessed.xml --xml app_python.prompt
```

5. Preprocess multiple prompt files and generate code for each (using multi-command chaining):
```
pdd preprocess --output preprocessed/ --temperature 0.0 api_python.prompt preprocess --output preprocessed/ --temperature 0.0 db_sql.prompt generate --output src/ --temperature 0.0 preprocessed/api_python_preprocessed.prompt generate --output src/ --temperature 0.0 preprocessed/db_sql_preprocessed.prompt
```

6. Fix errors in code and unit tests:
```
pdd fix --output-test fixed/test_app_fixed.py --output-code fixed/app_fixed.py --temperature 0.0 tests/test_app.py src/app.py error_log.txt
```

Note: The error messages in the `error_log.txt` file come from pytest and the output of the LLMs, all piped into this error file.

7. Split a large prompt file into smaller prompt files:
```
pdd split --output-sub sub_prompts/sub_app_python.prompt --output-modified modified_prompts/modified_app_python.prompt --temperature 0.0 large_app_python.prompt related_code.py example_code.py
```

8. Change a prompt file based on new requirements:
```
pdd change --output modified_prompts/modified_app_python.prompt --temperature 0.0 app_python.prompt src/app.py "Add error handling for network connections"
```

9. Update a prompt file based on modified code:
```
pdd update --output modified_prompts/modified_app_python.prompt --temperature 0.0 app_python.prompt src/original_app.py src/modified_app.py
```

10. Generate code with cost tracking:
```
pdd --output-cost cost_reports/usage.csv generate --output src/app.py --temperature 0.0 app_python.prompt
```

11. Run multiple commands with cost tracking:
```
pdd --output-cost cost_reports/usage.csv generate --output src/app.py app_python.prompt test --output tests/ --language python src/app.py app_python.prompt
```

12. Fix errors in code and unit tests with iterative process:
```
pdd fix --loop --verification-program verify_code.py --max-attempts 3 --budget 5.0 --output-test tests/test_app_fixed.py --output-code src/app_fixed.py --temperature 0.0 tests/test_app.py src/app.py error_log.txt
```

This example attempts to fix errors in `test_app.py` and `app.py` through multiple iterations. It uses `verify_code.py` to check if the code runs correctly after each fix attempt, with a maximum of 3 attempts and a budget of $5.0. The fixed files are saved as `test_app_fixed.py` and `app_fixed.py` respectively.

13. Force overwrite of existing files:
```
pdd --force generate --output src/existing_app.py app_python.prompt
```

This example generates code from `app_python.prompt` and saves it to `src/existing_app.py`, overwriting the file if it already exists without asking for confirmation.

## Conclusion

PDD (Prompt-Driven Development) CLI provides a comprehensive set of tools for managing prompt files, generating code, creating examples, and running tests. By leveraging the power of AI models and iterative processes, PDD aims to streamline the development workflow and improve code quality.

The various commands and options allow for flexible usage, from simple code generation to complex workflows involving multiple steps. The ability to track costs and manage output locations through environment variables further enhances the tool's utility in different development environments.

Remember to use the help command (`pdd --help` or `pdd COMMAND --help`) for more detailed information on each command and its options. As you become more familiar with PDD, you can create more complex workflows by chaining multiple commands and utilizing the full range of options available.

Happy coding with PDD!