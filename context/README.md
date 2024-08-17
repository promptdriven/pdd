# PDD (Prompt-Driven Development) CLI

PDD is a versatile tool for generating code, examples, unit tests, and managing prompts through various features like splitting large prompts into smaller ones.

## Prompt File Naming Convention

Prompt files in PDD follow this specific naming format:
```
<basename>_<language>.prompt
```
Where:
- `<basename>` is the base name of the file or project
- `<language>` is the programming language or context of the prompt

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

## Commands

Here are the main commands:

### 1. Generate

Create runnable code from a prompt file.

```
pdd generate [GLOBAL OPTIONS] [OPTIONS] PROMPT_FILE
```

Options:
- `--output LOCATION`: Specify where to save the generated code. If an environment variable `PDD_GENERATE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

### 2. Example

Create an example file from an existing code file.

```
pdd example [GLOBAL OPTIONS] [OPTIONS] CODE_FILE
```

Options:
- `--output LOCATION`: Specify where to save the generated example code. If an environment variable `PDD_EXAMPLE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

### 3. Test

Generate a unit test file for a given code file and its corresponding prompt.

```
pdd test [GLOBAL OPTIONS] [OPTIONS] CODE_FILE PROMPT_FILE
```

Options:
- `--output LOCATION`: Specify where to save the generated test file. If an environment variable `PDD_TEST_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--language`: Specify the programming language. Defaults to the language specified by the prompt file name.

### 4. Preprocess

Preprocess prompts and save the results.

```
pdd preprocess [GLOBAL OPTIONS] [OPTIONS] PROMPT_FILE
```

Options:
- `--output LOCATION`: Specify where to save the preprocessed prompt. If an environment variable `PDD_PREPROCESS_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--diff`: Show diff between original and preprocessed prompts.
- `--xml`: Automatically insert XML delimiters for long and complex prompts to structure the content better.

### 5. Fix

Fix errors in code and unit tests based on error messages.

```
pdd fix [GLOBAL OPTIONS] [OPTIONS] UNIT_TEST_FILE CODE_FILE ERROR_FILE
```

Options:
- `--output-test LOCATION`: Specify where to save the fixed unit test file. If an environment variable `PDD_FIX_TEST_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--output-code LOCATION`: Specify where to save the fixed code file. If an environment variable `PDD_FIX_CODE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

### 6. Split

Split large complex prompts into smaller, more manageable prompts.

```
pdd split [GLOBAL OPTIONS] [OPTIONS] INPUT_PROMPT INPUT_CODE EXAMPLE_CODE
```

Options:
- `--output-sub LOCATION`: Specify where to save the generated sub-prompt. If an environment variable `PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--output-modified LOCATION`: Specify where to save the modified prompt. If an environment variable `PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--output-cost LOCATION`: Specify where to save the cost estimation report. If an environment variable `PDD_SPLIT_COST_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

## Output Location Specification

For all commands that generate or modify files, the `--output` option (or its variant, such as `--output-sub`, `--output-modified`, or `--output-cost` for the `split` command) allows flexible specification of the output location:

1. **Filename only**: If you provide just a filename (e.g., `--output result.py`), the file will be created in the current working directory.
2. **Full path**: If you provide a full path (e.g., `--output /home/user/projects/result.py`), the file will be created at that exact location.
3. **Directory**: If you provide a directory name (e.g., `--output ./generated/`), a file with an automatically generated name will be created in that directory.
4. **Environment Variable**: If the `--output` option is not provided, and an environment variable specific to the command (`PDD_GENERATE_OUTPUT_PATH`, `PDD_EXAMPLE_OUTPUT_PATH`, `PDD_TEST_OUTPUT_PATH`, `PDD_PREPROCESS_OUTPUT_PATH`, `PDD_FIX_TEST_OUTPUT_PATH`, `PDD_FIX_CODE_OUTPUT_PATH`, `PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH`, `PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH`, `PDD_SPLIT_COST_OUTPUT_PATH`) is set, PDD will use the path specified by this variable. Otherwise, it will use default naming conventions and save the file in the current working directory.

## Multi-Command Chaining

PDD supports multi-command chaining, allowing you to execute multiple commands in a single line. Commands will be executed in the order they are specified.

Basic syntax for multi-command chaining:
```
pdd [GLOBAL OPTIONS] COMMAND1 [OPTIONS] [ARGS]... [COMMAND2 [OPTIONS] [ARGS]...]...
```

This feature enables you to perform complex workflows efficiently.

## Getting Help

For general help:
```
pdd --help
```

For help on a specific command:
```
pdd COMMAND --help
```

## Additional Features

- **Tab Completion**: PDD supports tab completion for commands and options in compatible shells. Install tab completion by running:
  ```
  pdd --install-completion
  ```
- **Colorized Output**: For better readability, PDD provides colorized output in compatible terminals.
- **Progress Indicators**: Long-running operations include progress indicators to keep you informed of the task status.

## Examples of Common Workflows

1. Preprocess a prompt, generate code, create an example, and generate tests (using multi-command chaining):
```
pdd preprocess --output preprocessed/ --temperature 0.0 app_python.prompt generate --output src/app.py --temperature 0.0 preprocessed/app_python_preprocessed.prompt example --output examples/ --temperature 0.0 src/app.py test --output tests/ --language python --temperature 0.0 src/app.py app_python.prompt
```

2. Generate code and create examples for multiple prompts (using multi-command chaining):
```
pdd generate --output src/api.py --temperature 0.0 api_python.prompt generate --output src/db.py --temperature 0.0 database_sql.prompt example --output examples/api_usage.py --temperature 0.0 src/api.py example --output examples/db_usage.py --temperature 0.0 src/db.py
```

3. Preprocess a prompt and view the diff:
```
pdd preprocess --output preprocessed/app_python_preprocessed.prompt --diff --temperature 0.0 app_python.prompt
```

4. Preprocess a prompt with XML delimiters inserted:
```
pdd preprocess --output preprocessed/app_python_preprocessed.xml --xml app_python.prompt
```

5. Preprocess multiple prompts and generate code for each (using multi-command chaining):
```
pdd preprocess --output preprocessed/ --temperature 0.0 api_python.prompt preprocess --output preprocessed/ --temperature 0.0 db_sql.prompt generate --output src/ --temperature 0.0 preprocessed/api_python_preprocessed.prompt generate --output src/ --temperature 0.0 preprocessed/db_sql_preprocessed.prompt
```

6. Fix errors in code and unit tests:
```
pdd fix --output-test fixed/test_app_fixed.py --output-code fixed/app_fixed.py --strength 0.7 --temperature 0.0 tests/test_app.py src/app.py error_log.txt
```

7. Split a large prompt into smaller prompts:
```
pdd split --output-sub sub_prompts/sub_app_python.prompt --output-modified modified_prompts/modified_app_python.prompt --output-cost cost_reports/cost_app_python.txt --strength 0.8 --temperature 0.0 large_app_python.prompt related_code.py example_code.py
```

This example splits a large prompt (`large_app_python.prompt`) into smaller sub-prompts and modifies the original prompt accordingly. The sub-prompt is saved in the `sub_prompts/` directory, the modified prompt is saved in the `modified_prompts/` directory, and a cost estimation report is saved in the `cost_reports/` directory.

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
- **`PDD_SPLIT_COST_OUTPUT_PATH`**: Default path for the cost estimation reports generated by the `split` command.

If these environment variables are set, the corresponding files will be saved to the specified paths by default unless overridden by the `--output`, `--output-sub`, `--output-modified`, or `--output-cost` options.