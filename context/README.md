# PDD (Prompt-Driven Development) CLI

PDD is a versatile tool for generating code, examples, and unit tests from prompts or existing code files. It also offers features for prompt management and preprocessing.

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
- `--strength FLOAT`: Set the strength of the AI model (0.0 to 1.0, default is 0.5).
- `--verbose`: Increase output verbosity for more detailed information.
- `--quiet`: Decrease output verbosity for minimal information.

## Commands

Here are the main commands:

### 1. Generate

Create runnable code from a prompt file.

```
pdd generate [OPTIONS] PROMPT_FILE
```

Options:
- `--output LOCATION`: Specify where to save the generated code. Can be a filename, full path, or directory. Default file name is <basename>.<language_file_extension>

### 2. Example

Create an example file from an existing code file.

```
pdd example [OPTIONS] CODE_FILE
```

Options:
- `--output LOCATION`: Specify where to save the generated example code. Can be a filename, full path, or directory. Default file name is <basename>_example.<language_file_extension>

### 3. Test

Generate a unit test file for a given code file and its corresponding prompt.

```
pdd test [OPTIONS] CODE_FILE PROMPT_FILE
```

Options:
- `--output LOCATION`: Specify where to save the generated test file. Can be a filename, full path, or directory. Default file name is <basename>_test.<language_file_extension>
- `--language`: Specify the programming language. Defaults to language specified by the prompt file name.

### 4. Preprocess

Preprocess prompts and save the results.

```
pdd preprocess [OPTIONS] PROMPT_FILE
```

Options:
- `--output LOCATION`: Specify where to save the preprocessed prompt. Can be a filename, full path, or directory. Default file name is <basename>_<language>_preprocessed.prompt
- `--diff`: Show diff between original and preprocessed prompts.

### 5. Fix

Fix errors in code and unit test based on error messages.

```
pdd fix [OPTIONS] UNIT_TEST_FILE CODE_FILE ERROR_FILE
```

Options:
- `--output-test LOCATION`: Specify where to save the fixed unit test file. Can be a filename, full path, or directory. Default file name is <basename>_fixed_test.<language_file_extension>
- `--output-code LOCATION`: Specify where to save the fixed code file. Can be a filename, full path, or directory. Default file name is <basename>_fixed.<language_file_extension>

This command attempts to fix errors in both the unit test and the code being tested. It uses the provided error file to understand the issues and generate appropriate fixes. The command produces two output files: one for the fixed unit test and another for the fixed code.

## Output Location Specification

For all commands that generate or modify files, the `--output` option allows flexible specification of the output location:

1. Filename only: If you provide just a filename (e.g., `--output result.py`), the file will be created in the current working directory.
2. Full path: If you provide a full path (e.g., `--output /home/user/projects/result.py`), the file will be created at that exact location.
3. Directory: If you provide a directory name (e.g., `--output ./generated/`), a file with an automatically generated name will be created in that directory.

If the `--output` option is not provided, PDD will use default naming conventions and save the file in the current working directory.

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

- Tab completion for commands and options in compatible shells (use `pdd --install-completion`).
- Colorized output for better readability.
- Progress indicators for long-running operations.

## Examples of Common Workflows

1. Preprocess a prompt, generate code, create an example, and generate tests (using multi-command chaining):
```
pdd preprocess --output preprocessed/ app_python.prompt generate --output src/app.py preprocessed/app_python_preprocessed.prompt example --output examples/ src/app.py test --output tests/ --language python src/app.py app_python.prompt
```

2. Generate code and create examples for multiple prompts (using multi-command chaining):
```
pdd generate --output src/api.py api_python.prompt generate --output src/db.py database_sql.prompt example --output examples/api_usage.py src/api.py example --output examples/db_usage.py src/db.py
```

3. Preprocess a prompt and view the diff:
```
pdd preprocess --output preprocessed/app_python_preprocessed.prompt --diff app_python.prompt
```

4. Preprocess multiple prompts and generate code for each (using multi-command chaining):
```
pdd preprocess --output preprocessed/ api_python.prompt preprocess --output preprocessed/ db_sql.prompt generate --output src/ preprocessed/api_python_preprocessed.prompt generate --output src/ preprocessed/db_sql_preprocessed.prompt
```

5. Fix errors in code and unit tests:
```
pdd fix --output-test fixed/test_app_fixed.py --output-code fixed/app_fixed.py --strength 0.7 tests/test_app.py src/app.py error_log.txt
```

This example fixes errors in the `test_app.py` unit test and the `app.py` code file, using the error messages from `error_log.txt`. The fixed unit test is saved as `test_app_fixed.py`, and the fixed code is saved as `app_fixed.py`, both in the `fixed/` directory.