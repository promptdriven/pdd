# PDD (Prompt-Driven Development) CLI

PDD is a versatile tool for generating code, examples, and unit tests from prompts or existing code files. It also offers features for prompt management, consistency checking, and preprocessing.

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
pdd [GLOBAL OPTIONS] COMMAND1 [ARGS]... [COMMAND2 [ARGS]...]...
```

## Global Options

These options can be used with any command:

- `--force`: Overwrite existing files without asking for confirmation.
- `--strength FLOAT`: Set the strength of the AI model (0.0 to 1.0, default is 0.5).
- `--verbose`: Increase output verbosity for more detailed information.
- `--quiet`: Decrease output verbosity for minimal information.
- `--no-preprocess`: Skip the default preprocessing step (use with caution).

## Default Preprocessing

By default, PDD automatically preprocesses prompts for all commands that use prompt files. This ensures consistency and optimizes the prompts for better results. If you need to skip preprocessing for any reason, use the `--no-preprocess` global option.

## Commands

PDD supports multi-command chaining, allowing you to execute multiple commands in a single line. Commands will be executed in the order they are specified.

### 1. Generate

Create runnable code and/or example code from a prompt file.

```
pdd generate [OPTIONS] PROMPT_FILE
```

Options:
- `--output FILE`: Specify where to save the generated runnable code.
- `--example-output FILE`: Specify where to save the generated example code.

### 2. Example

Create an example file from an existing code file.

```
pdd example [OPTIONS] CODE_FILE
```

Options:
- `--example-output FILE`: Specify where to save the generated example code.

### 3. Test

Generate a unit test file for a given code file and its corresponding prompt.

```
pdd test [OPTIONS] CODE_FILE PROMPT_FILE
```

Options:
- `--test-output DIRECTORY`: Specify where to save the generated test file.
- `--language [python|javascript|java|cpp]`: Specify the programming language.

### 4. Split

Divide a prompt into smaller sub-prompts.

```
pdd split [OPTIONS] PROMPT_FILE CODE_FILE EXAMPLE_FILE
```

Options:
- `--sub-prompt-output FILE`: Specify where to save the generated sub-prompt.
- `--modified-prompt-output FILE`: Specify where to save the modified main prompt.

### 5. Check

Verify consistency between different prompts.

```
pdd check [OPTIONS] PROMPT_FILES...
```

Options:
- `--output FILE`: Save the consistency report to a file.

### 6. Preprocess

Explicitly preprocess prompts. This command is mainly used for viewing or debugging the preprocessing step, as preprocessing happens automatically for other commands.

```
pdd preprocess [SUBCOMMAND] [OPTIONS] PROMPT_FILES...
```

Subcommands:
- `view`: Show preprocessed prompts.
- `apply`: Apply preprocessing to prompts and save the results.
- `xml`: Generate XML versions of prompts.

Options for `view` and `apply`:
- `--diff`: Show diff between original and preprocessed prompts.
- `--output FILE`: Save preprocessed prompts or diff to a file.

Options for `xml`:
- `--output DIRECTORY`: Specify where to save the XML versions of prompts.
- `--schema FILE`: Use a custom XML schema file.

### 7. Modify

Make changes to prompts and identify which prompts need modification.

```
pdd modify [OPTIONS] PROMPT_FILES...
```

Options:
- `--changes TEXT`: Specify the changes to apply to prompts.
- `--diff`: Show a preview of the proposed changes.
- `--apply`: Apply the proposed changes to the prompts.
- `--output FILE`: Save the modified prompts or diff to a file.

## Multi-Command Chaining

PDD allows you to chain multiple commands in a single invocation. This feature enables you to perform complex workflows efficiently. Commands are executed in the order they are specified.

Examples of multi-command chaining:

1. Generate code, create an example, and run tests in one go:
```
pdd generate app_python.prompt --output src/app.py example src/app.py --example-output examples/usage.py test src/app.py app_python.prompt --test-output tests/
```

2. Check consistency between prompts, modify them, and generate new code:
```
pdd check api_python.prompt database_sql.prompt modify api_python.prompt database_sql.prompt --changes "Update API" --apply generate api_python.prompt --output src/updated_api.py
```

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

- Tab completion for commands and options in compatible shells.
- Colorized output for better readability.
- Progress indicators for long-running operations.

## Examples of Common Workflows

1. Generate code, create an example, and run tests (with default preprocessing):
```
pdd generate app_python.prompt --output src/app.py example src/app.py --example-output examples/usage.py test src/app.py app_python.prompt --test-output tests/
```

2. Check consistency between prompts, modify them, and generate new code (skipping preprocessing):
```
pdd --no-preprocess check api_python.prompt database_sql.prompt modify api_python.prompt database_sql.prompt --changes "Update API endpoint" --apply generate api_python.prompt --output src/updated_api.py
```

3. Split a complex prompt and generate code from sub-prompts:
```
pdd split complex_python.prompt --sub-prompt-output module_python.prompt generate module_python.prompt --output src/module.py
```

4. View the results of preprocessing without applying changes:
```
pdd preprocess view app_python.prompt utils_python.prompt --diff
```

5. Generate code and create examples for multiple prompts:
```
pdd generate api_python.prompt --output src/api.py generate database_sql.prompt --output src/db.py example src/api.py example src/db.py
```