# PDD (Prompt-Driven Development) CLI

PDD is a versatile tool for generating code, examples, and unit tests from prompts or existing code files. It also offers features for prompt management, consistency checking, and preprocessing.

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
- `--preprocess`: View the preprocessed prompt before generating code.

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

View, manage, and transform preprocessed prompts. This command has three subcommands:

```
pdd preprocess [SUBCOMMAND] [OPTIONS] PROMPT_FILES...
```

Subcommands:
- `view`: Show preprocessed prompts.
- `apply`: Apply preprocessing to prompts.
- `xml`: Generate XML versions of prompts.

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
pdd generate app_prompt.prompt --output src/app.py example src/app.py --example-output examples/usage.py test src/app.py app_prompt.prompt --test-output tests/
```

2. Preprocess prompts, check consistency, and modify them:
```
pdd preprocess view prompt1.prompt prompt2.prompt --diff check prompt1.prompt prompt2.prompt modify prompt1.prompt prompt2.prompt --changes "Update API" --apply
```

3. Split a prompt, generate code from sub-prompts, and create examples:
```
pdd split complex_prompt.prompt --sub-prompt-output sub_prompt.prompt generate sub_prompt.prompt --output src/module.py example src/module.py
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

1. Generate code with preprocessing, create an example, and run tests:
```
pdd generate app_prompt.prompt --output src/app.py --preprocess example src/app.py --example-output examples/usage.py test src/app.py app_prompt.prompt --test-output tests/
```

2. Check consistency between prompts, view preprocessed versions, and modify:
```
pdd check prompt1.prompt prompt2.prompt preprocess view prompt1.prompt prompt2.prompt --diff modify prompt1.prompt prompt2.prompt --changes "Update API endpoint" --apply
```

3. Split a complex prompt, generate code from sub-prompts, and create XML versions:
```
pdd split complex_prompt.prompt --sub-prompt-output sub_prompt.prompt generate sub_prompt.prompt --output src/module.py preprocess xml sub_prompt.prompt --output xml_prompts/
```

4. Modify prompts, check consistency, and generate new code:
```
pdd modify prompt1.prompt prompt2.prompt --changes "Update feature" --apply check prompt1.prompt prompt2.prompt generate prompt1.prompt --output src/updated_app.py
```

5. Preprocess prompts, generate code, and create examples in one command:
```
pdd preprocess apply prompt1.prompt prompt2.prompt generate prompt1.prompt --output src/app1.py generate prompt2.prompt --output src/app2.py example src/app1.py example src/app2.py
```