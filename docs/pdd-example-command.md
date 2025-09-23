# PDD Example Command - Usage Guide

## Overview

The `pdd example` command generates comprehensive, self-contained example code that demonstrates how to use functionality defined in a prompt. It creates well-documented, executable scripts that serve as practical usage guides.

## Command Syntax

```bash
pdd example [OPTIONS] PROMPT_FILE CODE_FILE
```

### Options

- `--output PATH` - Specify where to save the generated example code (file or directory)
- `--help` - Show help message

## Quick Start Example

### Step 1: Navigate to Example Directory

```bash
cd examples/hello
```

### Step 2: Set Up API Key

```bash
export GEMINI_API_KEY=your_api_key_here
```

### Step 3: Run Example Command

```bash
# Using default output path
pdd example hello_python.prompt pdd/hello.py

# Using custom output path
pdd example hello_python.prompt pdd/hello.py --output my_example.py
```

## Input Files

### Prompt File (`hello_python.prompt`)
```
write a python function 'hello' that prints "hello"
```

### Generated Code File (`pdd/hello.py`)
```python
def hello() -> None:
    """
    Prints the string "hello" to the standard output.

    This function takes no arguments and has no return value (implicitly returns None).
    Its sole side effect is printing the literal string "hello" to the console,
    followed by a newline character.
    """
    print("hello")
```

## Generated Output

### Default Output Path
- **Pattern**: `{basename}_example{ext}`
- **Example**: `hello_example.py`
- **Location**: Same directory as prompt file

### Generated Example Content

The command creates a comprehensive example file with the following structure:

```python
"""
This script provides a clear example of how to define and use a simple function.
It combines the definition of a `hello` function and a script to run it
into a single, self-contained, and runnable file.
"""

def hello() -> None:
    """
    Prints the string "hello" to the standard output.

    This function takes no arguments and has no return value (implicitly returns None).
    Its sole side effect is printing the literal string "hello" to the console,
    followed by a newline character.
    """
    print("hello")

def run_example() -> None:
    """
    Demonstrates the proper usage of the `hello` function.

    This function serves as a wrapper for the example call, making the script's
    purpose clear.
    """
    print("Calling the `hello` function...")

    # Call the function. It takes no arguments and its only action
    # is to print "hello" to the console.
    hello()


# The `if __name__ == "__main__"` block is standard Python practice.
# It ensures the code inside only runs when the script is executed directly.
if __name__ == "__main__":
    run_example()
```

## Example Structure Analysis

### 1. Header Documentation
- Clear description of what the example demonstrates
- Brief overview of the script's purpose

### 2. Function Definition
- Original function with comprehensive docstring
- Type hints and proper Python practices
- Clear parameter and return documentation

### 3. Usage Demonstration
- `run_example()` function showing how to use the original function
- Step-by-step demonstration with explanatory comments
- Clear output messages

### 4. Executable Structure
- Proper `if __name__ == "__main__"` block
- Self-contained and runnable script
- Standard Python practices

## Running the Generated Example

```bash
python hello_example.py
```

**Expected Output:**
```
Calling the `hello` function...
hello
...function call complete.
```

## Output Path Resolution

The command uses the following priority order for determining output location:

1. **User-specified path** (`--output` parameter)
2. **Context configuration** (`.pddrc` file settings)
3. **Environment variables** (`PDD_EXAMPLE_OUTPUT_PATH`)
4. **Default naming** (`{basename}_example{ext}` in current directory)

## Configuration Options

### Environment Variables
- `PDD_EXAMPLE_OUTPUT_PATH` - Default path for example files

### Context Configuration (.pddrc)
```yaml
contexts:
  my_context:
    defaults:
      example_output_path: "examples/"
```

## API Requirements

The command requires an LLM API key for generation:
- **Gemini**: Set `GEMINI_API_KEY` environment variable
- **OpenAI**: Set `OPENAI_API_KEY` environment variable
- **Other providers**: See PDD documentation for supported models

## Troubleshooting

### Common Issues

1. **API Key Not Set**
   ```
   Error: API key environment variable 'GEMINI_API_KEY' for model 'gemini/gemini-2.5-pro' is not set.
   ```
   **Solution**: Set the appropriate API key environment variable

2. **Rate Limiting**
   ```
   Error: You exceeded your current quota, please check your plan and billing details.
   ```
   **Solution**: Wait for quota reset or upgrade your API plan

3. **File Not Found**
   ```
   Error: No such file or directory: 'prompt_file.prompt'
   ```
   **Solution**: Verify file paths are correct

### Verification Steps

1. **Check API Key**: `echo $GEMINI_API_KEY`
2. **Verify Files**: `ls -la prompt_file.prompt code_file.py`
3. **Test Command**: `pdd example --help`
4. **Run Example**: `python generated_example.py`

## Best Practices

1. **Use Descriptive Names**: Choose clear, descriptive names for your prompt files
2. **Organize Output**: Use `--output` to organize examples in dedicated directories
3. **Version Control**: Commit generated examples to track changes over time
4. **Test Examples**: Always run generated examples to verify they work
5. **Document Context**: Use `.pddrc` files for project-specific configurations

## Related Commands

- `pdd generate` - Generate code from prompts
- `pdd test` - Generate unit tests
- `pdd sync` - Complete workflow automation
- `pdd --help` - Show all available commands
