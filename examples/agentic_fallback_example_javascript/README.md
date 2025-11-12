# Agentic Fallback Example (JavaScript)

This example demonstrates the use of agentic fallback to resolve dependencies between code files during automated debugging.

## Project Structure

The source project consists of two separate JavaScript files:

- `src/main.js`: The main application logic.
- `src/utils.js`: A utility module that `main.js` depends on.

The error in `main.js` is due to a dependency on `utils.js`. It cannot be fixed without reading and understanding the contents of `utils.js`.

## Agentic Fallback

Agentic fallback is a feature that allows the debugging agent to read files across different development units to resolve dependencies. This is crucial in scenarios where a fix in one file requires context from another.

## Running the Example

### Using the `fix` command
To fix the error in `main.js` using agentic fallback, you would typically run a command that invokes a CLI agent. The exact command depends on the tool you are using. For example, with `pdd`, the command would look something like this:

```bash
pdd fix examples/agentic_fallback_example_javascript/main_javascript.prompt \
        examples/agentic_fallback_example_javascript/src/main.js \
        examples/agentic_fallback_example_javascript/tests/test_main.js \
        examples/agentic_fallback_example_javascript/error.log \
        --loop --max-attempts 2 \
        --verification-program examples/agentic_fallback_example_javascript/tests/test_main.js
```

This command will invoke a CLI agent that will use agentic fallback to read `utils.js`, understand the dependency, and fix the error in `main.js`.

### Using the `crash` command

Alternatively, you can use the `crash` command. First, run the program to generate an error log:

```bash
node examples/agentic_fallback_example_javascript/src/main.js 2> examples/agentic_fallback_example_javascript/crash_error.log
```

Then, run the following command:

```bash
pdd crash --loop examples/agentic_fallback_example_javascript/main_javascript.prompt examples/agentic_fallback_example_javascript/src/main.js examples/agentic_fallback_example_javascript/src/main.js examples/agentic_fallback_example_javascript/crash_error.log
```

This command will also invoke a CLI agent to fix the error.

### Using the `verify` command

You can also use the `verify` command to check the code against the prompt and fix it if there are issues.

```bash
pdd verify examples/agentic_fallback_example_javascript/main_javascript.prompt examples/agentic_fallback_example_javascript/src/main.js examples/agentic_fallback_example_javascript/src/main.js
```
