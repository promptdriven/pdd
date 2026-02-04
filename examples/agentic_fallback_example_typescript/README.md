# Agentic Fallback Example (TypeScript)

This example demonstrates the use of agentic fallback to resolve dependencies between code files during automated debugging.

## Project Structure

The source project consists of two separate TypeScript files:

- `src/main.ts`: The main application logic.
- `src/utils.ts`: A utility module that `main.ts` depends on.

The error in `main.ts` is due to a dependency on `utils.ts`. It cannot be fixed without reading and understanding the contents of `utils.ts`.

## Agentic Fallback

Agentic fallback is a feature that allows the debugging agent to read files across different development units to resolve dependencies. This is crucial in scenarios where a fix in one file requires context from another.

## Running the Example

### Using the `fix` command
To fix the error in `main.ts` using agentic fallback, you would typically run a command that invokes a CLI agent. The exact command depends on the tool you are using. For example, with `pdd`, the command would look something like this:

```bash
pdd fix examples/agentic_fallback_example_typescript/main_typescript.prompt \
        examples/agentic_fallback_example_typescript/src/main.ts \
        examples/agentic_fallback_example_typescript/tests/test_main.ts \
        examples/agentic_fallback_example_typescript/error.log \
        --loop --max-attempts 2 \
        --verification-program examples/agentic_fallback_example_typescript/tests/test_main.ts
```

This command will invoke a CLI agent that will use agentic fallback to read `utils.ts`, understand the dependency, and fix the error in `main.ts`.

### Using the `crash` command

Alternatively, you can use the `crash` command. First, run the program to generate an error log:

```bash
ts-node examples/agentic_fallback_example_typescript/src/main.ts 2> examples/agentic_fallback_example_typescript/crash_error.log
```

Then, run the following command:

```bash
pdd crash --loop examples/agentic_fallback_example_typescript/main_typescript.prompt examples/agentic_fallback_example_typescript/src/main.ts examples/agentic_fallback_example_typescript/src/main.ts examples/agentic_fallback_example_typescript/crash_error.log
```

This command will also invoke a CLI agent to fix the error.

### Using the `verify` command

You can also use the `verify` command to check the code against the prompt and fix it if there are issues.

```bash
pdd verify examples/agentic_fallback_example_typescript/main_typescript.prompt examples/agentic_fallback_example_typescript/src/main.ts examples/agentic_fallback_example_typescript/src/main.ts
```
