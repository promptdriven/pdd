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

To fix the error in `main.ts` using agentic fallback, you would typically run a command that invokes a CLI agent. The exact command depends on the tool you are using. For example, with `pdd`, the command would look something like this:

```bash
pdd fix examples/agentic_fallback_example_typescript/main_ts.prompt \
        examples/agentic_fallback_example_typescript/src/main.ts \
        examples/agentic_fallback_example_typescript/tests/test_main.ts \
        examples/agentic_fallback_example_typescript/error.log \
        --loop --max-attempts 2 \
        --verification-program examples/agentic_fallback_example_typescript/tests/test_main.ts
```

This command will invoke a CLI agent that will use agentic fallback to read `utils.ts`, understand the dependency, and fix the error in `main.ts`.
