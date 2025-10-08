# Agentic Fallback Example (Java)

This example demonstrates the use of agentic fallback to resolve dependencies between code files during automated debugging.

## Project Structure

The source project consists of two separate Java files:

- `src/Main.java`: The main application logic.
- `src/Utils.java`: A utility module that `Main.java` depends on.

The error in `Main.java` is due to a dependency on `Utils.java`. It cannot be fixed without reading and understanding the contents of `Utils.java`.

## Agentic Fallback

Agentic fallback is a feature that allows the debugging agent to read files across different development units to resolve dependencies. This is crucial in scenarios where a fix in one file requires context from another.

## Running the Example

To fix the error in `Main.java` using agentic fallback, you would typically run a command that invokes a CLI agent. The exact command depends on the tool you are using. For example, with `pdd`, the command would look something like this:

```bash
pdd fix examples/agentic_fallback_example_java/main_java.prompt \
        examples/agentic_fallback_example_java/src/Main.java \
        examples/agentic_fallback_example_java/tests/TestMain.java \
        examples/agentic_fallback_example_java/error.log \
        --loop --max-attempts 2 \
        --verification-program examples/agentic_fallback_example_java/tests/TestMain.java
```

This command will invoke a CLI agent that will use agentic fallback to read `Utils.java`, understand the dependency, and fix the error in `Main.java`.
