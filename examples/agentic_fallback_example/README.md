# Agentic Fallback Example

This example demonstrates the use of agentic fallback to resolve dependencies between code files during automated debugging.

## Project Structure

The source project consists of two separate Python files:

- `src/main.py`: The main application logic.
- `src/utils.py`: A utility module that `main.py` depends on.

The error in `main.py` is due to a dependency on `utils.py`. It cannot be fixed without reading and understanding the contents of `utils.py`.

## Agentic Fallback

Agentic fallback is a feature that allows the debugging agent to read files across different development units to resolve dependencies. This is crucial in scenarios where a fix in one file requires context from another.

## Running the Example

To fix the error in `main.py` using agentic fallback, run the following command:

```bash
pdd fix examples/agentic_fallback_example/main_python.prompt examples/agentic_fallback_example/src/main.py examples/agentic_fallback_example/tests/test_main.py examples/agentic_fallback_example/error.log --loop --max-attempts 2 --agentic-fallback --verification-program examples/agentic_fallback_example/tests/test_main.py
```

This command will invoke a CLI agent (such as Claude, Gemini, or Codex) that will use agentic fallback to read `utils.py`, understand the dependency, and fix the error in `main.py`.
