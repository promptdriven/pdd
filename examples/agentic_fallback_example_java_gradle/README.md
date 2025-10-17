# Agentic Fallback Example (Java)

This example demonstrates the use of agentic fallback to resolve dependencies between code files during automated debugging.

## Project Structure

The source project consists of two separate Java files:

- `src/main/java/Main.java`: The main application logic.
- `src/main/java/Util.java`: A utility module that `Main.java` depends on.

The error in `Main.java` is due to a dependency on `Util.java`. It cannot be fixed without reading and understanding the contents of `Util.java`.

## Agentic Fallback

Agentic fallback is a feature that allows the debugging agent to read files across different development units to resolve dependencies. This is crucial in scenarios where a fix in one file requires context from another.

## Running the Example

### Using the `fix` command
To fix the error in `Main.java` using agentic fallback, you would typically run a command that invokes a CLI agent. The exact command depends on the tool you are using. For example, with `pdd`, the command would look something like this:

```bash
pdd fix examples/agentic_fallback_example_java_gradle/main_java.prompt \
        examples/agentic_fallback_example_java_gradle/src/main/java/Main.java \
        examples/agentic_fallback_example_java_gradle/src/test/java/TestMain.java \
        examples/agentic_fallback_example_java_gradle/error.log \
        --loop --max-attempts 2 \
        --verification-program examples/agentic_fallback_example_java_gradle/src/test/java/TestMain.java
```

This command will invoke a CLI agent that will use agentic fallback to read `Util.java`, understand the dependency, and fix the error in `Main.java`.

### Using the `crash` command

Alternatively, you can use the `crash` command. First, run the program to generate an error log:

```bash
cd examples/agentic_fallback_example_java_gradle && ./gradlew -q run --console=plain 2> crash_error.log; cd -
```

Then, run the following command:

```bash
pdd crash --loop examples/agentic_fallback_example_java_gradle/util_java.prompt examples/agentic_fallback_example_java_gradle/src/main/java/Util.java examples/agentic_fallback_example_java_gradle/src/main/java/Main.java examples/agentic_fallback_example_java_gradle/crash_error.log
```

This command will also invoke a CLI agent to fix the error.
