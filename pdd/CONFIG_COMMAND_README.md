# PDD `config` Command

The `pdd config` command is a utility for creating project-specific configurations for the PDD CLI. It allows you to define which LLM providers and API keys should be used for all `pdd` commands run within a specific directory.

This is useful when you are working on multiple projects that require different sets of API keys or models, as it allows you to create a local configuration that overrides the global `~/.pdd/` setup.

## Command Syntax

```sh
pdd config [DIRECTORY]
```

-   `DIRECTORY` (optional): The path to the directory where the configuration should be created. If omitted, the configuration will be created in the current working directory.

## What it Does

Running the command performs the following actions:

1.  **Creates a `.pdd` Directory**: It creates a hidden directory named `.pdd` in the specified location (or the current directory).

2.  **Discovers API Keys**: The command scans your shell's environment variables for any variables that end with `_API_KEY` (e.g., `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`).

3.  **Interactive Selection**:
    -   If API keys are found, it will ask you one by one if you want to include them in the project's configuration.
    -   If no API keys are found, or if you decline all discovered keys, it will ask if you want to enter API keys manually.

4.  **Generates Configuration Files**: Based on your selections, it creates two files inside the `.pdd` directory:
    -   `llm_model.csv`: This file is a filtered version of the master model list, containing only the models that correspond to the API keys you selected.
    -   `api-env`: This is a shell script that exports the selected API keys as environment variables.

## How to Use

1.  Navigate to your project's root directory.
2.  Run the command:
    ```sh
    pdd config
    ```
3.  Follow the interactive prompts to select or enter your desired API keys.
4.  Once the command finishes, you can source the generated environment file to load the keys into your current shell session:
    ```sh
    source .pdd/api-env
    ```

Now, any `pdd` command you run from within this directory will use the models and keys defined in the local `.pdd` configuration.
