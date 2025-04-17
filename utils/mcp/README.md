# PDD CLI - MCP Server

[![PyPI version](https://badge.fury.io/py/pdd-mcp-server.svg)](https://badge.fury.io/py/pdd-mcp-server)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

**Integrate the power of Prompt-Driven Development (PDD) into your agentic workflows via the Model Context Protocol (MCP).**

This repository contains the implementation of an MCP server that acts as a bridge to the [PDD Command Line Interface (`pdd-cli`)](https://github.com/prompt-driven/pdd). It exposes PDD commands as MCP tools, allowing MCP clients (like Claude Desktop, Continue.dev, Cursor, etc.) to agentically generate code, run tests, fix errors, and more using PDD.

## Features

*   Exposes core `pdd` commands as MCP `Tools`.
*   Uses the efficient **stdio** transport for local execution.
*   Seamlessly integrates with MCP clients supporting stdio servers.
*   Leverages your existing `pdd-cli` installation and configuration (including authentication).
*   Designed for easy execution via `uvx`.

## Prerequisites

Before using this server, you **must** have the following installed and configured:

1.  **Python:** Version 3.10 or higher.
2.  **`uv`:** The fast Python installer and resolver. Installation instructions: [astral.sh/uv](https://astral.sh/uv).
3.  **`pdd-cli`:** The Prompt-Driven Development CLI tool.
    *   Install: `pip install pdd-cli`
    *   Verify: `pdd --version`
    *   **Crucially:** Ensure your `pdd-cli` is authenticated if you intend to use cloud features (e.g., via GitHub SSO). Run a simple `pdd` command first to trigger authentication if needed. See the [PDD CLI README](https://github.com/prompt-driven/pdd) for full details.

## Installation

This server is designed to be run directly using `uvx`, which handles installation automatically. There's typically no need to install it separately into a virtual environment unless you are developing the server itself.

If you *do* want to install it explicitly (e.g., for development):

```bash
# Recommended: Use uv
uv pip install pdd-mcp-server

# Or use pip
pip install pdd-mcp-server
```

## Usage

### Running the Server

The easiest way to run the server is using `uvx`:

```bash
uvx pdd-mcp-server
```

This command downloads `pdd-mcp-server` (if not already cached) and runs its entry point, starting the MCP server listening on stdio.

### Configuring MCP Clients

You need to configure your MCP client application to launch this server. Below is an example for **Claude Desktop**.

1.  **Find `uv` Path:** Determine the absolute path to your `uv` executable.
    *   On macOS/Linux: `which uv`
    *   On Windows: `where uv`
2.  **Edit Config:** Open your Claude Desktop configuration file:
    *   macOS: `~/Library/Application Support/Claude/claude_desktop_config.json`
    *   Windows: `%APPDATA%\Claude\claude_desktop_config.json`
    (Create the file if it doesn't exist).
3.  **Add Server Entry:** Add the following under the `mcpServers` key, replacing `/path/to/your/uv` with the actual path found in step 1:

    ```json
    {
      "mcpServers": {
        "pdd": {
          "command": "/path/to/your/uv",
          "args": [
            "run", // Use 'uv run' if installed, or 'uvx' if running directly
            "pdd-mcp-server"
          ],
          // Optional: Add environment variables if needed by pdd-cli or the server
          // "env": {
          //   "PDD_OUTPUT_COST_PATH": "/path/to/your/cost.csv"
          // }
        }
        // ... other servers
      }
    }
    ```

    *   **Note:** If you installed `pdd-mcp-server` into a specific virtual environment that Claude won't automatically activate, you might need to adjust the `command` and `args` to activate the environment first or point directly to the script within the environment. Using `uvx` (as shown above with `uv run pdd-mcp-server` or just `uvx pdd-mcp-server` if `uvx` is directly in PATH) is generally simpler.

4.  **Restart Claude Desktop:** Close and reopen Claude Desktop for the changes to take effect. You should see the MCP tools icon (hammer) appear if the connection is successful.

### Authentication Note

**Authentication is handled by `pdd-cli`**. When this MCP server invokes a `pdd` command (e.g., `pdd generate ...`), the `pdd-cli` tool will use its existing authentication (like GitHub SSO tokens stored locally) to interact with PDD Cloud services. This server *does not* handle or require user credentials directly. Ensure `pdd-cli` is authenticated *before* relying on cloud features via this MCP server.

### Cloud vs. Local Execution Note

This server simply executes `pdd` commands. Whether `pdd-cli` runs in **cloud mode** (default) or **local mode** (`--local` flag, requires API keys like `OPENAI_API_KEY`) depends on your `pdd-cli` configuration and any flags passed through the MCP tool arguments. Refer to the [PDD CLI documentation](https://github.com/prompt-driven/pdd) for details on cloud vs. local execution and associated requirements (API keys, costs, etc.). Arguments like `--local` can often be passed via the tool parameters.

## Exposed Tools

This server exposes `pdd` commands as MCP tools. The exact tool names and parameters mirror the `pdd-cli` commands:

*(This section should be populated with the actual tools implemented. Example below)*

| MCP Tool Name     | Corresponding PDD Command | Description                                      | Key Parameters (Example)                     |
| :---------------- | :------------------------ | :----------------------------------------------- | :------------------------------------------- |
| `pdd-generate`    | `pdd generate`            | Generates code from a prompt file.               | `prompt_file`, `output`, `strength`, etc.    |
| `pdd-test`        | `pdd test`                | Generates or enhances unit tests.                | `prompt_file`, `code_file`, `output`, etc.   |
| `pdd-fix`         | `pdd fix`                 | Fixes errors in code based on test failures.     | `prompt_file`, `code_file`, `test_file`, `error_file`, `output_code`, `output_test`, `loop`, etc. |
| `pdd-example`     | `pdd example`             | Creates an example file from code and prompt.    | `prompt_file`, `code_file`, `output`         |
| `pdd-preprocess`  | `pdd preprocess`          | Preprocesses prompt files.                       | `prompt_file`, `output`, `recursive`, etc.   |
| `pdd-split`       | `pdd split`               | Splits large prompt files.                       | `input_prompt`, `input_code`, `example_code`, `output_sub`, `output_modified` |
| `pdd-change`      | `pdd change`              | Modifies a prompt based on change instructions.  | `change_prompt_file`, `input_code`, `input_prompt_file`, `output`, `csv` |
| `pdd-update`      | `pdd update`              | Updates a prompt based on modified code.         | `input_prompt_file`, `modified_code_file`, `input_code_file`, `output`, `git` |
| `pdd-detect`      | `pdd detect`              | Detects which prompts need changes.              | `prompt_files`, `change_file`, `output`      |
| `pdd-conflicts`   | `pdd conflicts`           | Finds conflicts between two prompts.             | `prompt1`, `prompt2`, `output`               |
| `pdd-crash`       | `pdd crash`               | Fixes code that caused a program crash.          | `prompt_file`, `code_file`, `program_file`, `error_file`, `output`, `output_program`, `loop` |
| `pdd-trace`       | `pdd trace`               | Traces code lines back to prompt lines.          | `prompt_file`, `code_file`, `code_line`, `output` |
| `pdd-bug`         | `pdd bug`                 | Generates a unit test from observed/desired output. | `prompt_file`, `code_file`, `program_file`, `current_output_file`, `desired_output_file`, `output` |
| `pdd-auto-deps`   | `pdd auto-deps`           | Inserts dependencies into a prompt.              | `prompt_file`, `directory_path`, `output`, `csv`, `force_scan` |
| *(...add others)* | *(...)*                  | *(...)*                                          | *(...)*                                      |

*Note: Tool parameters generally match the command-line arguments/options of the corresponding `pdd` command. Refer to `pdd <command> --help` for details.*

## Architecture / Tech Stack

*   **Language:** Python 3.10+
*   **MCP SDK:** [`modelcontextprotocol/python-sdk`](https://github.com/modelcontextprotocol/python-sdk) (`mcp` package)
*   **Transport:** MCP stdio
*   **Core Logic:** Invokes the `pdd-cli` command-line tool using Python's `subprocess`.

## Development

1.  **Clone the repository:**
    ```bash
    git clone <repository-url>
    cd pdd-mcp-server
    ```
2.  **Setup Environment (using `uv`):**
    ```bash
    uv venv
    source .venv/bin/activate # or .venv\Scripts\activate on Windows
    uv pip install -e ".[dev]"
    ```
3.  **Run Locally:**
    ```bash
    # Activate environment if not already active
    source .venv/bin/activate
    # Run the server entry point directly
    python -m pdd_mcp_server.main # Adjust module path as needed
    ```
4.  **Testing:**
    *   Unit tests: `pytest`
    *   Integration: Use the [MCP Inspector](https://modelcontextprotocol.io/docs/tools/inspector) or configure a client like Claude Desktop to connect to your local development server.

## Troubleshooting

*   **Server Not Connecting:**
    *   Verify `pdd-cli` is installed and in your PATH.
    *   Verify `uv` is installed and its path is correct in the client configuration.
    *   Check Claude Desktop logs (`~/Library/Logs/Claude/mcp*.log` or `%APPDATA%\Claude\logs\mcp*.log`). Look for errors related to launching the command.
    *   Ensure the `command` and `args` in `claude_desktop_config.json` are correct and use absolute paths if necessary.
*   **Tools Failing:**
    *   Check the server logs (stderr, potentially captured by the client like Claude Desktop).
    *   Run the equivalent `pdd` command directly in your terminal to see if it works and if any errors occur (e.g., authentication issues, file not found).
    *   Ensure `pdd-cli` is properly authenticated for cloud commands.

## Contributing

Contributions are welcome! Please open an issue or submit a pull request.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.