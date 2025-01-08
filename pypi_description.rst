PDD (Prompt-Driven Development) Command Line Interface
======================================================

.. image:: https://img.shields.io/badge/pdd--cli-v0.0.4-blue
   :alt: PDD-CLI Version

**Unlock the power of prompt-driven development with the PDD-CLI!**

PDD (Prompt-Driven Development) is a revolutionary approach to software development that leverages the power of AI to streamline your workflow. The `pdd-cli` package provides a powerful command-line interface to interact with the PDD ecosystem, allowing you to generate code, create examples, run tests, and manage prompt files with ease.

Key Features
------------

*   **Code Generation:** Effortlessly generate runnable code from natural language prompts using the `generate` command.
*   **Example Creation:** Automatically create example files from existing code and prompts with the `example` command.
*   **Automated Testing:** Generate and enhance unit tests with the `test` command, including coverage analysis and improvement.
*   **Prompt Management:** Preprocess, split, change, and update prompt files using commands like `preprocess`, `split`, `change`, and `update`.
*   **Error Fixing:** Automatically fix errors in code and unit tests with the `fix` command, featuring iterative fixing and budget control.
*   **Conflict Resolution:** Analyze and resolve conflicts between prompts using the `conflicts` command.
*   **Crash Recovery:** Fix errors that caused a program to crash with the `crash` command, featuring iterative fixing and budget control.
*   **Trace Analysis:** Find the associated line number between a prompt file and the generated code with the `trace` command.
*   **Bug Reproduction:** Generate a unit test based on observed and desired outputs with the `bug` command.
*   **Dependency Management:** Automatically analyze and insert dependencies into prompts with the `auto-deps` command.
*   **Multi-Language Support:** Work with a wide range of programming languages, including Python, JavaScript, Java, C++, Ruby, and Go.
*   **AI Model Control:** Fine-tune the AI model's output with options like `--strength` and `--temperature`.
*   **Cost Tracking:** Monitor and report the cost of operations with the `--output-cost` option.
*   **Example Review:** Review and control the use of few-shot examples with the `--review-examples` option.
*   **Automatic Example Submission:** Automatically submit successful fixes to the PDD Cloud platform with the `--auto-submit` option.
*   **Environment Variable Configuration:** Customize output locations and other settings using environment variables.
*   **Git Integration:** Use git history to find the original code file with the `--git` option in the `update` command.
*   **Auto-Update:** Stay up-to-date with the latest features and security patches (controllable via environment variable).
*   **Comprehensive Help:** Access detailed help for all commands and options.
*   **Tab Completion:** Enjoy tab completion for commands and options in compatible shells.
*   **Colorized Output:** Benefit from colorized output for improved readability.

Installation
------------

Install `pdd-cli` using pip:

.. code-block:: bash

    pip install pdd-cli

Verify the installation:

.. code-block:: bash

    pdd --version

Advanced Installation
---------------------

For more control, you can install `pdd-cli` in a virtual environment:

.. code-block:: bash

    # Create virtual environment
    python -m venv pdd-env

    # Activate environment
    # On Windows:
    pdd-env\Scripts\activate
    # On Unix/MacOS:
    source pdd-env/bin/activate

    # Install PDD
    pip install pdd-cli

API Key Setup
-------------

`pdd-cli` requires an API key for the language model. Set up your environment variable:

.. code-block:: bash

    # For OpenAI
    export OPENAI_API_KEY=your_api_key_here

    # For Anthropic
    export ANTHROPIC_API_KEY=your_api_key_here

    # For other supported providers
    export PROVIDER_API_KEY=your_api_key_here

Add these to your `.bashrc`, `.zshrc`, or equivalent for persistence.

Post-Installation Setup
------------------------

1. Enable tab completion:

    .. code-block:: bash

        pdd install_completion

2. Configure environment variables (optional):

    .. code-block:: bash

        # Add to .bashrc, .zshrc, or equivalent
        export PDD_AUTO_UPDATE=true
        export PDD_GENERATE_OUTPUT_PATH=/path/to/generated/code/
        export PDD_TEST_OUTPUT_PATH=/path/to/tests/

Basic Usage
-----------

.. code-block:: bash

    pdd [GLOBAL OPTIONS] COMMAND [OPTIONS] [ARGS]...

Global Options
--------------

*   `--force`: Overwrite existing files without asking.
*   `--strength FLOAT`: Set the AI model strength (0.0 to 1.0, default 0.5).
*   `--temperature FLOAT`: Set the AI model temperature (default 0.0).
*   `--verbose`: Increase output verbosity.
*   `--quiet`: Decrease output verbosity.
*   `--output-cost PATH_TO_CSV_FILE`: Enable cost tracking.
*   `--review-examples`: Review and optionally exclude few-shot examples.

Commands
--------

Here's a quick overview of the core commands. Use `pdd COMMAND --help` for detailed information on each command.

1. **generate**: Create code from a prompt file.
2. **example**: Create an example file from code and its prompt.
3. **test**: Generate or enhance unit tests.
4. **preprocess**: Preprocess prompt files.
5. **fix**: Fix errors in code and unit tests.
6. **split**: Split large prompt files.
7. **change**: Modify a prompt based on a change prompt.
8. **update**: Update a prompt based on modified code.
9. **detect**: Determine which prompts need changes.
10. **conflicts**: Find conflicts between prompts.
11. **crash**: Fix errors that caused a program to crash.
12. **trace**: Find the associated line number between a prompt file and the generated code.
13. **bug**: Generate a unit test based on observed and desired outputs.
14. **auto-deps**: Analyze and insert dependencies into prompts.

Example Workflow
----------------

Here's a simple example of generating code and tests:

.. code-block:: bash

    # Generate code
    pdd generate --output src/factorial.py factorial_python.prompt

    # Generate tests
    pdd test --output tests/test_factorial.py factorial_python.prompt src/factorial.py

Multi-Command Chaining Example
------------------------------

You can chain multiple commands for complex workflows:

.. code-block:: bash

    pdd generate --output src/calculator.py calculator_python.prompt test --output tests/test_calculator.py calculator_python.prompt src/calculator.py test --coverage-report coverage.xml --existing-tests tests/test_calculator.py --merge --target-coverage 95.0 calculator_python.prompt src/calculator.py

Why Choose PDD-CLI?
-------------------

*   **Increased Productivity:** Automate tedious tasks and focus on higher-level design.
*   **Improved Code Quality:** Leverage AI to generate well-structured and tested code.
*   **Faster Development Cycles:** Rapidly prototype and iterate on your ideas.
*   **Reduced Errors:** Automatically identify and fix errors in your code.
*   **Enhanced Collaboration:** Work seamlessly with prompt files as a shared source of truth.
*   **Cost-Effective:** Track and optimize your AI model usage.

Get Started Today!
------------------

Install `pdd-cli` and revolutionize your development workflow with the power of prompt-driven development. Explore the comprehensive documentation and examples to unlock the full potential of PDD.

For more information, visit the `pdd-cli` repository: [https://github.com/gltanaka/pdd](https://github.com/gltanaka/pdd)