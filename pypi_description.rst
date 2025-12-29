.. image:: https://img.shields.io/badge/pdd--cli-v0.0.95-blue
   :alt: PDD-CLI Version

.. image:: https://img.shields.io/badge/Discord-join%20chat-7289DA.svg?logo=discord&logoColor=white&link=https://discord.gg/Yp4RTh8bG7
   :alt: Join us on Discord
   :target: https://discord.gg/Yp4RTh8bG7

PDD (Prompt-Driven Development) Command Line Interface
======================================================

The primary command is ``sync``, which automatically executes the complete PDD workflow loop—from dependency injection through code generation, testing, and verification. For most use cases, ``sync`` is the recommended starting point, as it intelligently determines what steps are needed and executes them in the correct order.

PDD (Prompt-Driven Development) is a command-line interface that harnesses AI models to generate and maintain code from prompt files. Whether you want to create new features, fix bugs, enhance unit tests, or manage complex prompt structures, pdd-cli streamlines your workflow through an intuitive interface and powerful automation.

.. image:: https://img.youtube.com/vi/5lBxpTSnjqo/0.jpg
   :alt: Watch a video demonstration of PDD
   :target: https://www.youtube.com/watch?v=5lBxpTSnjqo

Why Choose Prompt-Driven Development?
-------------------------------------

*   **Tackle the Root Cause of Maintenance Costs**: Traditional development spends up to 90% of its budget on maintaining and modifying existing code. PDD addresses this by treating prompts—not code—as the primary source of truth. Instead of applying costly, complex patches, you update the high-level prompt and regenerate clean, consistent code.
*   **Boost Developer Productivity & Focus**: PDD shifts your work from tedious, line-by-line coding to high-level system design. Its batch-oriented workflow (using commands like ``sync``) frees you from the constant supervision required by interactive AI assistants. You can define a task, launch the process, and focus on other priorities while the AI works in the background.
*   **Maintain Control and Determinism**: Unlike agentic coders that can introduce unpredictable changes across a project, PDD gives you full control. You precisely define the context for every operation, ensuring that changes are targeted, deterministic, and safe. This is especially critical in large codebases, where unpredictable modifications can have cascading and destructive effects.
*   **Enhance Code Quality and Consistency**: By using prompts as a single source of truth, PDD ensures your code, tests, and documentation never drift out of sync. This regenerative process produces a more reliable and understandable codebase compared to the tangled results of repeated patching.
*   **Improve Collaboration**: Prompts are written in natural language, making them accessible to both technical and non-technical stakeholders. This fosters clearer communication and ensures the final product aligns with business requirements.
*   **Reduce LLM Costs**: PDD's structured, batch-oriented nature is inherently more token-efficient and allows you to take advantage of significant discounts offered by LLM providers for batch processing APIs, making it a more cost-effective solution than many interactive tools.


Key Features
------------

*   **Automated `sync` Command**: A single command to automate the entire development cycle: from code generation and dependency management to testing and verification.
*   **Cloud & Local Execution**: Run securely in the cloud with GitHub SSO (no API keys needed) or switch to local mode with the ``--local`` flag for full control.
*   **Comprehensive Command Suite**: A full set of tools to ``generate``, ``test``, ``fix``, ``update``, and ``split`` your code and prompts.
*   **Intelligent Testing**: Generate new unit tests, or improve existing ones by analyzing coverage reports to hit your desired targets.
*   **Iterative Error Fixing**: Automatically find and correct errors in your code with commands like ``fix`` and ``crash``, which can loop until the issues are resolved.
*   **Cost Tracking & Configuration**: Fine-tune AI model behavior with ``--strength`` and ``--temperature`` and track usage with optional cost reporting.
*   **Cross-Language Support**: Work with Python, JavaScript, Java, C++, Go, and more, with automatic language detection from prompt filenames.


Quick Installation
------------------

**Recommended: Using uv (Faster & Better Dependency Management)**

We recommend installing PDD using the `uv <https://github.com/astral-sh/uv>`_ package manager for better dependency management and automatic environment configuration:

.. code-block:: console

   # Install uv if you haven't already
   curl -LsSf https://astral.sh/uv/install.sh | sh

   # Install PDD using uv tool install
   uv tool install pdd-cli

This installation method ensures:

- Faster installations with optimized dependency resolution
- Automatic environment setup without manual configuration
- Proper handling of the PDD_PATH environment variable
- Better isolation from other Python packages

**Alternative: Using pip**

If you prefer, you can install with pip:

.. code-block:: console

   pip install pdd-cli

After installation, verify:

.. code-block:: console

   pdd --version

You'll see the current PDD version (e.g., 0.0.95).

Getting Started with Examples
-----------------------------

To quickly see PDD in action, we recommend exploring the ``examples/`` directory in the project repository. It contains ready-to-use sample prompts and projects to help you get started.

For instance, the ``handpaint`` example demonstrates how to generate a complete HTML canvas application from a single prompt. After cloning the repository, you can run it yourself:

.. code-block:: console

   # Navigate to the example directory
   cd examples/handpaint/pdd/

   # Run the sync command
   pdd sync handpaint

This will generate the full application based on the ``handpaint_html.prompt`` file.


Advanced Installation Tips
--------------------------


**Virtual Environment**

Create and activate a virtual environment, then install pdd-cli:

.. code-block:: console

   python -m venv pdd-env

    # Activate environment
    # On Windows:
   pdd-env\Scripts\activate
    # On Unix/MacOS:
   source pdd-env/bin/activate

    # Install PDD (with uv - recommended)
   uv tool install pdd-cli
    # OR with pip
   pip install pdd-cli


**Environment Variables**

Optionally, add environment variables to your shell startup (e.g., ``.bashrc``, ``.zshrc``):

.. code-block:: console

   export PDD_AUTO_UPDATE=true
   export PDD_GENERATE_OUTPUT_PATH=/path/to/generated/code/
   export PDD_TEST_OUTPUT_PATH=/path/to/tests/

Tab Completion
~~~~~~~~~~~~~~
Enable shell completion:

.. code-block:: console

   pdd install_completion

Cloud vs Local
--------------

By default, PDD runs in cloud mode (currently waitlist), using GitHub SSO for secure access to AI models—no local API keys needed. If you want or need to run locally:

.. code-block:: console

   pdd --local generate my_prompt_python.prompt

Be sure to configure API keys in your environment ahead of time:

.. code-block:: console

   export OPENAI_API_KEY=your_api_key_here
   export ANTHROPIC_API_KEY=your_api_key_here
   # etc.

Basic Usage
-----------

All commands follow a standard pattern:

.. code-block:: console

   pdd [GLOBAL OPTIONS] COMMAND [COMMAND OPTIONS] [ARGS]...

**Example – Sync**

The ``sync`` command automates the entire PDD workflow for a given basename. It intelligently runs generation, testing, and fixing steps as needed, with real-time progress feedback.

.. code-block:: console

   pdd sync factorial_calculator

**Example – Generate Code**

Generate Python code from a prompt:

.. code-block:: console

   pdd generate factorial_calculator_python.prompt

In cloud mode (no local keys required). Or locally if you prefer:

.. code-block:: console

   pdd --local generate factorial_calculator_python.prompt

**Example – Test**

Automatically create or enhance tests:

.. code-block:: console

   pdd test factorial_calculator_python.prompt src/factorial_calculator.py

Use coverage analysis:

.. code-block:: console

   pdd test --coverage-report coverage.xml --existing-tests tests/test_factorial.py \
       factorial_prompt.prompt src/factorial.py


**Example – Fix Iteratively**

Attempt to fix failing code or tests in multiple loops:

.. code-block:: console

   pdd fix --loop \
       factorial_calculator_python.prompt src/factorial_calculator.py tests/test_factorial.py errors.log

PDD will keep trying (with a budget limit configurable by ``--budget``) until tests pass or attempts are exhausted.

Frequently Asked Questions (FAQ)
--------------------------------

**What's the main difference between PDD and using an AI chat assistant (agentic coder)?**

Control and predictability. Interactive AI assistants can be unpredictable and make broad, unintended changes, which is risky in large codebases. PDD gives you full control. You define the exact context for every change, making the process deterministic and safe. PDD's batch-oriented workflow also frees you from constant supervision, boosting productivity.

**What is "Cloud vs. Local" execution?**

By default, PDD runs in cloud mode, using GitHub SSO for secure access to AI models—no local API keys needed. If you want or need to run locally, use the `--local` flag:

.. code-block:: console

   pdd --local generate my_prompt_python.prompt

Be sure to configure API keys in your environment ahead of time:

.. code-block:: console

   export OPENAI_API_KEY=your_api_key_here
   export ANTHROPIC_API_KEY=your_api_key_here
   # etc.

**Can I use PDD on an existing project?**

Yes. PDD is designed for both new and existing projects. You can start by creating prompts for new features. For existing, manually written code, you can use the `pdd update` command to create a prompt file that reflects the current state of your code. This allows you to gradually bring parts of your existing codebase under the PDD methodology.

**Do I need to be an expert prompt engineer?**

Not at all. Effective prompts are more about clearly defining your requirements in natural language than about complex "engineering." If you can write a good specification or a clear bug report, you can write a good prompt. The goal is to describe *what* you want the code to do, not how to write it.


Getting Help
------------

Use inline help to discover commands and options:

.. code-block:: console

   pdd --help
   pdd generate --help
   pdd fix --help
   ...

Happy Prompt-Driven Coding!