.. image:: https://img.shields.io/badge/pdd--cli-v0.0.7-blue
   :alt: PDD-CLI Version

PDD (Prompt-Driven Development) Command Line Interface
======================================================

PDD (Prompt-Driven Development) is a command-line interface that harnesses AI models to generate and maintain code from prompt files. Whether you want to create new features, fix bugs, enhance unit tests, or manage complex prompt structures, pdd-cli streamlines your workflow through an intuitive interface and powerful automation.

Key Features
------------

- Cloud or Local Execution  
  • Run in the cloud (default) with no need to manage API keys.  
  • Switch to local mode with the ``--local`` flag for full control using your own API keys.

- GitHub Single Sign-On  
  • Secure authentication with GitHub SSO in cloud mode.  
  • Automatic token handling so you can focus on coding.

- Comprehensive Command Suite  
  • Generate: Create runnable code from prompt files.  
  • Example: Build examples that showcase generated code usage.  
  • Test: Produce or improve unit tests based on coverage goals.  
  • Fix & Crash: Automatically identify and correct errors, iterating if necessary.  
  • Update & Change: Keep your prompt files in sync with evolving codebases.  
  • Split & Detect: Manage and analyze complex prompts at scale.  
  • …and more!

- Automated Testing & Cost Tracking  
  • Generate coverage reports and additional test cases on the fly.  
  • Optional cost-tracking (CSV) for AI usage.  

- Rich Configuration & Customization  
  • Environment variables to define default output paths and settings.  
  • Fine-tune AI model behavior with ``--strength`` and ``--temperature``.  
  • Built-in auto-update (configurable via env var).

- Cross-Language Support  
  • Python, Java, JavaScript, Ruby, Go, C++, and beyond.  
  • Prompt naming conventions let PDD infer language automatically.


Quick Installation
------------------

.. code-block:: console

   pip install pdd-cli

After installation, verify:

.. code-block:: console

   pdd --version

You’ll see the current PDD version (e.g., 0.0.7).

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

    # Install PDD
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

By default, PDD runs in cloud mode, using GitHub SSO for secure access to AI models—no local API keys needed. If you want or need to run locally:

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

Why Prompt-Driven Development?
------------------------------

*   **Increased Productivity:** Automate tedious tasks and focus on higher-level design.
*   **Improved Code Quality:** Leverage AI to generate well-structured and tested code.
*   **Faster Development Cycles:** Rapidly prototype and iterate on your ideas.
*   **Reduced Errors:** Automatically identify and fix errors in your code.
*   **Enhanced Collaboration:** Work seamlessly with prompt files as a shared source of truth.

Getting Help
------------

Use inline help to discover commands and options:

.. code-block:: console

   pdd --help
   pdd generate --help
   pdd fix --help
   ...

Happy Prompt-Driven Coding!