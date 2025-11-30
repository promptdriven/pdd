#!/usr/bin/env python3
"""
Example usage of the pdd.core.utils module.

This module provides helper functions for the PDD CLI, including:
- Detecting the first pending subcommand in a Click context
- Checking if API environment files exist
- Verifying shell completion installation
- Detecting project-level configuration
- Determining whether to show onboarding reminders
- Running the interactive setup utility

File structure (relative to project root):
    pdd/
        core/
            utils.py          # The module being demonstrated
    context/
        core/
            utils_example.py  # This example file
"""

import os
import sys
from pathlib import Path
from unittest.mock import MagicMock

# Import the utility functions from the pdd.core.utils module
from pdd.core.utils import (
    _first_pending_command,
    _api_env_exists,
    _completion_installed,
    _project_has_local_configuration,
    _should_show_onboarding_reminder,
    _run_setup_utility,
)


def example_first_pending_command():
    """
    Demonstrate _first_pending_command function.
    
    This function extracts the first subcommand from a Click context's
    protected_args list, skipping any option flags (args starting with '-').
    
    Parameters (via ctx):
        ctx (click.Context): A Click context object with protected_args attribute.
            - protected_args (list[str]): List of arguments passed to the CLI.
    
    Returns:
        Optional[str]: The first non-option argument (subcommand name), or None
                       if no subcommand is found.
    
    Example protected_args scenarios:
        ['--verbose', 'generate', 'file.prompt'] -> returns 'generate'
        ['sync', '--force'] -> returns 'sync'
        ['--help'] -> returns None
    """
    print("=" * 60)
    print("Example: _first_pending_command")
    print("=" * 60)
    
    # Create a mock Click context with various protected_args scenarios
    
    # Scenario 1: Options followed by a subcommand
    mock_ctx_1 = MagicMock()
    mock_ctx_1.protected_args = ['--verbose', '--force', 'generate', 'myfile.prompt']
    result_1 = _first_pending_command(mock_ctx_1)
    print(f"protected_args: {mock_ctx_1.protected_args}")
    print(f"First pending command: {result_1}")  # Expected: 'generate'
    print()
    
    # Scenario 2: Subcommand first
    mock_ctx_2 = MagicMock()
    mock_ctx_2.protected_args = ['sync', '--budget', '5.0']
    result_2 = _first_pending_command(mock_ctx_2)
    print(f"protected_args: {mock_ctx_2.protected_args}")
    print(f"First pending command: {result_2}")  # Expected: 'sync'
    print()
    
    # Scenario 3: Only options, no subcommand
    mock_ctx_3 = MagicMock()
    mock_ctx_3.protected_args = ['--help', '--version']
    result_3 = _first_pending_command(mock_ctx_3)
    print(f"protected_args: {mock_ctx_3.protected_args}")
    print(f"First pending command: {result_3}")  # Expected: None
    print()
    
    # Scenario 4: Empty args
    mock_ctx_4 = MagicMock()
    mock_ctx_4.protected_args = []
    result_4 = _first_pending_command(mock_ctx_4)
    print(f"protected_args: {mock_ctx_4.protected_args}")
    print(f"First pending command: {result_4}")  # Expected: None
    print()


def example_api_env_exists():
    """
    Demonstrate _api_env_exists function.
    
    This function checks whether the ~/.pdd/api-env file exists.
    This file is created by 'pdd setup' and contains API key configurations.
    
    Parameters:
        None
    
    Returns:
        bool: True if ~/.pdd/api-env exists, False otherwise.
    
    The api-env file typically contains environment variable exports for:
        - OPENAI_API_KEY
        - ANTHROPIC_API_KEY
        - GOOGLE_API_KEY (or GEMINI_API_KEY)
    """
    print("=" * 60)
    print("Example: _api_env_exists")
    print("=" * 60)
    
    api_env_path = Path.home() / ".pdd" / "api-env"
    exists = _api_env_exists()
    
    print(f"Checking for: {api_env_path}")
    print(f"API env file exists: {exists}")
    
    if exists:
        print("  -> User has completed 'pdd setup' and configured API keys.")
    else:
        print("  -> User should run 'pdd setup' to configure API keys.")
    print()


def example_completion_installed():
    """
    Demonstrate _completion_installed function.
    
    This function checks if PDD shell completion is installed by examining
    the user's shell RC file (e.g., ~/.zshrc, ~/.bashrc) for PDD completion
    markers.
    
    Parameters:
        None
    
    Returns:
        bool: True if the shell RC file contains 'PDD CLI completion' or
              'pdd_completion' strings, False otherwise.
    
    The function:
        1. Detects the current shell (bash, zsh, fish)
        2. Gets the appropriate RC file path
        3. Reads the RC file content
        4. Searches for PDD completion markers
    """
    print("=" * 60)
    print("Example: _completion_installed")
    print("=" * 60)
    
    installed = _completion_installed()
    
    print(f"Shell completion installed: {installed}")
    
    if installed:
        print("  -> Tab completion for 'pdd' commands is available.")
    else:
        print("  -> Run 'pdd setup' or 'pdd install_completion' to enable tab completion.")
    print()


def example_project_has_local_configuration():
    """
    Demonstrate _project_has_local_configuration function.
    
    This function detects project-level environment configuration that
    should suppress the onboarding reminder. It checks for:
    
    1. A .env file in the current directory containing API keys:
       - OPENAI_API_KEY=
       - GOOGLE_API_KEY=
       - ANTHROPIC_API_KEY=
    
    2. A .pdd subdirectory in the current directory (project-specific config)
    
    Parameters:
        None (uses current working directory)
    
    Returns:
        bool: True if local configuration is detected, False otherwise.
    """
    print("=" * 60)
    print("Example: _project_has_local_configuration")
    print("=" * 60)
    
    # Create output directory for demonstration
    output_dir = Path("./output")
    output_dir.mkdir(exist_ok=True)
    
    # Save current directory
    original_cwd = os.getcwd()
    
    # Check current directory
    has_config = _project_has_local_configuration()
    print(f"Current directory: {Path.cwd()}")
    print(f"Has local configuration: {has_config}")
    
    # Explain what was checked
    env_file = Path.cwd() / ".env"
    pdd_dir = Path.cwd() / ".pdd"
    
    print(f"  Checked for .env file: {env_file.exists()}")
    print(f"  Checked for .pdd directory: {pdd_dir.exists()}")
    
    if has_config:
        print("  -> Project has local API configuration; onboarding reminder suppressed.")
    else:
        print("  -> No local configuration found.")
    print()


def example_should_show_onboarding_reminder():
    """
    Demonstrate _should_show_onboarding_reminder function.
    
    This function determines whether to display the onboarding reminder banner.
    The reminder is shown to guide new users to run 'pdd setup'.
    
    Parameters:
        ctx (click.Context): A Click context object used to detect the current
                             command being executed.
    
    Returns:
        bool: True if the onboarding reminder should be shown, False otherwise.
    
    The reminder is NOT shown when any of these conditions are true:
        1. PDD_SUPPRESS_SETUP_REMINDER env var is set to '1', 'true', or 'yes'
        2. The current command is 'setup' (user is already setting up)
        3. ~/.pdd/api-env file exists (setup was completed)
        4. Project has local .env with API keys or .pdd directory
        5. Shell completion is already installed
    """
    print("=" * 60)
    print("Example: _should_show_onboarding_reminder")
    print("=" * 60)
    
    # Scenario 1: Normal command (e.g., 'generate')
    mock_ctx_generate = MagicMock()
    mock_ctx_generate.protected_args = ['generate', 'myfile.prompt']
    
    # Clear any suppression env var for this test
    original_suppress = os.environ.get('PDD_SUPPRESS_SETUP_REMINDER')
    if 'PDD_SUPPRESS_SETUP_REMINDER' in os.environ:
        del os.environ['PDD_SUPPRESS_SETUP_REMINDER']
    
    show_reminder = _should_show_onboarding_reminder(mock_ctx_generate)
    print(f"Command: generate")
    print(f"Should show onboarding reminder: {show_reminder}")
    print()
    
    # Scenario 2: Setup command (should never show reminder)
    mock_ctx_setup = MagicMock()
    mock_ctx_setup.protected_args = ['setup']
    
    show_reminder_setup = _should_show_onboarding_reminder(mock_ctx_setup)
    print(f"Command: setup")
    print(f"Should show onboarding reminder: {show_reminder_setup}")  # Expected: False
    print()
    
    # Scenario 3: With suppression env var
    os.environ['PDD_SUPPRESS_SETUP_REMINDER'] = 'true'
    
    show_reminder_suppressed = _should_show_onboarding_reminder(mock_ctx_generate)
    print(f"Command: generate (with PDD_SUPPRESS_SETUP_REMINDER=true)")
    print(f"Should show onboarding reminder: {show_reminder_suppressed}")  # Expected: False
    
    # Restore original env var
    if original_suppress is not None:
        os.environ['PDD_SUPPRESS_SETUP_REMINDER'] = original_suppress
    elif 'PDD_SUPPRESS_SETUP_REMINDER' in os.environ:
        del os.environ['PDD_SUPPRESS_SETUP_REMINDER']
    print()


def example_run_setup_utility_info():
    """
    Demonstrate _run_setup_utility function (informational only).
    
    This function executes the interactive setup utility as a subprocess.
    It runs: python -m pdd.setup_tool
    
    Parameters:
        None
    
    Returns:
        None
    
    Raises:
        RuntimeError: If the setup utility exits with a non-zero status code.
                      The error message includes the exit status code.
    
    The setup utility performs:
        1. Installs shell tab completion
        2. Prompts for API keys (OpenAI, Anthropic, Google/Gemini)
        3. Creates ~/.pdd directory and configuration files
        4. Writes the api-env file with exported keys
    
    NOTE: This example does not actually run the setup utility to avoid
    interactive prompts. In real usage, call _run_setup_utility() directly.
    """
    print("=" * 60)
    print("Example: _run_setup_utility (informational)")
    print("=" * 60)
    
    print("The _run_setup_utility() function:")
    print("  - Runs: python -m pdd.setup_tool")
    print("  - Launches an interactive setup wizard")
    print("  - Installs shell completion")
    print("  - Configures API keys")
    print("  - Creates ~/.pdd/api-env file")
    print()
    print("Usage in code:")
    print("    from pdd.core.utils import _run_setup_utility")
    print("    ")
    print("    # This will launch the interactive setup")
    print("    _run_setup_utility()")
    print()
    print("Error handling:")
    print("    If setup fails, raises RuntimeError with exit status.")
    print()


def main():
    """
    Run all examples demonstrating the pdd.core.utils module.
    """
    print("\n" + "#" * 60)
    print("# PDD Core Utils Module - Usage Examples")
    print("#" * 60 + "\n")
    
    # Run each example
    example_first_pending_command()
    example_api_env_exists()
    example_completion_installed()
    example_project_has_local_configuration()
    example_should_show_onboarding_reminder()
    example_run_setup_utility_info()
    
    print("=" * 60)
    print("All examples completed successfully!")
    print("=" * 60)


if __name__ == "__main__":
    main()