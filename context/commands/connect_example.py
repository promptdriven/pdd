#!/usr/bin/env python3
"""
Example usage of the PDD Connect Command module.

This example demonstrates how to:
1. Integrate the `connect` command into a larger Click CLI application.
2. Programmatically invoke the command using `CliRunner` for testing.
3. Mock dependencies (like uvicorn and webbrowser) to simulate server startup without actually blocking.

The `connect` command is responsible for launching a local REST server that allows
a web frontend to interact with the PDD CLI tools.
"""

import sys
import os
from pathlib import Path
from unittest.mock import patch, MagicMock
import click
from click.testing import CliRunner

# Ensure we can import the module.
# We need to traverse UP two directories to reach the project root from context/commands/connect_example.py
# context/commands/connect_example.py -> context/commands -> context -> pdd (root)
# Use insert(0, ...) to prioritize local source over any installed packages
sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent))

# The module path for patching - this is where the connect command is located
MODULE_NAME = "pdd.commands.connect"

try:
    # Import the command function from the pdd package
    from pdd.commands.connect import connect
except ImportError as e:
    print(f"Error: Could not import 'connect' command. {e}")
    print(f"Current sys.path: {sys.path}")
    sys.exit(1)


def example_integrate_into_cli():
    """
    Example 1: Integrating 'connect' into a main CLI group.
    
    This shows how the command is typically registered in the main `pdd` entry point.
    """
    print("\n=== Example 1: CLI Integration ===")

    @click.group()
    def cli():
        """Main PDD CLI entry point."""
        pass

    # Register the connect command
    cli.add_command(connect)

    print("Successfully registered 'connect' command to main CLI group.")
    print(f"Commands available: {list(cli.commands.keys())}")
    
    # We can now inspect the help output programmatically
    runner = CliRunner()
    result = runner.invoke(cli, ['connect', '--help'])
    
    print("\n--- Help Output ---")
    print(result.output)


def example_simulate_server_start():
    """
    Example 2: Simulating server startup with mocked dependencies.

    Since `uvicorn.run` blocks execution, we mock it to verify that the command
    parses arguments correctly and attempts to start the server with the right config.
    """
    print("\n=== Example 2: Simulating Server Startup ===")

    runner = CliRunner()

    # We mock:
    # 1. uvicorn.run: To prevent actual server startup blocking
    # 2. webbrowser.open: To prevent opening a real browser tab
    # 3. create_app: To avoid needing the actual server factory logic
    # 4. os.environ: To check if token is set correctly

    with patch(f'{MODULE_NAME}.uvicorn.run') as mock_uvicorn, \
         patch(f'{MODULE_NAME}.webbrowser.open') as mock_browser, \
         patch(f'{MODULE_NAME}.create_app') as mock_create_app, \
         patch.dict(os.environ, {}, clear=True):
        
        # Mock the app object returned by create_app
        mock_app = MagicMock()
        mock_create_app.return_value = mock_app

        print("Invoking: pdd connect --port 8080 --no-browser")
        
        result = runner.invoke(connect, ['--port', '8080', '--no-browser'])

        # Check exit code
        if result.exit_code == 0:
            print("Command executed successfully.")
        else:
            print(f"Command failed with exit code {result.exit_code}")
            print(result.output)
            return

        # Verify uvicorn was called with correct arguments
        mock_uvicorn.assert_called_once()
        call_args = mock_uvicorn.call_args
        
        print("\n--- Verification ---")
        print(f"Uvicorn called with app: {call_args[0][0]}")
        print(f"Host: {call_args[1]['host']}")
        print(f"Port: {call_args[1]['port']} (Expected: 8080)")
        
        # Verify browser was NOT opened
        if not mock_browser.called:
            print("Browser was NOT opened (Correct, due to --no-browser)")
        else:
            print("Error: Browser was opened unexpectedly.")


def example_security_warning():
    """
    Example 3: Testing security warnings for remote connections.
    
    The command should warn the user if they try to bind to 0.0.0.0 (allow remote)
    without providing an authentication token.
    """
    print("\n=== Example 3: Security Warning Test ===")
    
    runner = CliRunner()
    
    # We simulate a user saying \"no\" (abort) to the security prompt
    # Input 'n' is passed to the confirmation prompt
    print("Invoking: pdd connect --allow-remote (without token)")
    print("Simulating user input: 'n' (abort)")
    
    result = runner.invoke(connect, ['--allow-remote'], input='n\n')

    print("\n--- Output ---")
    # We expect to see the warning in the output
    if "SECURITY WARNING" in result.output:
        print("Security warning displayed correctly.")
    
    # We expect a non-zero exit code because we aborted
    print(f"Exit code: {result.exit_code} (Expected: 1)")


def example_custom_frontend():
    """
    Example 4: Using a custom frontend URL.

    Demonstrates how the --frontend-url option overrides the default browser target.
    """
    print("\n=== Example 4: Custom Frontend URL ===")

    runner = CliRunner()

    with patch(f'{MODULE_NAME}.uvicorn.run'), \
         patch(f'{MODULE_NAME}.webbrowser.open') as mock_browser, \
         patch(f'{MODULE_NAME}.create_app'):
        
        custom_url = "http://my-custom-domain.com"
        print(f"Invoking: pdd connect --frontend-url {custom_url}")
        
        runner.invoke(connect, ['--frontend-url', custom_url])
        
        # Verify browser opened the custom URL
        mock_browser.assert_called_once_with(custom_url)
        print(f"Browser opened: {mock_browser.call_args[0][0]}")


if __name__ == "__main__":
    # Run the examples
    example_integrate_into_cli()
    example_simulate_server_start()
    example_security_warning()
    example_custom_frontend()