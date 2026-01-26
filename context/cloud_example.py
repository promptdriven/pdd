#!/usr/bin/env python3
"""
Example usage of the pdd.core.cloud module.

This module demonstrates how to use the centralized cloud configuration for PDD CLI commands.
It covers:
- Retrieving cloud base URLs and specific endpoint URLs
- Handling environment variable overrides for testing
- Checking if cloud features are enabled
- Authenticating via JWT tokens (simulated)

File structure (relative to project root):
    pdd/
        core/
            cloud.py          # The module being demonstrated
    context/
        cloud_example.py      # This example file
"""

import os
import sys
from unittest.mock import patch, MagicMock

# Ensure the project root is in sys.path so we can import pdd packages
# This allows running the example directly from the context directory
project_root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

# Import the CloudConfig class and constants from the module
from pdd.core.cloud import (
    CloudConfig,
    CLOUD_ENDPOINTS,
    PDD_CLOUD_URL_ENV,
    PDD_JWT_TOKEN_ENV,
    FIREBASE_API_KEY_ENV,
    GITHUB_CLIENT_ID_ENV,
)
from rich.console import Console

console = Console()


def example_get_urls():
    """
    Demonstrate retrieving base and endpoint URLs.
    
    Shows how CloudConfig resolves URLs based on default values and
    environment variable overrides.
    """
    console.print("[bold blue]=== URL Configuration Examples ===[/bold blue]")

    # 1. Default Configuration
    # Clear env var to ensure we see defaults
    if PDD_CLOUD_URL_ENV in os.environ:
        del os.environ[PDD_CLOUD_URL_ENV]

    base_url = CloudConfig.get_base_url()
    console.print(f"Default Base URL: [green]{base_url}[/green]")

    # Get a specific endpoint (e.g., generateCode)
    gen_url = CloudConfig.get_endpoint_url("generateCode")
    console.print(f"Generate Code Endpoint: [green]{gen_url}[/green]")

    # 2. Custom Environment (e.g., Local Emulator)
    # Simulate setting the environment variable for local testing
    local_url = "http://127.0.0.1:5001/pdd-project/us-central1"
    os.environ[PDD_CLOUD_URL_ENV] = local_url
    
    console.print(f"\n[dim]Setting {PDD_CLOUD_URL_ENV} to {local_url}[/dim]")
    
    custom_base = CloudConfig.get_base_url()
    console.print(f"Custom Base URL: [yellow]{custom_base}[/yellow]")
    
    custom_endpoint = CloudConfig.get_endpoint_url("fixCode")
    console.print(f"Custom Fix Endpoint: [yellow]{custom_endpoint}[/yellow]")

    # Clean up
    del os.environ[PDD_CLOUD_URL_ENV]
    console.print()


def example_cloud_enabled_check():
    """
    Demonstrate checking if cloud features are enabled.
    
    Cloud features require specific API keys to be present in the environment.
    """
    console.print("[bold blue]=== Cloud Enabled Check ===[/bold blue]")

    # 1. Simulate missing keys
    with patch.dict(os.environ, {}, clear=True):
        is_enabled = CloudConfig.is_cloud_enabled()
        console.print(f"Cloud enabled (no keys): [red]{is_enabled}[/red]")

    # 2. Simulate present keys
    mock_env = {
        FIREBASE_API_KEY_ENV: "dummy_firebase_key",
        GITHUB_CLIENT_ID_ENV: "dummy_github_id"
    }
    with patch.dict(os.environ, mock_env):
        is_enabled = CloudConfig.is_cloud_enabled()
        console.print(f"Cloud enabled (with keys): [green]{is_enabled}[/green]")
    console.print()


def example_authentication_flow():
    """
    Demonstrate the JWT token retrieval flow.
    
    Shows:
    1. Retrieving a token injected via environment variable (CI/Testing).
    2. Handling the device flow (mocked for this example to avoid interactive prompts).
    """
    console.print("[bold blue]=== Authentication Flow Examples ===[/bold blue]")

    # 1. Environment Variable Token (Priority)
    # This is often used in CI/CD pipelines or automated tests
    test_token = "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.test_payload"
    os.environ[PDD_JWT_TOKEN_ENV] = test_token
    
    console.print(f"[dim]Setting {PDD_JWT_TOKEN_ENV} environment variable...[/dim]")
    token = CloudConfig.get_jwt_token(verbose=True)
    
    if token == test_token:
        console.print("[success]Successfully retrieved injected token![/success]")
    else:
        console.print("[error]Failed to retrieve injected token.[/error]")

    # Clean up env var for next test
    del os.environ[PDD_JWT_TOKEN_ENV]

    # 2. Device Flow (Mocked)
    # In a real scenario, this would trigger an interactive browser login.
    # We mock the internal async function to demonstrate the success path.
    console.print("\n[dim]Simulating interactive device flow login...[/dim]")
    
    # We need the API keys present for the check to pass before calling the async function
    os.environ[FIREBASE_API_KEY_ENV] = "test_key"
    os.environ[GITHUB_CLIENT_ID_ENV] = "test_id"

    # Mock the async device_flow_get_token function imported inside CloudConfig
    # Since we can't easily patch the internal import, we'll mock the result behavior
    # In a real integration test, you would patch 'pdd.core.cloud.device_flow_get_token'
    
    with patch('pdd.core.cloud.device_flow_get_token') as mock_auth:
        # Configure the mock to return a future (since it's awaited)
        import asyncio
        f = asyncio.Future()
        f.set_result("device_flow_generated_token_123")
        mock_auth.return_value = f

        # Call the method
        token = CloudConfig.get_jwt_token(verbose=True, app_name="Example App")
        
        if token == "device_flow_generated_token_123":
            console.print("[success]Successfully retrieved token via device flow![/success]")
        else:
            console.print("[error]Failed to retrieve token via device flow.[/error]")

    # Clean up
    if FIREBASE_API_KEY_ENV in os.environ: del os.environ[FIREBASE_API_KEY_ENV]
    if GITHUB_CLIENT_ID_ENV in os.environ: del os.environ[GITHUB_CLIENT_ID_ENV]
    console.print()


def example_endpoint_listing():
    """
    List all available cloud endpoints defined in the configuration.
    """
    console.print("[bold blue]=== Available Cloud Endpoints ===[/bold blue]")
    
    base = CloudConfig.get_base_url()
    
    # Create a simple table-like output
    console.print(f"{'Endpoint Name':<20} | {'Full URL'}")
    console.print("-" * 60)
    
    for name in CLOUD_ENDPOINTS:
        url = CloudConfig.get_endpoint_url(name)
        # Just show the relative part for brevity in example, or full url
        console.print(f"{name:<20} | {url}")
    console.print()


def main():
    """Run all examples."""
    console.print("[bold magenta]PDD Cloud Configuration Module Example[/bold magenta]\n")
    
    example_get_urls()
    example_cloud_enabled_check()
    example_authentication_flow()
    example_endpoint_listing()


if __name__ == "__main__":
    main()