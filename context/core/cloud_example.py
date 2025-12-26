#!/usr/bin/env python3
"""
Example usage of the pdd.core.cloud module.

This module provides centralized cloud configuration and authentication handling
for PDD CLI commands. It manages:
- Cloud function URLs (base URLs and specific endpoints)
- JWT token retrieval (via environment variables or device flow)
- Cloud feature availability checks

File structure (relative to project root):
    pdd/
        core/
            cloud.py          # The module being demonstrated
    context/
        core/
            cloud_example.py  # This example file
"""

import os
import sys
from pathlib import Path

# Ensure output directory exists
script_dir = os.path.dirname(os.path.abspath(__file__))
output_dir = os.path.join(script_dir, "output")
os.makedirs(output_dir, exist_ok=True)

# Add project root to sys.path to allow importing pdd module
# Assuming script is in context/core/, project root is ../../
project_root = os.path.abspath(os.path.join(script_dir, "../../"))
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

# Import rich console for output
from rich.console import Console

console = Console()


def example_cloud_urls():
    """
    Demonstrate how to retrieve cloud URLs using CloudConfig.
    
    This shows:
    1. Getting the default base URL
    2. Getting specific endpoint URLs
    3. Overriding the base URL via environment variables (e.g., for local testing)
    """
    console.print("[bold cyan]=== Cloud URL Configuration ===[/bold cyan]")

    # 1. Default Configuration
    base_url = CloudConfig.get_base_url()
    console.print(f"Default Base URL: [green]{base_url}[/green]")

    # 2. Specific Endpoints
    # CloudConfig.get_endpoint_url handles path construction automatically
    console.print("\n[bold]Endpoint URLs:[/bold]")
    for name in CLOUD_ENDPOINTS:
        url = CloudConfig.get_endpoint_url(name)
        console.print(f"  - {name}: [blue]{url}[/blue]")

    # 3. Environment Override (Simulating a local emulator)
    console.print("\n[bold]Simulating Local Emulator Override:[/bold]")
    
    # Save original env var if it exists
    original_url = os.environ.get(PDD_CLOUD_URL_ENV)
    
    try:
        # Set a local emulator URL
        local_url = "http://127.0.0.1:5001/pdd-project/us-central1"
        os.environ[PDD_CLOUD_URL_ENV] = local_url
        
        console.print(f"  Set {PDD_CLOUD_URL_ENV} = {local_url}")
        
        # Verify the override works
        new_base = CloudConfig.get_base_url()
        new_endpoint = CloudConfig.get_endpoint_url("generateCode")
        
        console.print(f"  Overridden Base URL: [green]{new_base}[/green]")
        console.print(f"  Overridden Endpoint: [blue]{new_endpoint}[/blue]")
        
    finally:
        # Restore environment
        if original_url:
            os.environ[PDD_CLOUD_URL_ENV] = original_url
        else:
            if PDD_CLOUD_URL_ENV in os.environ:
                del os.environ[PDD_CLOUD_URL_ENV]
    console.print()


def example_cloud_availability():
    """
    Demonstrate checking if cloud features are enabled.
    
    Cloud features require specific API keys to be present in the environment.
    """
    console.print("[bold cyan]=== Cloud Availability Check ===[/bold cyan]")

    # Check current status
    is_enabled = CloudConfig.is_cloud_enabled()
    console.print(f"Cloud Enabled: [yellow]{is_enabled}[/yellow]")
    
    if not is_enabled:
        console.print("[dim]Cloud features are disabled because API keys are missing.[/dim]")
        console.print(f"[dim]Required: {FIREBASE_API_KEY_ENV}, {GITHUB_CLIENT_ID_ENV}[/dim]")
    else:
        console.print("[green]Cloud features are ready to use.[/green]")
    console.print()


def example_authentication_flow():
    """
    Demonstrate the authentication flow logic.
    
    Note: This example mocks the actual network calls to avoid interactive prompts
    or actual authentication requests during the demo run. It focuses on how
    the CloudConfig.get_jwt_token method prioritizes environment variables.
    """
    console.print("[bold cyan]=== Authentication Flow ===[/bold cyan]")

    # 1. Testing/CI Flow (Token Injection)
    # This is the preferred method for CI/CD pipelines or automated tests
    console.print("[bold]Scenario 1: Token Injection (CI/Testing)[/bold]")
    
    fake_token = "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.fake.token"
    os.environ[PDD_JWT_TOKEN_ENV] = fake_token
    
    try:
        # When PDD_JWT_TOKEN is set, it returns immediately without network calls
        token = CloudConfig.get_jwt_token(verbose=True)
        console.print(f"  Retrieved Token: [green]{token[:15]}...[/green]")
        
        if token == fake_token:
            console.print("  [success]Successfully retrieved injected token[/success]")
            
    finally:
        # Clean up
        if PDD_JWT_TOKEN_ENV in os.environ:
            del os.environ[PDD_JWT_TOKEN_ENV]

    # 2. Interactive Flow (Explanation)
    console.print("\n[bold]Scenario 2: Interactive Device Flow[/bold]")
    console.print("  If PDD_JWT_TOKEN is not set, CloudConfig.get_jwt_token() will:")
    console.print("  1. Check for Firebase/GitHub credentials")
    console.print("  2. Initiate the Device Flow (async)")
    console.print("  3. Prompt the user to authorize via browser")
    console.print("  4. Return the JWT token or None on failure")
    
    console.print("\n  [dim]Skipping actual interactive auth for this non-interactive example.[/dim]")
    console.print()


def main():
    """
    Run all examples demonstrating the pdd.core.cloud module.
    """
    console.print("\n[bold white on blue] PDD Cloud Config Module Examples [/bold white on blue]\n")
    
    example_cloud_urls()
    example_cloud_availability()
    example_authentication_flow()

    console.print("[bold green]Examples completed successfully![/bold green]")


if __name__ == "__main__":
    main()