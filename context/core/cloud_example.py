#!/usr/bin/env python3
"""
Example usage of the pdd.core.cloud module.

This module demonstrates how to use the centralized cloud configuration for PDD CLI commands.
It covers:
1. Retrieving cloud base URLs and specific endpoint URLs.
2. Handling environment variable overrides for custom cloud deployments.
3. Authenticating with the cloud service using JWT tokens (simulated).
4. Checking if cloud features are enabled based on API keys.

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

# Ensure the pdd package is in the python path
# This allows importing from pdd.core.cloud even if running this script directly
current_dir = Path(__file__).resolve().parent
project_root = current_dir.parents[2]  # Adjust based on file depth
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from rich.console import Console

# Import the CloudConfig class and constants from the module
from pdd.core.cloud import (
    CloudConfig,
    CLOUD_ENDPOINTS,
    PDD_CLOUD_URL_ENV,
    PDD_JWT_TOKEN_ENV,
    FIREBASE_API_KEY_ENV,
    GITHUB_CLIENT_ID_ENV,
)

console = Console()


def example_url_configuration():
    """
    Demonstrate how to retrieve cloud URLs.
    
    This shows:
    - Getting the default base URL.
    - Getting specific endpoint URLs (e.g., for generating code).
    - How environment variables override these URLs (useful for local testing).
    """
    console.print("[bold blue]=== URL Configuration Example ===[/bold blue]")

    # 1. Default Configuration
    # By default, this points to the production cloud functions
    base_url = CloudConfig.get_base_url()
    console.print(f"Default Base URL: [green]{base_url}[/green]")

    generate_url = CloudConfig.get_endpoint_url("generateCode")
    console.print(f"Generate Endpoint: [green]{generate_url}[/green]")

    # 2. Custom Configuration (e.g., Local Emulator)
    # We simulate setting the environment variable for a local emulator
    console.print("\n[dim]Simulating local emulator environment...[/dim]")
    original_url_env = os.environ.get(PDD_CLOUD_URL_ENV)
    
    try:
        # Set a custom URL (like a local firebase emulator)
        os.environ[PDD_CLOUD_URL_ENV] = "http://127.0.0.1:5001/pdd-project/us-central1"
        
        local_base = CloudConfig.get_base_url()
        console.print(f"Local Base URL: [yellow]{local_base}[/yellow]")
        
        # The endpoint builder appends the correct path to the custom base
        local_sync = CloudConfig.get_endpoint_url("syncState")
        console.print(f"Local Sync Endpoint: [yellow]{local_sync}[/yellow]")
        
    finally:
        # Cleanup: Restore original environment
        if original_url_env:
            os.environ[PDD_CLOUD_URL_ENV] = original_url_env
        else:
            if PDD_CLOUD_URL_ENV in os.environ:
                del os.environ[PDD_CLOUD_URL_ENV]
    console.print()


def example_authentication_flow():
    """
    Demonstrate how to retrieve authentication tokens.
    
    This shows:
    - Checking for a pre-injected token (CI/Testing scenario).
    - How the system behaves when auth is missing (simulated).
    
    Note: We do not demonstrate the interactive device flow here to avoid 
    blocking execution, but we show how to trigger it.
    """
    console.print("[bold blue]=== Authentication Flow Example ===[/bold blue]")

    # 1. CI/Testing Scenario (Pre-injected Token)
    # This is the fastest path and avoids user interaction
    console.print("[dim]Simulating CI environment with injected token...[/dim]")
    
    original_token = os.environ.get(PDD_JWT_TOKEN_ENV)
    dummy_token = "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.dummy_payload.signature"
    
    try:
        os.environ[PDD_JWT_TOKEN_ENV] = dummy_token
        
        # verbose=True prints status messages to the console
        token = CloudConfig.get_jwt_token(verbose=True, app_name="Example Script")
        
        if token == dummy_token:
            console.print("[success]Successfully retrieved injected token![/success]")
        else:
            console.print("[error]Failed to retrieve injected token.[/error]")
            
    finally:
        # Cleanup
        if original_token:
            os.environ[PDD_JWT_TOKEN_ENV] = original_token
        else:
            if PDD_JWT_TOKEN_ENV in os.environ:
                del os.environ[PDD_JWT_TOKEN_ENV]

    # 2. Missing Credentials Scenario
    # If we clear environment variables, we can see how it handles missing config
    console.print("\n[dim]Simulating missing API keys...[/dim]")
    
    # Save original keys
    orig_firebase = os.environ.get(FIREBASE_API_KEY_ENV)
    orig_github = os.environ.get(GITHUB_CLIENT_ID_ENV)
    
    # Temporarily unset keys to force a failure state for demonstration
    if FIREBASE_API_KEY_ENV in os.environ: del os.environ[FIREBASE_API_KEY_ENV]
    if GITHUB_CLIENT_ID_ENV in os.environ: del os.environ[GITHUB_CLIENT_ID_ENV]
    
    try:
        # This should fail gracefully and return None because keys are missing
        # and interactive auth cannot proceed without them.
        token = CloudConfig.get_jwt_token(verbose=True)
        
        if token is None:
            console.print("[info]Auth correctly returned None when keys are missing.[/info]")
        else:
            console.print(f"[error]Unexpectedly got token: {token}[/error]")
            
    finally:
        # Restore keys
        if orig_firebase: os.environ[FIREBASE_API_KEY_ENV] = orig_firebase
        if orig_github: os.environ[GITHUB_CLIENT_ID_ENV] = orig_github
    console.print()


def example_feature_flags():
    """
    Demonstrate checking if cloud features are enabled.
    
    Cloud features are considered 'enabled' if the necessary API keys
    (Firebase and GitHub) are present in the environment.
    """
    console.print("[bold blue]=== Feature Flag Example ===[/bold blue]")

    # 1. Check status
    is_enabled = CloudConfig.is_cloud_enabled()
    
    if is_enabled:
        console.print("[success]Cloud features are ENABLED.[/success]")
        console.print("API keys for Firebase and GitHub were found in environment.")
    else:
        console.print("[warning]Cloud features are DISABLED.[/warning]")
        console.print("Missing API keys. Cloud commands will likely fail or fallback to local mode.")
    
    # 2. List available endpoints
    console.print("\n[dim]Available Cloud Endpoints:[/dim]")
    for name, path in CLOUD_ENDPOINTS.items():
        console.print(f"  - {name}: {path}")
    console.print()


def main():
    """Run all cloud configuration examples."""
    console.print("[bold]PDD Cloud Configuration Examples[/bold]\n")
    
    example_url_configuration()
    example_authentication_flow()
    example_feature_flags()


if __name__ == "__main__":
    main()