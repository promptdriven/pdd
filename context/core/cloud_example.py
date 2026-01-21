#!/usr/bin/env python3
"""
Example usage of the CloudConfig module.

This script demonstrates how to use the centralized cloud configuration
for PDD CLI commands. It covers:
1. Retrieving cloud endpoint URLs.
2. Handling environment variable overrides.
3. Checking if cloud features are enabled.
4. Retrieving JWT tokens for authentication.
5. Configuring cloud request timeouts via PDD_CLOUD_TIMEOUT.

File structure (relative to project root):
    pdd/
        core/
            cloud_config.py   # The module being demonstrated
    context/
        core/
            cloud_config_example.py  # This example file
"""

import asyncio
import os
import sys
from unittest.mock import patch, MagicMock

# Ensure the project root is in sys.path so we can import the module
# This allows running the example directly from the context/core directory
project_root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

# Import the CloudConfig class and constants from the module
# Note: Adjust the import path based on your actual package structure
try:
    from pdd.core.cloud_config import (
        CloudConfig,
        CLOUD_ENDPOINTS,
        PDD_CLOUD_URL_ENV,
        PDD_JWT_TOKEN_ENV,
        PDD_CLOUD_TIMEOUT_ENV,
        DEFAULT_CLOUD_TIMEOUT,
        FIREBASE_API_KEY_ENV,
        GITHUB_CLIENT_ID_ENV,
        get_cloud_timeout,
    )
except ImportError:
    # Fallback for when running in a flat directory structure during testing
    try:
        from cloud_config import (
            CloudConfig,
            CLOUD_ENDPOINTS,
            PDD_CLOUD_URL_ENV,
            PDD_JWT_TOKEN_ENV,
            PDD_CLOUD_TIMEOUT_ENV,
            DEFAULT_CLOUD_TIMEOUT,
            FIREBASE_API_KEY_ENV,
            GITHUB_CLIENT_ID_ENV,
            get_cloud_timeout,
        )
    except ImportError:
        print("Error: Could not import CloudConfig. Please ensure the module is in the python path.")
        sys.exit(1)


def print_header(title: str) -> None:
    """Helper to print a styled header."""
    print("\n" + "=" * 60)
    print(f" {title}")
    print("=" * 60)


def example_url_configuration() -> None:
    """
    Demonstrates how to retrieve base URLs and specific endpoint URLs.
    Shows how environment variables can override defaults.
    """
    print_header("1. URL Configuration")

    # 1. Default Behavior
    print("--- Default Configuration ---")
    base_url = CloudConfig.get_base_url()
    print(f"Default Base URL: {base_url}")
    
    gen_url = CloudConfig.get_endpoint_url("generateCode")
    print(f"Generate Endpoint: {gen_url}")

    # 2. Overriding with Environment Variable (e.g., for local emulator)
    print("\n--- Custom Configuration (Emulator) ---")
    emulator_url = "http://127.0.0.1:5001/my-project/us-central1"
    
    # We use patch.dict to simulate setting the environment variable safely
    with patch.dict(os.environ, {PDD_CLOUD_URL_ENV: emulator_url}):
        custom_base = CloudConfig.get_base_url()
        print(f"Custom Base URL:   {custom_base}")
        
        sync_url = CloudConfig.get_endpoint_url("syncState")
        print(f"Sync Endpoint:     {sync_url}")
        
        # Verify it constructed the path correctly
        expected_sync = f"{emulator_url}{CLOUD_ENDPOINTS['syncState']}"
        assert sync_url == expected_sync
        print("✅ URL construction verified correctly.")


def example_cloud_enabled_check() -> None:
    """
    Demonstrates checking if cloud features are enabled based on API keys.
    """
    print_header("2. Cloud Enabled Check")

    # Case 1: Missing keys
    with patch.dict(os.environ, {}, clear=True):
        is_enabled = CloudConfig.is_cloud_enabled()
        print(f"With no env vars: Cloud Enabled? {is_enabled}")

    # Case 2: Keys present
    mock_env = {
        FIREBASE_API_KEY_ENV: "dummy_firebase_key",
        GITHUB_CLIENT_ID_ENV: "dummy_github_id"
    }
    with patch.dict(os.environ, mock_env):
        is_enabled = CloudConfig.is_cloud_enabled()
        print(f"With keys present: Cloud Enabled? {is_enabled}")


def example_jwt_token_handling() -> None:
    """
    Demonstrates retrieving the JWT token.
    1. Shows priority of PDD_JWT_TOKEN_ENV (CI/Testing mode).
    2. Shows fallback to device flow (mocked).
    """
    print_header("3. JWT Token Handling")

    # Scenario A: Token injected via Environment Variable (CI/Testing)
    print("--- Scenario A: Token from Environment ---")
    test_token = "eyJhbGciOiJIUzI1NiJ9.test_payload.signature"
    
    with patch.dict(os.environ, {PDD_JWT_TOKEN_ENV: test_token}):
        token = CloudConfig.get_jwt_token(verbose=True)
        print(f"Retrieved Token: {token[:15]}... (truncated)")
        
        if token == test_token:
            print("✅ Successfully retrieved token from environment.")
        else:
            print("❌ Failed to retrieve token from environment.")

    # Scenario B: Interactive Device Flow (Mocked)
    print("\n--- Scenario B: Interactive Device Flow ---")
    
    # We need API keys present for the device flow to trigger
    env_vars = {
        FIREBASE_API_KEY_ENV: "valid_key",
        GITHUB_CLIENT_ID_ENV: "valid_id"
    }
    
    # We mock the async device_flow_get_token function to avoid actual network calls
    with patch.dict(os.environ, env_vars):
        # We must patch where it is imported IN CloudConfig, not where it is defined
        # Assuming CloudConfig imports it as 'device_flow_get_token'
        with patch('pdd.core.cloud.device_flow_get_token') as mock_flow:
            # Setup the mock to return a future (since it's awaited in asyncio.run)
            future = asyncio.Future()
            future.set_result("device_flow_generated_token_123")
            mock_flow.return_value = future
            
            # Call the method
            token = CloudConfig.get_jwt_token(verbose=True, app_name="Example App")
            
            print(f"Retrieved Token: {token}")
            if token == "device_flow_generated_token_123":
                print("✅ Successfully retrieved token via device flow mock.")
            else:
                print("❌ Failed to retrieve token via device flow.")


def example_cloud_timeout() -> None:
    """
    Demonstrates how to retrieve and configure cloud request timeouts.
    Shows how the PDD_CLOUD_TIMEOUT environment variable can override the default.
    """
    print_header("4. Cloud Timeout Configuration")

    # Default timeout (900 seconds / 15 minutes)
    print("--- Default Configuration ---")
    timeout = get_cloud_timeout()
    print(f"Default Timeout: {timeout} seconds ({timeout / 60:.1f} minutes)")
    print(f"DEFAULT_CLOUD_TIMEOUT constant: {DEFAULT_CLOUD_TIMEOUT}")

    # Custom timeout via environment variable
    print("\n--- Custom Configuration ---")
    custom_timeout = "300"  # 5 minutes

    with patch.dict(os.environ, {PDD_CLOUD_TIMEOUT_ENV: custom_timeout}):
        timeout = get_cloud_timeout()
        print(f"Custom Timeout:  {timeout} seconds ({timeout / 60:.1f} minutes)")

        if timeout == int(custom_timeout):
            print("✅ Successfully retrieved custom timeout from environment.")
        else:
            print("❌ Failed to retrieve custom timeout from environment.")

    # Invalid value falls back to default
    print("\n--- Invalid Configuration (Fallback) ---")
    with patch.dict(os.environ, {PDD_CLOUD_TIMEOUT_ENV: "invalid_value"}):
        timeout = get_cloud_timeout()
        print(f"Timeout with invalid env var: {timeout} seconds")

        if timeout == DEFAULT_CLOUD_TIMEOUT:
            print("✅ Correctly fell back to default for invalid value.")
        else:
            print("❌ Did not fall back to default for invalid value.")


def example_error_handling() -> None:
    """
    Demonstrates how the configuration handles missing keys during auth.
    """
    print_header("5. Error Handling")

    print("--- Missing API Keys ---")
    # Ensure environment is empty of keys
    with patch.dict(os.environ, {}, clear=True):
        # This should fail gracefully and return None, printing an error to console
        token = CloudConfig.get_jwt_token(verbose=True)
        
        if token is None:
            print("✅ Correctly returned None when API keys are missing.")
        else:
            print(f"❌ Unexpectedly returned a token: {token}")


def main() -> None:
    """
    Run all examples.
    """
    print("Running CloudConfig Examples...")

    # 1. URL Configuration
    example_url_configuration()

    # 2. Cloud Enabled Check
    example_cloud_enabled_check()

    # 3. JWT Token Handling
    # Note: This uses mocks to simulate the async device flow
    example_jwt_token_handling()

    # 4. Cloud Timeout Configuration
    example_cloud_timeout()

    # 5. Error Handling
    example_error_handling()

    print("\nAll examples completed.")


if __name__ == "__main__":
    main()