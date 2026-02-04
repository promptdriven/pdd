#!/usr/bin/env python3
"""
Example usage of the python_env_detector module.
This script demonstrates how to detect the host Python environment
and retrieve environment information using the module's functions.
"""
from pdd.python_env_detector import (
    detect_host_python_executable,
    get_environment_info,
    is_in_virtual_environment,
    get_environment_type
)

def main():
    """Main function to demonstrate module usage."""
    print("=== Python Environment Detection Example ===\n")
    
    # Detect and display the host Python executable
    host_python = detect_host_python_executable()
    print(f"Host Python executable: {host_python}\n")
    
    # Check if running in a virtual environment
    in_venv = is_in_virtual_environment()
    print(f"Running in virtual environment: {in_venv}\n")
    
    # Get environment type
    env_type = get_environment_type()
    print(f"Environment type: {env_type}\n")
    
    # Get detailed environment information
    env_info = get_environment_info()
    print("Detailed environment information:")
    for key, value in env_info.items():
        print(f"  {key}: {value}")

if __name__ == "__main__":
    main()

