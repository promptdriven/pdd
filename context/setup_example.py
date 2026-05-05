import os
import sys
import subprocess

# The PDD_PATH environment variable is already set to the root of the repository.
# This example demonstrates how to interact with the pdd-cli package
# defined in the setup.py module.

def run_pdd_setup_example():
    """
    Example script demonstrating how the pdd-cli module is structured and how
    the setup configuration defined in setup.py enables the CLI application.

    The setup.py file defines the metadata, dependencies, and entry points
    for the 'pdd' command.
    """
    
    # 1. Verify environment prerequisites
    # setup.py requires python >= 3.8 as specified in python_requires
    major, minor = sys.version_info[:2]
    if major < 3 or (major == 3 and minor < 8):
        print(f"Python 3.8+ is required. Current version: {major}.{minor}")
        sys.exit(0)

    # 2. Check for an API key often used by PDD workflows (e.g., OPENAI_API_KEY)
    # While setup.py installs dependencies, the logic in pdd/cli.py often requires keys.
    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        print("OPENAI_API_KEY not set. PDD commands typically require an LLM provider key.")
        # We continue the example to show CLI help even without a key

    print("--- PDD-CLI Setup & Entry Point Example ---")

    # 3. Demonstrate the Entry Point defined in setup.py
    # setup.py defines entry_points={'console_scripts': ['pdd=pdd.cli:cli']}
    # This means running 'pdd' in the shell calls the cli() function in pdd/cli.py.
    
    try:
        # We simulate calling the CLI to show it is correctly configured.
        # We use '--help' to ensure the script is non-interactive and runs to completion.
        print("Executing 'pdd --help' to verify entry point logic...")
        
        # Use subprocess to call the installed 'pdd' command.
        # Since the package is installed in the environment, this should resolve.
        result = subprocess.run(
            ["pdd", "--help"],
            capture_output=True,
            text=True,
            check=True
        )
        
        print("\nCLI Help Output Snippet:")
        # Print the first 10 lines of the help output
        print("\n".join(result.stdout.splitlines()[:10]))
        
    except (subprocess.CalledProcessError, FileNotFoundError):
        print("\nNote: The 'pdd' command was not found in the PATH.")
        print("In a real environment, you would run 'pip install -e .' in the directory")
        print("containing setup.py to register the 'pdd' console script.")

    # 4. Demonstrate module metadata extraction
    # Information based on setup.py parameters:
    package_info = {
        "name": "pdd-cli",
        "version": "0.0.228",
        "author": "pdd-auto-heal[bot]",
        "description": "PDD (Prompt-Driven Development) - A toolkit for AI-powered code generation",
        "dependencies_count": 33 # Counted from install_requires in setup.py
    }

    print(f"\nPackage Metadata Summary:")
    print(f"- Name: {package_info['name']}")
    print(f"- Version: {package_info['version']}")
    print(f"- Author: {package_info['author']}")
    print(f"- Managed Dependencies: {package_info['dependencies_count']} libraries")

    # 5. Handling Data Files
    # setup.py includes 'package_data' for templates and CSVs.
    # Example of how pdd would access its own internal CSV:
    csv_rel_path = "pdd/data/llm_model.csv"
    full_csv_path = os.path.join(os.environ.get("PDD_PATH", "."), csv_rel_path)
    
    if os.path.exists(full_csv_path):
        print(f"\nFound internal data asset: {csv_rel_path}")
    else:
        print(f"\nData asset not found at {full_csv_path}. Ensure PDD_PATH is correct.")

    print("\nExample completed successfully.")

if __name__ == "__main__":
    run_pdd_setup_example()