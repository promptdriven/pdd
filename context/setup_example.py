import os
import sys
import subprocess

# The pdd-cli is primarily a CLI tool configured via setup.py.
# This example demonstrates how to install the package and verify the entry points
# defined in the setup configuration provided.

def run_pdd_setup_example():
    """
    Example of how the pdd-cli setup.py defines the package structure and CLI.

    The setup.py module defines:
    1. Package Identity: name='pdd-cli', version='0.0.229'
    2. Dependencies: A wide array of AI and CLI tools (openai, click, litellm, etc.)
    3. Entry Points: Maps the 'pdd' command to 'pdd.cli:cli'
    4. Data Files: Templates and CSV data files required for operation
    """

    # Ensure we are in a clean directory for output
    output_dir = './output'
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    print("--- PDD-CLI Setup Configuration Summary ---")

    # 1. Verification of the Entry Point
    # The setup.py defines: entry_points={'console_scripts': ['pdd=pdd.cli:cli']}
    # This means once installed via `pip install .`, the user runs `pdd` in the shell.

    print("Setup.py defines the CLI entry point as: 'pdd=pdd.cli:cli'")

    # 2. Simulating a CLI invocation
    # In a real environment, the user would run: pdd --version
    # Since the package is already installed in this environment, we can invoke it.
    try:
        # Using subprocess to simulate the console_script 'pdd' defined in setup.py
        result = subprocess.run(["pdd", "--version"], capture_output=True, text=True, check=True)
        print(f"Successfully verified pdd installation. Version: {result.stdout.strip()}")
    except (subprocess.CalledProcessError, FileNotFoundError):
        print("Note: 'pdd' command not found in PATH. Ensure 'pip install -e .' was run.")

    # 3. Demonstrating configuration detection
    # setup.py includes 'package_data' for templates and csv data.
    # These are stored relative to the 'pdd' package root.
    pdd_root = os.environ.get("PDD_PATH", ".")

    # We search for the llm_model.csv defined in setup.py's package_data
    model_data_path = os.path.join(pdd_root, "pdd", "data", "llm_model.csv")

    if os.path.exists(model_data_path):
        print(f"Confirmed existence of bundled data file: {model_data_path}")
        # The llm_model.csv contains costs in dollars per million tokens
        with open(model_data_path, 'r') as f:
            first_few_lines = [next(f) for _ in range(3)]
            print("Example Model Data (defines costs and ELO):")
            for line in first_few_lines:
                print(f"  {line.strip()}")
    else:
        print(f"Bundle data not found at {model_data_path}. Check PDD_PATH configuration.")

    # 4. Programmatic access to the Click CLI
    # The setup.py entry point maps to pdd.cli:cli
    try:
        from pdd.cli import cli
        print("\nTesting Click CLI initialization (simulating 'pdd --help' programmatically):")
        # context_settings allow us to run the Click command without exiting the process
        cli.main(args=["--help"], prog_name="pdd", standalone_mode=False)
    except ImportError:
        print("\nCould not import pdd.cli. Ensure the package is installed.")
    except Exception as e:
        # click.exceptions.Exit is normal here if standalone_mode is True,
        # but handled gracefully with False.
        pass

    print("\n--- Setup Example Complete ---")
    print("To use this module as intended by setup.py, run commands via your terminal:")
    print("  $ pdd setup")
    print("  $ pdd sync --force <module_name>")

if __name__ == "__main__":
    run_pdd_setup_example()
