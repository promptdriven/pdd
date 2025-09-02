#!/usr/bin/env python3
"""
Example usage of the PDD shell completion installation module.

This script demonstrates how to use the following functions from the pdd package:
  • get_local_pdd_path() -> str  
    Returns the absolute path to the PDD_PATH directory.  
    Input: None  
    Output: Absolute path as a string.
    
  • install_completion() -> None  
    Installs shell completion for the PDD CLI by:
      1. Detecting the current shell via get_current_shell().
      2. Determining the correct completion script filename using get_completion_script_extension().
      3. Looking up the local PDD_PATH (via get_local_pdd_path()).
      4. Locating the user’s shell RC file (via get_shell_rc_path()), 
         creating it if needed, and appending a source command if not already present.
    Input: None  
    Output: None (Feedback is provided via pretty printed messages using Rich.)

Note:
  • This example creates a dummy “home” directory (example_home) and a dummy PDD directory
    (example_pdd_path) under the current working directory. This ensures that the RC file and
    completion script are created safely without affecting your actual configuration.
    
To run the example:
  $ python example_install_completion.py
"""

import os
from rich import print as rprint

# In this example we assume that the pdd package is installed in a sibling directory.
# The PDD functions are imported from the package. (Adjust the import below if needed.)
from pdd.install_completion import get_local_pdd_path, install_completion

def setup_example_environment() -> None:
    """
    Set up the environment variables and create the required dummy files for the example.

    Environment variables and files created:
      - SHELL: Forced to "/bin/bash" so that get_completion_script_extension() returns "sh".
      - HOME: Set to a dummy home directory (example_home) which will serve to hold the shell RC file.
      - PDD_PATH: Set to a dummy absolute directory (example_pdd_path) that will contain the completion script.
      
    Also creates:
      - A dummy completion script file in example_pdd_path (named "pdd_completion.sh" for bash).
      - A dummy bash RC file in the example_home directory.
    """
    # Force the shell to bash.
    os.environ["SHELL"] = "/bin/bash"

    # Create a dummy home directory (so we don’t override the real ~/.bashrc)
    example_home = os.path.abspath("example_home")
    os.makedirs(example_home, exist_ok=True)
    os.environ["HOME"] = example_home

    # Create a dummy PDD_PATH directory where the completion script resides.
    example_pdd_path = os.path.abspath("pdd")
    os.makedirs(example_pdd_path, exist_ok=True)
    os.environ["PDD_PATH"] = example_pdd_path

    # Create a dummy completion script file.
    # For bash, get_completion_script_extension will return "sh", so we need "pdd_completion.sh"
    completion_script_filename = "pdd_completion.sh"
    completion_script_path = os.path.join(example_pdd_path, completion_script_filename)
    if not os.path.exists(completion_script_path):
        with open(completion_script_path, "w", encoding="utf-8") as cf:
            cf.write("# Dummy bash completion script for PDD CLI\n")
            cf.write("complete -W 'install update remove' pdd\n")
            
    # Create a dummy shell RC file.
    # For bash, get_shell_rc_path returns os.path.join(HOME, ".bashrc")
    rc_file = os.path.join(example_home, ".bashrc")
    if not os.path.exists(rc_file):
        os.makedirs(os.path.dirname(rc_file), exist_ok=True)
        with open(rc_file, "w", encoding="utf-8") as rf:
            rf.write("# Dummy bash RC file\n")
    rprint(f"[green]Example environment set up.[/green]\n  HOME: {example_home}\n  PDD_PATH: {example_pdd_path}")

def main() -> None:
    """
    Main function to run the example.
    
    Inputs: None (Environment variables and dummy files are created internally.)
    Outputs: None (Results are output to the console as pretty printed messages.)
    
    Example usage:
      $ python example_install_completion.py
    """
    setup_example_environment()
    rprint("[blue]Starting PDD shell completion installation example...[/blue]")

    # Retrieve and display the PDD_PATH using get_local_pdd_path.
    local_path = get_local_pdd_path()
    rprint(f"[cyan]Determined PDD_PATH: {local_path}[/cyan]")

    # Call install_completion() to update the user's shell RC file with the completion script.
    install_completion()

if __name__ == "__main__":
    main()