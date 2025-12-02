#!/usr/bin/env python3
"""
Example usage of the PDD utility commands module.

This script demonstrates how to use the following Click commands from pdd.commands.utility:

  • install_completion_cmd (Click command)
    Installs shell completion for the PDD CLI.
    Input: Click context with optional 'quiet' flag in ctx.obj
    Output: None (installs completion scripts and updates shell RC file)

  • verify (Click command)
    Verifies code using a verification program with iterative fixing.
    Input:
      - prompt_file (str): Path to the prompt file that generated the code
      - code_file (str): Path to the code file to verify
      - verification_program (str): Path to the verification program to run
      - output_code (Optional[str]): Where to save verified code file
      - output_program (Optional[str]): Where to save verified program file
      - output_results (Optional[str]): Where to save results log
      - max_attempts (int): Maximum verification attempts (default: 3)
      - budget (float): Maximum cost in USD allowed (default: 5.0)
    Output:
      - Tuple containing:
        - result dict with keys: success (bool), program_code (str),
          code_content (str), attempts (int)
        - total_cost (float): Cost in USD
        - model_name (str): Name of the model used

Note:
  This example creates dummy files in the './output' directory to demonstrate
  the verify command workflow. The install_completion command is shown but
  not executed to avoid modifying your shell configuration.

To run the example:
  $ python utility_example.py
"""

import os
import sys
import textwrap
from pathlib import Path

import click
from rich import print as rprint

# Import the utility commands from the pdd package
from pdd.commands.utility import install_completion_cmd, verify


def setup_output_directory() -> Path:
    """
    Create the output directory for example files.
    
    Returns:
        Path: The path to the output directory.
    """
    output_dir = Path("./output")
    output_dir.mkdir(exist_ok=True)
    return output_dir


def create_example_files(output_dir: Path) -> dict:
    """
    Create example files needed for the verify command demonstration.
    
    Args:
        output_dir: Directory where files will be created.
        
    Returns:
        dict: Paths to created files with keys 'prompt', 'code', 'verification'.
    """
    # Create a prompt file describing a simple calculator module
    prompt_content = textwrap.dedent("""
        Create a Python module 'calculator.py' with the following functions:
        
        1. add(a: int, b: int) -> int
           Returns the sum of two integers.
           
        2. multiply(a: int, b: int) -> int
           Returns the product of two integers.
           
        Both functions should handle integer inputs and return integer results.
    """)
    
    # Create code with an intentional bug (multiply subtracts instead of multiplies)
    code_content = textwrap.dedent('''\
        # calculator.py
        """Simple calculator module with basic arithmetic operations."""
        
        def add(a: int, b: int) -> int:
            """Returns the sum of two integers."""
            return a + b
        
        def multiply(a: int, b: int) -> int:
            """Returns the product of two integers (intentionally buggy)."""
            return a - b  # Bug: should be a * b
    ''')
    
    # Create a verification program that tests the calculator functions
    verification_content = textwrap.dedent('''\
        #!/usr/bin/env python3
        """Verification program for calculator module."""
        import sys
        sys.path.insert(0, "./output")
        
        # Import the calculator module from output directory
        import calculator
        
        print("Running calculator verification...")
        
        # Test add function
        result_add = calculator.add(5, 3)
        print(f"add(5, 3) = {result_add}")
        assert result_add == 8, f"add(5, 3) should be 8, got {result_add}"
        
        # Test multiply function
        result_mul = calculator.multiply(4, 3)
        print(f"multiply(4, 3) = {result_mul}")
        assert result_mul == 12, f"multiply(4, 3) should be 12, got {result_mul}"
        
        print("All verifications passed!")
        sys.exit(0)
    ''')
    
    # Write files to output directory
    prompt_file = output_dir / "calculator.prompt"
    code_file = output_dir / "calculator.py"
    verification_file = output_dir / "verify_calculator.py"
    
    prompt_file.write_text(prompt_content)
    code_file.write_text(code_content)
    verification_file.write_text(verification_content)
    
    rprint(f"[green]Created example files in {output_dir}:[/green]")
    rprint(f"  - Prompt: {prompt_file.name}")
    rprint(f"  - Code (with bug): {code_file.name}")
    rprint(f"  - Verification: {verification_file.name}")
    
    return {
        "prompt": str(prompt_file),
        "code": str(code_file),
        "verification": str(verification_file),
    }


def demonstrate_install_completion():
    """
    Demonstrate the install_completion_cmd command structure.
    
    Note: This does not actually run the command to avoid modifying
    your shell configuration. It shows how the command would be invoked.
    """
    rprint("\n[bold blue]=== install_completion Command ===[/bold blue]")
    rprint("""
The install_completion_cmd is a Click command that installs shell completion
for the PDD CLI. It:

1. Detects your current shell (bash, zsh, fish)
2. Locates the appropriate completion script in PDD_PATH
3. Updates your shell RC file to source the completion script

[yellow]Usage via CLI:[/yellow]
  $ pdd install_completion

[yellow]Programmatic invocation (not recommended for normal use):[/yellow]
""")
    
    # Show how the command is structured
    rprint(f"  Command name: {install_completion_cmd.name}")
    rprint(f"  Help text: {install_completion_cmd.help}")
    
    rprint("\n[cyan]Skipping actual execution to avoid modifying shell config.[/cyan]")


def demonstrate_verify_command(files: dict, output_dir: Path):
    """
    Demonstrate the verify command with example files.
    
    Args:
        files: Dictionary with paths to prompt, code, and verification files.
        output_dir: Directory for output files.
    """
    rprint("\n[bold blue]=== verify Command ===[/bold blue]")
    rprint("""
The verify command verifies code using a verification program and iteratively
fixes issues using an LLM. It:

1. Runs the verification program against the code
2. Uses an LLM to judge if output matches prompt intent
3. Iteratively fixes code if verification fails
4. Continues until success, max attempts, or budget exhausted

[yellow]Command Options:[/yellow]
  --output-code PATH      Where to save verified code
  --output-program PATH   Where to save verified program
  --output-results PATH   Where to save results log
  --max-attempts INT      Maximum fix attempts (default: 3)
  --budget FLOAT          Maximum cost in USD (default: 5.0)
""")
    
    # Define output paths
    output_code = str(output_dir / "calculator_verified.py")
    output_program = str(output_dir / "verify_calculator_verified.py")
    output_results = str(output_dir / "verify_results.log")
    
    rprint("\n[yellow]Example CLI invocation:[/yellow]")
    rprint(f"""
  $ pdd verify \\
      --output-code {output_code} \\
      --output-program {output_program} \\
      --output-results {output_results} \\
      --max-attempts 3 \\
      --budget 2.0 \\
      {files['prompt']} \\
      {files['code']} \\
      {files['verification']}
""")
    
    rprint("[yellow]Programmatic invocation using Click's testing utilities:[/yellow]")
    rprint("""
    from click.testing import CliRunner
    from pdd.commands.utility import verify
    
    runner = CliRunner()
    result = runner.invoke(verify, [
        '--output-code', 'output/calculator_verified.py',
        '--output-program', 'output/verify_calculator_verified.py', 
        '--output-results', 'output/verify_results.log',
        '--max-attempts', '3',
        '--budget', '2.0',
        'output/calculator.prompt',
        'output/calculator.py',
        'output/verify_calculator.py'
    ], obj={'quiet': False, 'strength': 0.5, 'temperature': 0.0})
""")
    
    # Show command structure
    rprint("\n[cyan]Command structure:[/cyan]")
    rprint(f"  Command name: {verify.name}")
    rprint(f"  Help text: {verify.help}")
    rprint(f"  Parameters: {[p.name for p in verify.params]}")
    
    rprint("\n[cyan]Note: Actual execution requires valid API keys and LLM access.[/cyan]")
    rprint("[cyan]The verify command is decorated with @track_cost for usage tracking.[/cyan]")


def show_return_value_structure():
    """
    Document the return value structure of the verify command.
    """
    rprint("\n[bold blue]=== verify Command Return Value ===[/bold blue]")
    rprint("""
When the verify command succeeds, it returns a tuple with three elements:

[yellow]Return Value Structure:[/yellow]
  Tuple[Optional[dict], float, str]:
  
  1. result (dict or None):
     - success (bool): Whether verification passed
     - program_code (str): Final program code content
     - code_content (str): Final verified code content  
     - attempts (int): Number of fix attempts made
     
  2. total_cost (float): 
     Total cost of the operation in USD
     
  3. model_name (str):
     Name of the LLM model used for verification/fixing

[yellow]Example return value:[/yellow]
  (
      {
          'success': True,
          'program_code': '#!/usr/bin/env python3\\n...',
          'code_content': '# calculator.py\\ndef add(a, b):\\n...',
          'attempts': 2
      },
      0.0234,  # Cost in USD
      'gpt-4'  # Model name
  )

[yellow]On error:[/yellow]
  Returns None (error is handled via handle_error function)
""")


def main():
    """
    Main function demonstrating the utility commands module.
    
    This example:
    1. Creates example files for demonstration
    2. Shows install_completion command structure
    3. Demonstrates verify command usage
    4. Documents return value structures
    """
    rprint("[bold magenta]=== PDD Utility Commands Example ===[/bold magenta]")
    rprint("This example demonstrates the utility commands in pdd.commands.utility\n")
    
    # Setup output directory and create example files
    output_dir = setup_output_directory()
    files = create_example_files(output_dir)
    
    # Demonstrate each command
    demonstrate_install_completion()
    demonstrate_verify_command(files, output_dir)
    show_return_value_structure()
    
    rprint("\n[bold magenta]=== Example Complete ===[/bold magenta]")
    rprint(f"Example files are available in: {output_dir.absolute()}")
    rprint("Run 'pdd verify --help' for full command documentation.")


if __name__ == "__main__":
    main()
