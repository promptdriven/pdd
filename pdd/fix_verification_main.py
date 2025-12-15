import sys
import os
import subprocess
import click
import logging
from pathlib import Path
from typing import Optional, Tuple, List, Dict, Any

# Use Rich for pretty printing to the console
from rich import print as rich_print
from rich.panel import Panel
from rich.syntax import Syntax
from rich.text import Text

# Internal imports using relative paths
from .construct_paths import construct_paths
from .fix_verification_errors import fix_verification_errors
from .fix_verification_errors_loop import fix_verification_errors_loop
# Import DEFAULT_STRENGTH from the main package
from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .python_env_detector import detect_host_python_executable

# Default values from the README
DEFAULT_TEMPERATURE = 0.0
DEFAULT_MAX_ATTEMPTS = 3
DEFAULT_BUDGET = 5.0

# Configure logging
logger = logging.getLogger(__name__)

# Define a constant for the verification program name
VERIFICATION_PROGRAM_NAME = "verification_program.py" # Example, adjust if needed

def run_program(program_path: str, args: List[str] = []) -> Tuple[bool, str, str]:
    """
    Executes a program file and captures its output.

    Args:
        program_path (str): The path to the executable program file.
        args (List[str]): Optional list of command-line arguments for the program.

    Returns:
        Tuple[bool, str, str]: A tuple containing:
            - bool: True if the program executed successfully (exit code 0), False otherwise.
            - str: The captured standard output.
            - str: The captured standard error.
    """
    try:
        # Determine the interpreter based on file extension (basic example)
        # A more robust solution might use the 'language' from construct_paths
        interpreter = []
        if program_path.endswith(".py"):
            interpreter = [detect_host_python_executable()] # Use environment-aware Python executable
        elif program_path.endswith(".js"):
            interpreter = ["node"]
        elif program_path.endswith(".sh"):
            interpreter = ["bash"]
        # Add other languages as needed

        command = interpreter + [program_path] + args
        rich_print(f"[dim]Running command:[/dim] {' '.join(command)}")
        rich_print(f"[dim]Working directory:[/dim] {os.path.dirname(program_path) if program_path else 'None'}")
        rich_print(f"[dim]Environment PYTHONPATH:[/dim] {os.environ.get('PYTHONPATH', 'Not set')}")

        # Create a copy of environment with PYTHONUNBUFFERED set
        env = os.environ.copy()
        env['PYTHONUNBUFFERED'] = '1'  # Force unbuffered output
        
        process = subprocess.run(
            command,
            capture_output=True,
            text=True,
            check=False, # Don't raise exception on non-zero exit code
            timeout=60, # Add a timeout to prevent hangs
            env=env, # Pass modified environment variables
            cwd=os.path.dirname(program_path) if program_path else None # Set working directory
        )

        success = process.returncode == 0
        stdout = process.stdout
        stderr = process.stderr

        if not success:
            rich_print(f"[yellow]Warning:[/yellow] Program '{os.path.basename(program_path)}' exited with code {process.returncode}.")
            
            # Check for syntax errors specifically
            if "SyntaxError" in stderr:
                rich_print("[bold red]Syntax Error Detected:[/bold red]")
                rich_print(Panel(stderr, border_style="red", title="Python Syntax Error"))
                # Return with special indicator for syntax errors
                return False, stdout, f"SYNTAX_ERROR: {stderr}"
            elif stderr:
                rich_print("[yellow]Stderr:[/yellow]")
                rich_print(Panel(stderr, border_style="yellow"))

        return success, stdout, stderr

    except FileNotFoundError:
        rich_print(f"[bold red]Error:[/bold red] Program file not found: '{program_path}'")
        return False, "", f"Program file not found: {program_path}"
    except subprocess.TimeoutExpired:
        rich_print(f"[bold red]Error:[/bold red] Program execution timed out: '{program_path}'")
        return False, "", f"Program execution timed out: {program_path}"
    except Exception as e:
        logger.error(f"An unexpected error occurred while running {program_path}: {e}")
        return False, "", f"An unexpected error occurred: {e}"

def fix_verification_main(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    program_file: str,
    output_results: Optional[str],
    output_code: Optional[str],
    output_program: Optional[str],
    loop: bool,
    verification_program: Optional[str],  # Only used if loop=True
    max_attempts: int = DEFAULT_MAX_ATTEMPTS,
    budget: float = DEFAULT_BUDGET,
    agentic_fallback: bool = True,
    strength: Optional[float] = None,
    temperature: Optional[float] = None,
) -> Tuple[bool, str, str, int, float, str]:
    """
    CLI wrapper for the 'verify' command. Verifies code correctness by running
    a program, using an LLM to judge its output against the prompt's intent,
    and potentially fixing the code iteratively.

    Args:
        ctx (click.Context): The Click context object.
        prompt_file (str): Path to the prompt file.
        code_file (str): Path to the code file to verify/fix.
        program_file (str): Path to the program to run for verification.
        output_results (Optional[str]): Path to save verification results log.
        output_code (Optional[str]): Path to save the verified code file.
        output_program (Optional[str]): Path to save the verified program file.
        loop (bool): If True, perform iterative verification and fixing.
        verification_program (Optional[str]): Path to a verification program (required if loop=True).
        max_attempts (int): Max attempts for the loop.
        budget (float): Max cost budget for the loop.

    Returns:
        Tuple[bool, str, str, int, float, str]:
            - success_status (bool): True if verification passed (or was fixed).
            - final_program (str): Content of the program file (potentially modified if loop=True).
            - final_code (str): Content of the code file after verification/fixing.
            - attempts (int): Number of attempts made.
            - total_cost (float): Total cost incurred.
            - model_name (str): Name of the LLM used.
    """
    # Extract global options from context (prefer passed parameters over ctx.obj)
    strength: float = strength if strength is not None else ctx.obj.get('strength', DEFAULT_STRENGTH)
    temperature: float = temperature if temperature is not None else ctx.obj.get('temperature', DEFAULT_TEMPERATURE)
    force: bool = ctx.obj.get('force', False)
    quiet: bool = ctx.obj.get('quiet', False)
    verbose: bool = ctx.obj.get('verbose', False)
    time: float = ctx.obj.get('time', DEFAULT_TIME) # Get time from context, default 0.25

    # --- Input Validation ---
    if loop and not verification_program:
        raise click.UsageError("The '--loop' option requires '--verification-program' to be specified.")

    if not quiet:
        rich_print(Panel(f"Starting Verification Process for [cyan]{os.path.basename(code_file)}[/cyan]", title="PDD Verify", border_style="blue"))
        rich_print(f"  Prompt: [green]{prompt_file}[/green]")
        rich_print(f"  Code: [green]{code_file}[/green]")
        rich_print(f"  Program: [green]{program_file}[/green]")
        if loop:
            rich_print(f"  Mode: [yellow]Iterative Loop[/yellow]")
            rich_print(f"  Verification Program: [green]{verification_program}[/green]")
            rich_print(f"  Max Attempts: {max_attempts}")
            rich_print(f"  Budget: ${budget:.2f}")
        else:
            rich_print(f"  Mode: [yellow]Single Pass[/yellow]")
        rich_print(f"  Strength: {strength}, Temperature: {temperature}")

    # ------------------- File-path handling -------------------
    input_file_paths: Dict[str, str] = {
        "prompt_file": prompt_file,
        "code_file": code_file,
        "program_file": program_file,
    }
    # verification_program is only needed as an *input file path* for the loop function
    if loop and verification_program:
         # Add verification_program path for construct_paths if loop is enabled
         # Although construct_paths doesn't read it, including it ensures consistency
         # and allows potential future use cases.
         input_file_paths["verification_program"] = verification_program

    command_options: Dict[str, Optional[str]] = {
        "output_results": output_results,
        "output_code": output_code,
        "output_program": output_program,
    }

    # Initial default values (in case we need the manual fallback)
    input_strings: Dict[str, str] = {}
    output_code_path: Optional[str] = output_code
    output_results_path: Optional[str] = output_results
    output_program_path: Optional[str] = output_program
    language: str = ""

    try:
        # First try the official helper.
        resolved_config, input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=force,
            quiet=quiet,
            command="verify",
            command_options=command_options,
            context_override=ctx.obj.get('context'),
            confirm_callback=ctx.obj.get('confirm_callback')
        )
        output_code_path = output_file_paths.get("output_code")
        output_results_path = output_file_paths.get("output_results")
        output_program_path = output_file_paths.get("output_program")

        if verbose:
            rich_print("[dim]Resolved output paths via construct_paths.[/dim]")

    except click.Abort:
        # User cancelled - re-raise to stop the sync loop
        raise
    except Exception as e:
        # If the helper does not understand the "verify" command fall back.
        if "invalid command" in str(e).lower():
            if verbose:
                rich_print(
                    "[yellow]construct_paths does not recognise "
                    "'verify'. Falling back to manual path handling.[/yellow]"
                )
            try:
                # Manually read the three mandatory files
                with open(prompt_file, "r") as f:
                    input_strings["prompt_file"] = f.read()
                with open(code_file, "r") as f:
                    input_strings["code_file"] = f.read()
                with open(program_file, "r") as f:
                    input_strings["program_file"] = f.read()
            except FileNotFoundError as fe:
                rich_print(f"[bold red]Error:[/bold red] {fe}")
                # Return error result instead of sys.exit(1) to allow orchestrator to handle gracefully
                return False, "", "", 0, 0.0, f"FileNotFoundError: {fe}"

            # Pick or build output paths
            if output_code_path is None:
                base, ext = os.path.splitext(code_file)
                output_code_path = f"{base}_verified{ext}"
            if output_results_path is None:
                base, _ = os.path.splitext(program_file)
                output_results_path = f"{base}_verify_results.log"
            if output_program_path is None:
                base_prog, ext_prog = os.path.splitext(program_file)
                output_program_path = f"{base_prog}_verified{ext_prog}"

            if program_file.endswith(".py"): language = "python"
            elif program_file.endswith(".js"): language = "javascript"
            elif program_file.endswith(".sh"): language = "bash"
        else:
            # Some other error – re‑raise / abort
            rich_print(f"[bold red]Error:[/bold red] Failed during path construction: {e}")
            if verbose:
                import traceback
                rich_print(Panel(traceback.format_exc(), title="Traceback", border_style="red"))
            # Return error result instead of sys.exit(1) to allow orchestrator to handle gracefully
            return False, "", "", 0, 0.0, f"Error: {e}"

    # --- Core Logic ---
    success: bool = False
    final_program: str = input_strings.get("program_file", "")
    final_code: str = input_strings.get("code_file", "")
    attempts: int = 0
    total_cost: float = 0.0
    model_name: str = "N/A"
    results_log_content: str = ""

    try:
        if loop:
            if not quiet:
                rich_print("[dim]Running Iterative Verification (fix_verification_errors_loop)...[/dim]")
            try:
                # Call fix_verification_errors_loop for iterative fixing
                loop_results = fix_verification_errors_loop(
                    program_file=program_file,                  # Changed to pass the program_file path
                    code_file=code_file,                        # Changed to pass the code_file path
                    prompt=input_strings["prompt_file"],        # Correctly passing prompt content
                    prompt_file=prompt_file,
                    verification_program=verification_program,      # Path to the verifier program
                    strength=strength,
                    temperature=temperature,
                    llm_time=time, # Changed 'time' to 'llm_time'
                    max_attempts=max_attempts,
                    budget=budget,
                    verification_log_file=output_results_path, # Use resolved output_results_path
                    # output_code_path should not be passed here
                    # output_program_path should not be passed here
                    verbose=verbose,
                    program_args=[], # Pass an empty list for program_args
                    agentic_fallback=agentic_fallback,
                )
                success = loop_results.get('success', False)
                final_program = loop_results.get('final_program', "") # Use .get for safety
                final_code = loop_results.get('final_code', "")       # Use .get for safety
                attempts = loop_results.get('total_attempts', 0)    # Use .get for safety
                total_cost = loop_results.get('total_cost', 0.0)    # Use .get for safety
                model_name = loop_results.get('model_name', "N/A")  # Use .get for safety
                # Capture full statistics if available
                # statistics = loop_results.get('statistics', {})
            except Exception as e:
                rich_print(f"[bold red]Error during loop execution:[/bold red] {e}")
                if verbose:
                    import traceback
                    rich_print(Panel(traceback.format_exc(), title="Traceback", border_style="red"))
                success = False
        else: # Single pass verification
            if not quiet:
                rich_print("\n[bold blue]Running Single Pass Verification (fix_verification_errors)...[/bold blue]")
            attempts = 1 # Single pass is one attempt

            # 1. Run the program file to get its output
            if not quiet:
                rich_print(f"Executing program: [cyan]{program_file}[/cyan]")
            run_success, program_stdout, program_stderr = run_program(program_file)
            program_output = program_stdout + ("\n--- STDERR ---\n" + program_stderr if program_stderr else "")

            if verbose:
                 rich_print("[dim]--- Program Output ---[/dim]")
                 rich_print(Panel(program_output if program_output else "[No Output]", border_style="dim"))
                 rich_print("[dim]--- End Program Output ---[/dim]")

            # Check if program ran successfully before calling LLM (optional, but good practice)
            # if not run_success:
            #     rich_print("[yellow]Warning:[/yellow] Program execution failed. LLM verification might be less effective.")

            # 2. Call fix_verification_errors with content and program output
            if not quiet:
                rich_print("Calling LLM to verify program output against prompt...")
            fix_results = fix_verification_errors(
                program=input_strings["program_file"],
                prompt=input_strings["prompt_file"],
                code=input_strings["code_file"],
                output=program_output,
                strength=strength,
                temperature=temperature,
                verbose=verbose,
                time=time # Pass time to single pass function
            )

            # Determine success: If no issues were found OR if fixes were applied
            # The definition of 'success' here means the *final* state is verified.
            issues_found = fix_results['verification_issues_count'] > 0
            code_updated = fix_results['fixed_code'] != input_strings["code_file"]
            program_updated = fix_results['fixed_program'] != input_strings["program_file"]

            if not issues_found:
                success = True
                if not quiet: rich_print("[green]Verification Passed:[/green] LLM found no discrepancies.")
            elif code_updated or program_updated:
                 # If issues were found AND fixes were made, assume success for this single pass.
                 # A more robust check might re-run the program with fixed code, but that's the loop's job.
                 success = True
                 if not quiet: rich_print("[yellow]Verification Issues Found:[/yellow] LLM proposed fixes.")
            else:
                 success = False
                 if not quiet: rich_print("[red]Verification Failed:[/red] LLM found discrepancies but proposed no fixes.")

            final_program = fix_results['fixed_program']
            final_code = fix_results['fixed_code']
            total_cost = fix_results['total_cost']
            model_name = fix_results['model_name']

            # Build results log content for single pass
            results_log_content = "PDD Verify Results (Single Pass)\n"
            results_log_content += f"Timestamp: {os.path.getmtime(prompt_file)}\n"
            results_log_content += f"Prompt File: {prompt_file}\n"
            results_log_content += f"Code File: {code_file}\n"
            results_log_content += f"Program File: {program_file}\n"
            results_log_content += f"Success: {success}\n"
            results_log_content += f"Issues Found Count: {fix_results['verification_issues_count']}\n"
            results_log_content += f"Code Updated: {code_updated}\n"
            results_log_content += f"Program Updated: {program_updated}\n"
            results_log_content += f"Model Used: {model_name}\n"
            results_log_content += f"Total Cost: ${total_cost:.6f}\n"
            results_log_content += "\n--- LLM Explanation ---\n"
            # The original code here was:
            # results_log_content += "\n".join(fix_results.get('explanation', ['N/A']))
            # This was incorrect because fix_results['explanation'] is a single string.
            # The list constructor would then iterate through it character-by-character,
            # causing the single-character-per-line output.
            # The fix is to just append the string directly, using a default value if it is None.
            results_log_content += fix_results.get('explanation') or 'N/A'
            results_log_content += "\n\n--- Program Output Used for Verification ---\n"
            results_log_content += program_output


    except Exception as e:
        success = False
        rich_print(f"[bold red]Error during verification process:[/bold red] {e}")
        # Optionally log the full traceback if verbose
        if verbose:
            import traceback
            rich_print(Panel(traceback.format_exc(), title="Traceback", border_style="red"))
        # Attempt to return partial results if possible
        return success, final_program, final_code, attempts, total_cost, model_name

    # --- Output File Writing ---
    saved_code_path: Optional[str] = None
    saved_results_path: Optional[str] = None
    saved_program_path: Optional[str] = None

    if verbose:
        rich_print(f"[cyan bold DEBUG] In fix_verification_main, BEFORE save attempt for CODE:")
        rich_print(f"  success: {success}")
        rich_print(f"  output_code_path: {output_code_path!r}")
        rich_print(f"  final_code is None: {final_code is None}")
        if final_code is not None:
            rich_print(f"  len(final_code): {len(final_code)}")

    if output_code_path and final_code is not None:
        try:
            if verbose:
                rich_print(f"[cyan bold DEBUG] In fix_verification_main, ATTEMPTING to write code to: {output_code_path!r}")
            output_code_path_obj = Path(output_code_path)
            output_code_path_obj.parent.mkdir(parents=True, exist_ok=True)
            with open(output_code_path_obj, "w") as f:
                f.write(final_code)
            saved_code_path = output_code_path
            if not quiet:
                rich_print(f"Successfully verified code saved to: [green]{output_code_path}[/green]")
        except Exception as e:
            rich_print(f"[bold red]Error:[/bold red] Failed to write code file '{output_code_path}': {type(e).__name__} - {e}")

    if verbose:
        rich_print(f"[cyan bold DEBUG] In fix_verification_main, BEFORE save attempt for PROGRAM:")
        rich_print(f"  success: {success}")
        rich_print(f"  output_program_path: {output_program_path!r}")
        rich_print(f"  final_program is None: {final_program is None}")
        if final_program is not None:
            rich_print(f"  len(final_program): {len(final_program)}")

    if output_program_path and final_program is not None:
        try:
            if verbose:
                rich_print(f"[cyan bold DEBUG] In fix_verification_main, ATTEMPTING to write program to: {output_program_path!r}")
            output_program_path_obj = Path(output_program_path)
            output_program_path_obj.parent.mkdir(parents=True, exist_ok=True)
            with open(output_program_path_obj, "w") as f:
                f.write(final_program)
            saved_program_path = output_program_path
            if not quiet:
                rich_print(f"Successfully verified program saved to: [green]{output_program_path}[/green]")
        except Exception as e:
            rich_print(f"[bold red]Error:[/bold red] Failed to write program file '{output_program_path}': {type(e).__name__} - {e}")

    if not loop and output_results_path:
        try:
            output_results_path_obj = Path(output_results_path)
            output_results_path_obj.parent.mkdir(parents=True, exist_ok=True)
            with open(output_results_path_obj, "w") as f:
                f.write(results_log_content)
            saved_results_path = output_results_path
            if not quiet:
                 rich_print(f"Verification results log saved to: [green]{output_results_path}[/green]")
        except IOError as e:
            rich_print(f"[bold red]Error:[/bold red] Failed to write results log file '{output_results_path}': {e}")
    elif loop and output_results_path:
        # For loop, just confirm the path where the loop function *should* have saved the log
        saved_results_path = output_results_path
        if not quiet:
            # We assume fix_verification_errors_loop handles its own logging confirmation.
            # This message confirms the path was passed.
            rich_print(f"Verification results log (from loop) expected at: [green]{output_results_path}[/green]")


    # --- Final User Feedback ---
    if verbose:
        rich_print(f"[cyan bold DEBUG] Before summary - saved_code_path: {saved_code_path!r}, output_code_path: {output_code_path!r}[/cyan bold DEBUG]")
        rich_print(f"[cyan bold DEBUG] Before summary - saved_program_path: {saved_program_path!r}, output_program_path: {output_program_path!r}[/cyan bold DEBUG]")

    if not quiet:
        rich_print("\n" + "="*40)
        title = "[bold green]Verification Complete[/bold green]" if success else "[bold red]Verification Failed[/bold red]"
        summary_panel_content = (
            f"Status: {'[green]Success[/green]' if success else '[red]Failure[/red]'}\n"
            f"Attempts: {attempts}\n"
            f"Total Cost: ${total_cost:.6f}\n"
            f"Model Used: {model_name}\n"
            f"Verified Code Saved: {saved_code_path or 'N/A (Not saved on failure or no path)'}\n"
            f"Verified Program Saved: {saved_program_path or 'N/A (Not saved on failure or no path)'}\n"
            f"Results Log Saved: {saved_results_path or 'N/A'}"
        )
        summary_panel = Panel(
            summary_panel_content,
            title=title,
            border_style="green" if success else "red"
        )
        rich_print(summary_panel)

        if verbose and not success and not loop: # Only show final code if verbose, failed, and single pass
             rich_print("[bold yellow]Final Code (after failed single pass, not saved):[/bold yellow]")
             rich_print(Syntax(final_code, language or "python", theme="default", line_numbers=True))
             rich_print("[bold yellow]Final Program (after failed single pass, not saved):[/bold yellow]")
             rich_print(Syntax(final_program, language or "python", theme="default", line_numbers=True))


    return success, final_program, final_code, attempts, total_cost, model_name
