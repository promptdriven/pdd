import sys
from typing import Tuple, Optional
import click
from rich import print as rprint
from rich.markup import MarkupError, escape

import requests
import asyncio
import os
from pathlib import Path

from .preprocess import preprocess

from .construct_paths import construct_paths
from .fix_errors_from_unit_tests import fix_errors_from_unit_tests
from .fix_error_loop import fix_error_loop
from .get_jwt_token import get_jwt_token
from .get_language import get_language

# Import DEFAULT_STRENGTH from the package
from . import DEFAULT_STRENGTH

def fix_main(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    unit_test_file: str,
    error_file: str,
    output_test: Optional[str],
    output_code: Optional[str],
    output_results: Optional[str],
    loop: bool,
    verification_program: Optional[str],
    max_attempts: int,
    budget: float,
    auto_submit: bool
) -> Tuple[bool, str, str, int, float, str]:
    """
    Main function to fix errors in code and unit tests.

    Args:
        ctx: Click context containing command-line parameters
        prompt_file: Path to the prompt file that generated the code
        code_file: Path to the code file to be fixed
        unit_test_file: Path to the unit test file
        error_file: Path to the error log file
        output_test: Path to save the fixed unit test file
        output_code: Path to save the fixed code file
        output_results: Path to save the fix results
        loop: Whether to use iterative fixing process
        verification_program: Path to program that verifies code correctness
        max_attempts: Maximum number of fix attempts
        budget: Maximum cost allowed for fixing
        auto_submit: Whether to auto-submit example if tests pass

    Returns:
        Tuple containing:
        - Success status (bool)
        - Fixed unit test code (str)
        - Fixed source code (str)
        - Total number of fix attempts (int)
        - Total cost of operation (float)
        - Name of model used (str)
    """
    # Check verification program requirement before any file operations
    if loop and not verification_program:
        raise click.UsageError("--verification-program is required when using --loop")
    
    # Initialize analysis_results to None to prevent reference errors
    analysis_results = None

    try:
        # Verify error file exists if not in loop mode
        if not loop:
            error_path = Path(error_file)
            if not error_path.exists():
                raise FileNotFoundError(f"Error file '{error_file}' does not exist.")
                
        # Construct file paths
        input_file_paths = {
            "prompt_file": prompt_file,
            "code_file": code_file,
            "unit_test_file": unit_test_file
        }
        if not loop:
            input_file_paths["error_file"] = error_file

        command_options = {
            "output_test": output_test,
            "output_code": output_code,
            "output_results": output_results
        }

        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=ctx.obj.get('quiet', False),
            command="fix",
            command_options=command_options,
            create_error_file=loop  # Only create error file if in loop mode
        )

        # Get parameters from context
        strength = ctx.obj.get('strength', DEFAULT_STRENGTH)
        temperature = ctx.obj.get('temperature', 0)
        verbose = ctx.obj.get('verbose', False)
        if loop:
            # Use fix_error_loop for iterative fixing
            success, fixed_unit_test, fixed_code, attempts, total_cost, model_name = fix_error_loop(
                unit_test_file=unit_test_file,
                code_file=code_file,
                prompt=input_strings["prompt_file"],
                verification_program=verification_program,
                strength=strength,
                temperature=temperature,
                max_attempts=max_attempts,
                budget=budget,
                error_log_file=output_file_paths.get("output_results"),
                verbose=verbose
            )
        else:
            # Use fix_errors_from_unit_tests for single-pass fixing
            update_unit_test, update_code, fixed_unit_test, fixed_code, analysis_results, total_cost, model_name = fix_errors_from_unit_tests(
                unit_test=input_strings["unit_test_file"],
                code=input_strings["code_file"],
                prompt=input_strings["prompt_file"],
                error=input_strings["error_file"],
                error_file=output_file_paths.get("output_results"),
                strength=strength,
                temperature=temperature,
                verbose=verbose
            )
            success = update_unit_test or update_code
            attempts = 1

        # Save fixed files
        if fixed_unit_test:
            with open(output_file_paths["output_test"], 'w') as f:
                f.write(fixed_unit_test)

        if fixed_code:
            with open(output_file_paths["output_code"], 'w') as f:
                f.write(fixed_code)

        # Provide user feedback
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold]{'Success' if success else 'Failed'} to fix errors[/bold]")
            rprint(f"[bold]Total attempts:[/bold] {attempts}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            if verbose and analysis_results:
                # Log the first 200 characters of analysis if in verbose mode
                analysis_preview = analysis_results[:200] + "..." if len(analysis_results) > 200 else analysis_results
                try:
                    # Attempt to print the preview using rich markup parsing
                    rprint(f"[bold]Analysis preview:[/bold] {analysis_preview}")
                except MarkupError as me:
                    # If markup fails, print a warning and the escaped preview
                    rprint(f"[bold yellow]Warning:[/bold yellow] Analysis preview contained invalid markup: {me}")
                    rprint(f"[bold]Raw Analysis preview (escaped):[/bold] {escape(analysis_preview)}")
                except Exception as e:
                    # Handle other potential errors during preview printing
                    rprint(f"[bold red]Error printing analysis preview: {e}[/bold red]")
            if success:
                rprint("[bold green]Fixed files saved:[/bold green]")
                rprint(f"  Test file: {output_file_paths['output_test']}")
                rprint(f"  Code file: {output_file_paths['output_code']}")
                if output_file_paths.get("output_results"):
                    rprint(f"  Results file: {output_file_paths['output_results']}")

                # Auto-submit example if requested and successful
                if auto_submit:
                    try:
                        # Get JWT token for cloud authentication
                        jwt_token = asyncio.run(get_jwt_token(
                            firebase_api_key=os.environ.get("REACT_APP_FIREBASE_API_KEY"),
                            github_client_id=os.environ.get("GITHUB_CLIENT_ID"),
                            app_name="PDD Code Generator"
                        ))
                        processed_prompt = preprocess(
                            input_strings["prompt_file"],
                            recursive=False,
                            double_curly_brackets=True
                        )
                        # Prepare the submission payload
                        payload = {
                            "command": "fix",
                            "input": {
                                "prompts": [{
                                    "content": processed_prompt,
                                    "filename": os.path.basename(prompt_file)
                                }],
                                "code": [{
                                    "content": input_strings["code_file"],
                                    "filename": os.path.basename(code_file)
                                }],
                                "test": [{
                                    "content": input_strings["unit_test_file"],
                                    "filename": os.path.basename(unit_test_file)
                                }]
                            },
                            "output": {
                                "code": [{
                                    "content": fixed_code,
                                    "filename": os.path.basename(output_file_paths["output_code"])
                                }],
                                "test": [{
                                    "content": fixed_unit_test,
                                    "filename": os.path.basename(output_file_paths["output_test"])
                                }]
                            },
                            "metadata": {
                                "title": f"Auto-submitted fix for {os.path.basename(code_file)}",
                                "description": "Automatically submitted successful code fix",
                                "language": get_language(os.path.splitext(code_file)[1]),  # Detect language from file extension
                                "framework": "",
                                "tags": ["auto-fix", "example"],
                                "isPublic": True,
                                "price": 0.0
                            }
                        }

                        # Add verification program if specified
                        if verification_program:
                            with open(verification_program, 'r') as f:
                                verifier_content = f.read()
                            payload["input"]["example"] = [{
                                "content": verifier_content,
                                "filename": os.path.basename(verification_program)
                            }]

                        # Add error logs if available
                        if "error_file" in input_strings:
                            payload["input"]["error"] = [{
                                "content": input_strings["error_file"],
                                "filename": os.path.basename(error_file)
                            }]

                        # Add analysis if available
                        if output_file_paths.get("output_results"):
                            try:
                                with open(output_file_paths["output_results"], 'r') as f:
                                    analysis_content = f.read()
                            except Exception as file_err:
                                # If unable to read analysis file, use analysis_results from LLM directly
                                if not ctx.obj.get('quiet', False):
                                    rprint(f"[bold yellow]Could not read analysis file, using direct LLM output: {str(file_err)}[/bold yellow]")
                                analysis_content = analysis_results
                            
                            payload["output"]["analysis"] = [{
                                "content": analysis_content,
                                "filename": os.path.basename(output_file_paths["output_results"])
                            }]
                        # If no output file but we have analysis results, use them directly
                        elif analysis_results:
                            payload["output"]["analysis"] = [{
                                "content": analysis_results,
                                "filename": "analysis.log"
                            }]

                        # Submit the example to Firebase Cloud Function
                        headers = {
                            "Authorization": f"Bearer {jwt_token}",
                            "Content-Type": "application/json"
                        }
                        response = requests.post(
                            'https://us-central1-prompt-driven-development.cloudfunctions.net/submitExample',
                            json=payload,
                            headers=headers
                        )
                        
                        if response.status_code == 200:
                            if not ctx.obj.get('quiet', False):
                                rprint("[bold green]Successfully submitted example[/bold green]")
                        else:
                            if not ctx.obj.get('quiet', False):
                                rprint(f"[bold red]Failed to submit example: {response.text}[/bold red]")

                    except Exception as e:
                        if not ctx.obj.get('quiet', False):
                            rprint(f"[bold red]Error submitting example: {str(e)}[/bold red]")

        return success, fixed_unit_test, fixed_code, attempts, total_cost, model_name

    except Exception as e:
        if not ctx.obj.get('quiet', False):
            # Safely handle and print MarkupError
            if isinstance(e, MarkupError):
                 rprint(f"[bold red]Markup Error in fix_main:[/bold red]")
                 rprint(escape(str(e)))
            else:
                 # Print other errors normally, escaping the error string
                 from rich.markup import escape # Ensure escape is imported
                 rprint(f"[bold red]Error:[/bold red] {escape(str(e))}")
        sys.exit(1)