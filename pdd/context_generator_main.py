import sys
import ast
from typing import Tuple, Optional
from pathlib import Path
import click
from rich import print as rprint

from .construct_paths import construct_paths
from .context_generator import context_generator


def _validate_python_syntax(code: str) -> Tuple[bool, Optional[str]]:
    """
    Validate that the code is valid Python syntax.

    Returns:
        Tuple of (is_valid, error_message)
    """
    try:
        ast.parse(code)
        return True, None
    except SyntaxError as e:
        return False, f"SyntaxError at line {e.lineno}: {e.msg}"


def _try_fix_json_garbage(code: str) -> Optional[str]:
    """
    Attempt to fix code that has JSON metadata garbage appended at the end.
    This is a common LLM extraction failure pattern.

    Returns:
        Fixed code if successful, None if not fixable.
    """
    lines = code.split('\n')

    # Look for JSON-like patterns at the end
    json_patterns = ['"explanation":', '"focus":', '"description":', '"code":']

    for i in range(len(lines) - 1, -1, -1):
        line = lines[i].strip()

        # If we find a line that's clearly JSON garbage
        if any(pattern in line for pattern in json_patterns):
            # Go back and find where valid Python ends
            for j in range(i - 1, -1, -1):
                candidate = '\n'.join(lines[:j + 1])
                is_valid, _ = _validate_python_syntax(candidate)
                if is_valid:
                    return candidate
            break

        # If line is just "}" or "]", likely JSON ending
        if line in ['}', ']', '},', '],']:
            continue

        # If line ends with '",  (JSON string end)
        if line.endswith('",') or line.endswith('"'):
            # Check if this looks like inside a JSON object
            if any(pattern in lines[i] if i < len(lines) else '' for pattern in json_patterns):
                continue

    return None

def context_generator_main(ctx: click.Context, prompt_file: str, code_file: str, output: Optional[str]) -> Tuple[str, float, str]:
    """
    Main function to generate example code from a prompt file and an existing code file.

    :param ctx: Click context containing command-line parameters.
    :param prompt_file: Path to the prompt file that generated the code.
    :param code_file: Path to the existing code file.
    :param output: Optional path to save the generated example code.
    :return: A tuple containing the generated example code, total cost, and model name used.
    """
    try:
        # Construct file paths
        input_file_paths = {
            "prompt_file": prompt_file,
            "code_file": code_file
        }
        command_options = {
            "output": output
        }
        resolved_config, input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=ctx.obj.get('quiet', False),
            command="example",
            command_options=command_options,
            context_override=ctx.obj.get('context'),
            confirm_callback=ctx.obj.get('confirm_callback')
        )

        # Load input files
        prompt_content = input_strings["prompt_file"]
        code_content = input_strings["code_file"]

        # Get resolved output path for file path information
        resolved_output = output_file_paths["output"]
        
        # Determine file path information for correct imports
        from pathlib import Path
        source_file_path = str(Path(code_file).resolve())
        example_file_path = str(Path(resolved_output).resolve()) if resolved_output else ""
        
        # Extract module name from the code file
        module_name = Path(code_file).stem

        # Generate example code
        strength = ctx.obj.get('strength', 0.5)
        temperature = ctx.obj.get('temperature', 0)
        time = ctx.obj.get('time')
        example_code, total_cost, model_name = context_generator(
            language=language,
            code_module=code_content,
            prompt=prompt_content,
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=ctx.obj.get('verbose', False),
            source_file_path=source_file_path,
            example_file_path=example_file_path,
            module_name=module_name
        )

        # Save results - if output is a directory, use resolved file path from construct_paths
        if output is None:
            final_output_path = resolved_output
        else:
            try:
                is_dir_hint = output.endswith('/')
            except Exception:
                is_dir_hint = False
            if is_dir_hint or (Path(output).exists() and Path(output).is_dir()):
                final_output_path = resolved_output
            else:
                final_output_path = output
        if final_output_path and example_code is not None:
            # Validate Python syntax before saving
            if language == "python":
                is_valid, error_msg = _validate_python_syntax(example_code)
                if not is_valid:
                    if not ctx.obj.get('quiet', False):
                        rprint(f"[yellow]Warning: Generated code has syntax error: {error_msg}[/yellow]")
                        rprint("[yellow]Attempting to fix JSON garbage pattern...[/yellow]")

                    # Try to fix JSON garbage at end of file
                    fixed_code = _try_fix_json_garbage(example_code)
                    if fixed_code:
                        is_valid_fixed, _ = _validate_python_syntax(fixed_code)
                        if is_valid_fixed:
                            if not ctx.obj.get('quiet', False):
                                rprint("[green]Successfully removed garbage and fixed syntax.[/green]")
                            example_code = fixed_code
                        else:
                            rprint("[red]Could not fix syntax error. Saving as-is.[/red]")
                    else:
                        rprint("[red]Could not detect fixable pattern. Saving as-is.[/red]")

            with open(final_output_path, 'w') as f:
                f.write(example_code)
        elif final_output_path and example_code is None:
            # Raise error instead of just warning
            raise click.UsageError("Example generation failed, no code produced.")

        # Provide user feedback
        if not ctx.obj.get('quiet', False):
            if example_code is not None:
                rprint("[bold green]Example code generated successfully.[/bold green]")
                rprint(f"[bold]Model used:[/bold] {model_name}")
                rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
                if final_output_path and example_code is not None:
                    rprint(f"[bold]Example code saved to:[/bold] {final_output_path}")
            else:
                rprint("[bold red]Example code generation failed.[/bold red]")
                rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")

        # Always print example code, even in quiet mode (if it exists)
        if example_code is not None:
            rprint("[bold]Generated Example Code:[/bold]")
            rprint(example_code)
        else:
            rprint("[bold red]No example code generated due to errors.[/bold red]")

        return example_code, total_cost, model_name

    except click.Abort:
        # User cancelled - re-raise to stop the sync loop
        raise
    except Exception as e:
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        # Return error result instead of sys.exit(1) to allow orchestrator to handle gracefully
        return "", 0.0, f"Error: {e}"
