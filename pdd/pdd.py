import sys
import os
import argparse
from typing import Tuple, Optional
from rich import print
from rich.console import Console
from rich.prompt import Confirm

from code_generator import code_generator
from context_generator import context_generator
from get_extension import get_extension
from construct_output_paths import construct_output_paths

console = Console()

def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="PDD: Prompt-Driven Development Tool")
    parser.add_argument("input_file", help="Input prompt file or code file")
    parser.add_argument("--force", action="store_true", help="Overwrite existing files without confirmation")
    parser.add_argument("-o", "--output", help="Path or filename of the output runnable code")
    parser.add_argument("-oe", "--example_output", help="Path for the example code output")
    parser.add_argument("-$", "--strength", type=float, default=0.5, help="Strength of the model to use (0-1)")
    return parser.parse_args()

def extract_basename_and_language(filename: str) -> Tuple[str, str]:
    basename, ext = os.path.splitext(filename)
    if '_' in basename:
        basename, language = basename.rsplit('_', 1)
        # remove path from basename
        basename = os.path.basename(basename)
    else:
        language = ext.lstrip('.')
    return basename, language

def write_file(content: str, filepath: str, force: bool) -> bool:
    if os.path.exists(filepath) and not force:
        if not Confirm.ask(f"[yellow]File {filepath} already exists. Overwrite?[/yellow]", default=True):
            return False
    
    os.makedirs(os.path.dirname(filepath), exist_ok=True)
    with open(filepath, 'w') as f:
        f.write(content)
    return True

def main():
    args = parse_arguments()

    # Step 1 & 2: Read input file and add '.prompt' if no extension
    input_file = args.input_file if os.path.splitext(args.input_file)[1] else f"{args.input_file}.prompt"

    # Step 3: Extract basename and language, get file extension
    basename, language = extract_basename_and_language(input_file)
    file_extension = get_extension(language)
    print(f"basename: {basename}, language: {language}, file_extension: {file_extension}")
    # Step 4: Construct output paths
    runnable_path, example_path = construct_output_paths(
        basename, file_extension, args.output, args.example_output
    )

    # Step 5: Handle prompt input
    if input_file.endswith('.prompt'):
        console.print(f"[bold green]Generating code from prompt: {input_file}[/bold green]")
        runnable_code = code_generator(input_file, language, args.strength)
        if write_file(runnable_code, runnable_path, args.force):
            console.print(f"[green]Runnable code written to: {runnable_path}[/green]")
        else:
            console.print("[red]Failed to write runnable code.[/red]")
            return

    # Step 6: Generate example code
    if not input_file.endswith('.prompt') or args.example_output:
        console.print(f"[bold blue]Generating example code from: {runnable_path or input_file}[/bold blue]")
        success = context_generator(runnable_path or input_file, example_path, args.force)
        if success:
            console.print(f"[green]Example code written to: {example_path}[/green]")
        else:
            console.print("[red]Failed to generate example code.[/red]")

if __name__ == "__main__":
    main()