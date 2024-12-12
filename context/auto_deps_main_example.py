import click
from pathlib import Path
from pdd.auto_deps_main import auto_deps_main

@click.command('auto-deps')
@click.option('--force', is_flag=True, help='Force file overwrites')
@click.option('--quiet', is_flag=True, help='Suppress output messages')
@click.option('--strength', default=0.9, help='Strength parameter for dependency analysis')
@click.option('--temperature', default=0.0, help='Temperature parameter for dependency analysis')
@click.option('--prompt-file', default='prompts/get_extension_python.prompt', help='Path to the input prompt file')
@click.option('--directory-path', default='context/*_example.py', help='Path to directory containing potential dependency files')
@click.option('--auto-deps-csv-path', default='./project_dependencies.csv', help='Path to CSV file containing auto-dependency information')
@click.option('--output', default='./', help='Path to save the modified prompt file')
@click.option('--force-scan', is_flag=True, help='Force a rescan of the directory')
def main(force, quiet, strength, temperature, prompt_file, directory_path, auto_deps_csv_path, output, force_scan):
    """Process a prompt file and analyze dependencies."""
    # Initialize the Click context with command-line options
    ctx = click.get_current_context()
    ctx.params['force'] = force
    ctx.params['quiet'] = quiet
    ctx.obj = {
        'strength': strength,
        'temperature': temperature
    }

    try:
        modified_prompt, total_cost, model_name = auto_deps_main(
            ctx=ctx,
            prompt_file=prompt_file,
            directory_path=directory_path,
            auto_deps_csv_path=auto_deps_csv_path,
            output=output,
            force_scan=force_scan
        )

        # Display the results
        print("Modified Prompt:")
        print(modified_prompt)
        print(f"Total Cost: ${total_cost:.6f}")
        print(f"Model Used: {model_name}")
    except Exception as e:
        print(f"Error: {e}")
        raise click.Abort()

if __name__ == "__main__":
    main()