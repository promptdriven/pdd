import os
import sys
import click
from pathlib import Path

# The PDD_PATH environment variable is set to the root of the pdd directory.
sys.path.append(os.environ.get("PDD_PATH", "."))

# Import the guard functions from the core module
try:
    from pdd.core.duplicate_cli_guard import (
        check_duplicate_before_subcommand,
        record_after_guarded_command
    )
except ImportError:
    # Fallback or placeholder for demonstration if module is not in path
    def check_duplicate_before_subcommand(ctx):
        pass
    def record_after_guarded_command(ctx, success=True):
        pass

@click.group()
@click.pass_context
def cli(ctx: click.Context):
    """
    Main CLI group. The duplicate guard is typically called here to check
    if the upcoming subcommand is a redundant, expensive operation.
    """
    # 1. Initialize context object if necessary
    ctx.ensure_object(dict)
    
    # 2. Check for duplicates BEFORE running the subcommand.
    # This looks at argv, git status, and the .pdd/last_run.json store.
    # If a duplicate is detected in a non-interactive environment, it raises click.UsageError.
    check_duplicate_before_subcommand(ctx)

@cli.command()
@click.pass_context
def generate(ctx: click.Context):
    """
    An example 'guarded' subcommand (listed in GUARDED_SUBCOMMANDS).
    """
    click.echo("Executing expensive 'generate' operation...")
    
    # Simulate logic...
    success = True 
    
    # 3. Record the run AFTER successful completion.
    # This persists the signature and fingerprint so the next identical run is blocked.
    # If success=False (e.g., LLM timeout), it won't be recorded, allowing an immediate retry.
    record_after_guarded_command(ctx, success=success)
    click.echo("Operation complete and recorded.")

def run_example():
    """
    Sets up the environment and executes the CLI commands to demonstrate the guard.
    """
    # Create a dummy .git directory if it doesn't exist to satisfy find_project_root
    project_root = Path.cwd()
    (project_root / ".git").mkdir(exist_ok=True)

    # Configure the window to 1 minute for this example (default is 15)
    os.environ["PDD_DUPLICATE_WINDOW_MIN"] = "1"
    
    # Set this to ensure the guard runs even during our example execution
    os.environ["PDD_TEST_DUPLICATE_GUARD"] = "true"

    print("--- First Run: Executing a new command ---")
    try:
        # We simulate 'pdd generate --prompt test'
        cli.main(args=["generate"], standalone_mode=False)
    except Exception as e:
        print(f"Unexpected error: {e}")

    print("\n--- Second Run: Executing the exact same command immediately ---")
    # This should trigger the duplicate guard.
    # Since this script is non-interactive, it will raise a UsageError.
    try:
        cli.main(args=["generate"], standalone_mode=False)
    except click.UsageError as e:
        print(f"Blocked as expected: {e.message}")
    except click.Abort:
        print("Blocked via Abort (user said No or EOF)")
    except Exception as e:
        print(f"Caught: {e}")

    print("\n--- Third Run: Executing with --force bypass ---")
    # Adding a mechanism to bypass (the module checks ctx.obj['force'])
    try:
        # Simulate passing a global flag like 'pdd --force generate'
        # Note: In a real app, you'd define --force in the @cli.group
        os.environ["PDD_ALLOW_DUPLICATE_RUN"] = "1"
        cli.main(args=["generate"], standalone_mode=False)
        print("Bypassed duplicate guard using environment variable.")
    finally:
        if "PDD_ALLOW_DUPLICATE_RUN" in os.environ:
            del os.environ["PDD_ALLOW_DUPLICATE_RUN"]

if __name__ == "__main__":
    run_example()