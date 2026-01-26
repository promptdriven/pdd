import click
import sys
import os

# Ensure the project root is in sys.path so we can import the module
# This allows running the example directly from the context/core directory
project_root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

try:
    # Import the auth_group from the module
    # In a real package, this would be: from pdd.commands.auth import auth_group
    from pdd.commands.auth import auth_group
except ImportError:
    print("Error: Could not import auth_group. Ensure pdd.commands.auth is available.")
    sys.exit(1)

@click.group()
def cli():
    """Main PDD CLI entry point."""
    pass

# Register the auth command group with the main CLI
# This adds 'login', 'logout', 'status', 'switch', and 'token' as subcommands under 'auth'
cli.add_command(auth_group)

if __name__ == "__main__":
    print("--- PDD Auth Command Integration Example ---")
    print("This script demonstrates how the auth commands are structured within the CLI.")
    print("In a real scenario, you would run 'pdd auth login' or 'pdd auth status'.\n")

    # Simulate running 'pdd auth --help' to show the registered commands
    try:
        with click.Context(cli) as ctx:
            click.echo("Invoking: pdd auth --help\n")
            
            # We invoke the auth group directly to show its help output
            # This proves the commands are correctly registered
            click.echo(auth_group.get_help(ctx))
            
    except Exception as e:
        print(f"An error occurred while demonstrating the CLI: {e}")

    print("\n--- Usage Examples ---")
    print("1. Login (Interactive):")
    print("   $ pdd auth login")
    print("\n2. Login (Headless/CI):")
    print("   $ pdd auth login --no-browser")
    print("\n3. Check Status:")
    print("   $ pdd auth status")
    print("\n4. Get Token for Scripts:")
    print("   $ pdd auth token --format json")
    print("\n5. Logout:")
    print("   $ pdd auth logout")