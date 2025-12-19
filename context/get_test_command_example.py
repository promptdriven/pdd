#!/usr/bin/env python3
"""Example usage of the get_test_command module.

This module demonstrates how to use get_test_command_for_file() to resolve
the appropriate test command for a given test file. The function uses a
layered resolution strategy:

1. CSV run_test_command (from language_format.csv)
2. Smart detection via default_verify_cmd_for()
3. None (signals agentic fallback is needed)

The example shows usage with different file types and language overrides.
"""

from pathlib import Path
from rich import print as rprint
from rich.panel import Panel
from rich.table import Table

from pdd.get_test_command import get_test_command_for_file


def demonstrate_python_test() -> None:
    """Demonstrate getting test command for a Python test file.
    
    For Python files (.py extension), the function will:
    - Check language_format.csv for a run_test_command
    - Fall back to smart detection (typically pytest)
    
    Returns:
        None - prints results to console
    """
    rprint(Panel("[bold cyan]Python Test File Example[/bold cyan]"))
    
    # Example Python test file path
    test_file = "tests/test_example.py"
    
    # Get the test command - no language override needed
    command = get_test_command_for_file(test_file)
    
    if command:
        rprint(f"[green]Test file:[/green] {test_file}")
        rprint(f"[green]Resolved command:[/green] {command}")
    else:
        rprint(f"[yellow]No command found for {test_file} - agentic fallback needed[/yellow]")
    print()


def demonstrate_javascript_test() -> None:
    """Demonstrate getting test command for a JavaScript test file.
    
    For JavaScript files (.js extension), the function will:
    - Check language_format.csv for a run_test_command
    - Fall back to smart detection (npm-based testing)
    
    Returns:
        None - prints results to console
    """
    rprint(Panel("[bold cyan]JavaScript Test File Example[/bold cyan]"))
    
    test_file = "src/components/Button.test.js"
    
    command = get_test_command_for_file(test_file)
    
    if command:
        rprint(f"[green]Test file:[/green] {test_file}")
        rprint(f"[green]Resolved command:[/green]")
        rprint(Panel(command, border_style="dim"))
    else:
        rprint(f"[yellow]No command found for {test_file} - agentic fallback needed[/yellow]")
    print()


def demonstrate_language_override() -> None:
    """Demonstrate using the language parameter to override detection.
    
    The language parameter allows you to explicitly specify the language
    instead of relying on file extension detection. This is useful when:
    - File extension is ambiguous
    - You want to force a specific test runner
    
    Args:
        None
    
    Returns:
        None - prints results to console
    """
    rprint(Panel("[bold cyan]Language Override Example[/bold cyan]"))
    
    # A .ts file that we want to treat as TypeScript
    test_file = "src/utils.test.ts"
    
    # Explicitly specify the language
    command = get_test_command_for_file(test_file, language="typescript")
    
    if command:
        rprint(f"[green]Test file:[/green] {test_file}")
        rprint(f"[green]Language override:[/green] typescript")
        rprint(f"[green]Resolved command:[/green]")
        rprint(Panel(command, border_style="dim"))
    else:
        rprint(f"[yellow]No command found - agentic fallback needed[/yellow]")
    print()


def demonstrate_multiple_files() -> None:
    """Demonstrate resolving commands for multiple test files at once.
    
    Shows how to batch process multiple test files and display
    the resolved commands in a table format.
    
    Returns:
        None - prints results to console
    """
    rprint(Panel("[bold cyan]Multiple Files Example[/bold cyan]"))
    
    test_files = [
        "tests/test_auth.py",
        "tests/test_api.py",
        "src/components/Header.test.js",
        "lib/utils.test.ts",
        "unknown_file.xyz",  # Unknown extension - will return None
    ]
    
    table = Table(title="Test Command Resolution")
    table.add_column("Test File", style="cyan")
    table.add_column("Command Found", style="green")
    table.add_column("Status", style="yellow")
    
    for test_file in test_files:
        command = get_test_command_for_file(test_file)
        
        if command:
            # Truncate long commands for display
            display_cmd = command[:50] + "..." if len(command) > 50 else command
            table.add_row(test_file, display_cmd, "✓ Resolved")
        else:
            table.add_row(test_file, "-", "⚠ Needs fallback")
    
    rprint(table)
    print()


def demonstrate_handling_none_result() -> None:
    """Demonstrate handling when no command can be resolved.
    
    When get_test_command_for_file returns None, it signals that:
    - No CSV command was found for the extension
    - Smart detection couldn't determine a command
    - The caller should use an agentic fallback approach
    
    Returns:
        None - prints results to console
    """
    rprint(Panel("[bold cyan]Handling None Result (Agentic Fallback)[/bold cyan]"))
    
    # An unknown file type
    test_file = "tests/test_something.unknown"
    
    command = get_test_command_for_file(test_file)
    
    if command is None:
        rprint(f"[yellow]No command resolved for:[/yellow] {test_file}")
        rprint("[dim]This signals that an agentic fallback should be used.[/dim]")
        rprint("[dim]The caller can use LLM-based detection or prompt the user.[/dim]")
    else:
        rprint(f"[green]Command:[/green] {command}")
    print()


def main() -> None:
    """Run all demonstration examples.
    
    This function executes each demonstration to show the various
    ways to use get_test_command_for_file().
    
    Returns:
        None
    """
    rprint(Panel(
        "[bold]get_test_command Module Usage Examples[/bold]\n\n"
        "This module resolves test commands using a layered strategy:\n"
        "1. CSV run_test_command (language_format.csv)\n"
        "2. Smart detection (default_verify_cmd_for)\n"
        "3. None (triggers agentic fallback)",
        title="Overview",
        border_style="blue"
    ))
    print()
    
    demonstrate_python_test()
    demonstrate_javascript_test()
    demonstrate_language_override()
    demonstrate_multiple_files()
    demonstrate_handling_none_result()
    
    rprint("[bold green]All examples completed![/bold green]")


if __name__ == "__main__":
    main()
