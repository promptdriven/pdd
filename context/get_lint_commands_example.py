#!/usr/bin/env python3
"""Example usage of the get_lint_commands module.

This module demonstrates how to use get_lint_commands() to resolve
the appropriate lint commands for a given source file. The function returns
a list of LintCommand(command=str, cwd=Optional[Path]) instances:

- For Python files (.py): returns two commands (ruff check + mypy),
  each with cwd set to the nearest config directory or None.
- For non-Python files: returns an empty list (hybrid contract),
  signaling the caller to fall back to agent-discovered commands.
"""

import sys
import os
import tempfile

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pathlib import Path

from pdd.get_lint_commands import LintCommand, get_lint_commands


def demonstrate_python_file() -> None:
    """Demonstrate lint commands for a Python file.

    For Python files, get_lint_commands returns two LintCommand instances:
    1. ruff check <file> - with cwd from nearest pyproject.toml
    2. mypy <file> - with cwd from nearest pyproject.toml or mypy.ini

    Returns:
        None - prints results to console.
    """
    print("=== Python File Example ===")
    print()

    # Create a temporary directory structure with a pyproject.toml
    with tempfile.TemporaryDirectory() as tmpdir:
        project_dir = Path(tmpdir)
        # Create pyproject.toml so config discovery finds it
        (project_dir / "pyproject.toml").write_text("[tool.ruff]\n")
        # Create a subdirectory with a Python file
        src_dir = project_dir / "src"
        src_dir.mkdir()
        py_file = src_dir / "example.py"
        py_file.write_text("print('hello')\n")

        commands = get_lint_commands(py_file)

        print(f"File: {py_file.name}")
        print(f"Number of commands: {len(commands)}")
        print()
        for i, cmd in enumerate(commands, 1):
            print(f"  Command {i}: {cmd.command}")
            print(f"  cwd: {cmd.cwd}")
            print()

        # Verify we got the expected commands
        assert len(commands) == 2, f"Expected 2 commands, got {len(commands)}"
        assert "ruff check" in commands[0].command
        assert "mypy" in commands[1].command
        assert commands[0].cwd == project_dir
        assert commands[1].cwd == project_dir
        print("All assertions passed.")
        print()


def demonstrate_non_python_file() -> None:
    """Demonstrate the hybrid contract for non-Python files.

    For non-Python files, get_lint_commands returns an empty list.
    This signals the orchestrator to fall back to agent-discovered commands.

    Returns:
        None - prints results to console.
    """
    print("=== Non-Python File (Hybrid Contract) ===")
    print()

    js_file = Path("src/app.js")
    commands = get_lint_commands(js_file)

    print(f"File: {js_file}")
    print(f"Commands returned: {commands}")
    print(f"Length: {len(commands)}")
    print()

    assert commands == [], f"Expected empty list, got {commands}"

    # Also test other extensions
    for ext in [".ts", ".tsx", ".rs", ".go", ".java", ".rb"]:
        result = get_lint_commands(Path(f"file{ext}"))
        assert result == [], f"Expected empty list for {ext}"

    print("All non-Python extensions return empty list (hybrid contract).")
    print()


def demonstrate_no_config_found() -> None:
    """Demonstrate behavior when no config file is found.

    When no pyproject.toml or mypy.ini is found walking up from the file,
    the LintCommand.cwd is set to None, meaning the caller decides the
    working directory.

    Returns:
        None - prints results to console.
    """
    print("=== No Config Found (cwd=None) ===")
    print()

    with tempfile.TemporaryDirectory() as tmpdir:
        # Create a Python file with no config files anywhere nearby
        isolated_dir = Path(tmpdir) / "deep" / "nested" / "dir"
        isolated_dir.mkdir(parents=True)
        py_file = isolated_dir / "lonely.py"
        py_file.write_text("x = 1\n")

        commands = get_lint_commands(py_file)

        print(f"File: {py_file.name}")
        for cmd in commands:
            print(f"  Command: {cmd.command}")
            print(f"  cwd: {cmd.cwd}")
            print()

        assert commands[0].cwd is None, "ruff cwd should be None when no pyproject.toml"
        assert commands[1].cwd is None, "mypy cwd should be None when no config found"
        print("Both commands have cwd=None (caller decides).")
        print()


def demonstrate_mypy_ini_discovery() -> None:
    """Demonstrate that mypy finds mypy.ini even without pyproject.toml.

    The mypy command searches for both pyproject.toml and mypy.ini,
    while ruff only searches for pyproject.toml.

    Returns:
        None - prints results to console.
    """
    print("=== mypy.ini Discovery ===")
    print()

    with tempfile.TemporaryDirectory() as tmpdir:
        project_dir = Path(tmpdir)
        # Only create mypy.ini, no pyproject.toml
        (project_dir / "mypy.ini").write_text("[mypy]\n")
        py_file = project_dir / "check_me.py"
        py_file.write_text("x: int = 1\n")

        commands = get_lint_commands(py_file)

        print(f"File: {py_file.name}")
        for cmd in commands:
            print(f"  Command: {cmd.command}")
            print(f"  cwd: {cmd.cwd}")
            print()

        # ruff won't find pyproject.toml -> cwd is None
        assert commands[0].cwd is None, "ruff should have cwd=None (no pyproject.toml)"
        # mypy will find mypy.ini -> cwd is the project dir
        assert commands[1].cwd == project_dir, "mypy should find mypy.ini"
        print("ruff cwd=None, mypy cwd found via mypy.ini.")
        print()


def demonstrate_lint_command_dataclass() -> None:
    """Demonstrate the LintCommand dataclass.

    LintCommand has two fields:
    - command (str): The resolved lint command string.
    - cwd (Optional[Path]): Working directory, defaults to None.

    Returns:
        None - prints results to console.
    """
    print("=== LintCommand Dataclass ===")
    print()

    cmd1 = LintCommand(command="ruff check foo.py")
    print(f"command: {cmd1.command}")
    print(f"cwd (default): {cmd1.cwd}")
    print()

    cmd2 = LintCommand(command="mypy foo.py", cwd=Path("/project"))
    print(f"command: {cmd2.command}")
    print(f"cwd (explicit): {cmd2.cwd}")
    print()


def main() -> None:
    """Run all demonstration examples.

    Returns:
        None
    """
    print("get_lint_commands Module Usage Examples")
    print("=" * 40)
    print()

    demonstrate_python_file()
    demonstrate_non_python_file()
    demonstrate_no_config_found()
    demonstrate_mypy_ini_discovery()
    demonstrate_lint_command_dataclass()

    print("All examples completed successfully!")


if __name__ == "__main__":
    main()
