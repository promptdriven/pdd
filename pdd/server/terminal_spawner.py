"""
Cross-platform terminal spawning utilities.

Allows spawning new terminal windows to run commands in isolation,
rather than running them in the same process as the server.
"""

import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Optional


class TerminalSpawner:
    """Spawn terminal windows on macOS, Linux, and Windows."""

    @staticmethod
    def spawn(command: str, working_dir: Optional[str] = None) -> bool:
        """
        Spawn a new terminal window and execute command.

        Args:
            command: Shell command to execute
            working_dir: Optional working directory for the command

        Returns:
            True if terminal was spawned successfully
        """
        if working_dir:
            command = f"cd {working_dir} && {command}"

        platform = sys.platform

        if platform == "darwin":
            return TerminalSpawner._darwin(command)
        elif platform == "linux":
            return TerminalSpawner._linux(command)
        elif platform == "win32":
            return TerminalSpawner._windows(command)
        return False

    @staticmethod
    def _darwin(command: str) -> bool:
        """
        macOS: Open Terminal.app with command.

        Creates a temporary shell script and opens it with Terminal.app.
        The script keeps the terminal open after command completes.
        """
        try:
            # Create unique script path to avoid conflicts
            script_path = Path(f"/tmp/pdd_terminal_{os.getpid()}_{id(command)}.sh")

            # Script that runs command and keeps terminal open
            script_content = f"""#!/bin/bash
{command}
exec bash
"""
            script_path.write_text(script_content)
            script_path.chmod(0o755)

            # Open with Terminal.app
            subprocess.Popen(["open", "-a", "Terminal", str(script_path)])
            return True

        except Exception as e:
            print(f"Failed to spawn terminal on macOS: {e}")
            return False

    @staticmethod
    def _linux(command: str) -> bool:
        """
        Linux: Use gnome-terminal, xfce4-terminal, or konsole.

        Tries each terminal emulator in order until one works.
        """
        try:
            terminals = [
                ("gnome-terminal", ["gnome-terminal", "--", "bash", "-c", f"{command}; exec bash"]),
                ("xfce4-terminal", ["xfce4-terminal", "-e", f"bash -c '{command}; exec bash'"]),
                ("konsole", ["konsole", "-e", "bash", "-c", f"{command}; exec bash"]),
                ("xterm", ["xterm", "-e", "bash", "-c", f"{command}; exec bash"]),
            ]

            for term_name, args in terminals:
                if shutil.which(term_name):
                    subprocess.Popen(args)
                    return True

            print("No supported terminal emulator found on Linux")
            return False

        except Exception as e:
            print(f"Failed to spawn terminal on Linux: {e}")
            return False

    @staticmethod
    def _windows(command: str) -> bool:
        """
        Windows: Use Windows Terminal or PowerShell.

        Tries Windows Terminal first, falls back to PowerShell.
        """
        try:
            # Try Windows Terminal first (modern)
            try:
                subprocess.Popen([
                    "wt.exe", "new-tab",
                    "powershell", "-NoExit", "-Command", command
                ])
                return True
            except FileNotFoundError:
                pass

            # Fallback to PowerShell directly
            subprocess.Popen([
                "powershell.exe", "-NoExit", "-Command", command
            ])
            return True

        except Exception as e:
            print(f"Failed to spawn terminal on Windows: {e}")
            return False
