"""
Cross-platform terminal spawning utilities.

Allows spawning new terminal windows to run commands in isolation,
rather than running them in the same process as the server.

Each spawned terminal calls back to the server when the command completes,
enabling automatic progress tracking in the frontend dashboard.
"""

import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Optional


# Default server port for callback
DEFAULT_SERVER_PORT = 5000


class TerminalSpawner:
    """Spawn terminal windows on macOS, Linux, and Windows."""

    @staticmethod
    def spawn(
        command: str,
        working_dir: Optional[str] = None,
        job_id: Optional[str] = None,
        server_port: int = DEFAULT_SERVER_PORT,
    ) -> bool:
        """
        Spawn a new terminal window and execute command.

        Args:
            command: Shell command to execute
            working_dir: Optional working directory for the command
            job_id: Optional job ID for tracking - enables completion callback
            server_port: Server port for completion callback (default: 5000)

        Returns:
            True if terminal was spawned successfully
        """
        if working_dir:
            # Quote the path to handle spaces and special characters
            command = f'cd "{working_dir}" && {command}'

        platform = sys.platform

        if platform == "darwin":
            return TerminalSpawner._darwin(command, job_id, server_port)
        elif platform == "linux":
            return TerminalSpawner._linux(command, job_id, server_port)
        elif platform == "win32":
            return TerminalSpawner._windows(command, job_id, server_port)
        return False

    @staticmethod
    def _darwin(
        command: str,
        job_id: Optional[str] = None,
        server_port: int = DEFAULT_SERVER_PORT,
    ) -> bool:
        """
        macOS: Open Terminal.app with command.

        Creates a temporary shell script and opens it with Terminal.app.
        The script keeps the terminal open after command completes.
        If job_id is provided, calls back to server with completion status.
        """
        try:
            # Create unique script path to avoid conflicts
            script_path = Path(f"/tmp/pdd_terminal_{os.getpid()}_{id(command)}.sh")

            # Build callback section if job_id provided
            if job_id:
                callback_section = f'''
# Report completion to server (non-blocking)
curl -s -X POST "http://localhost:{server_port}/api/v1/commands/spawned-jobs/{job_id}/complete" \\
  -H "Content-Type: application/json" \\
  -d '{{"success": '$((EXIT_CODE == 0))', "exit_code": '$EXIT_CODE'}}' &>/dev/null &

# Show result to user
echo ""
if [ $EXIT_CODE -eq 0 ]; then
    echo -e "\\033[32m✓ Command completed successfully\\033[0m"
else
    echo -e "\\033[31m✗ Command failed (exit code: $EXIT_CODE)\\033[0m"
fi
echo ""
'''
            else:
                callback_section = ""

            # Script that runs command and optionally reports status
            script_content = f"""#!/bin/bash
{command}
EXIT_CODE=$?
{callback_section}
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
    def _linux(
        command: str,
        job_id: Optional[str] = None,
        server_port: int = DEFAULT_SERVER_PORT,
    ) -> bool:
        """
        Linux: Use gnome-terminal, xfce4-terminal, or konsole.

        Tries each terminal emulator in order until one works.
        If job_id is provided, calls back to server with completion status.
        """
        try:
            # Build callback section if job_id provided
            if job_id:
                callback_cmd = f'''
EXIT_CODE=$?
curl -s -X POST "http://localhost:{server_port}/api/v1/commands/spawned-jobs/{job_id}/complete" \
  -H "Content-Type: application/json" \
  -d '{{"success": '$((EXIT_CODE == 0))', "exit_code": '$EXIT_CODE'}}' &>/dev/null &
echo ""
if [ $EXIT_CODE -eq 0 ]; then echo -e "\\033[32m✓ Command completed successfully\\033[0m"; else echo -e "\\033[31m✗ Command failed (exit code: $EXIT_CODE)\\033[0m"; fi
'''
                full_cmd = f"{command}; {callback_cmd}; exec bash"
            else:
                full_cmd = f"{command}; exec bash"

            terminals = [
                ("gnome-terminal", ["gnome-terminal", "--", "bash", "-c", full_cmd]),
                ("xfce4-terminal", ["xfce4-terminal", "-e", f"bash -c '{full_cmd}'"]),
                ("konsole", ["konsole", "-e", "bash", "-c", full_cmd]),
                ("xterm", ["xterm", "-e", "bash", "-c", full_cmd]),
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
    def _windows(
        command: str,
        job_id: Optional[str] = None,
        server_port: int = DEFAULT_SERVER_PORT,
    ) -> bool:
        """
        Windows: Use Windows Terminal or PowerShell.

        Tries Windows Terminal first, falls back to PowerShell.
        If job_id is provided, calls back to server with completion status.
        """
        try:
            # Build callback section if job_id provided
            if job_id:
                callback_cmd = f'''
$exitCode = $LASTEXITCODE
$success = if ($exitCode -eq 0) {{ "true" }} else {{ "false" }}
Invoke-RestMethod -Uri "http://localhost:{server_port}/api/v1/commands/spawned-jobs/{job_id}/complete" -Method Post -ContentType "application/json" -Body ('{{"success": ' + $success + ', "exit_code": ' + $exitCode + '}}') -ErrorAction SilentlyContinue
Write-Host ""
if ($exitCode -eq 0) {{ Write-Host "✓ Command completed successfully" -ForegroundColor Green }} else {{ Write-Host "✗ Command failed (exit code: $exitCode)" -ForegroundColor Red }}
'''
                full_cmd = f"{command}; {callback_cmd}"
            else:
                full_cmd = command

            # Try Windows Terminal first (modern)
            try:
                subprocess.Popen([
                    "wt.exe", "new-tab",
                    "powershell", "-NoExit", "-Command", full_cmd
                ])
                return True
            except FileNotFoundError:
                pass

            # Fallback to PowerShell directly
            subprocess.Popen([
                "powershell.exe", "-NoExit", "-Command", full_cmd
            ])
            return True

        except Exception as e:
            print(f"Failed to spawn terminal on Windows: {e}")
            return False
