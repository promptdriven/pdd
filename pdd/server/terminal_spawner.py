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


# Default server port for callback (must match PDD server port)
DEFAULT_SERVER_PORT = 9876


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
    def _get_env_activation(is_windows: bool = False) -> str:
        """
        Detect active Python environment (conda/venv) and return activation command.
        """
        # Check for Conda
        conda_prefix = os.environ.get('CONDA_PREFIX')
        conda_env = os.environ.get('CONDA_DEFAULT_ENV')
        
        if conda_prefix and conda_env:
            if is_windows:
                # Windows Conda activation
                activate_script = os.path.join(conda_prefix, "Scripts", "activate.bat")
                if os.path.exists(activate_script):
                    return f'call "{activate_script}"'
                return f"conda activate {conda_env}"
            else:
                # Unix Conda activation
                activate_script = os.path.join(conda_prefix, "bin", "activate")
                if os.path.exists(activate_script):
                    return f"source '{activate_script}'"
                return f"conda activate {conda_env}"

        # Check for Virtualenv
        virtual_env = os.environ.get('VIRTUAL_ENV')
        if virtual_env:
            if is_windows:
                # Windows venv activation (PowerShell)
                activate_script = os.path.join(virtual_env, "Scripts", "Activate.ps1")
                return f'. "{activate_script}"'
            else:
                # Unix venv activation
                activate_script = os.path.join(virtual_env, "bin", "activate")
                return f"source '{activate_script}'"

        return ""

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
# Report completion to server (must complete before exec bash)
EXIT_CODE=${{EXIT_CODE:-0}}
if [ "$EXIT_CODE" -eq 0 ]; then
    SUCCESS_JSON="true"
else
    SUCCESS_JSON="false"
fi
echo "[DEBUG] Sending callback to http://localhost:{server_port}/api/v1/commands/spawned-jobs/{job_id}/complete"
echo "[DEBUG] Payload: {{\\\"success\\\": $SUCCESS_JSON, \\\"exit_code\\\": $EXIT_CODE}}"
CURL_RESPONSE=$(curl -s -w "\\n[HTTP_STATUS:%{{http_code}}]" -X POST "http://localhost:{server_port}/api/v1/commands/spawned-jobs/{job_id}/complete" \\
  -H "Content-Type: application/json" \\
  -d "{{\\\"success\\\": $SUCCESS_JSON, \\\"exit_code\\\": $EXIT_CODE}}" 2>&1)
echo "[DEBUG] Curl response: $CURL_RESPONSE"

# Show result to user
echo ""
if [ "$EXIT_CODE" -eq 0 ]; then
    echo -e "\\033[32m✓ Command completed successfully\\033[0m"
else
    echo -e "\\033[31m✗ Command failed (exit code: $EXIT_CODE)\\033[0m"
fi
echo ""
'''
            else:
                callback_section = ""

            # Add environment activation if needed
            env_activation = TerminalSpawner._get_env_activation(is_windows=False)
            full_command = f"{env_activation}\n{command}" if env_activation else command

            # Script that runs command and optionally reports status
            script_content = f"""#!/bin/bash
{full_command}
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
            # Add environment activation if needed
            env_activation = TerminalSpawner._get_env_activation(is_windows=False)
            
            # Build callback section if job_id provided
            if job_id:
                callback_cmd = f'''
EXIT_CODE=$?
EXIT_CODE=${{EXIT_CODE:-0}}
if [ "$EXIT_CODE" -eq 0 ]; then SUCCESS_JSON="true"; else SUCCESS_JSON="false"; fi
echo "[DEBUG] Sending callback to http://localhost:{server_port}/api/v1/commands/spawned-jobs/{job_id}/complete"
CURL_RESPONSE=$(curl -s -w "\\n[HTTP_STATUS:%{{http_code}}]" -X POST "http://localhost:{server_port}/api/v1/commands/spawned-jobs/{job_id}/complete" \\
  -H "Content-Type: application/json" \\
  -d "{{\\\"success\\\": $SUCCESS_JSON, \\\"exit_code\\\": $EXIT_CODE}}" 2>&1)
echo "[DEBUG] Curl response: $CURL_RESPONSE"
echo ""
if [ "$EXIT_CODE" -eq 0 ]; then echo -e "\\033[32m✓ Command completed successfully\\033[0m"; else echo -e "\\033[31m✗ Command failed (exit code: $EXIT_CODE)\\033[0m"; fi
'''
                # Combine activation, command, callback, and shell keep-alive
                if env_activation:
                    full_cmd = f"{env_activation}; {command}; {callback_cmd}; exec bash"
                else:
                    full_cmd = f"{command}; {callback_cmd}; exec bash"
            else:
                if env_activation:
                    full_cmd = f"{env_activation}; {command}; exec bash"
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
            # Add environment activation if needed
            env_activation = TerminalSpawner._get_env_activation(is_windows=True)

            # Build callback section if job_id provided
            if job_id:
                callback_cmd = f'''
$exitCode = $LASTEXITCODE
$success = if ($exitCode -eq 0) {{ "true" }} else {{ "false" }}
Invoke-RestMethod -Uri "http://localhost:{server_port}/api/v1/commands/spawned-jobs/{job_id}/complete" -Method Post -ContentType "application/json" -Body ('{{"success": ' + $success + ', "exit_code": ' + $exitCode + '}}') -ErrorAction SilentlyContinue
Write-Host ""
if ($exitCode -eq 0) {{ Write-Host "✓ Command completed successfully" -ForegroundColor Green }} else {{ Write-Host "✗ Command failed (exit code: $exitCode)" -ForegroundColor Red }}
'''
                if env_activation:
                    full_cmd = f"{env_activation}; {command}; {callback_cmd}"
                else:
                    full_cmd = f"{command}; {callback_cmd}"
            else:
                if env_activation:
                    full_cmd = f"{env_activation}; {command}"
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
