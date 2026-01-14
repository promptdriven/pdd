"""
Firebase Emulator Manager for E2E Testing.

This module provides automated lifecycle management for the Firebase emulator,
including starting, stopping, and status checking.
"""

import os
import subprocess
import socket
import time
import signal
import sys
from pathlib import Path
from typing import Optional


class FirebaseEmulatorManager:
    """
    Manages the lifecycle of Firebase emulator for E2E testing.

    The emulator runs Firestore, Cloud Functions, and Auth services
    for local testing without hitting real Firebase infrastructure.
    """

    def __init__(
        self,
        pdd_cloud_path: str,
        firestore_port: int = 8080,
        functions_port: int = 5555,
        auth_port: int = 9098,
        log_file: str = "/tmp/pdd_emulator.log"
    ):
        """
        Initialize the emulator manager.

        Args:
            pdd_cloud_path: Path to pdd_cloud repository root
            firestore_port: Port for Firestore emulator (default 8080)
            functions_port: Port for Cloud Functions emulator (default 5555)
            auth_port: Port for Auth emulator (default 9098)
            log_file: Path to log file for emulator output
        """
        self.pdd_cloud_path = Path(pdd_cloud_path)
        self.firestore_port = firestore_port
        self.functions_port = functions_port
        self.auth_port = auth_port
        self.log_file = log_file
        self.process: Optional[subprocess.Popen] = None
        self.pid_file = "/tmp/pdd_emulator.pid"

    def is_running(self) -> bool:
        """
        Check if Firebase emulator is currently running.

        Uses socket connection test to verify the emulator is responsive.

        Returns:
            bool: True if emulator is running and responsive
        """
        # Check if we have a PID file and process is still running
        if os.path.exists(self.pid_file):
            try:
                with open(self.pid_file, 'r') as f:
                    pid = int(f.read().strip())

                # Check if process exists
                try:
                    os.kill(pid, 0)  # Signal 0 just checks if process exists
                except OSError:
                    # Process doesn't exist, clean up PID file
                    os.remove(self.pid_file)
                    return False
            except (ValueError, FileNotFoundError):
                pass

        # Verify emulator is actually responsive by checking port
        return self._check_port(self.firestore_port)

    def _check_port(self, port: int, timeout: float = 1.0) -> bool:
        """
        Check if a port is accessible.

        Args:
            port: Port number to check
            timeout: Connection timeout in seconds

        Returns:
            bool: True if port is accessible
        """
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(timeout)
            result = sock.connect_ex(('localhost', port))
            sock.close()
            return result == 0
        except Exception:
            return False

    def start(self, background: bool = True, wait_timeout: int = 60) -> bool:
        """
        Start the Firebase emulator.

        Args:
            background: If True, run emulator in background
            wait_timeout: Maximum seconds to wait for emulator to be ready

        Returns:
            bool: True if emulator started successfully

        Raises:
            RuntimeError: If emulator is already running or fails to start
            FileNotFoundError: If pdd_cloud_path doesn't exist or firebase CLI not found
        """
        # Check if already running
        if self.is_running():
            print("Firebase emulator is already running")
            return True

        # Verify pdd_cloud path exists
        if not self.pdd_cloud_path.exists():
            raise FileNotFoundError(
                f"pdd_cloud repository not found at: {self.pdd_cloud_path}"
            )

        # Check if firebase CLI is installed
        try:
            subprocess.run(
                ["firebase", "--version"],
                check=True,
                capture_output=True,
                text=True
            )
        except (subprocess.CalledProcessError, FileNotFoundError):
            raise FileNotFoundError(
                "Firebase CLI not found. Install with: npm install -g firebase-tools"
            )

        # Prepare command
        cmd = [
            "firebase",
            "emulators:start",
            "--only", "firestore,functions,auth",
            "--project", "prompt-driven-development"
        ]

        # Start emulator
        print(f"Starting Firebase emulator from {self.pdd_cloud_path}...")
        print(f"  Firestore: localhost:{self.firestore_port}")
        print(f"  Functions: localhost:{self.functions_port}")
        print(f"  Auth: localhost:{self.auth_port}")
        print(f"  Logs: {self.log_file}")

        try:
            # Open log file
            log_f = open(self.log_file, 'w')

            # Start process
            self.process = subprocess.Popen(
                cmd,
                cwd=self.pdd_cloud_path,
                stdout=log_f,
                stderr=subprocess.STDOUT,
                preexec_fn=os.setsid if sys.platform != 'win32' else None
            )

            # Save PID
            with open(self.pid_file, 'w') as f:
                f.write(str(self.process.pid))

            # Wait for emulator to be ready
            if not self.wait_for_ready(wait_timeout):
                self.stop()
                raise RuntimeError(
                    f"Emulator failed to start within {wait_timeout} seconds. "
                    f"Check logs at: {self.log_file}"
                )

            print("✅ Firebase emulator started successfully")
            return True

        except Exception as e:
            # Clean up on failure
            if self.process:
                self.stop()
            raise RuntimeError(f"Failed to start emulator: {str(e)}") from e

    def wait_for_ready(self, timeout: int = 60) -> bool:
        """
        Wait for emulator to be ready.

        Polls the Firestore port until it's accessible or timeout is reached.

        Args:
            timeout: Maximum seconds to wait

        Returns:
            bool: True if emulator became ready within timeout
        """
        print("Waiting for emulator to be ready...", end='', flush=True)
        start_time = time.time()
        poll_interval = 0.5  # Check every 500ms

        while time.time() - start_time < timeout:
            if self._check_port(self.firestore_port, timeout=0.5):
                elapsed = time.time() - start_time
                print(f" ready! ({elapsed:.1f}s)")
                return True

            print(".", end='', flush=True)
            time.sleep(poll_interval)

        print(" timeout!")
        return False

    def stop(self) -> bool:
        """
        Stop the Firebase emulator.

        Sends SIGTERM to the emulator process group and waits for shutdown.

        Returns:
            bool: True if emulator stopped successfully
        """
        # Check if emulator is running
        if not self.is_running():
            print("Firebase emulator is not running")
            # Clean up PID file if it exists
            if os.path.exists(self.pid_file):
                os.remove(self.pid_file)
            return True

        print("Stopping Firebase emulator...")

        # Try to get PID from file
        pid = None
        if os.path.exists(self.pid_file):
            try:
                with open(self.pid_file, 'r') as f:
                    pid = int(f.read().strip())
            except (ValueError, FileNotFoundError):
                pass

        # If we have a process reference, use it
        if self.process and self.process.poll() is None:
            try:
                # Send SIGTERM to process group (kills all children)
                if sys.platform != 'win32':
                    os.killpg(os.getpgid(self.process.pid), signal.SIGTERM)
                else:
                    self.process.terminate()

                # Wait for process to terminate
                self.process.wait(timeout=10)
                print("✅ Emulator stopped successfully")

            except subprocess.TimeoutExpired:
                # Force kill if graceful shutdown failed
                print("⚠️  Emulator didn't stop gracefully, force killing...")
                if sys.platform != 'win32':
                    os.killpg(os.getpgid(self.process.pid), signal.SIGKILL)
                else:
                    self.process.kill()
                self.process.wait()

            except Exception as e:
                print(f"⚠️  Error stopping emulator: {e}")

        # If we only have PID, kill that
        elif pid:
            try:
                if sys.platform != 'win32':
                    os.killpg(os.getpgid(pid), signal.SIGTERM)
                else:
                    os.kill(pid, signal.SIGTERM)
                print("✅ Emulator stopped successfully (via PID)")
            except ProcessLookupError:
                print("Process already terminated")
            except Exception as e:
                print(f"⚠️  Error killing process: {e}")

        # Clean up PID file
        if os.path.exists(self.pid_file):
            os.remove(self.pid_file)

        # Verify ports are released
        time.sleep(1)
        if self._check_port(self.firestore_port):
            print("⚠️  Warning: Firestore port still in use")
            return False

        return True

    def get_status(self) -> dict:
        """
        Get the current status of the emulator.

        Returns:
            dict: Status information including:
                - running: bool
                - firestore_port: bool (accessible)
                - functions_port: bool (accessible)
                - auth_port: bool (accessible)
                - pid: Optional[int]
        """
        pid = None
        if os.path.exists(self.pid_file):
            try:
                with open(self.pid_file, 'r') as f:
                    pid = int(f.read().strip())
            except (ValueError, FileNotFoundError):
                pass

        return {
            "running": self.is_running(),
            "firestore_port": self._check_port(self.firestore_port),
            "functions_port": self._check_port(self.functions_port),
            "auth_port": self._check_port(self.auth_port),
            "pid": pid
        }

    def __enter__(self):
        """Context manager entry: start emulator."""
        self.start()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit: stop emulator."""
        self.stop()


def main():
    """CLI interface for emulator manager."""
    import argparse

    parser = argparse.ArgumentParser(description="Manage Firebase emulator for E2E testing")
    parser.add_argument(
        "command",
        choices=["start", "stop", "status"],
        help="Command to execute"
    )
    parser.add_argument(
        "--pdd-cloud-path",
        default=os.environ.get("PDD_CLOUD_PATH", "/Users/caijiamin/Desktop/pdd_cloud/pdd_cloud"),
        help="Path to pdd_cloud repository"
    )
    parser.add_argument(
        "--background",
        action="store_true",
        help="Run emulator in background (for start command)"
    )

    args = parser.parse_args()

    manager = FirebaseEmulatorManager(pdd_cloud_path=args.pdd_cloud_path)

    if args.command == "start":
        try:
            manager.start(background=args.background)
            sys.exit(0)
        except Exception as e:
            print(f"❌ Error: {e}", file=sys.stderr)
            sys.exit(1)

    elif args.command == "stop":
        success = manager.stop()
        sys.exit(0 if success else 1)

    elif args.command == "status":
        status = manager.get_status()
        print("\nFirebase Emulator Status:")
        print(f"  Running: {'✅ Yes' if status['running'] else '❌ No'}")
        print(f"  Firestore ({manager.firestore_port}): {'✅' if status['firestore_port'] else '❌'}")
        print(f"  Functions ({manager.functions_port}): {'✅' if status['functions_port'] else '❌'}")
        print(f"  Auth ({manager.auth_port}): {'✅' if status['auth_port'] else '❌'}")
        if status['pid']:
            print(f"  PID: {status['pid']}")
        sys.exit(0 if status['running'] else 1)


if __name__ == "__main__":
    main()
