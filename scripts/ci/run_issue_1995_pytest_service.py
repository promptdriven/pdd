"""Open the issue-1995 regular log inside the service, then exec pytest."""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path


def main() -> int:
    """Replace this process after binding child stdout/stderr to one log file."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", required=True, type=Path)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    arguments = parser.parse_args()
    command = arguments.command
    if command and command[0] == "--":
        command = command[1:]
    if not command:
        parser.error("a command is required after --")
    arguments.log.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(
        arguments.log,
        os.O_WRONLY | os.O_CREAT | os.O_TRUNC | os.O_CLOEXEC,
        0o600,
    )
    try:
        os.dup2(descriptor, sys.stdout.fileno(), inheritable=True)
        os.dup2(descriptor, sys.stderr.fileno(), inheritable=True)
    finally:
        os.close(descriptor)
    os.execvpe(command[0], command, os.environ.copy())
    return 127


if __name__ == "__main__":
    raise SystemExit(main())
