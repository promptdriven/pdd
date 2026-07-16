#!/usr/bin/env python3
"""Run a command with release env plus Claude OAuth slots from SOPS files."""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path


CLAUDE_SLOT_NAMES = (
    "CLAUDE_CODE_OAUTH_TOKEN_1",
    "CLAUDE_CODE_OAUTH_TOKEN_2",
    "CLAUDE_CODE_OAUTH_TOKEN_3",
)

# GNU Make accepts control input from its environment before it reads the
# Makefile. Do not let either the caller's ambient state or decrypted release
# data provide include files, flags, recursive overrides, or an alternate
# shell/Make command to the child process.
MAKE_CONTROL_NAMES = (
    "MAKEFILES",
    "MAKEFLAGS",
    "GNUMAKEFLAGS",
    "MFLAGS",
    "MAKEOVERRIDES",
    "MAKELEVEL",
    "MAKE_RESTARTS",
    "MAKE_TERMOUT",
    "MAKE_TERMERR",
    "MAKE",
    "MAKE_COMMAND",
    "MAKE_INCLUDE_PATH",
    "VPATH",
    "SHELL",
)

# The reviewed public Make invocation supplies these again as explicit command
# arguments after SOPS. They must never originate in decrypted or ambient env.
ATTESTATION_NAMES = (
    "PDD_CLOUD_RELEASE_ATTESTATION_VERSION",
    "PDD_CLOUD_VALIDATED_SHA",
    "PDD_CLOUD_RELEASE_LEASE_OWNER",
    "PDD_CLOUD_RELEASE_LEASE_REF",
)


def parse_dotenv(text: str) -> dict[str, str]:
    """Parse the dotenv subset emitted by the SOPS release files."""
    env: dict[str, str] = {}
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        if line.startswith("export "):
            line = line[len("export ") :].lstrip()
        key, value = line.split("=", 1)
        key = key.strip()
        if not key or key.startswith("sops_"):
            continue
        value = value.strip()
        if len(value) >= 2 and value[0] == value[-1] and value[0] in {"'", '"'}:
            value = value[1:-1]
        env[key] = value
    return env


def decrypt_env_file(sops: str, path: Path) -> dict[str, str]:
    """Decrypt a SOPS dotenv file and return parsed environment variables."""
    if not path.is_file():
        raise RuntimeError(f"SOPS env file not found: {path}")
    completed = subprocess.run(
        [sops, "decrypt", str(path)],
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        details = completed.stderr.strip() or "sops decrypt failed"
        raise RuntimeError(f"Could not decrypt {path}: {details}")
    return parse_dotenv(completed.stdout)


def build_env(args: argparse.Namespace) -> dict[str, str]:
    """Build the child process environment from release and Claude SOPS files."""
    if shutil.which(args.sops) is None:
        raise RuntimeError(f"{args.sops} CLI is required")

    env = os.environ.copy()
    for name in (*MAKE_CONTROL_NAMES, *ATTESTATION_NAMES):
        env.pop(name, None)
    release_env = decrypt_env_file(args.sops, Path(args.release_env_file))
    for name in (*MAKE_CONTROL_NAMES, *ATTESTATION_NAMES):
        release_env.pop(name, None)
    env.update(release_env)

    for name in CLAUDE_SLOT_NAMES:
        env.pop(name, None)

    seen_tokens: set[str] = set()
    slot_index = 0
    for source in args.claude_env_file:
        source_path = Path(source)
        if slot_index >= len(CLAUDE_SLOT_NAMES):
            print(
                f"Claude Code OAuth source ignored because all slots are assigned: {source_path}",
                file=sys.stderr,
            )
            continue
        slot_name = CLAUDE_SLOT_NAMES[slot_index]
        source_env = decrypt_env_file(args.sops, source_path)
        token = source_env.get("CLAUDE_CODE_OAUTH_TOKEN", "").strip()
        if not token:
            print(
                "Claude Code OAuth source has no CLAUDE_CODE_OAUTH_TOKEN "
                f"for {slot_name}: {source_path}",
                file=sys.stderr,
            )
            continue
        if token in seen_tokens:
            print(
                "Claude Code OAuth source duplicates an earlier token; "
                f"not assigning another slot: {source_path}",
                file=sys.stderr,
            )
            continue
        env[slot_name] = token
        seen_tokens.add(token)
        slot_index += 1
        print(
            f"Mapped {source_path} CLAUDE_CODE_OAUTH_TOKEN to {slot_name}.",
            file=sys.stderr,
        )

    env["REQUIRE_CLAUDE_OAUTH_SLOTS"] = args.require_claude_slots
    env["RELEASE_VIDEO"] = args.release_video
    return env


def main() -> int:
    """CLI entrypoint."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--sops", default="sops")
    parser.add_argument("--release-env-file", required=True)
    parser.add_argument("--claude-env-file", action="append", default=[])
    parser.add_argument("--require-claude-slots", default="1")
    parser.add_argument("--release-video", default="1")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()

    command = args.command
    if command and command[0] == "--":
        command = command[1:]
    if not command:
        parser.error("command is required after --")

    try:
        env = build_env(args)
    except RuntimeError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1

    completed = subprocess.run(command, env=env, check=False)
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main())
