"""Register the frozen run environment on the pilot machine (design §8.1.1).

The env fingerprint deliberately covers the *values* of the allowlisted
environment variables (PATH etc.), so it is **machine-bound**: the committed
``pilot_arm_codex.json`` freezes the choices, and this CLI — run once on the
machine that will execute the pilot — emits the ``registered_env_fingerprint``
to paste into the experiment config. Every subsequent trial re-derives the
fingerprint and aborts on any mismatch.

Run::

    python3 -m harness.runner.register_env \
        --arm harness/runner/pilot_arm_codex.json \
        --out registered_env.json

Checks performed (no model tokens, no network):

1. the pinned CLI is installed and ``--version`` output matches the pin
   byte-exactly;
2. the frozen config renders and its fingerprint is stable across two
   derivations;
3. the fingerprint (+ the environment values it covers) is written to
   ``--out`` for the experiment config and the run log.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path

from harness.runner.env_freeze import FreezeConfig, FreezeViolation, capture_cli_version


def load_arm_config(path: Path) -> FreezeConfig:
    data = json.loads(path.read_text(encoding="utf-8"))
    data.pop("_comment", None)
    data["cli_version_command"] = list(data["cli_version_command"])
    for key in ("mcp_servers", "env_allowlist"):
        if key in data:
            data[key] = tuple(data[key])
    return FreezeConfig(**data)


def register(arm_path: Path, check_binary: bool = True) -> dict:
    config = load_arm_config(arm_path)
    result: dict = {
        "arm_config": str(arm_path),
        "pinned_cli_version": config.pinned_cli_version,
        "model_id": config.model_id,
        "reasoning_effort": config.reasoning_effort,
        "context_window_tokens": config.context_window_tokens,
    }
    if check_binary:
        found = capture_cli_version(config.cli_version_command)
        if found != config.pinned_cli_version:
            raise FreezeViolation(
                f"installed CLI is {found!r}, pin is {config.pinned_cli_version!r} "
                "— install the pinned build; do not re-pin casually"
            )
        result["cli_version_verified"] = found
    fingerprint = config.fingerprint()
    if config.fingerprint() != fingerprint:
        raise FreezeViolation("fingerprint not stable across derivations")
    result["registered_env_fingerprint"] = fingerprint
    result["env_allowlist_values"] = {
        name: os.environ.get(name) for name in sorted(config.env_allowlist)
    }
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--arm", required=True, type=Path,
                        help="committed arm config (pilot_arm_codex.json)")
    parser.add_argument("--out", type=Path, default=None,
                        help="write the registration record here")
    parser.add_argument("--skip-binary-check", action="store_true",
                        help="derive the fingerprint without the pinned CLI "
                        "installed (registration record is then NOT valid "
                        "for runs on this machine)")
    args = parser.parse_args(argv)

    try:
        record = register(args.arm, check_binary=not args.skip_binary_check)
    except FreezeViolation as exc:
        print(f"REGISTRATION FAILED: {exc}", file=sys.stderr)
        return 1
    if args.out:
        args.out.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(f"registered_env_fingerprint: {record['registered_env_fingerprint']}")
    print("Paste into the experiment config as \"registered_env_fingerprint\" "
          "alongside \"freeze\" (the arm config's fields).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
