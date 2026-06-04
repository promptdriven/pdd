"""Prompt/architecture contract for sync agentic_fallback_events plumbing."""
from __future__ import annotations

import inspect
import json
import re
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent

_CLI_CONTRACTS = (
    (
        "fix_main",
        REPO_ROOT / "pdd" / "prompts" / "fix_main_python.prompt",
        "fix_main_python.prompt",
        "pdd.fix_main",
        "fix_main",
    ),
    (
        "fix_verification_main",
        REPO_ROOT / "pdd" / "prompts" / "fix_verification_main_python.prompt",
        "fix_verification_main_python.prompt",
        "pdd.fix_verification_main",
        "fix_verification_main",
    ),
)


def _parse_pdd_interface(prompt_path: Path) -> dict:
    text = prompt_path.read_text(encoding="utf-8")
    match = re.search(
        r"<pdd-interface>\s*(\{.*?\})\s*</pdd-interface>",
        text,
        re.DOTALL,
    )
    assert match, f"{prompt_path.name} must declare <pdd-interface>"
    return json.loads(match.group(1))


def _cli_command_signature(interface: dict, command_name: str) -> str:
    commands = interface.get("cli", {}).get("commands", [])
    command = next((c for c in commands if c.get("name") == command_name), None)
    assert command is not None, f"missing cli command {command_name!r}"
    return command["signature"]


def _architecture_cli_signature(arch_filename: str, command_name: str) -> str:
    arch = json.loads((REPO_ROOT / "architecture.json").read_text(encoding="utf-8"))
    entry = next(e for e in arch if e.get("filename") == arch_filename)
    commands = entry.get("interface", {}).get("cli", {}).get("commands", [])
    command = next((c for c in commands if c.get("name") == command_name), None)
    assert command is not None, f"architecture.json missing {command_name!r}"
    return command["signature"]


@pytest.mark.parametrize(
    "command_name,prompt_path,arch_filename,module_path,function_name",
    _CLI_CONTRACTS,
    ids=[c[0] for c in _CLI_CONTRACTS],
)
def test_agentic_fallback_events_in_prompt_architecture_and_runtime(
    command_name: str,
    prompt_path: Path,
    arch_filename: str,
    module_path: str,
    function_name: str,
) -> None:
    """Sync telemetry param must appear in prompt, architecture.json, and code."""
    prompt_sig = _cli_command_signature(_parse_pdd_interface(prompt_path), command_name)
    arch_sig = _architecture_cli_signature(arch_filename, command_name)

    assert prompt_sig == arch_sig, (
        f"{command_name}: prompt/architecture signature drift:\n"
        f"  prompt: {prompt_sig!r}\n"
        f"  arch:   {arch_sig!r}"
    )
    assert "agentic_fallback_events" in prompt_sig

    import importlib

    module = importlib.import_module(module_path)
    runtime_params = list(inspect.signature(getattr(module, function_name)).parameters)
    assert "agentic_fallback_events" in runtime_params
