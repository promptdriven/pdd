"""Example usage of pdd.agentic_split.

This script exercises the public CLI-facing wrapper with external dependencies
mocked, so it runs without a real git repository, network access, or LLM
credentials.

Run from anywhere:

    python context/agentic_split_example.py
"""
from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

# Ensure pdd is importable regardless of cwd.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.agentic_split import run_agentic_split

MODULE = "pdd.agentic_split"


def demo_run_agentic_split_success(tmp_path: Path) -> None:
    """run_agentic_split validates inputs, resolves repo root, and delegates."""
    target = tmp_path / "demo.py"
    target.write_text("def demo():\n    return 1\n", encoding="utf-8")

    with (
        patch(f"{MODULE}.get_language", return_value="Python"),
        patch(f"{MODULE}.get_git_root", return_value=tmp_path),
        patch(
            f"{MODULE}.run_agentic_split_orchestrator",
            return_value=(
                True,
                "Split complete (AUTO_SHIP)",
                0.12,
                "mock-model",
                ["demo.py"],
            ),
        ) as orchestrator,
    ):
        ok, msg, cost, model, files = run_agentic_split(
            str(target),
            quiet=True,
            use_github_state=False,
            intent="REDUCE_MONOLITH",
            no_phase_extraction=True,
        )

    kwargs = orchestrator.call_args.kwargs
    print("=== run_agentic_split success ===")
    print(f"  ok={ok}, msg={msg!r}, cost={cost}, model={model!r}, files={files}")
    print(f"  cwd delegated to orchestrator: {kwargs['cwd'] == tmp_path}")
    print(f"  intent forwarded: {kwargs['intent']!r}")
    print(f"  no_phase_extraction forwarded: {kwargs['no_phase_extraction']}")
    print()


def demo_run_agentic_split_missing_target(tmp_path: Path) -> None:
    """Missing targets fail before language detection or orchestration."""
    missing = tmp_path / "missing.py"

    with (
        patch(f"{MODULE}.get_language") as get_language,
        patch(f"{MODULE}.run_agentic_split_orchestrator") as orchestrator,
    ):
        ok, msg, cost, model, files = run_agentic_split(str(missing), quiet=True)

    print("=== run_agentic_split missing target ===")
    print(f"  ok={ok}, cost={cost}, model={model!r}, files={files}")
    print(f"  msg={msg!r}")
    print(f"  language detection called: {get_language.called}")
    print(f"  orchestrator called: {orchestrator.called}")
    print()


def demo_run_agentic_split_strangler(tmp_path: Path) -> None:
    """strangler=True delegates to the sequential strangler wrapper."""
    target = tmp_path / "demo.py"
    target.write_text("def demo():\n    return 1\n", encoding="utf-8")

    with (
        patch(f"{MODULE}.get_language", return_value="Python"),
        patch(f"{MODULE}.get_git_root", return_value=tmp_path),
        patch(
            f"{MODULE}._run_strangler_split",
            return_value=(
                True,
                "Strangler split complete",
                0.34,
                "mock-model",
                ["demo.py"],
            ),
        ) as strangler,
    ):
        ok, msg, cost, model, files = run_agentic_split(
            str(target),
            quiet=True,
            use_github_state=False,
            strangler=True,
            intent="ENABLE_PARALLEL_WORK",
        )

    kwargs = strangler.call_args.kwargs
    print("=== run_agentic_split strangler ===")
    print(f"  ok={ok}, msg={msg!r}, cost={cost}, model={model!r}, files={files}")
    print(f"  target_path forwarded: {kwargs['target_path'] == target.resolve()}")
    print(f"  intent forwarded: {kwargs['intent']!r}")
    print()


if __name__ == "__main__":
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        demo_run_agentic_split_success(root)
        demo_run_agentic_split_missing_target(root)
        demo_run_agentic_split_strangler(root)
