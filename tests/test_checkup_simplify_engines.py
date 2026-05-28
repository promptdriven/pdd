"""Tests for simplify engine selection and agentic invocation."""
from __future__ import annotations

from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.checkup_simplify_engines import (
    build_agentic_simplify_instruction,
    build_simplify_command_repr,
    normalize_simplify_engine,
    resolve_simplify_engine,
    run_simplify_engine_command,
)


def test_normalize_simplify_engine_rejects_unknown() -> None:
    with pytest.raises(ValueError, match="Unknown simplify engine"):
        normalize_simplify_engine("unknown")


def test_build_simplify_command_repr_claude() -> None:
    command = build_simplify_command_repr(
        "claude",
        ["pdd/foo.py"],
        focus="tighten error handling",
    )
    assert command.startswith("/simplify tighten error handling")
    assert "pdd/foo.py" in command


def test_build_simplify_command_repr_codex() -> None:
    command = build_simplify_command_repr("codex", ["pdd/foo.py"], focus="")
    assert command == "agentic-simplify (codex)"


def test_build_agentic_simplify_instruction_includes_files() -> None:
    instruction = build_agentic_simplify_instruction(
        ["pdd/foo.py", "pdd/bar.py"],
        focus="reduce duplication",
    )
    assert "In-scope files" in instruction
    assert "pdd/foo.py" in instruction
    assert "reduce duplication" in instruction


def test_resolve_auto_prefers_claude_when_available() -> None:
    with patch(
        "pdd.checkup_simplify_engines.check_claude_code_simplify_available",
        return_value=("/bin/claude", (2, 1, 0), None),
    ):
        assert resolve_simplify_engine("auto") == "claude"


def test_resolve_auto_falls_back_to_codex() -> None:
    with patch(
        "pdd.checkup_simplify_engines.check_claude_code_simplify_available",
        return_value=(None, None, "missing"),
    ), patch(
        "pdd.checkup_simplify_engines.get_available_agents",
        return_value=["openai"],
    ):
        assert resolve_simplify_engine("auto") == "codex"


def test_run_simplify_engine_command_codex_uses_agentic_task(tmp_path: Path) -> None:
    with patch(
        "pdd.checkup_simplify_engines.get_available_agents",
        return_value=["openai"],
    ), patch(
        "pdd.checkup_simplify_engines.run_agentic_task",
        return_value=(True, "cleaned up", 0.25, "openai"),
    ) as mock_task:
        success, summary, cost, provider = run_simplify_engine_command(
            "codex",
            ["pdd/sample.py"],
            tmp_path,
            focus="",
            verbose=False,
            quiet=True,
        )

    assert success is True
    assert summary == "cleaned up"
    assert cost == 0.25
    assert provider == "openai"
    mock_task.assert_called_once()
    instruction = mock_task.call_args[0][0]
    assert "pdd/sample.py" in instruction
