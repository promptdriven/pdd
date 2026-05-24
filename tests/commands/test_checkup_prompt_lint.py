"""CLI tests for deterministic ``pdd checkup lint``."""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.commands.checkup import checkup

FIXTURES = Path(__file__).parents[1] / "fixtures" / "prompt_lint"
REPO_ROOT = Path(__file__).parents[2]


def test_checkup_lint_clean_prompt_json() -> None:
    result = CliRunner().invoke(
        checkup,
        ["lint", "--json", str(FIXTURES / "clean.prompt")],
        obj={"quiet": True},
    )

    assert result.exit_code == 0
    payload = json.loads(result.output)
    assert payload[0]["issues"] == []


def test_checkup_lint_reports_warning() -> None:
    result = CliRunner().invoke(
        checkup,
        ["lint", "--json", str(FIXTURES / "vague_undefined.prompt")],
        obj={"quiet": True},
    )

    assert result.exit_code == 1
    assert json.loads(result.output)[0]["warn_count"] > 0


def test_checkup_lint_strict_promotes_warning_to_error() -> None:
    result = CliRunner().invoke(
        checkup,
        ["lint", "--strict", "--json", str(FIXTURES / "vague_undefined.prompt")],
        obj={"quiet": True},
    )

    assert result.exit_code == 2
    assert json.loads(result.output)[0]["error_count"] > 0


@pytest.mark.parametrize("as_json", [False, True])
def test_checkup_lint_ambiguity_never_writes_without_explicit_apply(
    tmp_path: Path, as_json: bool
) -> None:
    prompt = tmp_path / "vague_undefined.prompt"
    prompt.write_bytes((FIXTURES / "vague_undefined.prompt").read_bytes())
    before = prompt.read_bytes()
    args = ["lint", "--ambiguity"]
    if as_json:
        args.append("--json")
    args.append(str(prompt))

    with patch("pdd.commands.prompt.run_llm_ambiguity_pass", return_value=[]):
        result = CliRunner().invoke(checkup, args, obj={"quiet": True})

    assert result.exit_code == 1
    assert prompt.read_bytes() == before


@pytest.mark.parametrize(
    ("fixture_name", "expected_exit_code"),
    [("clean.prompt", 0), ("vague_undefined.prompt", 1)],
)
def test_checkup_lint_real_cli_json_stdout_is_parseable_only(
    fixture_name: str, expected_exit_code: int
) -> None:
    env = os.environ.copy()
    env.update(
        {
            "PDD_PATH": str(REPO_ROOT / "pdd"),
            "PYTHONPATH": str(REPO_ROOT),
            "PDD_AUTO_UPDATE": "true",
        }
    )
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "pdd",
            "checkup",
            "lint",
            "--json",
            str(FIXTURES / fixture_name),
        ],
        cwd=REPO_ROOT,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode == expected_exit_code
    payload = json.loads(result.stdout)
    assert isinstance(payload, list)
