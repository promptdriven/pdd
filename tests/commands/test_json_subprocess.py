"""Subprocess JSON-output checks for prompt and contract commands."""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
PROMPT_FIXTURES = REPO_ROOT / "tests" / "fixtures" / "prompt_lint"
CONTRACT_FIXTURES = REPO_ROOT / "tests" / "fixtures" / "contract_check"
COMPILE_FIXTURES = REPO_ROOT / "tests" / "fixtures" / "contract_compile"
COVERAGE_FIXTURES = REPO_ROOT / "tests" / "fixtures" / "coverage_contracts"


def _run_json_command(*args: str) -> subprocess.CompletedProcess[str]:
    env = {
        **os.environ,
        "PYTHONPATH": str(REPO_ROOT),
        "PDD_AUTO_UPDATE": "false",
    }
    return subprocess.run(
        [sys.executable, "-m", "pdd.cli", *args],
        cwd=REPO_ROOT,
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )


def _loads_stdout(proc: subprocess.CompletedProcess[str]) -> object:
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise AssertionError(
            f"stdout is not JSON-only; exit={proc.returncode}\n"
            f"stdout:\n{proc.stdout}\n"
            f"stderr:\n{proc.stderr}"
        ) from exc


def test_prompt_lint_json_stdout_is_parseable_for_zero_exit() -> None:
    proc = _run_json_command(
        "prompt",
        "lint",
        "--json",
        str(PROMPT_FIXTURES / "clean.prompt"),
    )

    assert proc.returncode == 0
    data = _loads_stdout(proc)
    assert isinstance(data, list)


def test_prompt_lint_json_stdout_is_parseable_for_nonzero_exit() -> None:
    proc = _run_json_command(
        "prompt",
        "lint",
        "--json",
        str(PROMPT_FIXTURES / "vague_undefined.prompt"),
    )

    assert proc.returncode == 1
    data = _loads_stdout(proc)
    assert isinstance(data, list)


def test_contracts_check_json_stdout_is_parseable_for_nonzero_exit() -> None:
    proc = _run_json_command(
        "contracts",
        "check",
        "--json",
        str(CONTRACT_FIXTURES / "duplicate_ids_python.prompt"),
    )

    assert proc.returncode in (1, 2)
    data = _loads_stdout(proc)
    assert isinstance(data, list)


def test_contracts_compile_json_stdout_is_parseable_for_nonzero_exit() -> None:
    proc = _run_json_command(
        "contracts",
        "compile",
        "--json",
        str(COMPILE_FIXTURES / "uncompilable_python.prompt"),
    )

    assert proc.returncode == 2
    data = _loads_stdout(proc)
    assert isinstance(data, list)


def test_coverage_contracts_json_stdout_is_parseable_for_nonzero_exit() -> None:
    proc = _run_json_command(
        "coverage",
        "--contracts",
        "--json",
        "--stories-dir",
        str(COVERAGE_FIXTURES / "stories"),
        "--tests-dir",
        str(COVERAGE_FIXTURES / "fake_tests"),
        str(COVERAGE_FIXTURES / "failed_receipt_python.prompt"),
    )

    assert proc.returncode in (1, 2)
    data = _loads_stdout(proc)
    assert isinstance(data, dict)
