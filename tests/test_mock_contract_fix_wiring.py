"""Workflow wiring tests for the issue #1939 mock-contract gate."""
from __future__ import annotations

import inspect
from pathlib import Path
from unittest.mock import patch

import click
import pytest

from pdd.agentic_e2e_fix_orchestrator import (
    _validate_changed_mock_contracts,
    run_agentic_e2e_fix_orchestrator,
)
from pdd.fix_main import fix_main
from pdd.mock_contract_validation import MockContractDivergenceError


BROKEN_CODE = """
def load(ids):
    return query_collection("user_waitlist", filters=[("userId", "in", ids)])
"""

BROKEN_TEST = """
def test_load(mock_query):
    mock_query.return_value = [{"userId": "u-1"}]
    assert load(["u-1"])
"""


def _schema(root: Path, field: str = "email") -> None:
    path = root / "context" / "database-schema.md"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "```\nuser_waitlist/\n    {uid}/\n"
        f"        {field}: string\n```\n",
        encoding="utf-8",
    )


def _ctx() -> click.Context:
    ctx = click.Context(click.Command("fix"))
    ctx.obj = {
        "confirm_callback": None,
        "context": None,
        "force": False,
        "local": True,
        "quiet": True,
        "strength": 0.5,
        "temperature": 0.0,
        "time": 0.25,
        "verbose": False,
    }
    return ctx


def _run_manual_fix(tmp_path: Path, schema_field: str) -> tuple:
    _schema(tmp_path, schema_field)
    error = tmp_path / "errors.log"
    error.write_text("failing assertion", encoding="utf-8")
    output_code = tmp_path / "src" / "reader.py"
    output_test = tmp_path / "tests" / "test_reader.py"
    constructed = (
        {},
        {
            "prompt_file": "% Goal\nRead waitlist rows.\n",
            "code_file": "def load(ids): return []\n",
            "unit_test_file": "def test_old(): pass\n",
            "error_file": "failing assertion",
        },
        {
            "output_code": str(output_code),
            "output_test": str(output_test),
            "output_results": str(tmp_path / "results.log"),
        },
        None,
    )
    generated = (True, True, BROKEN_TEST, BROKEN_CODE, "analysis", 0.1, "model")
    effective = {
        "strength": 0.5,
        "temperature": 0.0,
        "time": 0.25,
        "compress_test_context": False,
        "context_compression": "off",
        "compression_fallback": "full",
    }
    with patch("pdd.fix_main.construct_paths", return_value=constructed), patch(
        "pdd.fix_main.resolve_effective_config", return_value=effective
    ), patch(
        "pdd.fix_main.fix_errors_from_unit_tests", return_value=generated
    ), patch(
        "pdd.fix_main.run_pytest_on_file", return_value=(0, 0, 0, "passed")
    ):
        result = fix_main(
            ctx=_ctx(),
            prompt_file="prompts/reader_python.prompt",
            code_file="src/reader.py",
            unit_test_file="tests/test_reader.py",
            error_file=str(error),
            output_test=None,
            output_code=None,
            output_results=None,
            loop=False,
            verification_program=None,
            max_attempts=1,
            budget=1.0,
            auto_submit=False,
        )
    return result, output_code, output_test


def test_manual_fix_fails_before_writing_schema_divergent_mock(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.chdir(tmp_path)
    with pytest.raises(MockContractDivergenceError, match="user_waitlist.userId"):
        _run_manual_fix(tmp_path, "email")
    assert not (tmp_path / "src" / "reader.py").exists()
    assert not (tmp_path / "tests" / "test_reader.py").exists()


def test_manual_fix_with_real_mock_field_remains_successful(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.chdir(tmp_path)
    result, output_code, output_test = _run_manual_fix(tmp_path, "userId")
    assert result[0] is True
    assert output_code.read_text(encoding="utf-8") == BROKEN_CODE
    assert output_test.read_text(encoding="utf-8") == BROKEN_TEST


def test_loop_fix_restores_inputs_when_contract_gate_rejects(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The iterative fixer writes candidates in place; rejection must roll back."""
    monkeypatch.chdir(tmp_path)
    _schema(tmp_path, "email")
    prompt = tmp_path / "prompts" / "reader_python.prompt"
    code = tmp_path / "src" / "reader.py"
    test = tmp_path / "tests" / "test_reader.py"
    verifier = tmp_path / "verify.py"
    prompt.parent.mkdir(parents=True)
    code.parent.mkdir(parents=True)
    test.parent.mkdir(parents=True)
    prompt.write_text("% Goal\nRead waitlist rows.\n", encoding="utf-8")
    original_code = "def load(ids): return []\n"
    original_test = "def test_old(): pass\n"
    code.write_text(original_code, encoding="utf-8")
    test.write_text(original_test, encoding="utf-8")
    verifier.write_text("print('ok')\n", encoding="utf-8")
    effective = {
        "strength": 0.5,
        "temperature": 0.0,
        "time": 0.25,
        "compress_test_context": False,
        "context_compression": "off",
        "compression_fallback": "full",
    }

    def _write_bad_candidate(**_kwargs):
        code.write_text(BROKEN_CODE, encoding="utf-8")
        test.write_text(BROKEN_TEST, encoding="utf-8")
        return True, BROKEN_TEST, BROKEN_CODE, 1, 0.1, "model"

    with patch(
        "pdd.fix_main.resolve_effective_config", return_value=effective
    ), patch("pdd.fix_main.fix_error_loop", side_effect=_write_bad_candidate):
        with pytest.raises(MockContractDivergenceError, match="user_waitlist.userId"):
            fix_main(
                ctx=_ctx(),
                prompt_file=str(prompt),
                code_file=str(code),
                unit_test_file=str(test),
                error_file="",
                output_test=None,
                output_code=None,
                output_results=None,
                loop=True,
                verification_program=str(verifier),
                max_attempts=1,
                budget=1.0,
                auto_submit=False,
            )

    assert code.read_text(encoding="utf-8") == original_code
    assert test.read_text(encoding="utf-8") == original_test


def test_agentic_gate_reads_changed_files_and_real_schema(tmp_path: Path) -> None:
    _schema(tmp_path, "email")
    code = tmp_path / "backend" / "reader.py"
    test = tmp_path / "backend" / "tests" / "test_reader.py"
    code.parent.mkdir(parents=True)
    test.parent.mkdir(parents=True)
    code.write_text(BROKEN_CODE, encoding="utf-8")
    test.write_text(BROKEN_TEST, encoding="utf-8")

    report = _validate_changed_mock_contracts(
        cwd=tmp_path,
        changed_files=["backend/reader.py", "backend/tests/test_reader.py"],
        baseline_ref=None,
    )
    assert report.diverged


def test_agentic_success_gate_runs_before_commit_and_push() -> None:
    source = inspect.getsource(run_agentic_e2e_fix_orchestrator)
    success_branch = source.index("if success:")
    gate = source.index("_validate_changed_mock_contracts(", success_branch)
    commit = source.index("_commit_and_push(", gate)
    assert success_branch < gate < commit


def test_post_validation_repair_paths_recheck_before_push() -> None:
    """CI and pre-checkup mutations cannot bypass the terminal contract gate."""
    source = inspect.getsource(run_agentic_e2e_fix_orchestrator)
    ci_hook = source.index("pre_commit_check=")
    pre_checkup = source.index("_run_pre_checkup_gate_with_remediation(", ci_hook)
    final_gate = source.index("final_contract_error =", pre_checkup)
    gate_sync_push = source.index("_commit_and_push(", final_gate)

    assert ci_hook < pre_checkup < final_gate < gate_sync_push
