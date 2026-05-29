"""CLI smoke for contract-rule test generation (PR #1283 / issue #821 test plan)."""
from __future__ import annotations

import os
import shutil
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd import cli

REPO_ROOT = Path(__file__).resolve().parents[2]
FIXTURE_DIR = REPO_ROOT / "tests" / "fixtures" / "test_generation"


def _contract_rule_generated_tests() -> str:
    """Simulate LLM output that follows contract-rule naming guidance."""
    return (
        "# R1: positive refund within charge\n"
        "def test_R1_approves_valid_refund():\n"
        "    assert validate_refund(1000, 500) == \"approved\"\n\n"
        "# R2: MUST NOT approve over-refund\n"
        "def test_R2_rejects_over_refund():\n"
        "    assert validate_refund(1000, 1500) == \"rejected\"\n"
    )


@pytest.fixture(autouse=True)
def _set_pdd_path(monkeypatch: pytest.MonkeyPatch) -> None:
    import pdd

    monkeypatch.setenv("PDD_PATH", str(Path(pdd.__file__).parent))


@pytest.fixture
def runner() -> CliRunner:
    return CliRunner()


def test_pdd_test_merge_smoke_contract_rule_ids(
    runner: CliRunner,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """
    Maintainer smoke (PR #1283): ``pdd test --manual --merge`` on a prompt with
    MUST and MUST NOT contract rules preserves accumulated tests and appends
    rule-ID-visible generated tests.
    """
    project = tmp_path / "project"
    project.mkdir()
    context_dir = project / "context"
    context_dir.mkdir()
    shutil.copy(REPO_ROOT / "context" / "test.prompt", context_dir / "test.prompt")

    prompt_path = project / "refund_policy_python.prompt"
    code_path = project / "refund_policy.py"
    shutil.copy(FIXTURE_DIR / "refund_policy_python.prompt", prompt_path)
    shutil.copy(FIXTURE_DIR / "refund_policy.py", code_path)

    tests_dir = project / "tests"
    tests_dir.mkdir()
    existing_test = tests_dir / "test_refund_policy.py"
    existing_test.write_text(
        "def test_existing_accumulated_refund_case():\n"
        "    assert True\n",
        encoding="utf-8",
    )

    monkeypatch.chdir(project)
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    if not os.environ.get("OPENAI_API_KEY"):
        monkeypatch.setenv("OPENAI_API_KEY", "sk-test-key-for-smoke-testing")

    generated = _contract_rule_generated_tests()

    with patch("pdd.cmd_test_main.generate_test") as mock_generate_test:
        mock_generate_test.return_value = (generated, 0.05, "smoke-model")

        result = runner.invoke(
            cli.cli,
            [
                "--local",
                "--force",
                "--quiet",
                "test",
                "--manual",
                str(prompt_path.name),
                str(code_path.name),
                "--existing-tests",
                str(existing_test),
                "--merge",
                "--output",
                str(tests_dir / "unused_output.py"),
            ],
            catch_exceptions=False,
        )

    assert result.exit_code == 0, result.output

    mock_generate_test.assert_called_once()
    sent_prompt = mock_generate_test.call_args.kwargs["prompt"]
    assert "<contract_rules>" in sent_prompt
    assert "MUST NOT" in sent_prompt

    merged = existing_test.read_text(encoding="utf-8")
    assert "test_existing_accumulated_refund_case" in merged
    assert "test_R1_approves_valid_refund" in merged
    assert "test_R2_rejects_over_refund" in merged
    assert "R1:" in merged or "R1" in merged
    assert "R2:" in merged or "R2" in merged or "MUST NOT" in merged
