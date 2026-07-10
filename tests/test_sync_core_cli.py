"""CLI contract tests for canonical synchronization certification."""

from click.testing import CliRunner

from pdd.cli import cli


def test_documented_sync_certify_spelling_is_registered() -> None:
    result = CliRunner().invoke(cli, ["sync", "certify", "--help"])
    assert result.exit_code == 0, result.output
    assert "--repos" in result.output
    assert "--run-lifecycle-matrix" in result.output


def test_global_certify_requires_complete_acceptance_inputs(tmp_path) -> None:
    replay = tmp_path / "replay"
    result = CliRunner().invoke(
        cli,
        [
            "sync",
            "certify",
            "--repos",
            "pdd,pdd_cloud",
            "--replay-ledger",
            str(replay),
        ],
    )
    assert result.exit_code == 1
    assert "global certification requires" in result.output
    assert "--full-inventory" in result.output


def test_reviewed_baseline_command_is_registered() -> None:
    result = CliRunner().invoke(cli, ["baseline", "--help"])
    assert result.exit_code == 0, result.output
    assert "--reviewed-by" in result.output
    assert "--reason" in result.output


def test_trusted_validate_command_is_registered() -> None:
    result = CliRunner().invoke(cli, ["validate", "--help"])
    assert result.exit_code == 0, result.output
    assert "--base-ref" in result.output
