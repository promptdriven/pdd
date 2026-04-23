"""--time → PDD_REASONING_EFFORT plumbing.

The top-level Click group must translate the user's --time value into a
low/medium/high effort level and expose it as an environment variable so
provider subprocesses (Codex, etc.) can forward it to the model. Without
this signal the --time flag only affects LiteLLM-invoked steps and silently
drops on the floor for agentic subprocess launches.
"""

import os
from unittest.mock import patch

import click
from click.testing import CliRunner


def _capture_env_for_time(time_arg):
    from pdd.core.cli import cli

    runner = CliRunner()
    captured = {}

    @cli.command("_test_effort_env")
    @click.pass_context
    def _probe(ctx):
        captured["PDD_REASONING_EFFORT"] = os.environ.get(
            "PDD_REASONING_EFFORT", "NOT_SET"
        )

    try:
        with patch.dict(os.environ, {}, clear=False):
            os.environ.pop("PDD_REASONING_EFFORT", None)
            args = []
            if time_arg is not None:
                args.extend(["--time", str(time_arg)])
            args.append("_test_effort_env")
            runner.invoke(cli, args)
        return captured.get("PDD_REASONING_EFFORT", "NOT_SET")
    finally:
        cli.commands.pop("_test_effort_env", None)
        os.environ.pop("PDD_REASONING_EFFORT", None)


def test_high_time_maps_to_high_effort():
    assert _capture_env_for_time(0.85) == "high"


def test_medium_time_maps_to_medium_effort():
    assert _capture_env_for_time(0.5) == "medium"


def test_low_time_maps_to_low_effort():
    assert _capture_env_for_time(0.2) == "low"


def test_boundary_just_above_medium_threshold_is_medium():
    # 0.3 exclusive lower bound for medium; 0.31 must bump to medium.
    assert _capture_env_for_time(0.31) == "medium"


def test_boundary_just_above_high_threshold_is_high():
    assert _capture_env_for_time(0.71) == "high"


def test_no_time_flag_leaves_env_unset():
    # When the user does not pass --time, we must not forcibly clobber
    # anything the worker env.yaml already set for the subprocess.
    assert _capture_env_for_time(None) == "NOT_SET"
