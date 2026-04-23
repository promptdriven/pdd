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


def test_zero_time_maps_to_low_effort():
    # --time 0.0 is a valid value (click.FloatRange lower bound) and must
    # map to "low" — the user did opt in.
    assert _capture_env_for_time(0.0) == "low"


def test_one_time_maps_to_high_effort():
    # --time 1.0 is the click.FloatRange upper bound; must produce "high".
    assert _capture_env_for_time(1.0) == "high"


def test_exact_low_medium_boundary_maps_to_low():
    # Thresholds use strict >; exact 0.3 stays "low".
    assert _capture_env_for_time(0.3) == "low"


def test_exact_medium_high_boundary_maps_to_medium():
    # Thresholds use strict >; exact 0.7 stays "medium", does not flip to "high".
    assert _capture_env_for_time(0.7) == "medium"


def test_cli_env_survives_to_downstream_same_process():
    """End-to-end: after the CLI callback fires with --time, a later call to
    _run_with_provider in the same Python process sees the env var and
    injects Codex's -c flag. Guards against the failure mode where one
    end of the chain works in isolation but the seam silently breaks.
    """
    import json
    from pathlib import Path
    from unittest.mock import patch

    from pdd.agentic_common import _run_with_provider
    from pdd.core.cli import cli

    captured_cmd = {}

    def fake_subprocess_run(cmd, **kwargs):
        captured_cmd["cmd"] = cmd
        import subprocess
        return subprocess.CompletedProcess(
            cmd, 0,
            stdout=json.dumps({
                "type": "result", "output": "ok",
                "usage": {"input_tokens": 10, "output_tokens": 10, "cached_input_tokens": 0},
            }),
            stderr="",
        )

    runner = CliRunner()

    @cli.command("_test_full_chain")
    @click.pass_context
    def _probe(ctx):
        tmpdir = Path(os.environ["_TEST_TMPDIR"])
        prompt_file = tmpdir / "prompt.txt"
        prompt_file.write_text("hi")
        with patch("pdd.agentic_common._subprocess_run", side_effect=fake_subprocess_run):
            with patch("pdd.agentic_common._find_cli_binary", return_value="/bin/codex"):
                _run_with_provider(
                    "openai", prompt_file, tmpdir,
                    verbose=False, quiet=True,
                )

    try:
        with runner.isolated_filesystem() as tmpdir:
            os.environ["_TEST_TMPDIR"] = str(tmpdir)
            with patch.dict(os.environ, {}, clear=False):
                os.environ.pop("PDD_REASONING_EFFORT", None)
                result = runner.invoke(cli, ["--time", "0.85", "_test_full_chain"])
                assert result.exit_code == 0, result.output
                cmd = captured_cmd.get("cmd") or []
                assert "-c" in cmd, f"Codex -c flag missing from full-chain cmd: {cmd}"
                assert cmd[cmd.index("-c") + 1] == "model_reasoning_effort=high"
                assert cmd.index("-c") < cmd.index("exec")
    finally:
        cli.commands.pop("_test_full_chain", None)
        os.environ.pop("_TEST_TMPDIR", None)
        os.environ.pop("PDD_REASONING_EFFORT", None)
