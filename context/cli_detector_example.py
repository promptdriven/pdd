from __future__ import annotations

import os
import sys
from subprocess import CompletedProcess
from unittest import mock

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.cli_detector import CliBootstrapResult, detect_and_bootstrap_cli, detect_cli_tools


def run_bootstrap_demo() -> list[CliBootstrapResult]:
    """Run a non-interactive bootstrap demo.

    Inputs:
        None. The example supplies mocked terminal input, CLI paths, API keys,
        and subprocess results. CLI paths are filesystem path strings.

    Outputs:
        A list of CliBootstrapResult objects. Each result reports the CLI name,
        provider name, CLI path string, whether an API key is configured, and
        whether that CLI was skipped.
    """

    fake_paths = {
        "claude": "/mock/bin/claude",
        "codex": "/mock/bin/codex",
        "gemini": "/mock/bin/gemini",
        "opencode": "/mock/bin/opencode",
    }

    def fake_which(command: str) -> str | None:
        return fake_paths.get(command)

    def fake_run(command: list[str], **_: object) -> CompletedProcess[str]:
        cli_name = os.path.basename(command[0])
        return CompletedProcess(command, 0, stdout=f"{cli_name} 1.2.3", stderr="")

    env = {
        "ANTHROPIC_API_KEY": "sk-ant-demo",
        "OPENAI_API_KEY": "sk-openai-demo",
        "GEMINI_API_KEY": "sk-gemini-demo",
    }

    with mock.patch.dict(os.environ, env, clear=False), mock.patch(
        "builtins.input", return_value="1,4"
    ), mock.patch("pdd.cli_detector.shutil.which", side_effect=fake_which), mock.patch(
        "pdd.cli_detector.subprocess.run", side_effect=fake_run
    ), mock.patch(
        "pdd.cli_detector._print_step_banner",
        side_effect=lambda title: print(f"== {title} =="),
    ):
        return detect_and_bootstrap_cli()


def run_legacy_demo() -> None:
    """Run the legacy detection demo.

    Inputs:
        None. CLI discovery and environment variables are mocked.

    Outputs:
        Printed detection status for Claude CLI, Codex CLI, Gemini CLI, and
        OpenCode CLI. The function itself returns None.
    """

    fake_paths = {
        "claude": "/mock/bin/claude",
        "codex": "/mock/bin/codex",
        "gemini": "/mock/bin/gemini",
        "opencode": "/mock/bin/opencode",
    }

    with mock.patch.dict(
        os.environ,
        {
            "ANTHROPIC_API_KEY": "sk-ant-demo",
            "OPENAI_API_KEY": "sk-openai-demo",
            "GEMINI_API_KEY": "sk-gemini-demo",
        },
        clear=False,
    ), mock.patch("pdd.cli_detector.shutil.which", side_effect=fake_paths.get):
        detect_cli_tools()


def main() -> None:
    """Print a complete, non-interactive cli_detector usage example."""

    print("Primary pdd setup bootstrap flow")
    results = run_bootstrap_demo()
    print()
    print("Returned results")
    for result in results:
        print(result)

    print()
    print("Legacy detection flow")
    run_legacy_demo()


if __name__ == "__main__":
    main()
