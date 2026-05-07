"""Tests for pdd.cli_detector.

Test plan
---------
1. Dataclass contract: defaults, skipped result, populated result, return shape.
2. Public constants: provider key/display mappings, CLI preference order, shell
   RC map, provider/CLI package forwarding, and OpenCode package configuration.
3. Banner and table: detect_and_bootstrap_cli calls the imported banner and
   prints Claude, Codex, Gemini, OpenCode in the required numbered order.
4. CLI discovery: shutil.which wins; ~/.local/bin, /usr/local/bin,
   /opt/homebrew/bin, and nvm node version bins are checked as fallbacks.
5. Selection parsing: comma-separated input, whitespace, deduplication, q/n skip,
   invalid fallback, and default installed+key > installed > Claude.
6. Install branch coverage: installed CLIs skip npm; missing CLIs prompt; npm
   availability is checked; npm install receives each exact package; decline,
   npm-missing, install-failure, and post-install binary-missing branches skip
   only the current CLI and continue to later selections.
7. API key existing branches: Anthropic/OpenAI/Google key detection skips prompts;
   Google displays GEMINI_API_KEY before GOOGLE_API_KEY; OpenCode accepts any
   supported provider key or auth.json without prompting.
8. API key write branches: new Anthropic/OpenAI/Google keys are saved to the
   primary env var, update os.environ, and use the selected shell file.
9. OpenCode no-auth branches: the user can decline and is pointed to
   opencode auth login, or can choose a supported provider key by number/name.
10. Shell persistence: bash, zsh, and fish output syntax and RC source syntax
    match the spec.
11. Deduplication: repeated saves replace old lines for the same key and add the
    RC source line only once.
12. CLI verification: --version runs first, --help is fallback, and the no-binary
    branch is still reached after install skip/failure.
13. Prompt interruption: KeyboardInterrupt and EOFError at selection, install,
    and key prompts return graceful skipped or partial results.
14. Legacy detection: all four CLIs report found/not-found and key status.
15. Legacy installation: missing CLIs offer npm install only when a matching
    provider key or OpenCode auth source is present.
16. Parameter forwarding: subprocess receives npm install -g package, CLI
    --version/--help commands, and direct dependency patches receive expected
    command names.
17. Error cases: q/n selection and empty result paths return
    [CliBootstrapResult(skipped=True)] or per-CLI skipped results as appropriate.
18. Regression checks: dynamic HOME fallback discovery, OpenCode auth file
    discovery, unquoted API env syntax, and selection-interrupt skip behavior.
"""

from __future__ import annotations

import os
from pathlib import Path
from subprocess import CompletedProcess
from unittest import mock

import pytest

import pdd.cli_detector as cli_detector
from pdd.cli_detector import (
    CLI_PREFERENCE,
    PROVIDER_DISPLAY,
    PROVIDER_PRIMARY_KEY,
    SHELL_RC_MAP,
    CliBootstrapResult,
    detect_and_bootstrap_cli,
    detect_cli_tools,
)


ALL_CLI_PATHS = {
    "claude": "/mock/bin/claude",
    "codex": "/mock/bin/codex",
    "gemini": "/mock/bin/gemini",
    "opencode": "/mock/bin/opencode",
}

ALL_KEYS = {
    "ANTHROPIC_API_KEY": "sk-ant-test",
    "OPENAI_API_KEY": "sk-openai-test",
    "GEMINI_API_KEY": "sk-gemini-test",
}

ENV_KEYS = [
    "ANTHROPIC_API_KEY",
    "OPENAI_API_KEY",
    "GEMINI_API_KEY",
    "GOOGLE_API_KEY",
    "OPENROUTER_API_KEY",
    "GITHUB_TOKEN",
    "GROQ_API_KEY",
]


def _prepare_home(monkeypatch: pytest.MonkeyPatch, tmp_path: Path, shell: str = "/bin/bash") -> None:
    monkeypatch.setenv("HOME", str(tmp_path))
    monkeypatch.setenv("SHELL", shell)
    monkeypatch.setattr(cli_detector.Path, "home", staticmethod(lambda: tmp_path))
    if shell.endswith("fish"):
        rc_file = tmp_path / ".config" / "fish" / "config.fish"
    elif shell.endswith("zsh"):
        rc_file = tmp_path / ".zshrc"
    else:
        rc_file = tmp_path / ".bashrc"
    rc_file.parent.mkdir(parents=True, exist_ok=True)
    rc_file.write_text("# existing rc\n")


def _clear_keys(monkeypatch: pytest.MonkeyPatch) -> None:
    for key in ENV_KEYS:
        monkeypatch.delenv(key, raising=False)


def _run_bootstrap_capture(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    inputs: list[str | BaseException],
    *,
    cli_paths: dict[str, str] | None = None,
    env_keys: dict[str, str] | None = None,
    shell: str = "/bin/bash",
    npm_available: bool = False,
    install_succeeds: bool = False,
    install_then_found: dict[str, str] | None = None,
    version_returncode: int = 0,
    version_output: str = "cli 1.0.0",
    help_returncode: int = 0,
    help_output: str = "usage: cli",
) -> tuple[str, list[CliBootstrapResult], list[list[str]]]:
    cli_paths = dict(cli_paths or {})
    env_keys = dict(env_keys or {})
    install_then_found = dict(install_then_found or {})
    _clear_keys(monkeypatch)
    _prepare_home(monkeypatch, tmp_path, shell)
    for key, value in env_keys.items():
        monkeypatch.setenv(key, value)

    input_iter = iter(inputs)

    def fake_input(_prompt: str = "") -> str:
        try:
            value = next(input_iter)
        except StopIteration as exc:
            raise AssertionError("Unexpected input prompt") from exc
        if isinstance(value, BaseException):
            raise value
        return value

    which_calls: dict[str, int] = {}

    def fake_which(command: str) -> str | None:
        which_calls[command] = which_calls.get(command, 0) + 1
        if command == "npm":
            return "/mock/bin/npm" if npm_available else None
        if command in cli_paths:
            return cli_paths[command]
        if command in install_then_found and which_calls[command] > 1 and install_succeeds:
            return install_then_found[command]
        return None

    subprocess_calls: list[list[str]] = []

    def fake_run(command: list[str], **_: object) -> CompletedProcess[str]:
        subprocess_calls.append(command)
        if command[:3] == ["npm", "install", "-g"]:
            return CompletedProcess(command, 0 if install_succeeds else 1, "", "")
        if command[-1] == "--version":
            return CompletedProcess(command, version_returncode, version_output, "")
        return CompletedProcess(command, help_returncode, help_output, "")

    printed: list[str] = []

    def capture_print(*args: object, **_: object) -> None:
        printed.append(" ".join(str(arg) for arg in args))

    monkeypatch.setattr("builtins.input", fake_input)
    monkeypatch.setattr(cli_detector.shutil, "which", fake_which)
    monkeypatch.setattr(cli_detector.subprocess, "run", fake_run)
    monkeypatch.setattr(cli_detector, "console", mock.Mock(print=capture_print))
    monkeypatch.setattr(cli_detector, "_print_step_banner", lambda title: printed.append(f"BANNER:{title}"))

    results = detect_and_bootstrap_cli()
    return "\n".join(printed), results, subprocess_calls


def _run_legacy_capture(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    inputs: list[str] | None = None,
    *,
    cli_paths: dict[str, str] | None = None,
    env_keys: dict[str, str] | None = None,
    npm_available: bool = True,
    install_succeeds: bool = True,
) -> tuple[str, list[list[str]]]:
    cli_paths = dict(cli_paths or {})
    env_keys = dict(env_keys or {})
    _clear_keys(monkeypatch)
    _prepare_home(monkeypatch, tmp_path)
    for key, value in env_keys.items():
        monkeypatch.setenv(key, value)

    input_iter = iter(inputs or [])

    def fake_input(_prompt: str = "") -> str:
        return next(input_iter, "n")

    def fake_which(command: str) -> str | None:
        if command == "npm":
            return "/mock/bin/npm" if npm_available else None
        return cli_paths.get(command)

    subprocess_calls: list[list[str]] = []

    def fake_run(command: list[str], **_: object) -> CompletedProcess[str]:
        subprocess_calls.append(command)
        return CompletedProcess(command, 0 if install_succeeds else 1, "", "")

    printed: list[str] = []

    def capture_print(*args: object, **_: object) -> None:
        printed.append(" ".join(str(arg) for arg in args))

    monkeypatch.setattr("builtins.input", fake_input)
    monkeypatch.setattr(cli_detector.shutil, "which", fake_which)
    monkeypatch.setattr(cli_detector.subprocess, "run", fake_run)
    monkeypatch.setattr(cli_detector, "console", mock.Mock(print=capture_print))

    detect_cli_tools()
    return "\n".join(printed), subprocess_calls


class TestCliBootstrapResult:
    def test_defaults_to_empty_values(self) -> None:
        result = CliBootstrapResult()
        assert result.cli_name == ""
        assert result.provider == ""
        assert result.cli_path == ""
        assert result.api_key_configured is False
        assert result.skipped is False

    def test_skipped_result_preserves_defaults(self) -> None:
        result = CliBootstrapResult(skipped=True)
        assert result.skipped is True
        assert result.cli_name == ""
        assert result.provider == ""

    def test_populated_result(self) -> None:
        result = CliBootstrapResult("claude", "anthropic", "/mock/bin/claude", True)
        assert result.cli_name == "claude"
        assert result.provider == "anthropic"
        assert result.cli_path == "/mock/bin/claude"
        assert result.api_key_configured is True
        assert result.skipped is False


class TestConstants:
    def test_provider_constants_include_opencode(self) -> None:
        assert PROVIDER_PRIMARY_KEY["anthropic"] == "ANTHROPIC_API_KEY"
        assert PROVIDER_PRIMARY_KEY["openai"] == "OPENAI_API_KEY"
        assert PROVIDER_PRIMARY_KEY["google"] == "GEMINI_API_KEY"
        assert PROVIDER_PRIMARY_KEY["opencode"] is None
        assert PROVIDER_DISPLAY["opencode"] == "OpenCode CLI"
        assert CLI_PREFERENCE == ["claude", "codex", "gemini", "opencode"]
        assert SHELL_RC_MAP["fish"] == "~/.config/fish/config.fish"

    def test_opencode_npm_package_is_opencode_ai(self) -> None:
        assert cli_detector._CLI_NPM_PACKAGE["opencode"] == "opencode-ai"


class TestCliDetection:
    def test_table_shows_all_four_clis_in_spec_order(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        output, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["q"],
            cli_paths=ALL_CLI_PATHS,
            env_keys=ALL_KEYS,
        )
        assert "BANNER:Step: Detect & bootstrap agentic CLI" in output
        assert output.index("Claude CLI") < output.index("Codex CLI") < output.index("Gemini CLI") < output.index("OpenCode CLI")
        assert results == [CliBootstrapResult(skipped=True)]

    def test_find_cli_uses_shutil_which_first(self, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setattr(cli_detector.shutil, "which", lambda command: f"/which/{command}")
        assert cli_detector._find_cli("claude") == "/which/claude"

    def test_find_cli_uses_local_bin_fallback(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _prepare_home(monkeypatch, tmp_path)
        monkeypatch.setattr(cli_detector.shutil, "which", lambda _command: None)
        binary = tmp_path / ".local" / "bin" / "codex"
        binary.parent.mkdir(parents=True)
        binary.write_text("#!/bin/sh\n")
        binary.chmod(0o755)
        assert cli_detector._find_cli("codex") == str(binary)

    def test_find_cli_uses_nvm_version_fallback(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _prepare_home(monkeypatch, tmp_path)
        monkeypatch.setattr(cli_detector.shutil, "which", lambda _command: None)
        binary = tmp_path / ".nvm" / "versions" / "node" / "v22.0.0" / "bin" / "gemini"
        binary.parent.mkdir(parents=True)
        binary.write_text("#!/bin/sh\n")
        binary.chmod(0o755)
        assert cli_detector._find_cli("gemini") == str(binary)


class TestBootstrapSelection:
    def test_select_single_cli(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["1"],
            cli_paths=ALL_CLI_PATHS,
            env_keys=ALL_KEYS,
        )
        assert [result.cli_name for result in results] == ["claude"]
        assert results[0].provider == "anthropic"
        assert results[0].api_key_configured is True

    def test_multi_select_with_spaces_and_deduplication(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["1, 1, 3"],
            cli_paths=ALL_CLI_PATHS,
            env_keys=ALL_KEYS,
        )
        assert [result.cli_name for result in results] == ["claude", "gemini"]

    def test_empty_input_defaults_to_installed_with_key_by_preference(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            [""],
            cli_paths={"gemini": "/mock/bin/gemini", "codex": "/mock/bin/codex"},
            env_keys={"GEMINI_API_KEY": "gm-test"},
        )
        assert [result.cli_name for result in results] == ["gemini"]

    def test_empty_input_defaults_to_installed_without_key(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["", "n"],
            cli_paths={"codex": "/mock/bin/codex"},
        )
        assert [result.cli_name for result in results] == ["codex"]
        assert results[0].api_key_configured is False

    def test_empty_input_defaults_to_claude_when_nothing_available(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        output, results, _ = _run_bootstrap_capture(monkeypatch, tmp_path, ["", "n"])
        assert [result.cli_name for result in results] == ["claude"]
        assert results[0].skipped is True
        assert "Cannot test Claude CLI" in output

    def test_invalid_input_defaults_to_default(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        output, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["invalid"],
            cli_paths={"claude": "/mock/bin/claude"},
            env_keys={"ANTHROPIC_API_KEY": "sk-ant-test"},
        )
        assert "Defaulting to 1" in output
        assert [result.cli_name for result in results] == ["claude"]

    @pytest.mark.parametrize("selection", ["q", "n"])
    def test_q_or_n_returns_skipped(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path, selection: str) -> None:
        _, results, _ = _run_bootstrap_capture(monkeypatch, tmp_path, [selection])
        assert results == [CliBootstrapResult(skipped=True)]


class TestInstallFlow:
    def test_installed_cli_skips_npm_install(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _, results, calls = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["1"],
            cli_paths={"claude": "/mock/bin/claude"},
            env_keys={"ANTHROPIC_API_KEY": "sk-ant-test"},
        )
        assert results[0].cli_path == "/mock/bin/claude"
        assert ["npm", "install", "-g", "@anthropic-ai/claude-code"] not in calls

    def test_missing_cli_installs_with_npm_package(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _, results, calls = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["4", "y", "n"],
            npm_available=True,
            install_succeeds=True,
            install_then_found={"opencode": "/mock/bin/opencode"},
        )
        assert ["npm", "install", "-g", "opencode-ai"] in calls
        assert results[0].cli_name == "opencode"
        assert results[0].cli_path == "/mock/bin/opencode"
        assert results[0].api_key_configured is False

    def test_npm_missing_marks_current_cli_skipped(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        output, results, calls = _run_bootstrap_capture(monkeypatch, tmp_path, ["1", "y"])
        assert results[0].skipped is True
        assert "npm is not installed" in output
        assert not calls
        assert "Cannot test Claude CLI" in output

    def test_install_failure_continues_to_later_selection(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _, results, calls = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["1,2", "y"],
            cli_paths={"codex": "/mock/bin/codex"},
            env_keys={"OPENAI_API_KEY": "sk-openai-test"},
            npm_available=True,
            install_succeeds=False,
        )
        assert ["npm", "install", "-g", "@anthropic-ai/claude-code"] in calls
        assert [result.cli_name for result in results] == ["claude", "codex"]
        assert results[0].skipped is True
        assert results[1].skipped is False

    def test_user_declines_install_marks_skipped(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        output, results, _ = _run_bootstrap_capture(monkeypatch, tmp_path, ["1", "n"])
        assert results[0].skipped is True
        assert "Skipping Claude CLI" in output
        assert "Cannot test Claude CLI" in output

    def test_install_success_but_binary_not_found_is_skipped(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        output, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["1", "y"],
            npm_available=True,
            install_succeeds=True,
        )
        assert results[0].skipped is True
        assert "not found on PATH" in output


class TestApiKeyFlow:
    def test_existing_key_skips_key_prompt(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        output, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["1"],
            cli_paths={"claude": "/mock/bin/claude"},
            env_keys={"ANTHROPIC_API_KEY": "sk-ant-test"},
        )
        assert results[0].api_key_configured is True
        assert "ANTHROPIC_API_KEY is set" in output

    def test_new_key_is_saved_to_env_file_and_process_env(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["1", "y", "sk-new-key"],
            cli_paths={"claude": "/mock/bin/claude"},
        )
        assert results[0].api_key_configured is True
        assert os.environ["ANTHROPIC_API_KEY"] == "sk-new-key"
        assert (tmp_path / ".pdd" / "api-env.bash").read_text() == "export ANTHROPIC_API_KEY=sk-new-key\n"
        assert f"source {tmp_path / '.pdd' / 'api-env.bash'}" in (tmp_path / ".bashrc").read_text()

    def test_user_declines_key_configuration(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["2", "n"],
            cli_paths={"codex": "/mock/bin/codex"},
        )
        assert results[0].api_key_configured is False

    def test_google_prefers_gemini_key_over_google_key(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        output, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["3"],
            cli_paths={"gemini": "/mock/bin/gemini"},
            env_keys={"GOOGLE_API_KEY": "google-test", "GEMINI_API_KEY": "gemini-test"},
        )
        assert results[0].api_key_configured is True
        assert "GEMINI_API_KEY is set" in output

    def test_google_falls_back_to_google_api_key_display(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        output, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["3"],
            cli_paths={"gemini": "/mock/bin/gemini"},
            env_keys={"GOOGLE_API_KEY": "google-test"},
        )
        assert results[0].api_key_configured is True
        assert "GOOGLE_API_KEY is set" in output

    def test_google_saves_primary_gemini_key(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["3", "y", "gemini-new"],
            cli_paths={"gemini": "/mock/bin/gemini"},
        )
        assert results[0].api_key_configured is True
        assert (tmp_path / ".pdd" / "api-env.bash").read_text() == "export GEMINI_API_KEY=gemini-new\n"

    def test_opencode_accepts_any_provider_key(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        output, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["4"],
            cli_paths={"opencode": "/mock/bin/opencode"},
            env_keys={"GROQ_API_KEY": "groq-test"},
        )
        assert results[0].api_key_configured is True
        assert "GROQ_API_KEY" in output

    def test_opencode_accepts_auth_file(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        auth_file = tmp_path / ".local" / "share" / "opencode" / "auth.json"
        auth_file.parent.mkdir(parents=True)
        auth_file.write_text("{}")
        output, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["4"],
            cli_paths={"opencode": "/mock/bin/opencode"},
        )
        assert results[0].api_key_configured is True
        assert "auth file" in output

    def test_opencode_can_save_chosen_provider_key(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["4", "y", "2", "sk-ant-opencode"],
            cli_paths={"opencode": "/mock/bin/opencode"},
        )
        assert results[0].api_key_configured is True
        assert os.environ["ANTHROPIC_API_KEY"] == "sk-ant-opencode"
        assert (tmp_path / ".pdd" / "api-env.bash").read_text() == "export ANTHROPIC_API_KEY=sk-ant-opencode\n"

    def test_opencode_decline_mentions_auth_login(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        output, results, _ = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["4", "n"],
            cli_paths={"opencode": "/mock/bin/opencode"},
        )
        assert results[0].api_key_configured is False
        assert "opencode auth login" in output


class TestApiKeyPersistence:
    def test_zsh_uses_zshrc_and_export_syntax(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["1", "y", "sk-zsh"],
            cli_paths={"claude": "/mock/bin/claude"},
            shell="/bin/zsh",
        )
        assert (tmp_path / ".pdd" / "api-env.zsh").read_text() == "export ANTHROPIC_API_KEY=sk-zsh\n"
        assert f"source {tmp_path / '.pdd' / 'api-env.zsh'}" in (tmp_path / ".zshrc").read_text()

    def test_fish_uses_set_gx_and_fish_source_line(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["1", "y", "sk-fish"],
            cli_paths={"claude": "/mock/bin/claude"},
            shell="/usr/bin/fish",
        )
        assert (tmp_path / ".pdd" / "api-env.fish").read_text() == "set -gx ANTHROPIC_API_KEY sk-fish\n"
        rc_text = (tmp_path / ".config" / "fish" / "config.fish").read_text()
        assert f"test -f {tmp_path / '.pdd' / 'api-env.fish'} ; and source {tmp_path / '.pdd' / 'api-env.fish'}" in rc_text

    def test_duplicate_key_lines_are_deduplicated(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _run_bootstrap_capture(monkeypatch, tmp_path, ["1", "y", "sk-first"], cli_paths={"claude": "/mock/bin/claude"})
        monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
        _run_bootstrap_capture(monkeypatch, tmp_path, ["1", "y", "sk-second"], cli_paths={"claude": "/mock/bin/claude"})
        lines = (tmp_path / ".pdd" / "api-env.bash").read_text().splitlines()
        assert lines == ["export ANTHROPIC_API_KEY=sk-second"]
        assert (tmp_path / ".bashrc").read_text().count("source ") == 1


class TestCliVerification:
    def test_version_success_is_reported(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        output, _, calls = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["1"],
            cli_paths={"claude": "/mock/bin/claude"},
            env_keys={"ANTHROPIC_API_KEY": "sk-ant-test"},
            version_output="claude 2.5.0",
        )
        assert ["/mock/bin/claude", "--version"] in calls
        assert "claude 2.5.0" in output

    def test_help_is_used_when_version_fails(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        output, _, calls = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["2"],
            cli_paths={"codex": "/mock/bin/codex"},
            env_keys={"OPENAI_API_KEY": "sk-openai-test"},
            version_returncode=1,
            help_output="codex help",
        )
        assert ["/mock/bin/codex", "--version"] in calls
        assert ["/mock/bin/codex", "--help"] in calls
        assert "codex help" in output


class TestInterruptHandling:
    @pytest.mark.parametrize("error", [KeyboardInterrupt(), EOFError()])
    def test_selection_interrupt_returns_skipped(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path, error: BaseException) -> None:
        _, results, _ = _run_bootstrap_capture(monkeypatch, tmp_path, [error])
        assert results == [CliBootstrapResult(skipped=True)]

    def test_eof_during_key_prompt_is_graceful(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _, results, calls = _run_bootstrap_capture(
            monkeypatch,
            tmp_path,
            ["1", "y", EOFError()],
            cli_paths={"claude": "/mock/bin/claude"},
        )
        assert results[0].api_key_configured is False
        assert ["/mock/bin/claude", "--version"] in calls


class TestDetectCliToolsLegacy:
    def test_reports_all_four_clis_and_key_status(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        output, _ = _run_legacy_capture(
            monkeypatch,
            tmp_path,
            cli_paths=ALL_CLI_PATHS,
            env_keys=ALL_KEYS,
        )
        assert "Detecting agentic CLI tools" in output
        for display in ("Claude CLI", "Codex CLI", "Gemini CLI", "OpenCode CLI"):
            assert display in output
        assert "ANTHROPIC_API_KEY is set" in output
        assert "GEMINI_API_KEY is set" in output
        assert "OpenCode auth via OPENAI_API_KEY" in output

    def test_missing_cli_with_matching_key_offers_install(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        output, calls = _run_legacy_capture(
            monkeypatch,
            tmp_path,
            ["y"],
            env_keys={"OPENAI_API_KEY": "sk-openai-test"},
        )
        assert "Codex CLI not found" in output
        assert ["npm", "install", "-g", "@openai/codex"] in calls

    def test_missing_cli_without_key_does_not_install(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        output, calls = _run_legacy_capture(monkeypatch, tmp_path, inputs=["y"])
        assert "Claude CLI not found" in output
        assert "ANTHROPIC_API_KEY not set" in output
        assert calls == []

    def test_opencode_missing_with_provider_key_installs_opencode_ai(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        _, calls = _run_legacy_capture(
            monkeypatch,
            tmp_path,
            ["y"],
            env_keys={"GITHUB_TOKEN": "ghp-test"},
        )
        assert ["npm", "install", "-g", "opencode-ai"] in calls
