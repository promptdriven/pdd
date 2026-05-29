"""Tests for ``pdd checkup simplify`` (Claude Code /simplify)."""
from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.checkup_file_selection import discover_simplify_targets, resolve_simplify_repo_root
from pdd.checkup_simplify import (
    SimplifyVerifyCommands,
    _build_simplify_slash_message,
    _build_verify_command,
    _guess_pytest_targets,
    _parse_claude_code_version,
    _run_verification,
    check_claude_code_simplify_available,
    run_checkup_simplify,
)
from pdd.commands.checkup import checkup


def _init_git_repo(root: Path) -> None:
    subprocess.run(["git", "init"], cwd=root, check=True, capture_output=True)
    subprocess.run(
        ["git", "config", "user.email", "test@example.com"],
        cwd=root,
        check=True,
        capture_output=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Test"],
        cwd=root,
        check=True,
        capture_output=True,
    )


def test_parse_claude_code_version() -> None:
    assert _parse_claude_code_version("2.1.63 (Claude Code)") == (2, 1, 63)
    assert _parse_claude_code_version("no version") is None


def test_version_probe_accepts_installed_version(monkeypatch) -> None:
    def fake_run(cmd, **kwargs):
        class Result:
            stdout = "1.0.35 (Claude Code)\n"
            stderr = ""

        return Result()

    with patch("pdd.checkup_simplify_claude._find_cli_binary", return_value="/bin/claude"):
        with patch("pdd.checkup_simplify_claude.subprocess.run", side_effect=fake_run):
            path, version, err = check_claude_code_simplify_available(quiet=True)

    assert path == "/bin/claude"
    assert version == (1, 0, 35)
    assert err is None


def test_version_probe_does_not_reject_newer_claude(monkeypatch) -> None:
    def fake_run(cmd, **kwargs):
        class Result:
            stdout = "2.1.200 (Claude Code)\n"
            stderr = ""

        return Result()

    with patch("pdd.checkup_simplify_claude._find_cli_binary", return_value="/bin/claude"):
        with patch("pdd.checkup_simplify_claude.subprocess.run", side_effect=fake_run):
            path, version, err = check_claude_code_simplify_available(quiet=True)

    assert path == "/bin/claude"
    assert version == (2, 1, 200)
    assert err is None


def test_version_gate_accepts_supported(monkeypatch) -> None:
    monkeypatch.delenv("PDD_SKIP_CLAUDE_SIMPLIFY_VERSION_CHECK", raising=False)

    def fake_run(cmd, **kwargs):
        class Result:
            stdout = "2.1.100 (Claude Code)\n"
            stderr = ""

        return Result()

    with patch("pdd.checkup_simplify_claude._find_cli_binary", return_value="/bin/claude"):
        with patch("pdd.checkup_simplify_claude.subprocess.run", side_effect=fake_run):
            path, version, err = check_claude_code_simplify_available(quiet=True)

    assert path == "/bin/claude"
    assert version == (2, 1, 100)
    assert err is None


def test_build_simplify_slash_message() -> None:
    msg = _build_simplify_slash_message(
        ["pdd/foo.py", "pdd/bar.py"],
        focus="focus on error handling",
    )
    assert msg.startswith("/simplify focus on error handling")
    assert "pdd/foo.py" in msg
    assert "pdd/bar.py" in msg


def test_discover_simplify_targets_since_ref(tmp_path: Path) -> None:
    _init_git_repo(tmp_path)
    src = tmp_path / "pdd"
    src.mkdir()
    target = src / "widget.py"
    target.write_text("def run():\n    return 1\n", encoding="utf-8")
    subprocess.run(["git", "add", "pdd/widget.py"], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "add widget"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
    )
    target.write_text("def run():\n    return 2\n", encoding="utf-8")

    _, files = discover_simplify_targets(since="HEAD", cwd=tmp_path, max_files=10)
    rel = [f.name for f in files]
    assert "widget.py" in rel


def test_discover_simplify_targets_staged(tmp_path: Path) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "pdd" / "staged.py"
    module.parent.mkdir(parents=True)
    module.write_text("x = 1\n", encoding="utf-8")
    subprocess.run(["git", "add", "pdd/staged.py"], cwd=tmp_path, check=True, capture_output=True)

    _, files = discover_simplify_targets(staged=True, cwd=tmp_path, max_files=10)
    assert any(f.name == "staged.py" for f in files)


def test_discover_defaults_to_local_changed_files(tmp_path: Path) -> None:
    _init_git_repo(tmp_path)
    src = tmp_path / "pdd"
    src.mkdir()
    changed = src / "changed.py"
    untouched = src / "untouched.py"
    changed.write_text("x = 1\n", encoding="utf-8")
    untouched.write_text("y = 1\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-m", "init"], cwd=tmp_path, check=True, capture_output=True)
    changed.write_text("x = 2\n", encoding="utf-8")

    _, files = discover_simplify_targets(cwd=tmp_path, max_files=10)

    assert [path.name for path in files] == ["changed.py"]


def test_discover_since_and_staged_mutually_exclusive(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="mutually exclusive"):
        discover_simplify_targets(since="HEAD~1", staged=True, cwd=tmp_path)


def test_auto_preview_does_not_resolve_engine(tmp_path: Path, monkeypatch) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "pdd" / "auto_preview.py"
    module.parent.mkdir(parents=True)
    module.write_text("def value():\n    return 1\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "init"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
    )
    monkeypatch.chdir(tmp_path)

    def forbid_resolve(*_args, **_kwargs):
        raise AssertionError("resolve_simplify_engine must not run in preview mode")

    preview_patches = (
        patch(
            "pdd.checkup_simplify_engines.check_claude_code_simplify_available",
            return_value=(None, None, "missing"),
        ),
        patch("pdd.checkup_simplify_engines.get_available_agents", return_value=[]),
        patch("pdd.checkup_simplify.resolve_simplify_engine", side_effect=forbid_resolve),
    )

    with preview_patches[0], preview_patches[1], preview_patches[2], patch(
        "pdd.checkup_simplify.discover_simplify_targets",
        return_value=(tmp_path, []),
    ):
        no_targets = run_checkup_simplify(
            path=None,
            apply=False,
            since=None,
            staged=False,
            max_files=5,
            attempts=None,
            engine="auto",
            evidence=False,
            verify=False,
            no_format=False,
            quiet=True,
            verbose=False,
        )

    assert no_targets.success is True
    assert no_targets.exit_code == 0
    assert no_targets.files_analyzed == []
    assert "auto" in "\n".join(no_targets.summary_lines).lower()
    assert "Preview only" in "\n".join(no_targets.summary_lines)

    module.write_text("def value():\n    return 2\n", encoding="utf-8")
    with preview_patches[0], preview_patches[1], preview_patches[2]:
        preview = run_checkup_simplify(
            path=module,
            apply=False,
            since=None,
            staged=False,
            max_files=5,
            attempts=None,
            engine="auto",
            evidence=False,
            verify=False,
            no_format=False,
            quiet=True,
            verbose=False,
        )

    assert preview.success is True
    assert preview.files_analyzed
    assert "Preview only" in "\n".join(preview.summary_lines)


def test_preview_without_apply_does_not_invoke_claude(tmp_path: Path, monkeypatch) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "pdd" / "sample.py"
    module.parent.mkdir(parents=True)
    original = "def value():\n    return 42\n"
    module.write_text(original, encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "init"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
    )
    monkeypatch.chdir(tmp_path)

    with patch("pdd.checkup_simplify.run_simplify_engine_command") as mock_run, patch(
        "pdd.checkup_simplify.check_simplify_engine_available"
    ) as mock_probe:
        result = run_checkup_simplify(
            path=module,
            apply=False,
            since=None,
            staged=False,
            max_files=5,
            attempts=None,
            engine=None,
            evidence=False,
            verify=False,
            no_format=False,
            quiet=True,
            verbose=False,
        )

    mock_run.assert_not_called()
    mock_probe.assert_not_called()
    assert module.read_text(encoding="utf-8") == original
    assert result.files_modified == []
    assert "Preview only" in "\n".join(result.summary_lines)


def test_apply_invokes_claude_simplify(tmp_path: Path, monkeypatch) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "pdd" / "apply_me.py"
    module.parent.mkdir(parents=True)
    module.write_text("def before():\n    return 1\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "init"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
    )
    module.write_text("def after():\n    return 2\n", encoding="utf-8")
    monkeypatch.chdir(tmp_path)

    captured: dict[str, str] = {}

    def fake_simplify(_engine, _rel_files, repo_root, **kwargs):
        captured["cwd"] = str(repo_root)
        (repo_root / "pdd" / "apply_me.py").write_text(
            "def simplified():\n    return 2\n",
            encoding="utf-8",
        )
        return True, "Simplified 1 file.", 0.5, "Simplified 1 file."

    with patch("pdd.checkup_simplify.run_simplify_engine_command", side_effect=fake_simplify):
        with patch(
            "pdd.checkup_simplify.check_simplify_engine_available",
            return_value=("2.1.100", "claude", None),
        ):
            result = run_checkup_simplify(
                path=module,
                apply=True,
                since=None,
                staged=False,
                max_files=5,
                attempts=1,
                engine=None,
                evidence=True,
                verify=False,
                no_format=True,
                quiet=True,
                verbose=False,
            )

    assert result.slash_command.startswith("/simplify")
    assert "pdd/apply_me.py" in result.slash_command
    assert "pdd/apply_me.py" in result.files_modified
    assert result.evidence_path is not None
    payload = json.loads(result.evidence_path.read_text(encoding="utf-8"))
    assert payload["engine"] == "claude-code/simplify"
    assert payload["slash_command"].startswith("/simplify")


def test_checkup_cli_dispatches_simplify_preview(tmp_path: Path, monkeypatch) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "pdd" / "cli_sample.py"
    module.parent.mkdir(parents=True)
    module.write_text("def ok():\n    return True\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "init"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
    )
    monkeypatch.chdir(tmp_path)

    with patch("pdd.checkup_simplify.run_simplify_engine_command") as mock_run:
        with patch(
            "pdd.checkup_simplify.check_simplify_engine_available",
            return_value=("2.1.100", "claude", None),
        ):
            result = CliRunner().invoke(
                checkup,
                ["simplify", str(module)],
                obj={"quiet": False, "verbose": False},
            )

    mock_run.assert_not_called()
    assert result.exit_code == 0
    assert "PDD Checkup: simplify" in result.output


def test_checkup_simplify_help_is_forwarded_to_nested_command() -> None:
    result = CliRunner().invoke(checkup, ["simplify", "--help"])

    assert result.exit_code == 0
    assert "--attempts" in result.output
    assert "--engine" in result.output
    assert "Independent /simplify candidates" in result.output


def test_apply_codex_engine_writes_evidence(tmp_path: Path, monkeypatch) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "pdd" / "codex_target.py"
    module.parent.mkdir(parents=True)
    module.write_text("def before():\n    return 1\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "init"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
    )
    module.write_text("def after():\n    return 2\n", encoding="utf-8")
    monkeypatch.chdir(tmp_path)

    def fake_simplify(engine, _rel_files, repo_root, **kwargs):
        assert engine == "codex"
        (repo_root / "pdd" / "codex_target.py").write_text(
            "def simplified():\n    return 2\n",
            encoding="utf-8",
        )
        return True, "agentic simplify", 0.3, "openai"

    with patch("pdd.checkup_simplify.run_simplify_engine_command", side_effect=fake_simplify):
        with patch(
            "pdd.checkup_simplify.check_simplify_engine_available",
            return_value=("codex-cli", "openai", None),
        ):
            result = run_checkup_simplify(
                path=module,
                apply=True,
                since=None,
                staged=False,
                max_files=5,
                attempts=1,
                engine="codex",
                evidence=True,
                verify=False,
                no_format=True,
                quiet=True,
                verbose=False,
            )

    assert result.provider == "openai"
    assert result.evidence_path is not None
    payload = json.loads(result.evidence_path.read_text(encoding="utf-8"))
    assert payload["engine"] == "openai-codex/simplify"


def test_apply_and_verify_flags(tmp_path: Path, monkeypatch) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "pdd" / "apply_me.py"
    module.parent.mkdir(parents=True)
    module.write_text("def before():\n    return 1\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "init"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
    )
    module.write_text("def changed():\n    return 1\n", encoding="utf-8")
    monkeypatch.chdir(tmp_path)

    verify_calls: list[str] = []

    def fake_verify(**kwargs):
        verify_calls.append("ran")
        return {"format": "passed", "lint": "passed", "tests": "passed"}

    def fake_simplify(_engine, _rel_files, repo_root, **kwargs):
        (repo_root / "pdd" / "apply_me.py").write_text(
            "def changed():\n    return 2\n",
            encoding="utf-8",
        )
        return True, "done", 0.2, "claude"

    with patch("pdd.checkup_simplify.run_simplify_engine_command", side_effect=fake_simplify):
        with patch(
            "pdd.checkup_simplify.check_simplify_engine_available",
            return_value=("2.1.100", "claude", None),
        ):
            with patch("pdd.checkup_simplify._run_verification", side_effect=fake_verify):
                result = run_checkup_simplify(
                    path=module,
                    apply=True,
                    since=None,
                    staged=False,
                    max_files=5,
                    attempts=1,
                    engine=None,
                    evidence=False,
                    verify=True,
                    no_format=True,
                    quiet=True,
                    verbose=False,
                )

    assert verify_calls == ["ran"]
    assert "pdd/apply_me.py" in result.files_modified


def test_apply_attempts_selects_verified_candidate(
    tmp_path: Path, monkeypatch
) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "pdd" / "candidate.py"
    module.parent.mkdir(parents=True)
    module.write_text("def value():\n    return 0\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-m", "init"], cwd=tmp_path, check=True, capture_output=True)
    module.write_text("def value():\n    return 1\n", encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    seen = 0

    def fake_simplify(_engine, _rel_files, repo_root, **_kwargs):
        nonlocal seen
        seen += 1
        value = 20 if seen == 1 else 10
        (repo_root / "pdd" / "candidate.py").write_text(
            f"def value():\n    return {value}\n",
            encoding="utf-8",
        )
        return True, f"candidate {seen}", 0.1, f"candidate {seen}"

    def fake_verify(**kwargs):
        content = (kwargs["repo_root"] / "pdd" / "candidate.py").read_text()
        return {"tests": "failed" if "20" in content else "passed"}

    with patch("pdd.checkup_simplify.run_simplify_engine_command", side_effect=fake_simplify), patch(
        "pdd.checkup_simplify.check_simplify_engine_available",
        return_value=("2.1.200", "claude", None),
    ), patch("pdd.checkup_simplify._run_verification", side_effect=fake_verify):
        result = run_checkup_simplify(
            path=module,
            apply=True,
            since=None,
            staged=False,
            max_files=5,
            attempts=2,
            engine=None,
            evidence=True,
            verify=True,
            no_format=True,
            quiet=True,
            verbose=False,
        )

    assert result.selected_attempt == 2
    assert "return 10" in module.read_text(encoding="utf-8")


def test_apply_rejects_out_of_scope_candidate_edits(tmp_path: Path, monkeypatch) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "pdd" / "selected.py"
    other = tmp_path / "pdd" / "other.py"
    module.parent.mkdir(parents=True)
    module.write_text("value = 1\n", encoding="utf-8")
    other.write_text("other = 1\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-m", "init"], cwd=tmp_path, check=True, capture_output=True)
    module.write_text("value = 2\n", encoding="utf-8")
    monkeypatch.chdir(tmp_path)

    def fake_simplify(_engine, _rel_files, repo_root, **_kwargs):
        (repo_root / "pdd" / "selected.py").write_text("value = 3\n", encoding="utf-8")
        (repo_root / "pdd" / "other.py").write_text("other = 2\n", encoding="utf-8")
        return True, "edited too far", 0.1, "claude"

    with patch("pdd.checkup_simplify.run_simplify_engine_command", side_effect=fake_simplify), patch(
        "pdd.checkup_simplify.check_simplify_engine_available",
        return_value=("2.1.200", "claude", None),
    ):
        result = run_checkup_simplify(
            path=module,
            apply=True,
            since=None,
            staged=False,
            max_files=5,
            attempts=1,
            engine=None,
            evidence=True,
            verify=False,
            no_format=True,
            quiet=True,
            verbose=False,
        )

    assert result.success is False
    assert result.exit_code == 2
    assert module.read_text(encoding="utf-8") == "value = 2\n"


def test_staged_apply_refuses_to_overwrite_unstaged_contents(tmp_path: Path, monkeypatch) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "pdd" / "selected.py"
    module.parent.mkdir(parents=True)
    module.write_text("value = 1\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-m", "init"], cwd=tmp_path, check=True, capture_output=True)
    module.write_text("value = 2\n", encoding="utf-8")
    subprocess.run(["git", "add", "pdd/selected.py"], cwd=tmp_path, check=True, capture_output=True)
    module.write_text("value = 999\n", encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    with patch("pdd.checkup_simplify.run_simplify_engine_command") as mock_simplify, patch(
        "pdd.checkup_simplify.check_simplify_engine_available",
        return_value=("2.1.200", "claude", None),
    ):
        result = run_checkup_simplify(
            path=None,
            apply=True,
            since=None,
            staged=True,
            max_files=5,
            attempts=1,
            engine=None,
            evidence=False,
            verify=False,
            no_format=True,
            quiet=True,
            verbose=False,
        )

    mock_simplify.assert_not_called()
    assert result.success is False
    assert result.exit_code == 2
    assert module.read_text(encoding="utf-8") == "value = 999\n"


def test_staged_candidate_reads_staged_snapshot(tmp_path: Path, monkeypatch) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "pdd" / "selected.py"
    module.parent.mkdir(parents=True)
    module.write_text("value = 1\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-m", "init"], cwd=tmp_path, check=True, capture_output=True)
    module.write_text("value = 2\n", encoding="utf-8")
    subprocess.run(["git", "add", "pdd/selected.py"], cwd=tmp_path, check=True, capture_output=True)
    monkeypatch.chdir(tmp_path)
    observed: list[str] = []

    def fake_simplify(_engine, _rel_files, repo_root, **_kwargs):
        candidate_file = repo_root / "pdd" / "selected.py"
        observed.append(candidate_file.read_text(encoding="utf-8"))
        candidate_file.write_text("value = 3\n", encoding="utf-8")
        return True, "safe", 0.1, "claude"

    with patch("pdd.checkup_simplify.run_simplify_engine_command", side_effect=fake_simplify), patch(
        "pdd.checkup_simplify.check_simplify_engine_available",
        return_value=("2.1.200", "claude", None),
    ):
        result = run_checkup_simplify(
            path=None,
            apply=True,
            since=None,
            staged=True,
            max_files=5,
            attempts=1,
            engine=None,
            evidence=False,
            verify=False,
            no_format=True,
            quiet=True,
            verbose=False,
        )

    assert observed == ["value = 2\n"]
    assert result.success is True
    assert module.read_text(encoding="utf-8") == "value = 3\n"


def test_build_verify_command_scopes_format_and_lint() -> None:
    repo_root = Path("/repo")
    assert _build_verify_command(
        "format", "ruff format", ["a.py", "b.py"], repo_root=repo_root
    ) == "ruff format -- a.py b.py"
    assert _build_verify_command("format", "ruff format", [], repo_root=repo_root) == (
        "ruff format"
    )


def test_build_verify_command_scopes_mypy_to_explicit_files() -> None:
    repo_root = Path("/repo")
    assert _build_verify_command(
        "typecheck",
        "mypy pdd",
        ["pdd/checkup_simplify.py"],
        repo_root=repo_root,
    ) == "mypy --follow-imports=skip pdd/checkup_simplify.py"


def test_build_verify_command_scopes_pytest_to_colocated_tests(tmp_path: Path) -> None:
    tests_dir = tmp_path / "tests" / "commands"
    tests_dir.mkdir(parents=True)
    test_file = tests_dir / "test_widget.py"
    test_file.write_text("def test_ok():\n    assert True\n", encoding="utf-8")
    rel_source = "pdd/widget.py"
    assert _guess_pytest_targets(tmp_path, [rel_source]) == [
        "tests/commands/test_widget.py"
    ]
    assert _build_verify_command(
        "test",
        "pytest -q",
        [rel_source],
        repo_root=tmp_path,
    ) == "pytest -q -- tests/commands/test_widget.py"


def test_build_verify_command_leaves_pytest_unscoped_without_colocated_test(
    tmp_path: Path,
) -> None:
    assert _build_verify_command(
        "test",
        "pytest -q",
        ["pdd/orphan.py"],
        repo_root=tmp_path,
    ) == "pytest -q"


@pytest.mark.skipif(shutil.which("ruff") is None, reason="ruff required")
def test_run_verification_scopes_format_to_touched_files(tmp_path: Path) -> None:
    _init_git_repo(tmp_path)
    in_scope = tmp_path / "in_scope.py"
    out_scope = tmp_path / "out_scope.py"
    in_scope.write_text("x=1\n", encoding="utf-8")
    out_scope.write_text("y  =  2\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "init"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
    )
    before_out_scope = out_scope.read_text(encoding="utf-8")

    checks = _run_verification(
        repo_root=tmp_path,
        touched=[in_scope],
        commands=SimplifyVerifyCommands(
            format="ruff format",
            lint="",
            typecheck="",
            test="",
        ),
        no_format=False,
        quiet=True,
    )

    assert checks["format"] == "passed"
    assert out_scope.read_text(encoding="utf-8") == before_out_scope


@pytest.mark.skipif(shutil.which("mypy") is None, reason="mypy required")
def test_default_mypy_verify_command_runs_for_scoped_file() -> None:
    repo_root = Path(__file__).resolve().parents[2]
    rel_source = "pdd/checkup_simplify.py"
    source = repo_root / rel_source
    if not source.is_file():
        pytest.skip("pdd checkout layout required")

    command = _build_verify_command(
        "typecheck", "mypy pdd", [rel_source], repo_root=repo_root
    )
    result = subprocess.run(
        command,
        shell=True,
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=False,
        timeout=120,
    )
    assert result.returncode == 0, result.stderr or result.stdout


@pytest.mark.skipif(shutil.which("pytest") is None, reason="pytest required")
def test_default_pytest_verify_command_runs_colocated_tests() -> None:
    repo_root = Path(__file__).resolve().parents[2]
    rel_source = "pdd/checkup_simplify.py"
    test_file = repo_root / "tests" / "commands" / "test_checkup_simplify.py"
    if not (repo_root / rel_source).is_file() or not test_file.is_file():
        pytest.skip("pdd checkout layout required")

    command = _build_verify_command(
        "test", "pytest -q", [rel_source], repo_root=repo_root
    )
    assert command == "pytest -q -- tests/commands/test_checkup_simplify.py"

    # Run one fast test from the colocated module to prove the scoped command works.
    smoke_command = (
        "pytest -q tests/commands/test_checkup_simplify.py::test_parse_claude_code_version"
    )
    result = subprocess.run(
        smoke_command,
        shell=True,
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=False,
        timeout=120,
    )
    assert result.returncode == 0, result.stderr or result.stdout


def test_discover_respects_pyproject_defaults_from_subdirectory(
    tmp_path: Path, monkeypatch
) -> None:
    _init_git_repo(tmp_path)
    (tmp_path / "pyproject.toml").write_text(
        "[tool.pdd.checkup.simplify]\nmax_files = 2\n",
        encoding="utf-8",
    )
    for index in range(3):
        module = tmp_path / f"mod_{index}.py"
        module.write_text(f"x{index} = {index}\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "init"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
    )
    for index in range(3):
        (tmp_path / f"mod_{index}.py").write_text(
            f"x{index} = {index + 1}\n",
            encoding="utf-8",
        )
    subdir = tmp_path / "nested" / "deep"
    subdir.mkdir(parents=True)
    monkeypatch.chdir(subdir)

    result = run_checkup_simplify(
        path=None,
        apply=False,
        since=None,
        staged=False,
        max_files=None,
        attempts=None,
        engine=None,
        evidence=False,
        verify=False,
        no_format=True,
        quiet=True,
        verbose=False,
    )

    assert len(result.files_analyzed) == 2


def test_resolve_repo_root_from_worktree_subdirectory(tmp_path: Path) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "pkg" / "sample.py"
    module.parent.mkdir(parents=True)
    module.write_text("value = 1\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "init"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
    )

    worktree_path = tmp_path / "linked-worktree"
    subprocess.run(
        ["git", "worktree", "add", str(worktree_path), "HEAD"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
    )
    nested = worktree_path / "pkg"

    resolved = resolve_simplify_repo_root(nested)

    assert resolved == worktree_path.resolve()


def test_apply_multiple_attempts_requires_verify(tmp_path: Path, monkeypatch) -> None:
    _init_git_repo(tmp_path)
    module = tmp_path / "sample.py"
    module.write_text("x = 1\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "init"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
    )
    module.write_text("x = 2\n", encoding="utf-8")
    monkeypatch.chdir(tmp_path)

    with pytest.raises(ValueError, match="--verify is required"):
        run_checkup_simplify(
            path=module,
            apply=True,
            since=None,
            staged=False,
            max_files=5,
            attempts=2,
            engine=None,
            evidence=False,
            verify=False,
            no_format=True,
            quiet=True,
            verbose=False,
        )
