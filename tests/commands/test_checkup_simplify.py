"""Tests for ``pdd checkup simplify`` (Claude Code /simplify)."""
from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.checkup_file_selection import discover_simplify_targets
from pdd.checkup_simplify import (
    SimplifyVerifyCommands,
    _build_simplify_slash_message,
    _parse_claude_code_version,
    _run_verification,
    _scoped_verify_command,
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

    with patch("pdd.checkup_simplify._find_cli_binary", return_value="/bin/claude"):
        with patch("pdd.checkup_simplify.subprocess.run", side_effect=fake_run):
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

    with patch("pdd.checkup_simplify._find_cli_binary", return_value="/bin/claude"):
        with patch("pdd.checkup_simplify.subprocess.run", side_effect=fake_run):
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

    with patch("pdd.checkup_simplify._find_cli_binary", return_value="/bin/claude"):
        with patch("pdd.checkup_simplify.subprocess.run", side_effect=fake_run):
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

    with patch("pdd.checkup_simplify.run_claude_simplify_command") as mock_run, patch(
        "pdd.checkup_simplify.check_claude_code_simplify_available"
    ) as mock_probe:
        result = run_checkup_simplify(
            path=module,
            apply=False,
            since=None,
            staged=False,
            max_files=5,
            attempts=None,
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

    def fake_simplify(slash_message, repo_root, **kwargs):
        captured["slash"] = slash_message
        captured["cwd"] = str(repo_root)
        (repo_root / "pdd" / "apply_me.py").write_text(
            "def simplified():\n    return 2\n",
            encoding="utf-8",
        )
        return True, "Simplified 1 file.", 0.5, "Simplified 1 file."

    with patch("pdd.checkup_simplify.run_claude_simplify_command", side_effect=fake_simplify):
        with patch(
            "pdd.checkup_simplify.check_claude_code_simplify_available",
            return_value=("/bin/claude", (2, 1, 100), None),
        ):
            result = run_checkup_simplify(
                path=module,
                apply=True,
                since=None,
                staged=False,
                max_files=5,
                attempts=1,
                evidence=True,
                verify=False,
                no_format=True,
                quiet=True,
                verbose=False,
            )

    assert captured["slash"].startswith("/simplify")
    assert "pdd/apply_me.py" in captured["slash"]
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

    with patch("pdd.checkup_simplify.run_claude_simplify_command") as mock_run:
        with patch(
            "pdd.checkup_simplify.check_claude_code_simplify_available",
            return_value=("/bin/claude", (2, 1, 100), None),
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
    assert "Independent /simplify candidates" in result.output


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

    def fake_simplify(slash_message, repo_root, **kwargs):
        (repo_root / "pdd" / "apply_me.py").write_text(
            "def changed():\n    return 2\n",
            encoding="utf-8",
        )
        return True, "done", 0.2, "done"

    with patch("pdd.checkup_simplify.run_claude_simplify_command", side_effect=fake_simplify):
        with patch(
            "pdd.checkup_simplify.check_claude_code_simplify_available",
            return_value=("/bin/claude", (2, 1, 100), None),
        ):
            with patch("pdd.checkup_simplify._run_verification", side_effect=fake_verify):
                result = run_checkup_simplify(
                    path=module,
                    apply=True,
                    since=None,
                    staged=False,
                    max_files=5,
                    attempts=1,
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

    def fake_simplify(_slash_message, repo_root, **_kwargs):
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

    with patch("pdd.checkup_simplify.run_claude_simplify_command", side_effect=fake_simplify), patch(
        "pdd.checkup_simplify.check_claude_code_simplify_available",
        return_value=("/bin/claude", (2, 1, 200), None),
    ), patch("pdd.checkup_simplify._run_verification", side_effect=fake_verify):
        result = run_checkup_simplify(
            path=module,
            apply=True,
            since=None,
            staged=False,
            max_files=5,
            attempts=2,
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

    def fake_simplify(_message, repo_root, **_kwargs):
        (repo_root / "pdd" / "selected.py").write_text("value = 3\n", encoding="utf-8")
        (repo_root / "pdd" / "other.py").write_text("other = 2\n", encoding="utf-8")
        return True, "edited too far", 0.1, "claude"

    with patch("pdd.checkup_simplify.run_claude_simplify_command", side_effect=fake_simplify), patch(
        "pdd.checkup_simplify.check_claude_code_simplify_available",
        return_value=("/bin/claude", (2, 1, 200), None),
    ):
        result = run_checkup_simplify(
            path=module,
            apply=True,
            since=None,
            staged=False,
            max_files=5,
            attempts=1,
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
    with patch("pdd.checkup_simplify.run_claude_simplify_command") as mock_simplify, patch(
        "pdd.checkup_simplify.check_claude_code_simplify_available",
        return_value=("/bin/claude", (2, 1, 200), None),
    ):
        result = run_checkup_simplify(
            path=None,
            apply=True,
            since=None,
            staged=True,
            max_files=5,
            attempts=1,
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

    def fake_simplify(_message, repo_root, **_kwargs):
        candidate_file = repo_root / "pdd" / "selected.py"
        observed.append(candidate_file.read_text(encoding="utf-8"))
        candidate_file.write_text("value = 3\n", encoding="utf-8")
        return True, "safe", 0.1, "claude"

    with patch("pdd.checkup_simplify.run_claude_simplify_command", side_effect=fake_simplify), patch(
        "pdd.checkup_simplify.check_claude_code_simplify_available",
        return_value=("/bin/claude", (2, 1, 200), None),
    ):
        result = run_checkup_simplify(
            path=None,
            apply=True,
            since=None,
            staged=True,
            max_files=5,
            attempts=1,
            evidence=False,
            verify=False,
            no_format=True,
            quiet=True,
            verbose=False,
        )

    assert observed == ["value = 2\n"]
    assert result.success is True
    assert module.read_text(encoding="utf-8") == "value = 3\n"


def test_scoped_verify_command_appends_paths() -> None:
    assert _scoped_verify_command("ruff format", ["a.py", "b.py"]) == (
        "ruff format -- a.py b.py"
    )
    assert _scoped_verify_command("ruff format", []) == "ruff format"


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
            evidence=False,
            verify=False,
            no_format=True,
            quiet=True,
            verbose=False,
        )
