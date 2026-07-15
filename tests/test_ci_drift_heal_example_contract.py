"""Execution contract for the generated ``ci_drift_heal`` example."""

# pylint: disable=duplicate-code

from __future__ import annotations

import ast
import hashlib
import importlib.util
import inspect
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from types import ModuleType
from types import SimpleNamespace

import pytest

from pdd.ci_drift_heal import main as ci_drift_heal_main


ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "context" / "ci_drift_heal_example.py"
PROMPT = ROOT / "pdd" / "prompts" / "ci_drift_heal_python.prompt"


def _load_example() -> ModuleType:
    spec = importlib.util.spec_from_file_location("ci_drift_heal_example", EXAMPLE)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _tree_digest(root: Path) -> dict[str, str]:
    """Return a stable digest of files outside Git's administrative data."""
    return {
        path.relative_to(root).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(root.rglob("*"))
        if path.is_file() and ".git" not in path.relative_to(root).parts
    }


def _git_admin_snapshot(repo: Path) -> dict[str, object]:
    """Capture refs, config, HEAD, and every Git administrative file."""
    def git(*args: str) -> str:
        return subprocess.run(
            ["git", *args],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        ).stdout

    return {
        "head": git("rev-parse", "HEAD"),
        "refs": git("for-each-ref", "--format=%(refname) %(objectname)"),
        "config": git("config", "--local", "--null", "--list"),
        "files": _tree_digest(repo / ".git"),
    }


def _provider_free_env() -> dict[str, str]:
    env = os.environ.copy()
    for name in tuple(env):
        if name.endswith("_API_KEY") or name in {
            "ANTHROPIC_AUTH_TOKEN",
            "GOOGLE_APPLICATION_CREDENTIALS",
            "PDD_SYNC_PROTECTED_BASE_SHA",
        }:
            env.pop(name, None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["PYTHONPATH"] = os.pathsep.join(
        item for item in (str(ROOT), env.get("PYTHONPATH", "")) if item
    )
    return env


def test_example_propagates_dry_run_failure(monkeypatch, capsys):
    """A failed ``main(dry_run=True)`` must make the example fail truthfully."""
    assert "dry_run" in inspect.signature(ci_drift_heal_main).parameters
    example = _load_example()
    monkeypatch.setattr(example, "main", lambda **_kwargs: 7)

    with tempfile.TemporaryDirectory() as temp:
        assert example.invoke_main(Path(temp)) == 7

    monkeypatch.setattr(example, "run_dry_run", lambda _workspace: 7)

    assert example.run() == 7
    output = capsys.readouterr()
    assert "failed with exit code 7" in output.err
    assert "completed successfully" not in output.out


def test_invoke_main_restores_cwd_after_failure(monkeypatch, tmp_path: Path):
    """An exception from the real entry-point boundary cannot strand the CWD."""
    example = _load_example()
    original = Path.cwd()

    def fail(**_kwargs):
        raise RuntimeError("sentinel failure")

    monkeypatch.setattr(example, "main", fail)
    with pytest.raises(RuntimeError, match="sentinel failure"):
        example.invoke_main(tmp_path)
    assert Path.cwd() == original


def test_child_environment_is_minimal_isolated_and_bytecode_safe(
    monkeypatch, tmp_path: Path
):
    """Capture the actual child env and reject inherited secrets/config roots."""
    example = _load_example()
    sensitive = {
        "CLAUDE_CODE_OAUTH_TOKEN": "sentinel-claude-oauth",
        "AWS_ACCESS_KEY_ID": "sentinel-aws-id",
        "AWS_SECRET_ACCESS_KEY": "sentinel-aws-secret",
        "AWS_SESSION_TOKEN": "sentinel-aws-session",
        "AZURE_CLIENT_ID": "sentinel-azure-id",
        "AZURE_CLIENT_SECRET": "sentinel-azure-secret",
        "GOOGLE_APPLICATION_CREDENTIALS": str(tmp_path / "ambient-adc.json"),
        "HOME": str(tmp_path / "ambient-home"),
        "XDG_CONFIG_HOME": str(tmp_path / "ambient-xdg"),
        "AWS_CONFIG_FILE": str(tmp_path / "ambient-aws-config"),
        "AWS_SHARED_CREDENTIALS_FILE": str(tmp_path / "ambient-aws-creds"),
        "AZURE_CONFIG_DIR": str(tmp_path / "ambient-azure"),
        "CLOUDSDK_CONFIG": str(tmp_path / "ambient-gcloud"),
        "PYTHONPATH": "sentinel-ambient-pythonpath",
    }
    for name, value in sensitive.items():
        monkeypatch.setenv(name, value)

    captured: dict[str, object] = {}

    def capture_run(*_args, **kwargs):
        captured.update(kwargs)
        return SimpleNamespace(returncode=0)

    monkeypatch.setattr(example.subprocess, "run", capture_run)
    workspace = tmp_path / "workspace"
    workspace.mkdir()

    assert example.run_dry_run(workspace) == 0
    child_env = captured["env"]
    assert isinstance(child_env, dict)
    assert not set(sensitive).intersection(child_env)
    assert not set(sensitive.values()).intersection(child_env.values())
    assert Path(child_env["HOME"]).is_relative_to(workspace)
    assert Path(child_env["XDG_CONFIG_HOME"]).is_relative_to(workspace)
    assert child_env["PYTHONPATH"] == str(ROOT)
    assert child_env["PYTHONDONTWRITEBYTECODE"] == "1"
    assert example.sys.dont_write_bytecode is True


def test_example_runs_twice_without_checkout_or_caller_repo_residue(tmp_path: Path):
    """The provider-free example is repeatable and leaves both repos untouched."""
    caller_repo = tmp_path / "caller"
    caller_repo.mkdir()
    (caller_repo / "marker.txt").write_text("unchanged\n", encoding="utf-8")
    subprocess.run(["git", "init", "-q", "-b", "main"], cwd=caller_repo, check=True)
    subprocess.run(
        ["git", "config", "user.email", "example@example.com"],
        cwd=caller_repo,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Example"], cwd=caller_repo, check=True
    )
    subprocess.run(["git", "add", "marker.txt"], cwd=caller_repo, check=True)
    subprocess.run(
        ["git", "commit", "-q", "-m", "initial"], cwd=caller_repo, check=True
    )

    real_git = shutil.which("git")
    assert real_git is not None
    shim_dir = tmp_path / "bin"
    shim_dir.mkdir()
    shim_log = tmp_path / "git-shim.log"
    git_shim = shim_dir / "git"
    git_shim.write_text(
        "#!/bin/sh\n"
        f"printf '%s\\n' \"$*\" >> {shim_log!s}\n"
        "case \"$1\" in\n"
        "  add|commit|push|checkout|reset|restore|clean|update-ref|write-tree|"
        "read-tree|merge|rebase) exit 97 ;;\n"
        "esac\n"
        f"exec {real_git} \"$@\"\n",
        encoding="utf-8",
    )
    git_shim.chmod(0o755)

    caller_before = _tree_digest(caller_repo)
    admin_before = _git_admin_snapshot(caller_repo)
    checkout_before = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=all"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout

    env = _provider_free_env()
    env["PATH"] = os.pathsep.join((str(shim_dir), env["PATH"]))
    for _attempt in range(2):
        result = subprocess.run(
            [sys.executable, str(EXAMPLE)],
            cwd=caller_repo,
            env=env,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert "completed successfully" in result.stdout

    assert _tree_digest(caller_repo) == caller_before
    assert _git_admin_snapshot(caller_repo) == admin_before
    if shim_log.exists():
        forbidden = {
            "add", "commit", "push", "checkout", "reset", "restore", "clean",
            "update-ref", "write-tree", "read-tree", "merge", "rebase",
        }
        observed = {line.split(maxsplit=1)[0] for line in shim_log.read_text().splitlines()}
        assert observed.isdisjoint(forbidden)
    assert (
        subprocess.run(
            ["git", "status", "--porcelain", "--untracked-files=all"],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        ).stdout
        == checkout_before
    )


def test_prompt_pins_non_mutating_truthful_example_contract():
    """Hosted regeneration must preserve the safety contract from issue #2061."""
    prompt = PROMPT.read_text(encoding="utf-8")
    required = (
        "disposable temporary project",
        "provider credentials",
        "never call `commit_and_push`",
        "propagate that exact non-zero exit code",
        "must not write to the source checkout",
        "bounded timeout",
        "minimal environment allowlist",
        "isolated temporary HOME",
    )
    assert all(fragment in prompt for fragment in required)
    assert EXAMPLE.read_bytes().endswith(b"\n")


def test_example_ast_forbids_healing_git_and_non_dry_run_paths():
    """Generated bytes, not prompt prose, must exclude mutation entry points."""
    tree = ast.parse(EXAMPLE.read_text(encoding="utf-8"))
    forbidden = {"commit_and_push", "heal_module", "detect_drift"}

    imported = {
        alias.name.rsplit(".", 1)[-1]
        for node in ast.walk(tree)
        if isinstance(node, (ast.Import, ast.ImportFrom))
        for alias in node.names
    }
    called = {
        node.func.id
        for node in ast.walk(tree)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
    }
    assert imported.isdisjoint(forbidden)
    assert called.isdisjoint(forbidden | {"commit", "push"})

    main_calls = [
        node
        for node in ast.walk(tree)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "main"
    ]
    assert len(main_calls) == 1
    dry_run = next(
        (keyword.value for keyword in main_calls[0].keywords if keyword.arg == "dry_run"),
        None,
    )
    assert isinstance(dry_run, ast.Constant) and dry_run.value is True
