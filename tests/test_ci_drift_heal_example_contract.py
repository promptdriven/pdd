"""Execution contract for the generated ``ci_drift_heal`` example."""

# pylint: disable=duplicate-code

from __future__ import annotations

import hashlib
import importlib.util
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from types import ModuleType


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
    example = _load_example()
    monkeypatch.setattr(example, "main", lambda **_kwargs: 7)

    with tempfile.TemporaryDirectory() as temp:
        assert example.invoke_main(Path(temp)) == 7

    monkeypatch.setattr(example, "run_dry_run", lambda _workspace: 7)

    assert example.run() == 7
    output = capsys.readouterr()
    assert "failed with exit code 7" in output.err
    assert "completed successfully" not in output.out


def test_example_runs_twice_without_checkout_or_caller_repo_residue(tmp_path: Path):
    """The provider-free example is repeatable and leaves both repos untouched."""
    caller_repo = tmp_path / "caller"
    caller_repo.mkdir()
    (caller_repo / "marker.txt").write_text("unchanged\n", encoding="utf-8")
    subprocess.run(["git", "init", "-q"], cwd=caller_repo, check=True)

    caller_before = _tree_digest(caller_repo)
    checkout_before = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=all"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout

    for _attempt in range(2):
        result = subprocess.run(
            [sys.executable, str(EXAMPLE)],
            cwd=caller_repo,
            env=_provider_free_env(),
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert "completed successfully" in result.stdout

    assert _tree_digest(caller_repo) == caller_before
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
    )
    assert all(fragment in prompt for fragment in required)
    assert EXAMPLE.read_bytes().endswith(b"\n")
