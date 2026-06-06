"""CLI E2E coverage for PR-scope CI drift healing.

These tests exercise the user-facing CI entrypoint (`python -m
pdd.ci_drift_heal`) against a real temporary git repository. The nested
`pdd sync` executable is represented by a PATH-level test double so the test
can verify the parent-to-child environment contract without real LLM calls.
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path


def _project_root() -> Path:
    current = Path(__file__).resolve()
    for parent in current.parents:
        if (parent / "pdd").is_dir() and (parent / "pyproject.toml").exists():
            return parent
    raise RuntimeError("Could not locate project root")


def _run(cmd: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=cwd,
        check=True,
        capture_output=True,
        text=True,
    )


def _init_pr_repo(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    remote = tmp_path / "remote.git"
    repo.mkdir()

    _run(["git", "init", "--bare", str(remote)], tmp_path)
    _run(["git", "init", "-b", "main"], repo)
    _run(["git", "config", "user.email", "test@example.com"], repo)
    _run(["git", "config", "user.name", "Test User"], repo)
    _run(["git", "remote", "add", "origin", str(remote)], repo)

    (repo / "prompts").mkdir()
    (repo / "pdd").mkdir()
    (repo / "tests").mkdir()
    (repo / ".pdd" / "meta").mkdir(parents=True)

    (repo / "prompts" / "agentic_common_python.prompt").write_text(
        "% Keep agentic_common narrow.\n",
        encoding="utf-8",
    )
    (repo / "pdd" / "agentic_common.py").write_text(
        "def changed_behavior() -> str:\n"
        "    return 'fixed'\n",
        encoding="utf-8",
    )
    (repo / "tests" / "test_agentic_common.py").write_text(
        "def test_existing_behavior():\n"
        "    assert True\n",
        encoding="utf-8",
    )
    (repo / "README.md").write_text("initial\n", encoding="utf-8")

    _run(["git", "add", "."], repo)
    _run(["git", "commit", "-m", "initial"], repo)
    _run(["git", "push", "-u", "origin", "main"], repo)

    _run(["git", "checkout", "-b", "fix/narrow-pr"], repo)
    (repo / "README.md").write_text("initial\nnarrow PR note\n", encoding="utf-8")
    _run(["git", "add", "README.md"], repo)
    _run(["git", "commit", "-m", "narrow pr change"], repo)
    _run(["git", "push", "-u", "origin", "fix/narrow-pr"], repo)
    return repo


def _write_sitecustomize(patches_dir: Path) -> None:
    patches_dir.mkdir()
    (patches_dir / "sitecustomize.py").write_text(
        """
from pathlib import Path
from types import SimpleNamespace

import pdd.sync_determine_operation as sdo


def _decision(*args, **kwargs):
    return SimpleNamespace(operation="test", reason="coverage-triggering broad sync fallback")


def _paths(basename, language):
    root = Path.cwd()
    return {
        "prompt": root / "prompts" / f"{basename}_{language}.prompt",
        "code": root / "pdd" / f"{basename}.py",
        "test": root / "tests" / f"test_{basename}.py",
        "example": root / "context" / f"{basename}_example.py",
    }


sdo.sync_determine_operation = _decision
sdo.get_pdd_file_paths = _paths
""".lstrip(),
        encoding="utf-8",
    )


def _write_fake_pdd(bin_dir: Path) -> None:
    bin_dir.mkdir()
    fake_pdd = bin_dir / "pdd"
    fake_pdd.write_text(
        f"""#!{sys.executable}
from pathlib import Path
import json
import os
import sys

truthy = {{"1", "true", "yes", "on"}}
disabled = os.environ.get("PDD_DISABLE_TEST_EXTEND", "").strip().lower() in truthy
if "sync" in sys.argv and "agentic_common" in sys.argv and not disabled:
    test_path = Path("tests/test_agentic_common.py")
    test_path.write_text(
        test_path.read_text(encoding="utf-8")
        + "\\n# unrelated generated test block from coverage test_extend\\n",
        encoding="utf-8",
    )
    meta_path = Path(".pdd/meta/agentic_common_python.json")
    meta_path.parent.mkdir(parents=True, exist_ok=True)
    meta_path.write_text(json.dumps({{"command": "test_extend"}}), encoding="utf-8")
sys.exit(0)
""",
        encoding="utf-8",
    )
    fake_pdd.chmod(0o755)


def test_pr_ci_drift_heal_cli_does_not_commit_test_extend_churn(tmp_path: Path):
    """A PR auto-heal run must not re-bloat a narrow PR with test_extend output.

    The fake nested `pdd sync` appends the exact user-facing symptom unless the
    parent process passes `PDD_DISABLE_TEST_EXTEND=1` through the subprocess env.
    This fails on the buggy code and passes once the PR-scope guard is applied.
    """
    repo = _init_pr_repo(tmp_path)
    patches_dir = tmp_path / "patches"
    bin_dir = tmp_path / "bin"
    _write_sitecustomize(patches_dir)
    _write_fake_pdd(bin_dir)

    project_root = _project_root()
    env = os.environ.copy()
    env["PYTHONPATH"] = os.pathsep.join([str(patches_dir), str(project_root)])
    env["PATH"] = os.pathsep.join([str(bin_dir), env.get("PATH", "")])
    env["PDD_PATH"] = str(project_root / "pdd")
    env["PDD_HEAL_SUBPROCESS_TIMEOUT"] = "30"
    env.pop("PDD_DISABLE_TEST_EXTEND", None)

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "pdd.ci_drift_heal",
            "--diff-base",
            "HEAD~1",
            "--modules",
            "agentic_common",
        ],
        cwd=repo,
        env=env,
        capture_output=True,
        text=True,
        timeout=60,
    )

    assert result.returncode == 0, result.stdout + result.stderr

    test_text = (repo / "tests" / "test_agentic_common.py").read_text(encoding="utf-8")
    assert "unrelated generated test block from coverage test_extend" not in test_text

    meta_path = repo / ".pdd" / "meta" / "agentic_common_python.json"
    if meta_path.exists():
        assert '"command": "test_extend"' not in meta_path.read_text(encoding="utf-8")

    committed_diff = subprocess.run(
        ["git", "show", "--stat", "--oneline", "HEAD"],
        cwd=repo,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    assert "tests/test_agentic_common.py" not in committed_diff
