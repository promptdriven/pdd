"""Issue #1932 deterministic continuous-sync acceptance coverage."""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Callable, Dict, List

import pytest

from pdd.operation_log import save_fingerprint
from pdd.sync_determine_operation import get_pdd_file_paths


REPO_ROOT = Path(__file__).resolve().parents[2]


def _env() -> Dict[str, str]:
    env = os.environ.copy()
    env["PYTHONPATH"] = os.pathsep.join(
        [str(REPO_ROOT), env.get("PYTHONPATH", "")]
    )
    env["PDD_AUTO_UPDATE"] = "false"
    env["PDD_FORCE_LOCAL"] = "1"
    env["NO_COLOR"] = "1"
    return env


def _run(
    cwd: Path,
    args: List[str],
    *,
    check: bool = True,
) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        args,
        cwd=str(cwd),
        env=_env(),
        text=True,
        capture_output=True,
        check=False,
    )
    if check and result.returncode != 0:
        raise AssertionError(
            f"{args} failed with {result.returncode}\nSTDOUT:\n{result.stdout}\nSTDERR:\n{result.stderr}"
        )
    return result


def _git(cwd: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return _run(cwd, ["git", *args], check=check)


def _pdd_json(cwd: Path, *args: str, check: bool = True) -> dict:
    result = _run(cwd, [sys.executable, "-m", "pdd", *args], check=check)
    start = result.stdout.find("{")
    assert start >= 0, f"expected JSON on stdout, got: {result.stdout!r}"
    return json.loads(result.stdout[start:])


def _ci_json(cwd: Path, check: bool = True) -> dict:
    result = _run(
        cwd,
        [sys.executable, "-m", "pdd.ci_drift_heal", "--dry-run", "--json"],
        check=check,
    )
    start = result.stdout.find("{")
    assert start >= 0, f"expected JSON on stdout, got: {result.stdout!r}"
    return json.loads(result.stdout[start:])


@pytest.fixture()
def pdd_project(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "issue-1932@example.com")
    _git(repo, "config", "user.name", "Issue 1932")

    for directory in ("prompts", "src", "examples", "tests", "docs", ".pdd/meta"):
        (repo / directory).mkdir(parents=True, exist_ok=True)

    (repo / ".pddrc").write_text(
        "contexts:\n"
        "  default:\n"
        "    paths: [\"**\"]\n"
        "    defaults:\n"
        "      prompts_dir: prompts\n",
        encoding="utf-8",
    )
    (repo / "architecture.json").write_text(
        json.dumps(
            [
                {
                    "filename": "widget_python.prompt",
                    "filepath": "src/widget.py",
                    "description": "Widget module",
                }
            ],
            indent=2,
        ),
        encoding="utf-8",
    )
    (repo / "prompts/widget_python.prompt").write_text(
        "Build a deterministic widget.\n<include>../docs/widget.md</include>\n",
        encoding="utf-8",
    )
    (repo / "prompts/runtime_template_LLM.prompt").write_text(
        "Summarize the runtime context.\n",
        encoding="utf-8",
    )
    (repo / "prompts/unbaselined_helper_python.prompt").write_text(
        "Build an unbaselined helper.\n",
        encoding="utf-8",
    )
    (repo / "docs/widget.md").write_text("Widget docs v1\n", encoding="utf-8")
    (repo / "src/widget.py").write_text(
        "def value():\n    return 1\n",
        encoding="utf-8",
    )
    (repo / "examples/widget_example.py").write_text(
        "from src.widget import value\nprint(value())\n",
        encoding="utf-8",
    )
    (repo / "tests/test_widget.py").write_text(
        "from src.widget import value\n\n\ndef test_value():\n    assert value() == 1\n",
        encoding="utf-8",
    )

    old_cwd = Path.cwd()
    try:
        os.chdir(repo)
        paths = get_pdd_file_paths("widget", "python", "prompts")
        save_fingerprint("widget", "python", "fix", paths, 0.0, "baseline")
    finally:
        os.chdir(old_cwd)

    _git(repo, "add", ".")
    _git(repo, "commit", "-q", "-m", "baseline")
    _run(repo, [sys.executable, "-m", "pdd", "install-hooks"])
    return repo


def _unit_classification(report: dict) -> str:
    units = report["units"]
    assert len(units) == 1
    return units[0]["classification"]


def _assert_all_consumers_classify(repo: Path, expected: str) -> None:
    reports = {
        "reconcile": _pdd_json(repo, "reconcile", "--json", "--ledger", check=False),
        "sync": _pdd_json(repo, "sync", "--dry-run", "--json"),
        "update": _pdd_json(repo, "update", "--all", "--dry-run", "--json"),
        "change": _pdd_json(repo, "change", "--preflight", "--json"),
        "ci": _ci_json(repo, check=False),
    }
    assert {name: _unit_classification(report) for name, report in reports.items()} == {
        "reconcile": expected,
        "sync": expected,
        "update": expected,
        "change": expected,
        "ci": expected,
    }


def _last_ledger_classification(repo: Path) -> str:
    ledger = repo / ".pdd/drift-ledger.jsonl"
    assert ledger.exists()
    lines = [line for line in ledger.read_text(encoding="utf-8").splitlines() if line]
    assert lines
    return json.loads(lines[-1])["classification"]


def _fingerprint(repo: Path) -> dict:
    return json.loads((repo / ".pdd/meta/widget_python.json").read_text(encoding="utf-8"))


def _assert_valid_fingerprint(repo: Path) -> None:
    fingerprint = _fingerprint(repo)
    for key in ("prompt_hash", "code_hash", "example_hash", "test_hash"):
        assert fingerprint.get(key), f"{key} missing from fingerprint"


def test_issue_1932_clean_baseline_reports_no_drift(pdd_project: Path) -> None:
    reconcile = _pdd_json(pdd_project, "reconcile", "--json", "--strict")
    sync = _pdd_json(pdd_project, "sync", "--dry-run", "--json")
    update = _pdd_json(pdd_project, "update", "--all", "--dry-run", "--json")

    for report in (reconcile, sync, update):
        assert report["ok"] is True
        assert report["metadata_stale"] == 0
        assert report["summary"]["conflicts"] == 0
        assert report["summary"]["unbaselined"] == 0
        assert report["summary"]["total"] == 1
        assert report["units"][0]["basename"] == "widget"


@pytest.mark.parametrize(
    ("name", "path", "edit", "classification"),
    [
        (
            "doc",
            "docs/widget.md",
            lambda p: p.write_text("Widget docs v2\n", encoding="utf-8"),
            "DOC_CHANGED",
        ),
        (
            "prompt",
            "prompts/widget_python.prompt",
            lambda p: p.write_text(
                "Build a deterministic widget with a new requirement.\n"
                "<include>../docs/widget.md</include>\n",
                encoding="utf-8",
            ),
            "PROMPT_CHANGED",
        ),
        (
            "code",
            "src/widget.py",
            lambda p: p.write_text("def value():\n    return 2\n", encoding="utf-8"),
            "CODE_CHANGED",
        ),
        (
            "test",
            "tests/test_widget.py",
            lambda p: p.write_text(
                "from src.widget import value\n\n\ndef test_value():\n    assert value() in {1, 2}\n",
                encoding="utf-8",
            ),
            "TEST_CHANGED",
        ),
    ],
)
def test_issue_1932_all_consumers_classify_and_heal_idempotently(
    pdd_project: Path,
    name: str,
    path: str,
    edit: Callable[[Path], None],
    classification: str,
) -> None:
    baseline = _git(pdd_project, "rev-parse", "HEAD").stdout.strip()
    edit(pdd_project / path)
    _git(pdd_project, "add", path)
    _git(pdd_project, "commit", "-q", "-m", f"{name} drift")

    _assert_all_consumers_classify(pdd_project, classification)
    assert _last_ledger_classification(pdd_project) == classification

    first_heal = _pdd_json(pdd_project, "reconcile", "--json", "--strict", "--heal")
    assert first_heal["ok"] is True
    assert first_heal["metadata_stale"] == 0
    _assert_valid_fingerprint(pdd_project)

    _git(pdd_project, "add", ".pdd/meta/widget_python.json")
    _git(pdd_project, "commit", "-q", "-m", f"{name} metadata heal")

    second_heal = _pdd_json(pdd_project, "reconcile", "--json", "--strict", "--heal")
    assert second_heal["ok"] is True
    assert second_heal["metadata_stale"] == 0
    _git(pdd_project, "diff", "--exit-code")

    _git(pdd_project, "reset", "--hard", baseline)


def test_issue_1932_unbaselined_fingerprints_are_not_stamped(pdd_project: Path) -> None:
    fingerprint_path = pdd_project / ".pdd/meta/widget_python.json"

    original = fingerprint_path.read_text(encoding="utf-8")
    fingerprint_path.unlink()
    missing = _pdd_json(
        pdd_project,
        "reconcile",
        "--json",
        "--strict",
        "--heal",
        "--module",
        "widget",
        check=False,
    )
    assert missing["ok"] is False
    assert missing["unbaselined"][0]["classification"] == "UNBASELINED"
    assert not fingerprint_path.exists()

    fingerprint_path.write_text("{not-json", encoding="utf-8")
    invalid = _pdd_json(
        pdd_project,
        "reconcile",
        "--json",
        "--strict",
        "--heal",
        "--module",
        "widget",
        check=False,
    )
    assert invalid["ok"] is False
    assert invalid["unbaselined"][0]["reason"] == "fingerprint invalid"
    assert fingerprint_path.read_text(encoding="utf-8") == "{not-json"

    fingerprint_path.write_text(original, encoding="utf-8")


def test_issue_1932_prompt_code_coedit_is_conflict_without_data_loss(pdd_project: Path) -> None:
    fingerprint_before = (pdd_project / ".pdd/meta/widget_python.json").read_text(encoding="utf-8")
    prompt_path = pdd_project / "prompts/widget_python.prompt"
    prompt_text = (
        "Build a deterministic widget with a conflicting prompt change.\n"
        "<include>../docs/widget.md</include>\n"
    )
    prompt_path.write_text(prompt_text, encoding="utf-8")
    (pdd_project / "src/widget.py").write_text(
        "def value():\n    return 99\n",
        encoding="utf-8",
    )

    _assert_all_consumers_classify(pdd_project, "CONFLICT")
    conflict = _pdd_json(
        pdd_project,
        "reconcile",
        "--json",
        "--strict",
        "--heal",
        check=False,
    )
    assert conflict["ok"] is False
    assert conflict["conflicts"][0]["operation"] == "conflict"
    assert (pdd_project / ".pdd/meta/widget_python.json").read_text(encoding="utf-8") == fingerprint_before
    assert prompt_path.read_text(encoding="utf-8") == prompt_text


def test_issue_1932_incomplete_metadata_reports_failure_not_success(pdd_project: Path) -> None:
    fingerprint_path = pdd_project / ".pdd/meta/widget_python.json"
    fingerprint = _fingerprint(pdd_project)
    fingerprint["code_hash"] = None
    fingerprint_path.write_text(json.dumps(fingerprint, indent=2), encoding="utf-8")

    report = _pdd_json(pdd_project, "reconcile", "--json", "--strict", check=False)
    assert report["ok"] is False
    assert report["failures"][0]["classification"] == "FAILURE"
    assert report["failures"][0]["failure"] == "incomplete_metadata"
