"""Semantic tests for the disposable issue-1995 hosted diagnostic."""

from __future__ import annotations

import hashlib
import ast
import json
import os
import subprocess
import sys
from pathlib import Path

import yaml


DIAGNOSTIC_WORKFLOW = Path(".github/workflows/1995-node-diagnostic.yml")
UNIT_WORKFLOW = Path(".github/workflows/unit-tests.yml")
SUBJECT_SHA = "385ab8872411e740480bb164fb2b840b91f2624c"
PARITY_ACTION_STEPS = (
    "Set up Python",
    "Set up Node for real Vitest sandbox coverage",
)


def _workflow(path: Path) -> dict:
    loaded = yaml.safe_load(path.read_text(encoding="utf-8"))
    assert isinstance(loaded, dict)
    return loaded


def _steps(workflow: dict, job: str) -> dict[str, dict]:
    entries = workflow["jobs"][job]["steps"]
    return {entry["name"]: entry for entry in entries}


def _run(*args: str, cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=cwd, text=True, capture_output=True, check=False)


def test_workflow_pins_pr_head_and_matches_original_lane_setup() -> None:
    """The diagnostic must execute the attributed head in an equivalent lane."""
    diagnostic = _workflow(DIAGNOSTIC_WORKFLOW)
    unit = _workflow(UNIT_WORKFLOW)
    diagnostic_job = diagnostic["jobs"]["node-lifecycle-diagnostic"]
    diagnostic_steps = _steps(diagnostic, "node-lifecycle-diagnostic")
    unit_steps = _steps(unit, "unit-tests")

    checkout = diagnostic_steps["Check out the recorded source"]
    assert checkout["with"]["ref"] == (
        "${{ github.event.pull_request.head.sha || github.sha }}"
    )
    assert checkout["with"]["fetch-depth"] == 0
    assert diagnostic_job["env"]["PDD_ISSUE_1995_SUBJECT_SHA"] == SUBJECT_SHA
    assert "Verify attributed issue-1995 source" in diagnostic_steps

    for name in PARITY_ACTION_STEPS:
        assert name in diagnostic_steps
        for field in ("uses", "with"):
            assert diagnostic_steps[name].get(field) == unit_steps[name].get(field), (
                name,
                field,
            )
    unit_order = [step["name"] for step in unit["jobs"]["unit-tests"]["steps"]]
    shell_steps = unit_order[
        unit_order.index(PARITY_ACTION_STEPS[-1])
        + 1 : unit_order.index("Run focused protected-runner tests")
    ]
    runner_source = Path("scripts/ci/run_issue_1995_lane_step.py").read_text(
        encoding="utf-8"
    )
    runner_tree = ast.parse(runner_source)
    assignments = {
        target.id: ast.literal_eval(node.value)
        for node in runner_tree.body
        if isinstance(node, ast.Assign)
        for target in node.targets
        if isinstance(target, ast.Name)
    }
    assert assignments["ALLOWED_STEPS"] == set(shell_steps)
    for name in shell_steps:
        assert diagnostic_steps[name]["run"] == (
            f'python scripts/ci/run_issue_1995_lane_step.py "{name}"'
        )
        assert unit_steps[name].get("shell", "bash") == "bash"

    command = diagnostic_steps["Run the bounded lifecycle diagnostic once"]["run"]
    assert "--expected-collected 759 --expected-skipped 16" in command
    assert "ps -eo pid=,ppid=,state=,comm=" in command
    assert "ps -ef" not in command
    assert "systemd-run --scope --wait --collect" in command
    assert "seal_issue_1995_evidence.py" in command
    verify = diagnostic_steps["Verify sealed diagnostic evidence"]
    assert verify["if"] == "always()"
    assert " verify " in f" {verify['run']} "


def test_source_verifier_allows_only_diagnostic_paths(tmp_path: Path) -> None:
    """The provenance gate fails closed on any subject-code byte change."""
    repository = tmp_path / "repo"
    repository.mkdir()
    assert _run("git", "init", cwd=repository).returncode == 0
    assert (
        _run(
            "git", "config", "user.email", "ci@example.test", cwd=repository
        ).returncode
        == 0
    )
    assert _run("git", "config", "user.name", "CI", cwd=repository).returncode == 0
    production = repository / "production.py"
    diagnostic = repository / "diagnostic.yml"
    production.write_text("subject = True\n", encoding="utf-8")
    diagnostic.write_text("version: 1\n", encoding="utf-8")
    assert _run("git", "add", ".", cwd=repository).returncode == 0
    assert _run("git", "commit", "-m", "subject", cwd=repository).returncode == 0
    subject = _run("git", "rev-parse", "HEAD", cwd=repository).stdout.strip()
    diagnostic.write_text("version: 2\n", encoding="utf-8")
    assert _run("git", "commit", "-am", "diagnostic", cwd=repository).returncode == 0
    head = _run("git", "rev-parse", "HEAD", cwd=repository).stdout.strip()

    verifier = Path("scripts/ci/verify_issue_1995_diagnostic_source.py").resolve()
    command = (
        sys.executable,
        str(verifier),
        "--subject",
        subject,
        "--expected-head",
        head,
        "--allow",
        "diagnostic.yml",
    )
    assert _run(*command, cwd=repository).returncode == 0

    production.write_text("subject = False\n", encoding="utf-8")
    assert (
        _run("git", "commit", "-am", "production drift", cwd=repository).returncode == 0
    )
    drifted_head = _run("git", "rev-parse", "HEAD", cwd=repository).stdout.strip()
    drifted = list(command)
    drifted[drifted.index(head)] = drifted_head
    result = _run(*drifted, cwd=repository)
    assert result.returncode != 0
    assert "production.py" in result.stderr


def test_lifecycle_distinguishes_normal_error_and_interrupt(tmp_path: Path) -> None:
    """Only a successful phase receives a normal finish record."""
    test_file = tmp_path / "test_cases.py"
    test_file.write_text(
        "def test_pass(): pass\n"
        "def test_error(): assert False\n"
        "def test_interrupt(): raise KeyboardInterrupt()\n",
        encoding="utf-8",
    )
    plugin_path = str(Path("scripts/ci").resolve())

    def events(node: str) -> list[dict]:
        lifecycle = tmp_path / f"{node}.jsonl"
        environment = os.environ.copy()
        environment["PYTHONPATH"] = plugin_path
        environment["PDD_PYTEST_LIFECYCLE_JSONL"] = str(lifecycle)
        command = [
            sys.executable,
            "-m",
            "pytest",
            "-q",
            "-p",
            "pytest_lifecycle_jsonl",
            f"{test_file}::{node}",
        ]
        subprocess.run(
            command,
            env=environment,
            text=True,
            capture_output=True,
            check=False,
        )
        return [json.loads(line) for line in lifecycle.read_text().splitlines()]

    def call_boundaries(node: str) -> list[dict]:
        return [
            entry
            for entry in events(node)
            if entry.get("phase") == "call"
            and str(entry.get("event", "")).startswith("phase.")
        ]

    passed = call_boundaries("test_pass")
    errored = call_boundaries("test_error")
    interrupted = call_boundaries("test_interrupt")
    assert [entry["event"] for entry in passed] == ["phase.start", "phase.finish"]
    assert [entry["event"] for entry in errored] == ["phase.start", "phase.error"]
    assert [entry["event"] for entry in interrupted] == ["phase.start", "phase.abort"]
    assert errored[-1]["exception_type"] == "AssertionError"
    assert interrupted[-1]["exception_type"] == "KeyboardInterrupt"


def test_sealed_evidence_manifest_detects_changes_and_rejects_tokens(
    tmp_path: Path,
) -> None:
    """Only closed, sanitized evidence with verified hashes is uploadable."""
    live = tmp_path / "live"
    sealed = tmp_path / "sealed"
    live.mkdir()
    (live / "pytest.log").write_text("complete\n", encoding="utf-8")
    script = Path("scripts/ci/seal_issue_1995_evidence.py").resolve()
    seal = _run(sys.executable, str(script), "seal", str(live), str(sealed))
    assert seal.returncode == 0, seal.stderr
    manifest_line = (sealed / "SHA256SUMS").read_text().strip()
    expected = hashlib.sha256(b"complete\n").hexdigest()
    assert manifest_line == f"{expected}  pytest.log"
    assert _run(sys.executable, str(script), "verify", str(sealed)).returncode == 0

    os.chmod(sealed / "pytest.log", 0o644)
    (sealed / "pytest.log").write_text("changed\n", encoding="utf-8")
    assert _run(sys.executable, str(script), "verify", str(sealed)).returncode != 0

    unsafe_live = tmp_path / "unsafe-live"
    unsafe_sealed = tmp_path / "unsafe-sealed"
    unsafe_live.mkdir()
    (unsafe_live / "snapshot.txt").write_text(
        "credential=ghp_abcdefghijklmnopqrstuvwxyz0123456789\n",
        encoding="utf-8",
    )
    unsafe = _run(
        sys.executable, str(script), "seal", str(unsafe_live), str(unsafe_sealed)
    )
    assert unsafe.returncode != 0
    assert not unsafe_sealed.exists()
