"""Semantic tests for the disposable issue-1995 hosted diagnostic."""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

import yaml

from scripts.ci.run_issue_1995_lane_step import (
    ALLOWED_STEPS,
    extract_unit_job_command,
)


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
    assert checkout["with"]["ref"] == "${{ github.event.pull_request.head.sha }}"
    assert checkout["with"]["fetch-depth"] == 0
    assert diagnostic_job["env"]["PDD_ISSUE_1995_SUBJECT_SHA"] == SUBJECT_SHA
    assert "Verify attributed issue-1995 source" in diagnostic_steps
    assert set(diagnostic["on"]) == {"pull_request"}
    assert diagnostic["on"]["pull_request"] == {
        "branches": ["main"],
        "types": ["opened", "synchronize", "reopened"],
    }
    assert diagnostic_job["if"] == (
        "github.event.pull_request.draft == true && "
        "github.event.pull_request.number == 2107"
    )

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
    assert ALLOWED_STEPS == set(shell_steps)
    for name in shell_steps:
        assert diagnostic_steps[name]["run"] == (
            f'python scripts/ci/run_issue_1995_lane_step.py "{name}"'
        )
        assert unit_steps[name].get("shell", "bash") == "bash"

    command = diagnostic_steps["Run the bounded lifecycle diagnostic once"]["run"]
    assert "ps -eo pid=,ppid=,state=,comm=" in command
    assert "ps -ef" not in command
    assert "systemd-run --wait" in command
    assert "--service-type=exec" in command
    assert "--scope" not in command
    initialize = diagnostic_steps["Initialize minimal diagnostic evidence"]
    assert diagnostic_job["steps"].index(initialize) < diagnostic_job["steps"].index(
        diagnostic_steps["Check out the recorded source"]
    )
    finalize = diagnostic_steps["Always finalize diagnostic evidence"]
    assert finalize["if"] == "always()"
    assert "seal_issue_1995_evidence.py" in finalize["run"]
    assert "--expected-outcomes" not in finalize["run"]
    assert finalize["run"].count("--allowed-path") == 6
    verify = diagnostic_steps["Always verify sealed diagnostic evidence"]
    assert verify["if"] == "always()"
    assert verify["id"] == "verify_evidence"
    assert " verify " in f" {verify['run']} "
    upload = diagnostic_steps["Always upload collision-safe diagnostic evidence"]
    assert upload["if"] == ("always() && steps.verify_evidence.outcome == 'success'")


def test_lane_step_runner_works_before_project_install(tmp_path: Path) -> None:
    """The exact-source runner has no non-stdlib import on a clean host."""
    environment = os.environ.copy()
    environment["HOME"] = str(tmp_path)
    script = Path("scripts/ci/run_issue_1995_lane_step.py").resolve()
    result = subprocess.run(
        [sys.executable, "-I", str(script), "Configure git identity"],
        cwd=Path.cwd(),
        env=environment,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert "import yaml" not in script.read_text(encoding="utf-8")


def test_stdlib_runner_extracts_exact_source_commands() -> None:
    """The clean-host parser must match authoritative parsed scalar values."""
    document = UNIT_WORKFLOW.read_text(encoding="utf-8")
    workflow = _workflow(UNIT_WORKFLOW)
    authoritative = {
        step["name"]: step["run"]
        for step in workflow["jobs"]["unit-tests"]["steps"]
        if step.get("name") in ALLOWED_STEPS
    }
    assert set(authoritative) == ALLOWED_STEPS
    for name, command in authoritative.items():
        assert extract_unit_job_command(document, name) == command


def test_self_inventory_attestation_validates_complete_and_partial_runs(
    tmp_path: Path,
) -> None:
    """One run attests terminal coverage against its own collected node set."""
    lifecycle = tmp_path / "lifecycle.jsonl"
    allowed = [f"tests/selected_{index}.py" for index in range(6)]
    nodeids = [f"{path}::test_case" for path in allowed]
    digest = hashlib.sha256(("\n".join(nodeids) + "\n").encode()).hexdigest()
    records = [
        {
            "event": "collection.inventory",
            "item_count": len(nodeids),
            "nodeid_sha256": digest,
            "per_file": {path: 1 for path in allowed},
            "nodeids": nodeids,
        }
    ]
    records.extend(
        {
            "event": "node.report",
            "nodeid": nodeid,
            "phase": "call",
            "outcome": "passed",
        }
        for nodeid in nodeids
    )
    records.extend(
        {"event": "node.finish", "nodeid": nodeid} for nodeid in nodeids[:-1]
    )
    script = Path("scripts/ci/attest_issue_1995_lifecycle.py").resolve()
    command = [sys.executable, str(script), str(lifecycle)]
    for path in allowed:
        command.extend(("--allowed-path", path))

    def attest(current: list[dict]) -> subprocess.CompletedProcess[str]:
        lifecycle.write_text(
            "".join(json.dumps(record) + "\n" for record in current),
            encoding="utf-8",
        )
        return _run(*command)

    partial = attest(records)
    assert partial.returncode == 0, partial.stderr
    assert json.loads(partial.stdout)["complete"] is False
    assert json.loads(partial.stdout)["terminal_count"] == len(nodeids)
    assert json.loads(partial.stdout)["node_finish_count"] == len(nodeids) - 1
    completed_but_missing = attest([*records, {"event": "session.finish"}])
    assert completed_but_missing.returncode != 0
    records.append({"event": "node.finish", "nodeid": nodeids[-1]})
    complete = attest([*records, {"event": "session.finish"}])
    assert complete.returncode == 0, complete.stderr
    assert json.loads(complete.stdout)["complete"] is True


def test_finished_setup_failure_and_skip_have_truthful_node_outcomes(
    tmp_path: Path,
) -> None:
    """Setup terminal reports count without requiring a call report."""
    lifecycle = tmp_path / "lifecycle.jsonl"
    allowed = [f"tests/selected_{index}.py" for index in range(6)]
    nodeids = [f"{path}::test_case" for path in allowed]
    digest = hashlib.sha256(("\n".join(nodeids) + "\n").encode()).hexdigest()
    records = [
        {
            "event": "collection.inventory",
            "item_count": 6,
            "nodeid_sha256": digest,
            "per_file": {path: 1 for path in allowed},
            "nodeids": nodeids,
        },
        {
            "event": "node.report",
            "nodeid": nodeids[0],
            "phase": "setup",
            "outcome": "failed",
        },
        {
            "event": "node.report",
            "nodeid": nodeids[0],
            "phase": "teardown",
            "outcome": "passed",
        },
        {
            "event": "node.report",
            "nodeid": nodeids[1],
            "phase": "setup",
            "outcome": "skipped",
        },
    ]
    records.extend(
        {"event": "node.report", "nodeid": nodeid, "phase": "call", "outcome": "passed"}
        for nodeid in nodeids[2:]
    )
    records.extend({"event": "node.finish", "nodeid": nodeid} for nodeid in nodeids)
    records.append({"event": "session.finish"})
    lifecycle.write_text(
        "".join(json.dumps(record) + "\n" for record in records), encoding="utf-8"
    )
    script = Path("scripts/ci/attest_issue_1995_lifecycle.py").resolve()
    command = [sys.executable, str(script), str(lifecycle)]
    for path in allowed:
        command.extend(("--allowed-path", path))
    result = _run(*command)
    assert result.returncode == 0, result.stderr
    summary = json.loads(result.stdout)
    assert summary["complete"] is True
    assert summary["outcome_counts"] == {"failed": 1, "passed": 4, "skipped": 1}


def test_real_pytest_setup_failure_and_skip_attest_complete(tmp_path: Path) -> None:
    """Real pytest reports complete truthfully without call reports for two nodes."""
    files = [tmp_path / f"selected_{index}.py" for index in range(6)]
    files[0].write_text(
        "import pytest\n@pytest.fixture\ndef value(): raise RuntimeError('setup')\n"
        "def test_case(value): pass\n",
        encoding="utf-8",
    )
    files[1].write_text(
        "import pytest\n@pytest.fixture\ndef value(): pytest.skip('setup')\n"
        "def test_case(value): pass\n",
        encoding="utf-8",
    )
    for path in files[2:]:
        path.write_text("def test_case(): pass\n", encoding="utf-8")
    lifecycle = tmp_path / "real-setup.jsonl"
    environment = os.environ.copy()
    environment["PYTHONPATH"] = str(Path("scripts/ci").resolve())
    environment["PDD_PYTEST_LIFECYCLE_JSONL"] = str(lifecycle)
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "pytest",
            "-q",
            "-p",
            "pytest_lifecycle_jsonl",
            *map(str, files),
        ],
        env=environment,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 1
    records = [json.loads(line) for line in lifecycle.read_text().splitlines()]
    inventory = next(
        record for record in records if record["event"] == "collection.inventory"
    )
    attester = Path("scripts/ci/attest_issue_1995_lifecycle.py").resolve()
    command = [sys.executable, str(attester), str(lifecycle)]
    for path in inventory["per_file"]:
        command.extend(("--allowed-path", path))
    attested = _run(*command)
    assert attested.returncode == 0, attested.stderr
    summary = json.loads(attested.stdout)
    assert summary["complete"] is True
    assert summary["outcome_counts"] == {"failed": 1, "passed": 4, "skipped": 1}


def test_real_teardown_kill_is_always_partial(tmp_path: Path) -> None:
    """A hard kill after a passed call cannot become complete evidence."""
    marker = tmp_path / "teardown-started"
    test_file = tmp_path / "selected.py"
    test_file.write_text(
        "import time\nfrom pathlib import Path\nimport pytest\n"
        "@pytest.fixture\ndef value():\n    yield\n"
        f"    Path({str(marker)!r}).write_text('started')\n"
        "    while True: time.sleep(0.1)\n"
        "def test_case(value): pass\n",
        encoding="utf-8",
    )
    lifecycle = tmp_path / "teardown-kill.jsonl"
    environment = os.environ.copy()
    environment["PYTHONPATH"] = str(Path("scripts/ci").resolve())
    environment["PDD_PYTEST_LIFECYCLE_JSONL"] = str(lifecycle)
    with subprocess.Popen(
        [
            sys.executable,
            "-m",
            "pytest",
            "-q",
            "-p",
            "pytest_lifecycle_jsonl",
            str(test_file),
        ],
        env=environment,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    ) as process:
        try:
            for _ in range(100):
                if marker.exists():
                    break
                time.sleep(0.05)
            assert marker.exists()
            process.kill()
            process.wait(timeout=5)
        finally:
            if process.poll() is None:
                process.kill()
                process.wait(timeout=5)
    records = [json.loads(line) for line in lifecycle.read_text().splitlines()]
    inventory = next(
        record for record in records if record["event"] == "collection.inventory"
    )
    attester = Path("scripts/ci/attest_issue_1995_lifecycle.py").resolve()
    command = [sys.executable, str(attester), str(lifecycle)]
    for path in inventory["per_file"]:
        command.extend(("--allowed-path", path))
    attested = _run(*command)
    assert attested.returncode == 0, attested.stderr
    summary = json.loads(attested.stdout)
    assert summary["terminal_count"] == 1
    assert summary["node_finish_count"] == 0
    assert summary["session_finished"] is False
    assert summary["complete"] is False


def test_service_wrapper_owns_regular_log_descriptor(tmp_path: Path) -> None:
    """Child stdout and stderr land in one service-opened regular file."""
    wrapper = Path("scripts/ci/run_issue_1995_pytest_service.py").resolve()
    log = tmp_path / "pytest.log"
    result = _run(
        sys.executable,
        str(wrapper),
        "--log",
        str(log),
        "--",
        sys.executable,
        "-c",
        "import sys; print('stdout'); print('stderr', file=sys.stderr)",
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout == "" and result.stderr == ""
    assert log.is_file() and not log.is_symlink()
    assert sorted(log.read_text(encoding="utf-8").splitlines()) == [
        "stderr",
        "stdout",
    ]
    assert log.stat().st_mode & 0o777 == 0o600

    log.write_text("old\n", encoding="utf-8")
    log.chmod(0o644)
    replaced = _run(
        sys.executable,
        str(wrapper),
        "--log",
        str(log),
        "--",
        sys.executable,
        "-c",
        "print('new')",
    )
    assert replaced.returncode == 0, replaced.stderr
    assert log.read_text(encoding="utf-8") == "new\n"
    assert log.stat().st_mode & 0o777 == 0o600

    target = tmp_path / "target.log"
    target.write_text("protected\n", encoding="utf-8")
    link = tmp_path / "linked.log"
    link.symlink_to(target)
    rejected = _run(
        sys.executable,
        str(wrapper),
        "--log",
        str(link),
        "--",
        sys.executable,
        "-c",
        "print('unsafe')",
    )
    assert rejected.returncode != 0
    assert target.read_text(encoding="utf-8") == "protected\n"


def test_inline_fallback_seals_checkout_failure_and_rejects_corruption(
    tmp_path: Path,
) -> None:
    """Pre-checkout fallback is executable without repository files."""
    workflow = _workflow(DIAGNOSTIC_WORKFLOW)
    initialize = _steps(workflow, "node-lifecycle-diagnostic")[
        "Initialize minimal diagnostic evidence"
    ]["run"]
    match = re.search(
        r"<<'PY'\n(?P<script>.*?)\nPY(?:\n|$)", initialize, flags=re.DOTALL
    )
    assert match is not None
    fallback = tmp_path / "fallback.py"
    fallback.write_text(match.group("script") + "\n", encoding="utf-8")
    live, sealed = tmp_path / "live", tmp_path / "sealed"
    live.mkdir()
    (live / "run-id.txt").write_text("setup failed\n", encoding="utf-8")
    assert (
        _run(sys.executable, str(fallback), "seal", str(live), str(sealed)).returncode
        == 0
    )
    assert _run(sys.executable, str(fallback), "verify", str(sealed)).returncode == 0
    os.chmod(sealed / "run-id.txt", 0o644)
    (sealed / "run-id.txt").write_text("corrupt\n", encoding="utf-8")
    assert _run(sys.executable, str(fallback), "verify", str(sealed)).returncode != 0


def test_setup_failure_minimal_evidence_is_sealable(tmp_path: Path) -> None:
    """An early setup failure still has a verifiable fallback artifact."""
    live = tmp_path / "live"
    sealed = tmp_path / "sealed"
    live.mkdir()
    (live / "step-outcomes.json").write_text(
        '{"vitest":{"outcome":"failure"}}\n', encoding="utf-8"
    )
    script = Path("scripts/ci/seal_issue_1995_evidence.py").resolve()
    assert (
        _run(sys.executable, str(script), "seal", str(live), str(sealed)).returncode
        == 0
    )
    assert _run(sys.executable, str(script), "verify", str(sealed)).returncode == 0


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

    def call_boundaries(records: list[dict]) -> list[dict]:
        return [
            entry
            for entry in records
            if entry.get("phase") == "call"
            and str(entry.get("event", "")).startswith("phase.")
        ]

    passed_records = events("test_pass")
    inventories = [
        entry
        for entry in passed_records
        if entry.get("event") == "collection.inventory"
    ]
    assert len(inventories) == 1
    inventory = inventories[0]
    assert inventory["item_count"] == 1
    assert inventory["nodeids"] == sorted(inventory["nodeids"])
    encoded = ("\n".join(inventory["nodeids"]) + "\n").encode()
    assert inventory["nodeid_sha256"] == hashlib.sha256(encoded).hexdigest()

    passed = call_boundaries(passed_records)
    errored = call_boundaries(events("test_error"))
    interrupted = call_boundaries(events("test_interrupt"))
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
