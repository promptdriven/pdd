"""Structural contracts for the Unit Tests GitHub Actions workflow."""

from __future__ import annotations

import math
import re
import shlex
from collections.abc import Callable
from pathlib import Path

import pytest
import yaml


WORKFLOW_PATH = Path(".github/workflows/unit-tests.yml")
NODE_DIAGNOSTIC_WORKFLOW_PATH = Path(
    ".github/workflows/1995-node-diagnostic.yml"
)
SETUP_AND_FOCUSED_SECONDS = 16 * 60 + 37
BROAD_SUITE_SECONDS = 30 * 60
FULL_JOB_SECONDS = SETUP_AND_FOCUSED_SECONDS + BROAD_SUITE_SECONDS
HEADROOM_FRACTION = 0.50
REQUIRED_TIMEOUT_MINUTES = math.ceil(
    FULL_JOB_SECONDS * (1 + HEADROOM_FRACTION) / 60
)
LINUX_JOB_ID = "unit-tests"
APPROVED_DRAFT_GUARD = "github.event.pull_request.draft != true"
PROVISION_STEP_NAME = "Provision and verify protected Linux sandbox"
HOSTED_STEP_NAME = "Run real protected Playwright and authenticated supervisor protocols"
HOSTED_SUPERVISOR_NODE = "tests/test_sync_core_supervisor.py::"
REQUIRED_HOSTED_NODES = (
    "tests/test_sync_core_runner_playwright.py::"
    "test_real_playwright_1_55_config_suffixes_collect_and_use_config_dir",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_authenticated_termination_and_cleanup",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_adapter_environment_handoff[pytest]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_adapter_environment_handoff[vitest]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_adapter_environment_handoff[playwright]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[normal-hierarchy-environment]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[parent-exit-before-start]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[parent-exit-during-execution]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[parent-exit-after-result]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[stalled-result-reader]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[missing-ack]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[duplicate-ack]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[trailing-frame]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[trailing-raw]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[reordered-extra]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[stalled-observation-reader]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[initial-scan-failure]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[initial-watched-assertion-failure]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[fd-only-namespace-holder-cleanup]",
    "tests/test_sync_core_supervisor.py::"
    "test_simultaneous_high_volume_stdio_has_one_aggregate_bound",
)
EXPECTED_PROVISION_COMMANDS = (
    ("set", "-euo", "pipefail"),
    ("sudo", "apt-get", "update"),
    ("sudo", "apt-get", "install", "--yes", "bubblewrap"),
    ("command", "-v", "bwrap"),
    ("command", "-v", "systemd-run"),
    ("command", "-v", "unshare"),
    ("command", "-v", "nsenter"),
    ("sudo", "-n", "true"),
    ("bwrap", "--version"),
)
EXPECTED_HOSTED_COMMAND = (
    "pytest", "-q", *REQUIRED_HOSTED_NODES, "--timeout=90",
)
DIAGNOSTIC_FILES = (
    "tests/test_sync_core_supervisor.py",
    "tests/test_sync_core_runner.py",
    "tests/test_sync_core_trust.py",
    "tests/test_sync_core_lifecycle_scenarios.py",
    "tests/test_sync_core_reporting.py",
    "tests/test_sync_core_runner_playwright.py",
)


def _workflow() -> dict:
    """Load the workflow with YAML semantics, never comment-sensitive text matching."""
    loaded = yaml.safe_load(WORKFLOW_PATH.read_text(encoding="utf-8"))
    assert isinstance(loaded, dict)
    return loaded


def _named_step(job: dict, name: str) -> dict:
    """Return exactly one active, stable-named workflow step."""
    steps = job.get("steps")
    assert isinstance(steps, list)
    matches = [step for step in steps if isinstance(step, dict) and step.get("name") == name]
    assert len(matches) == 1, name
    return matches[0]


def _shell_commands(command: object) -> tuple[tuple[str, ...], ...]:
    """Parse top-level shell lines while excluding comments and heredoc bodies."""
    assert isinstance(command, str)
    commands = []
    continuation = ""
    heredoc_end = None
    for line in command.splitlines():
        if heredoc_end is not None:
            if line == heredoc_end:
                heredoc_end = None
            continue
        current = continuation + line
        if current.rstrip().endswith("\\"):
            continuation = current.rstrip()[:-1] + " "
            continue
        continuation = ""
        tokens = tuple(shlex.split(current, comments=True, posix=True))
        if not tokens:
            continue
        commands.append(tokens)
        marker = re.search(r"<<-?\s*['\"]?([A-Za-z_][A-Za-z0-9_]*)", current)
        if marker:
            heredoc_end = marker.group(1)
    assert heredoc_end is None
    assert not continuation
    return tuple(commands)


def _assert_enabled(subject: dict) -> None:
    """Require unconditional execution with ordinary failure propagation."""
    assert "if" not in subject
    assert "continue-on-error" not in subject


def _diagnostic_workflow() -> dict:
    """Load the temporary issue-1995 diagnostic workflow."""
    loaded = yaml.safe_load(
        NODE_DIAGNOSTIC_WORKFLOW_PATH.read_text(encoding="utf-8")
    )
    assert isinstance(loaded, dict)
    return loaded


def _assert_approved_draft_guard(job: dict) -> None:
    """Require the reviewed job-level draft guard without equivalent rewrites."""
    assert job.get("if") == APPROVED_DRAFT_GUARD
    assert "continue-on-error" not in job


def _assert_hosted_linux_contract(workflow: dict) -> None:
    """Check the exact active hosted Linux command and prerequisites."""
    jobs = workflow.get("jobs")
    assert isinstance(jobs, dict)
    job = jobs.get(LINUX_JOB_ID)
    assert isinstance(job, dict)
    assert job.get("runs-on") == "ubuntu-latest"
    _assert_approved_draft_guard(job)

    steps = job.get("steps")
    assert isinstance(steps, list)
    provision = _named_step(job, PROVISION_STEP_NAME)
    hosted = _named_step(job, HOSTED_STEP_NAME)
    assert steps.index(provision) < steps.index(hosted)
    _assert_enabled(provision)
    _assert_enabled(hosted)

    provision_commands = _shell_commands(provision.get("run"))
    assert provision_commands[:len(EXPECTED_PROVISION_COMMANDS)] == (
        EXPECTED_PROVISION_COMMANDS
    )

    hosted_commands = _shell_commands(hosted.get("run"))
    assert hosted_commands == (EXPECTED_HOSTED_COMMAND,)
    pytest_command = hosted_commands[0]
    selectors = []
    for argument in pytest_command[1:]:
        if argument in {"-q", "--timeout=90"}:
            continue
        assert not argument.startswith("-"), argument
        selectors.append(argument)
    assert tuple(selectors) == REQUIRED_HOSTED_NODES
    assert len(selectors) == len(set(selectors))


def _hosted_command(workflow: dict) -> tuple[dict, str]:
    job = workflow["jobs"][LINUX_JOB_ID]
    hosted = _named_step(job, HOSTED_STEP_NAME)
    return hosted, hosted["run"]


def _append_hosted_argument(command: str, argument: str) -> str:
    """Append one active argument before the frozen pytest timeout argument."""
    return command.replace("--timeout=90", f"{argument} \\\n            --timeout=90")


def _remove_hosted_node_line(command: str) -> str:
    """Physically remove one complete required selector line."""
    node = REQUIRED_HOSTED_NODES[6]
    lines = command.splitlines(keepends=True)
    matches = [index for index, line in enumerate(lines) if node in line]
    assert len(matches) == 1
    del lines[matches[0]]
    mutated = "".join(lines)
    assert mutated != command and node not in mutated
    return mutated


def test_unit_tests_timeout_covers_documented_full_job_budget() -> None:
    """The broad-suite margin must account for required prior job work too."""
    workflow_text = WORKFLOW_PATH.read_text(encoding="utf-8")
    timeout_minutes = _workflow()["jobs"][LINUX_JOB_ID]["timeout-minutes"]

    assert isinstance(timeout_minutes, int)
    assert timeout_minutes > 0
    assert timeout_minutes >= REQUIRED_TIMEOUT_MINUTES, (
        "Unit Tests timeout must cover the 16m37s setup/protected/browser budget "
        "plus the ~30 minute broad suite with 50% headroom "
        f"({REQUIRED_TIMEOUT_MINUTES} minutes minimum)."
    )
    assert "16m37s" in workflow_text
    assert "~30 minutes" in workflow_text
    assert "46m37s" in workflow_text
    assert "50% headroom" in workflow_text


def test_issue_1995_node_diagnostic_workflow_contract() -> None:
    """The disposable diagnostic is bounded, attributable, and evidence preserving."""
    workflow = _diagnostic_workflow()
    triggers = workflow["on"]
    assert set(triggers) == {"push", "pull_request", "workflow_dispatch"}
    assert triggers["push"] == {"branches": ["main"]}
    assert triggers["pull_request"] == {
        "branches": ["main"],
        "types": ["opened", "synchronize", "reopened", "ready_for_review"],
    }
    assert triggers["workflow_dispatch"] is None
    assert workflow.get("permissions") == {"contents": "read"}

    jobs = workflow["jobs"]
    assert list(jobs) == ["node-lifecycle-diagnostic"]
    job = jobs["node-lifecycle-diagnostic"]
    assert job["if"] == (
        "github.event_name != 'pull_request' || github.event.pull_request.draft == true"
    )
    assert job["runs-on"] == "ubuntu-latest"
    assert job["timeout-minutes"] == 25
    assert "permissions" not in job

    steps = job["steps"]
    checkout = _named_step(job, "Check out the recorded source")
    assert checkout["uses"] == "actions/checkout@v4"
    assert checkout["with"] == {"persist-credentials": False}

    diagnostic = _named_step(job, "Run the bounded lifecycle diagnostic once")
    assert diagnostic["id"] == "diagnostic"
    assert diagnostic["continue-on-error"] is True
    command = diagnostic["run"]
    assert isinstance(command, str)
    assert command.count("timeout --signal=INT --kill-after=30s 900s") == 1
    assert command.count("pytest -vv --capture=tee-sys") == 1
    assert "--timeout=60 --timeout-method=signal" in command
    assert "-p pytest_lifecycle_jsonl" in command
    assert command.count(" >\"$EVIDENCE_DIR/pytest.log\" 2>&1") == 1
    assert "| tee" not in command
    assert "PIPESTATUS" not in command
    for selected in DIAGNOSTIC_FILES:
        assert command.count(selected) == 1
    assert "PDD_PYTEST_LIFECYCLE_JSONL" in command
    assert "GITHUB_SHA" in command
    assert "sha256sum" in command
    assert "sort -z" in command
    assert "system-before.txt" in command
    assert "system-after.txt" in command

    upload = _named_step(job, "Always upload collision-safe diagnostic evidence")
    assert upload["if"] == "always()"
    assert upload["uses"] == "actions/upload-artifact@v4"
    assert upload["with"]["name"] == (
        "issue-1995-${{ github.run_id }}-${{ github.run_attempt }}-${{ github.sha }}"
    )
    assert upload["with"]["if-no-files-found"] == "error"
    assert upload["with"]["path"] == "${{ runner.temp }}/issue-1995-evidence"

    propagate = _named_step(job, "Propagate the diagnostic result")
    assert propagate["if"] == "steps.diagnostic.outcome == 'failure'"
    assert _shell_commands(propagate["run"]) == (("exit", "1"),)

    plugin = Path("scripts/ci/pytest_lifecycle_jsonl.py").read_text(encoding="utf-8")
    for hook in (
        "pytest_sessionstart",
        "pytest_sessionfinish",
        "pytest_collection_start",
        "pytest_collection_finish",
        "pytest_runtest_logstart",
        "pytest_runtest_logfinish",
        "pytest_runtest_setup",
        "pytest_runtest_call",
        "pytest_runtest_teardown",
    ):
        assert f"def {hook}(" in plugin
    assert "os.fsync" in plugin
    assert "flush()" in plugin


def test_unit_tests_requires_complete_privileged_descriptor_matrix() -> None:
    """The active hosted Linux lane has one exact frozen pytest node set."""
    _assert_hosted_linux_contract(_workflow())


def test_unit_tests_protected_smokes_use_credential_free_environment() -> None:
    """Hosted protected setup never forwards the runner's ambient credentials."""
    workflow_text = WORKFLOW_PATH.read_text(encoding="utf-8")

    assert "env=dict(os.environ)" not in workflow_text
    assert workflow_text.count("env=environment") == 10


@pytest.mark.parametrize(
    "mutate",
    (
        lambda command: command.replace(
            REQUIRED_HOSTED_NODES[6], "# " + REQUIRED_HOSTED_NODES[6]
        ),
        lambda command: _append_hosted_argument(command, REQUIRED_HOSTED_NODES[10]),
        lambda command: _append_hosted_argument(
            command, "tests/test_sync_core_supervisor.py::unexpected_hosted_case"
        ),
        _remove_hosted_node_line,
        lambda command: _append_hosted_argument(command, "-k parent-exit"),
        lambda command: _append_hosted_argument(
            command, "tests/test_sync_core_supervisor.py"
        ),
    ),
    ids=("commented", "duplicated", "unexpected", "removed", "k", "file-selector"),
)
def test_unit_tests_hosted_contract_rejects_selector_mutations(
    mutate: Callable[[str], str],
) -> None:
    """Every selection change must invalidate the exact hosted command."""
    workflow = _workflow()
    hosted, command = _hosted_command(workflow)
    mutated = mutate(command)
    assert mutated != command
    hosted["run"] = mutated

    with pytest.raises(AssertionError):
        _assert_hosted_linux_contract(workflow)


@pytest.mark.parametrize(
    "mutated_guard",
    (None, False, "github.event.pull_request.draft == false"),
    ids=("removed", "false", "altered"),
)
def test_unit_tests_hosted_contract_rejects_draft_guard_mutations(
    mutated_guard: object,
) -> None:
    """The reviewed draft guard must remain exactly attached to the unit-test job."""
    workflow = _workflow()
    job = workflow["jobs"][LINUX_JOB_ID]
    if mutated_guard is None:
        del job["if"]
    else:
        job["if"] = mutated_guard

    with pytest.raises(AssertionError):
        _assert_hosted_linux_contract(workflow)


@pytest.mark.parametrize(
    ("subject", "field", "value"),
    (
        ("provision", "if", False),
        ("hosted", "if", False),
        ("provision", "continue-on-error", True),
        ("hosted", "continue-on-error", True),
    ),
)
def test_unit_tests_hosted_contract_rejects_disabling_semantics(
    subject: str, field: str, value: object,
) -> None:
    """Critical steps must stay unconditional and failure-propagating."""
    workflow = _workflow()
    job = workflow["jobs"][LINUX_JOB_ID]
    targets = {
        "job": job,
        "provision": _named_step(job, PROVISION_STEP_NAME),
        "hosted": _named_step(job, HOSTED_STEP_NAME),
    }
    targets[subject][field] = value

    with pytest.raises(AssertionError):
        _assert_hosted_linux_contract(workflow)


def test_unit_tests_hosted_contract_rejects_reordered_steps() -> None:
    """Provisioning must execute before the hosted privileged test command."""
    workflow = _workflow()
    steps = workflow["jobs"][LINUX_JOB_ID]["steps"]
    provision = _named_step(workflow["jobs"][LINUX_JOB_ID], PROVISION_STEP_NAME)
    hosted = _named_step(workflow["jobs"][LINUX_JOB_ID], HOSTED_STEP_NAME)
    first, second = steps.index(provision), steps.index(hosted)
    steps[first], steps[second] = steps[second], steps[first]

    with pytest.raises(AssertionError):
        _assert_hosted_linux_contract(workflow)


def test_unit_tests_hosted_contract_rejects_dead_branch_prerequisite() -> None:
    """A prerequisite hidden in a dead shell branch is not top-level active setup."""
    workflow = _workflow()
    provision = _named_step(workflow["jobs"][LINUX_JOB_ID], PROVISION_STEP_NAME)
    active = "sudo apt-get install --yes bubblewrap"
    dead = f"if false; then\n          {active}\n          fi"
    provision["run"] = provision["run"].replace(active, dead)

    with pytest.raises(AssertionError):
        _assert_hosted_linux_contract(workflow)


def test_unit_tests_hosted_contract_rejects_commented_prerequisite() -> None:
    """A provisioning comment cannot satisfy the active Linux prerequisite contract."""
    workflow = _workflow()
    provision = _named_step(workflow["jobs"][LINUX_JOB_ID], PROVISION_STEP_NAME)
    provision["run"] = provision["run"].replace("sudo -n true", "# sudo -n true")

    with pytest.raises(AssertionError):
        _assert_hosted_linux_contract(workflow)
