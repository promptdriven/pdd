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
SETUP_AND_FOCUSED_SECONDS = 16 * 60 + 37
BROAD_SUITE_SECONDS = 30 * 60
FULL_JOB_SECONDS = SETUP_AND_FOCUSED_SECONDS + BROAD_SUITE_SECONDS
HEADROOM_FRACTION = 0.50
REQUIRED_TIMEOUT_MINUTES = math.ceil(
    FULL_JOB_SECONDS * (1 + HEADROOM_FRACTION) / 60
)
LINUX_JOB_ID = "unit-tests"
PROVISION_STEP_NAME = "Provision and verify protected Linux sandbox"
HOSTED_STEP_NAME = "Run real protected Playwright and authenticated supervisor protocols"
HOSTED_SUPERVISOR_NODE = "tests/test_sync_core_supervisor.py::"
REQUIRED_HOSTED_NODES = frozenset((
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
    "tests/test_sync_core_supervisor.py::"
    "test_simultaneous_high_volume_stdio_has_one_aggregate_bound",
))


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
    """Parse active POSIX shell commands, excluding comments and quoted text."""
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


def _assert_hosted_linux_contract(workflow: dict) -> None:
    """Check the exact active hosted Linux command and prerequisites."""
    jobs = workflow.get("jobs")
    assert isinstance(jobs, dict)
    job = jobs.get(LINUX_JOB_ID)
    assert isinstance(job, dict)
    assert job.get("runs-on") == "ubuntu-latest"

    provision = _named_step(job, PROVISION_STEP_NAME)
    provision_commands = _shell_commands(provision.get("run"))
    for command in (
        ("sudo", "apt-get", "install", "--yes", "bubblewrap"),
        ("command", "-v", "bwrap"),
        ("command", "-v", "systemd-run"),
        ("command", "-v", "unshare"),
        ("sudo", "-n", "true"),
    ):
        assert command in provision_commands, command

    hosted = _named_step(job, HOSTED_STEP_NAME)
    hosted_commands = _shell_commands(hosted.get("run"))
    pytest_commands = [
        command for command in hosted_commands if command and command[0] == "pytest"
    ]
    assert len(pytest_commands) == 1
    active_nodes = tuple(
        token for token in pytest_commands[0]
        if token.startswith("tests/") and "::" in token
    )
    assert len(active_nodes) == len(set(active_nodes)), active_nodes
    assert frozenset(active_nodes) == REQUIRED_HOSTED_NODES


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


def test_unit_tests_requires_complete_privileged_descriptor_matrix() -> None:
    """The active hosted Linux lane has one exact frozen pytest node set."""
    _assert_hosted_linux_contract(_workflow())


def _append_hosted_node(command: str, node: str) -> str:
    """Append one active node before the pytest timeout argument."""
    return command.replace("--timeout=90", f"{node} \\\n            --timeout=90")


@pytest.mark.parametrize(
    "mutate",
    (
        lambda command: command.replace(
            "tests/test_sync_core_supervisor.py::"
            "test_real_linux_playwright_descriptor_exact_chain[parent-exit-before-start]",
            "# tests/test_sync_core_supervisor.py::"
            "test_real_linux_playwright_descriptor_exact_chain[parent-exit-before-start]",
        ),
        lambda command: _append_hosted_node(
            command,
            "tests/test_sync_core_supervisor.py::"
            "test_real_linux_playwright_descriptor_exact_chain[missing-ack]",
        ),
        lambda command: _append_hosted_node(
            command, "tests/test_sync_core_supervisor.py::unexpected_hosted_case",
        ),
    ),
    ids=("commented", "duplicated", "unexpected"),
)
def test_unit_tests_hosted_contract_rejects_node_mutations(
    mutate: Callable[[str], str],
) -> None:
    """Comments, duplicate nodes, and additions cannot weaken the hosted lane."""
    workflow = _workflow()
    job = workflow["jobs"][LINUX_JOB_ID]
    hosted = _named_step(job, HOSTED_STEP_NAME)
    hosted["run"] = mutate(hosted["run"])

    with pytest.raises(AssertionError):
        _assert_hosted_linux_contract(workflow)


def test_unit_tests_hosted_contract_rejects_commented_prerequisite() -> None:
    """A provisioning comment cannot satisfy the active Linux prerequisite contract."""
    workflow = _workflow()
    job = workflow["jobs"][LINUX_JOB_ID]
    provision = _named_step(job, PROVISION_STEP_NAME)
    provision["run"] = provision["run"].replace("sudo -n true", "# sudo -n true")

    with pytest.raises(AssertionError):
        _assert_hosted_linux_contract(workflow)
