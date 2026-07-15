"""Structural contracts for the Unit Tests GitHub Actions workflow."""

from __future__ import annotations

import math
from pathlib import Path

import yaml


WORKFLOW_PATH = Path(".github/workflows/unit-tests.yml")
SETUP_AND_FOCUSED_SECONDS = 16 * 60 + 37
BROAD_SUITE_SECONDS = 30 * 60
FULL_JOB_SECONDS = SETUP_AND_FOCUSED_SECONDS + BROAD_SUITE_SECONDS
HEADROOM_FRACTION = 0.50
REQUIRED_TIMEOUT_MINUTES = math.ceil(
    FULL_JOB_SECONDS * (1 + HEADROOM_FRACTION) / 60
)
HOSTED_SUPERVISOR_NODE = "tests/test_sync_core_supervisor.py::"
REQUIRED_HOSTED_NODES = (
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
)


def test_unit_tests_timeout_covers_documented_full_job_budget() -> None:
    """The broad-suite margin must account for required prior job work too."""
    workflow_text = WORKFLOW_PATH.read_text(encoding="utf-8")
    workflow = yaml.safe_load(workflow_text)
    timeout_minutes = workflow["jobs"]["unit-tests"]["timeout-minutes"]

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
    """Every real-chain case and prerequisite must be explicit in the hosted lane."""
    workflow_text = WORKFLOW_PATH.read_text(encoding="utf-8")

    for node in REQUIRED_HOSTED_NODES:
        assert workflow_text.count(node) == 1, node
    assert (
        "tests/test_sync_core_supervisor.py::"
        "test_real_linux_playwright_descriptor_exact_chain \\\n"
    ) not in workflow_text
    for prerequisite in (
        "sudo apt-get install --yes bubblewrap",
        "command -v bwrap",
        "command -v systemd-run",
        "command -v unshare",
        "sudo -n true",
    ):
        assert prerequisite in workflow_text
