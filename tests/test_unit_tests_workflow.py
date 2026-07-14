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
