"""Tests for the contract_loss_regression fixture module."""
from __future__ import annotations

from source import run_worker


def test_run_worker_returns_job_id():
    result = run_worker("job-42")
    assert result["job_id"] == "job-42"


def test_run_worker_includes_secrets():
    result = run_worker("job-99")
    assert "secrets" in result
    assert result["secrets"]["id"] == "job-99"
