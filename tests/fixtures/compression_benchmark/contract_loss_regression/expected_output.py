"""Expected output for the contract_loss_regression fixture.

This represents the ideal regenerated module that preserves both the public
contract symbol `run_worker` and its private helper `_get_job_secrets`.
"""
from __future__ import annotations


def _get_job_secrets(job_id: str) -> dict:
    return {"id": job_id, "key": f"secret-{job_id}"}


def run_worker(job_id: str) -> dict:
    secrets = _get_job_secrets(job_id)
    return {"job_id": job_id, "secrets": secrets}
