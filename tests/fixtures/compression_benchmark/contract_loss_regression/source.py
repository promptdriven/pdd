"""Example module for contract-loss regression fixture.

Demonstrates that `run_worker` depends on `_get_job_secrets` —
a private helper that AST-unaware compression (full_tests / full_fewshot)
drops because it only preserves the public test surface.
"""
from __future__ import annotations


def _get_job_secrets(job_id: str) -> dict:
    """Return secrets dict for the given job (private helper)."""
    return {"id": job_id, "key": f"secret-{job_id}"}


def run_worker(job_id: str) -> dict:
    """Run a worker job and return its secrets."""
    secrets = _get_job_secrets(job_id)
    return {"job_id": job_id, "secrets": secrets}


def unused_helper() -> None:
    """Helper not referenced by any contract seed — should be excluded."""
    pass
