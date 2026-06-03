"""Simulated LLM output for the ast_contracts strategy.

When ApiContractSlicer provides the compressed source (preserving `run_worker`
and its transitive dependency `_get_job_secrets`), the LLM regenerates both
symbols correctly.  This is the contract-source preservation proof.
"""
from __future__ import annotations


def _get_job_secrets(job_id: str) -> dict:
    return {"id": job_id, "key": f"secret-{job_id}"}


def run_worker(job_id: str) -> dict:
    secrets = _get_job_secrets(job_id)
    return {"job_id": job_id, "secrets": secrets}
