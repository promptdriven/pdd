"""Simulated LLM output for the compressed_fewshot strategy.

When AST-contracted source (preserving `_get_job_secrets` as a transitive
dependency) is concatenated with compressed tests, the LLM sees all required
symbols and regenerates both correctly.
"""
from __future__ import annotations


def _get_job_secrets(job_id: str) -> dict:
    return {"id": job_id, "key": f"secret-{job_id}"}


def run_worker(job_id: str) -> dict:
    secrets = _get_job_secrets(job_id)
    return {"job_id": job_id, "secrets": secrets}
