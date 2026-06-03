"""Simulated LLM output for the full_tests strategy.

When only the raw test file is provided as context (no source implementation),
the LLM regenerates `run_worker` but omits `_get_job_secrets` because the
private helper body was never in its context window.
"""
from __future__ import annotations


def run_worker(job_id: str) -> dict:
    # _get_job_secrets not available in context — inlined naively
    return {"job_id": job_id, "secrets": {"id": job_id, "key": f"secret-{job_id}"}}
