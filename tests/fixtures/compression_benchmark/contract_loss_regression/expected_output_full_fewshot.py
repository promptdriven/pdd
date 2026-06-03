"""Simulated LLM output for the full_fewshot strategy.

When the full test file is used as a few-shot usage example (without the source
implementation), the LLM sees only how `run_worker` is called in tests.
It regenerates the public function but drops `_get_job_secrets` because the
private helper body was not in the few-shot context.
"""
from __future__ import annotations


def run_worker(job_id: str) -> dict:
    # _get_job_secrets not available in context — inlined naively
    return {"job_id": job_id, "secrets": {"id": job_id, "key": f"secret-{job_id}"}}
