"""Simulated LLM output for the ast_tests strategy.

When AST-sliced tests are provided (function signatures / call sites only,
no source implementation), the LLM regenerates `run_worker` but still omits
`_get_job_secrets` because the private helper body is absent from the context.
"""
from __future__ import annotations


def run_worker(job_id: str) -> dict:
    # _get_job_secrets not available in context — inlined naively
    return {"job_id": job_id, "secrets": {"id": job_id, "key": f"secret-{job_id}"}}
