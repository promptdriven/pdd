"""Runnable demo for API contract slicing (#875).

Human verification::

    conda activate pdd
    cd /path/to/pdd
    python context/api_contract_slicer_example.py

Expect output containing ``_get_job_secrets`` and ``run_worker`` (not the full module).
"""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from pdd.api_contract_slicer import ApiContractSlicer

MODULE = """
import os

def _get_job_secrets(job_id: str) -> dict:
    return {"id": job_id}

def run_worker(job_id: str) -> dict:
    return _get_job_secrets(job_id)

def unused_helper() -> None:
    pass
"""


def main() -> None:
    slicer = ApiContractSlicer(MODULE, file_path="worker.py")
    output, manifest = slicer.slice(["run_worker"])
    print(output)
    print("Included:", ", ".join(manifest.included_symbols))
    assert "_get_job_secrets" in manifest.included_symbols
    assert "unused_helper" not in output
    print("\nSTEP_COMPLETE:api_contract_slicer_example")


if __name__ == "__main__":
    main()
