from __future__ import annotations

import pytest

from pdd.api_contract_slicer import ApiContractSlicer, ContractSlicerError
from pdd.content_selector import ContentSelector, SelectorError


MODULE_SOURCE = '''
import os
from typing import Optional

WORKER_STATE = "idle"

def _get_job_secrets(job_id: str) -> dict:
    return {"id": job_id}

def _monotonic() -> int:
    return _get_job_secrets("x").get("ts", 0)

class WorkerState:
    def __init__(self) -> None:
        self.value = WORKER_STATE

def run_worker(job_id: str) -> WorkerState:
    secrets = _get_job_secrets(job_id)
    _monotonic()
    return WorkerState()
'''

TEST_SOURCE = '''
from unittest.mock import patch
from myapp.worker import run_worker, WorkerState

@patch("myapp.worker._get_job_secrets")
def test_run_worker(mock_secrets):
    mock_secrets.return_value = {"id": "1"}
    result = run_worker("1")
    assert isinstance(result, WorkerState)
'''


def test_slice_includes_private_dependencies():
    slicer = ApiContractSlicer(MODULE_SOURCE, file_path="worker.py")
    output, manifest = slicer.slice(["run_worker"])
    assert "_get_job_secrets" in manifest.included_symbols
    assert "_monotonic" in manifest.included_symbols
    assert "WorkerState" in manifest.included_symbols
    assert "def _get_job_secrets" in output
    ApiContractSlicer.verify_contract(output, manifest.included_symbols)


def test_seeds_from_test_patch_targets():
    seeds = ApiContractSlicer.seeds_from_test(TEST_SOURCE, "myapp.worker")
    assert "_get_job_secrets" in seeds
    assert "run_worker" in seeds


def test_verify_contract_missing_symbol():
    with pytest.raises(ContractSlicerError, match="missing symbols"):
        ApiContractSlicer.verify_contract("def foo(): pass\n", ["missing_fn"])


def test_slice_preserves_required_imports():
    """Import drift: kept helpers must retain imports their bodies reference."""
    source = """
import os

def _helper(path: str) -> str:
    return os.path.join(path, "x")

def public_api() -> str:
    return _helper("a")
"""
    slicer = ApiContractSlicer(source, file_path="api.py")
    output, manifest = slicer.slice(["public_api"])
    assert "import os" in output
    assert manifest.included_imports == ["import os"]
    ApiContractSlicer.verify_contract(output, manifest.included_symbols)


def test_slice_raises_when_seed_missing():
    with pytest.raises(ContractSlicerError, match="Seed symbol 'missing' not found"):
        ApiContractSlicer("def foo(): pass\n", file_path="mod.py").slice(["missing"])


def test_seeds_from_test_then_slice():
    seeds = ApiContractSlicer.seeds_from_test(TEST_SOURCE, "myapp.worker")
    output, manifest = ApiContractSlicer(MODULE_SOURCE, file_path="worker.py").slice(seeds)
    assert "_get_job_secrets" in manifest.included_symbols
    assert "def _get_job_secrets" in output


def test_content_selector_contract_kind():
    out = ContentSelector.select(MODULE_SOURCE, "contract:run_worker", file_path="worker.py")
    assert "def run_worker" in out
    assert "_get_job_secrets" in out


def test_content_selector_contract_invalid_kind_message():
    with pytest.raises(SelectorError, match="contract"):
        ContentSelector.select(MODULE_SOURCE, "contracts:run_worker", file_path="worker.py")
