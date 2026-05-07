"""Gated real-LLM smoke tests for the incremental PRD propagation flow.

These tests hit a real cloud LLM and cost real credits. They are SKIPPED
by default — set ``PDD_RUN_REAL_LLM_TESTS=1`` in the environment to enable
them.

    PDD_RUN_REAL_LLM_TESTS=1 pytest -m real tests/test_incremental_prd_architecture_real.py -v

Each test sets up a synthetic PDD project under tmp_path, invokes the real
flow against a real LLM, and asserts the architecture/prompts were updated
correctly. Total budget for the suite is ~$1.00.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
from typing import Dict

import pytest

from pdd.incremental_prd_architecture import (
    ArchitecturePatch,
    DependencyUpdate,
    ModuleToAdd,
    run_incremental_prd_propagation,
)


# Hard skip when the env var isn't set so cloud-test / general CI does not
# accidentally invoke real LLM calls and incur cost or flakiness.
pytestmark = pytest.mark.skipif(
    not os.getenv("PDD_RUN_REAL_LLM_TESTS"),
    reason="Set PDD_RUN_REAL_LLM_TESTS=1 to run real-LLM smoke tests.",
)


def _module_entry(filename: str, *, deps=None, description=None) -> Dict:
    return {
        "filename": filename,
        "reason": f"{filename} reason",
        "description": description or f"{filename} description",
        "dependencies": deps or [],
        "priority": 1,
        "filepath": f"src/{filename.replace('.prompt', '.py')}",
        "tags": ["module", "python"],
        "interface": {"type": "module"},
    }


@pytest.fixture
def synthetic_pdd_repo(tmp_path: Path) -> Dict[str, Path]:
    """Create a minimal synthetic PDD project: architecture.json + 2 prompts + a PRD."""
    docs = tmp_path / "docs"
    docs.mkdir()
    prd = docs / "prd.md"
    prd.write_text(
        "# PRD\n\n## API Layer\nAPI must route requests.\n\n"
        "## Database\nProvide a simple key-value store.\n",
        encoding="utf-8",
    )

    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "api_router_python.prompt").write_text(
        "<pdd-reason>API routing</pdd-reason>\n"
        "<pdd-interface>{}</pdd-interface>\n\n"
        "## Requirements\n\n- Route incoming HTTP requests to handlers.\n",
        encoding="utf-8",
    )
    (prompts / "database_python.prompt").write_text(
        "<pdd-reason>Persistent KV store</pdd-reason>\n"
        "<pdd-interface>{}</pdd-interface>\n\n"
        "## Requirements\n\n- Provide get/set primitives over a KV store.\n",
        encoding="utf-8",
    )

    src = tmp_path / "src"
    src.mkdir()
    (src / "api_router_python.py").write_text("def route(): pass\n", encoding="utf-8")
    (src / "database_python.py").write_text("def get(k): pass\n", encoding="utf-8")

    arch = {
        "prd_files": ["docs/prd.md"],
        "modules": [
            _module_entry("api_router_python.prompt", deps=["database_python.prompt"]),
            _module_entry("database_python.prompt"),
        ],
    }
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps(arch, indent=2), encoding="utf-8")

    return {
        "root": tmp_path,
        "prd": prd,
        "arch": arch_path,
        "prompts": prompts,
    }


def _seed_prd_snapshot(repo: Dict[str, Path], previous_text: str) -> None:
    """Write a snapshot of the previous PRD content so the next call sees a real diff."""
    import hashlib

    snap_dir = repo["root"] / ".pdd" / "meta"
    snap_dir.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256(previous_text.encode("utf-8")).hexdigest()
    snapshot = {
        "sources": {
            "docs/prd.md": {
                "content": previous_text,
                "hash": digest,
            }
        }
    }
    (snap_dir / "prd_hashes.json").write_text(json.dumps(snapshot, indent=2), encoding="utf-8")


@pytest.mark.real
def test_real_incremental_add_module(synthetic_pdd_repo, capsys):
    """PRD v1 → v2 adds an audit-logging requirement → expect a new module."""
    repo = synthetic_pdd_repo
    previous_prd = repo["prd"].read_text(encoding="utf-8")
    _seed_prd_snapshot(repo, previous_prd)

    repo["prd"].write_text(
        previous_prd + "\n## Audit Logging\nAll API mutations must emit audit events.\n",
        encoding="utf-8",
    )

    success, message, cost, model, changed_files = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=repo["arch"],
        prompts_dir=repo["prompts"],
        project_root=repo["root"],
        quiet=True,
    )

    print(f"[real-add] success={success} cost=${cost:.4f} model={model}")
    print(f"[real-add] message={message}")
    assert success, f"propagation failed: {message}"
    assert cost < 2.0, f"cost {cost} exceeded $2 budget"

    arch = json.loads(repo["arch"].read_text(encoding="utf-8"))
    names = [m["filename"] for m in arch["modules"]]
    assert "api_router_python.prompt" in names
    assert "database_python.prompt" in names
    assert len(names) >= 3, f"expected at least one new module, got {names}"

    for prompt_file in repo["prompts"].glob("*.prompt"):
        text = prompt_file.read_text(encoding="utf-8")
        assert "<pdd-" in text, f"{prompt_file.name} lost <pdd-*> tags"

    snap = json.loads((repo["root"] / ".pdd" / "meta" / "prd_hashes.json").read_text(encoding="utf-8"))
    previous_hash = hashlib.sha256(previous_prd.encode("utf-8")).hexdigest()
    assert snap["sources"]["docs/prd.md"]["hash"] != previous_hash


@pytest.mark.real
def test_real_incremental_modify_only(synthetic_pdd_repo, capsys):
    """PRD scope-only change on an existing module; expect description/Requirements update, no new module."""
    repo = synthetic_pdd_repo
    previous_prd = repo["prd"].read_text(encoding="utf-8")
    _seed_prd_snapshot(repo, previous_prd)

    new_prd = previous_prd.replace(
        "API must route requests.",
        "API must route requests and validate request bodies against a JSON schema.",
    )
    assert new_prd != previous_prd
    repo["prd"].write_text(new_prd, encoding="utf-8")

    arch_before = json.loads(repo["arch"].read_text(encoding="utf-8"))
    api_before = next(m for m in arch_before["modules"] if m["filename"] == "api_router_python.prompt")
    db_prompt_before = (repo["prompts"] / "database_python.prompt").read_text(encoding="utf-8")
    api_prompt_before = (repo["prompts"] / "api_router_python.prompt").read_text(encoding="utf-8")

    success, message, cost, model, changed_files = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=repo["arch"],
        prompts_dir=repo["prompts"],
        project_root=repo["root"],
        quiet=True,
    )

    print(f"[real-modify] success={success} cost=${cost:.4f} model={model}")
    print(f"[real-modify] message={message}")
    assert cost < 2.0, f"cost {cost} exceeded $2 budget"

    if not success:
        # The LLM is allowed to refuse the patch and surface conflicts for
        # human review on a scope-only PRD edit (this is the conservative
        # path through `PatchConflict`). Treat that as a valid outcome and
        # assert no destructive writes occurred.
        assert (
            "conflicts" in message.lower()
            or "full regeneration" in message.lower()
            or "validation" in message.lower()
        ), f"unexpected failure mode: {message}"
        api_prompt_after = (repo["prompts"] / "api_router_python.prompt").read_text(encoding="utf-8")
        db_prompt_after = (repo["prompts"] / "database_python.prompt").read_text(encoding="utf-8")
        assert api_prompt_after == api_prompt_before, "router prompt should not change on conflict"
        assert db_prompt_after == db_prompt_before, "database prompt should not change on conflict"
        return

    arch_after = json.loads(repo["arch"].read_text(encoding="utf-8"))
    names_after = [m["filename"] for m in arch_after["modules"]]
    assert set(names_after) == {"api_router_python.prompt", "database_python.prompt"}, (
        f"expected no module additions, got {names_after}"
    )

    api_after = next(m for m in arch_after["modules"] if m["filename"] == "api_router_python.prompt")
    api_prompt_after = (repo["prompts"] / "api_router_python.prompt").read_text(encoding="utf-8")
    db_prompt_after = (repo["prompts"] / "database_python.prompt").read_text(encoding="utf-8")

    arch_changed = api_after.get("description") != api_before.get("description")
    requirements_changed = api_prompt_after != api_prompt_before
    assert arch_changed or requirements_changed, (
        "expected at least one of: api_router description in architecture or api_router prompt to change"
    )
    assert db_prompt_after == db_prompt_before, "database prompt should be untouched"


@pytest.mark.real
def test_real_incremental_retry_after_bad_patch(synthetic_pdd_repo, monkeypatch, capsys):
    """Hybrid: first patch is hand-crafted invalid (unknown dep). Second call hits real LLM and must recover."""
    from pdd import incremental_prd_architecture as ipa

    repo = synthetic_pdd_repo
    previous_prd = repo["prd"].read_text(encoding="utf-8")
    _seed_prd_snapshot(repo, previous_prd)

    repo["prd"].write_text(
        previous_prd + "\n## Audit Logging\nAll API mutations must emit audit events.\n",
        encoding="utf-8",
    )

    real_ask = ipa._ask_llm_for_patch
    call_count = {"n": 0}
    seen_validation_errors = []

    bad_patch = ArchitecturePatch(
        dependency_updates=[
            DependencyUpdate(
                source="api_router_python.prompt",
                add=["nonexistent_module_python.prompt"],
                justification="forced-bad first attempt",
            )
        ]
    )

    def hybrid_ask(**kwargs):
        seen_validation_errors.append(list(kwargs.get("validation_errors", [])))
        call_count["n"] += 1
        if call_count["n"] == 1:
            return bad_patch, 0.0, "fake-bad-patch-model"
        return real_ask(**kwargs)

    monkeypatch.setattr(ipa, "_ask_llm_for_patch", hybrid_ask)

    success, message, cost, model, changed_files = run_incremental_prd_propagation(
        "docs/prd.md",
        architecture_path=repo["arch"],
        prompts_dir=repo["prompts"],
        project_root=repo["root"],
        quiet=True,
        max_patch_attempts=3,
    )

    print(f"[real-retry] success={success} cost=${cost:.4f} model={model} attempts={call_count['n']}")
    print(f"[real-retry] validation_errors_seen={seen_validation_errors}")
    print(f"[real-retry] message={message}")

    assert call_count["n"] >= 2, "real LLM was never called for retry"
    assert success, f"retry path failed: {message}"
    assert cost < 2.0, f"cost {cost} exceeded $2 budget"

    assert seen_validation_errors[0] == []
    assert seen_validation_errors[1], "second attempt did not receive validation errors"
    assert any("nonexistent_module_python.prompt" in err for err in seen_validation_errors[1])
