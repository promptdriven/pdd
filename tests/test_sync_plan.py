"""Focused contracts for the deterministic Agentic Sync V1 planner."""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from pdd.resolved_sync_unit import resolve_sync_unit
from pdd.agentic_sync import _load_fallback_scope_execution
from pdd.agentic_sync_runner import AsyncSyncRunner
from pdd.json_atomic import atomic_write_json
from pdd.sync_plan import (
    AmbiguousSyncModuleError,
    PlanProvenance,
    SyncPlanCandidate,
    SyncPlanDetails,
    SyncPlanError,
    ambiguity_request,
    apply_ambiguity_selection,
    build_sync_plan,
    canonical_module_id,
    plan_digest,
    validate_explicit_scope_evidence,
    resolve_selection_aliases,
    selection_digest,
    validate_explicit_scope,
)


def _candidate(root: Path, module_id: str, *, dependencies: tuple[str, ...] = ()) -> SyncPlanCandidate:
    target = module_id.rsplit("/", 1)[-1]
    cwd = root / Path(*module_id.split("/")[:-1])
    cwd.mkdir(parents=True, exist_ok=True)
    prompt = cwd / "prompts" / f"{target}_python.prompt"
    prompt.parent.mkdir(parents=True, exist_ok=True)
    prompt.write_text("prompt", encoding="utf-8")
    unit = resolve_sync_unit(module_id, target, cwd)
    return SyncPlanCandidate(
        module_id=module_id,
        unit=unit,
        prompt_paths=(prompt,),
        output_paths=(cwd / "pdd" / f"{target}.py",),
        details=SyncPlanDetails(
            changed_reason="PDD_CHANGED_MODULES",
            expected_operation="generate",
            confidence="high",
            provenance=(PlanProvenance("PDD_CHANGED_MODULES", module_id),),
        ),
        dependencies=dependencies,
    )


def test_sync_plan_serialization_and_digests_are_deterministic(tmp_path: Path) -> None:
    backend = _candidate(tmp_path, "backend/service")
    api = _candidate(tmp_path, "api/routes", dependencies=("backend/service",))
    first = build_sync_plan(tmp_path, [api, backend], ["api/routes", "backend/service"])
    second = build_sync_plan(tmp_path, [backend, api], ["backend/service", "api/routes"])

    assert first.serialized() == second.serialized()
    assert first.sync_plan_digest == second.sync_plan_digest
    assert first.selection_digest == selection_digest(["api/routes", "backend/service"])
    evidence = first.to_dict()
    assert evidence["candidates"][0]["provenance"]
    assert first.dependency_order == ("backend/service", "api/routes")


def test_ambiguous_alias_only_accepts_path_qualified_candidate(tmp_path: Path) -> None:
    candidates = [_candidate(tmp_path, "api/page"), _candidate(tmp_path, "web/page")]
    with pytest.raises(AmbiguousSyncModuleError) as error:
        resolve_selection_aliases(["page"], candidates)
    assert error.value.candidates == ("api/page", "web/page")
    assert resolve_selection_aliases(["web/page"], candidates) == ("web/page",)


def test_ambiguity_agent_protocol_is_bounded_and_rejects_invention(tmp_path: Path) -> None:
    candidates = [_candidate(tmp_path, "api/page"), _candidate(tmp_path, "web/page")]
    plan = build_sync_plan(tmp_path, candidates, [])
    request = ambiguity_request(plan, ["api/page", "web/page"])
    assert request["candidate_ids"] == ["api/page", "web/page"]
    assert "command_args" not in request

    with pytest.raises(SyncPlanError, match="invented or invalid"):
        apply_ambiguity_selection(plan, ["api/page", "web/page"], ["outside/module"])
    selected = apply_ambiguity_selection(plan, ["api/page", "web/page"], ["web/page"])
    assert selected.selected_module_ids == ("web/page",)


def test_fallback_scope_must_match_frozen_plan_and_digests(tmp_path: Path) -> None:
    candidate = _candidate(tmp_path, "frontend/profile")
    plan = build_sync_plan(tmp_path, [candidate], ["frontend/profile"])
    scope = {
        "module_id_encoding": "pdd.module-id-list.v1",
        "module_ids": ["frontend/profile"],
        "sync_plan_digest": plan.sync_plan_digest,
        "selection_digest": selection_digest(["frontend/profile"]),
    }
    assert validate_explicit_scope(plan, scope) == ("frontend/profile",)
    scope["module_ids"] = ["outside/profile"]
    scope["selection_digest"] = selection_digest(["outside/profile"])
    with pytest.raises(SyncPlanError, match="stale or extra"):
        validate_explicit_scope(plan, scope)


def test_persisted_primary_evidence_binds_fallback_scope(tmp_path: Path) -> None:
    backend = _candidate(tmp_path, "backend/service")
    frontend = _candidate(
        tmp_path, "frontend/profile", dependencies=("backend/service",)
    )
    plan = build_sync_plan(tmp_path, [backend, frontend], ["frontend/profile"])
    document = plan.to_dict()
    evidence = {
        "schema_version": "pdd.sync.scope-evidence.v1",
        "module_id_encoding": "pdd.module-id-list.v1",
        "selected_module_ids": list(plan.selected_module_ids),
        "sync_plan_digest": plan_digest(document),
        "selection_digest": plan.selection_digest,
        "sync_plan": document,
    }
    scope = {
        "module_id_encoding": "pdd.module-id-list.v1",
        "module_ids": ["frontend/profile"],
        "sync_plan_digest": plan.sync_plan_digest,
        "selection_digest": selection_digest(["frontend/profile"]),
    }
    persisted, selected = validate_explicit_scope_evidence(scope, evidence)
    assert persisted == document
    assert selected == ("frontend/profile",)

    evidence["sync_plan_digest"] = "0" * 64
    with pytest.raises(SyncPlanError, match="persisted SyncPlan digest mismatch"):
        validate_explicit_scope_evidence(scope, evidence)

    evidence["sync_plan_digest"] = plan.sync_plan_digest
    evidence["sync_plan"]["selected_module_ids"] = []
    evidence["sync_plan_digest"] = plan_digest(evidence["sync_plan"])
    with pytest.raises(SyncPlanError, match="selection/order is inconsistent"):
        validate_explicit_scope_evidence(scope, evidence)


def test_dependency_closure_is_selected_and_missing_edges_fail(tmp_path: Path) -> None:
    backend = _candidate(tmp_path, "backend/service")
    frontend = _candidate(
        tmp_path, "frontend/profile", dependencies=("backend/service",)
    )
    plan = build_sync_plan(tmp_path, [frontend, backend], ["frontend/profile"])
    assert plan.selected_module_ids == ("backend/service", "frontend/profile")
    assert plan.dependency_order == ("backend/service", "frontend/profile")

    missing = _candidate(
        tmp_path, "frontend/missing", dependencies=("not/in-candidates",)
    )
    with pytest.raises(SyncPlanError, match="missing dependency IDs"):
        build_sync_plan(tmp_path, [missing], ["frontend/missing"])


def test_complete_candidate_inventory_is_not_limited_to_execution_bound(tmp_path: Path) -> None:
    """Planning may inventory a large repository while execution stays bounded."""
    candidates = [_candidate(tmp_path, f"pkg/module_{index:03d}") for index in range(65)]
    plan = build_sync_plan(tmp_path, candidates, ["pkg/module_000"])
    assert len(plan.candidates) == 65
    assert plan.selected_module_ids == ("pkg/module_000",)


def test_fallback_loader_rejects_ambient_diff_scope_before_runner(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    candidate = _candidate(tmp_path, "frontend/profile")
    plan = build_sync_plan(tmp_path, [candidate], ["frontend/profile"])
    evidence = {
        "schema_version": "pdd.sync.scope-evidence.v1",
        "module_id_encoding": "pdd.module-id-list.v1",
        "selected_module_ids": list(plan.selected_module_ids),
        "sync_plan_digest": plan.sync_plan_digest,
        "selection_digest": plan.selection_digest,
        "sync_plan": plan.to_dict(),
    }
    evidence_path = tmp_path / ".pdd" / "evidence" / "sync-plans" / f"{plan.sync_plan_digest}.json"
    atomic_write_json(evidence_path, evidence)
    scope = {
        "module_id_encoding": "pdd.module-id-list.v1",
        "module_ids": ["frontend/profile"],
        "sync_plan_digest": plan.sync_plan_digest,
        "selection_digest": plan.selection_digest,
    }
    monkeypatch.setenv(
        "PDD_EXPLICIT_SYNC_SCOPE_V1",
        json.dumps(scope, sort_keys=True, separators=(",", ":")),
    )
    loaded, selected, cwds, targets, _contexts, _raw = _load_fallback_scope_execution(tmp_path)
    assert loaded == plan.to_dict()
    assert selected == ("frontend/profile",)
    assert cwds["frontend/profile"] == tmp_path / "frontend"
    assert targets["frontend/profile"] == "profile"

    monkeypatch.setenv("PDD_CHANGED_MODULES", "frontend/profile")
    with pytest.raises(SyncPlanError, match="forbidden"):
        _load_fallback_scope_execution(tmp_path)


def test_runner_uses_frozen_plan_for_order_env_and_evidence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    backend = _candidate(tmp_path, "backend/service")
    frontend = _candidate(
        tmp_path, "frontend/profile", dependencies=("backend/service",)
    )
    plan = build_sync_plan(tmp_path, [frontend, backend], ["frontend/profile"])
    scope = {
        "module_id_encoding": "pdd.module-id-list.v1",
        "module_ids": ["frontend/profile"],
        "sync_plan_digest": plan.sync_plan_digest,
        "selection_digest": selection_digest(["frontend/profile"]),
    }
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_CHANGED_MODULES", "must-not-reach-child")
    runner = AsyncSyncRunner(
        basenames=["untrusted"],
        dep_graph={"untrusted": []},
        sync_options={
            "sync_plan": plan.to_dict(),
            "sync_plan_digest": plan.sync_plan_digest,
            "selection_digest": scope["selection_digest"],
            "execution_selected_module_ids": ["frontend/profile"],
            "execution_dependency_order": ["frontend/profile"],
            "explicit_sync_scope": json.dumps(scope, sort_keys=True, separators=(",", ":")),
        },
        github_info=None,
        quiet=True,
    )
    assert runner.basenames == ["frontend/profile"]
    assert runner.dep_graph == {"frontend/profile": []}
    child_env = runner._build_env("/tmp/cost.csv")
    assert "PDD_CHANGED_MODULES" not in child_env
    assert child_env["PDD_SYNC_SCOPE_SOURCE"] == "fallback_payload_v1"
    runner._persist_scope_evidence()
    evidence = tmp_path / ".pdd" / "evidence" / "sync-plans" / f"{plan.sync_plan_digest}.json"
    assert json.loads(evidence.read_text(encoding="utf-8"))["selected_module_ids"] == list(
        plan.selected_module_ids
    )
    execution = (
        tmp_path / ".pdd" / "evidence" / "sync-executions"
        / f"{plan.sync_plan_digest}-{scope['selection_digest']}.json"
    )
    assert json.loads(execution.read_text(encoding="utf-8"))["selected_module_ids"] == [
        "frontend/profile"
    ]


def test_wrong_root_output_is_rejected_before_execution(tmp_path: Path) -> None:
    candidate = _candidate(tmp_path, "service/worker")
    wrong = SyncPlanCandidate(
        module_id=candidate.module_id,
        unit=candidate.unit,
        prompt_paths=candidate.prompt_paths,
        output_paths=(tmp_path.parent / "escape.py",),
    )
    with pytest.raises(SyncPlanError, match="escapes governing root"):
        build_sync_plan(tmp_path, [wrong], ["service/worker"])


def test_path_aware_identity_reuses_resolved_sync_unit(tmp_path: Path) -> None:
    nested = tmp_path / "apps" / "worker"
    nested.mkdir(parents=True)
    unit = resolve_sync_unit("apps/worker/job", "job", nested)
    assert canonical_module_id(tmp_path, unit) == "apps/worker/job"


def test_external_validated_cwd_is_rejected_instead_of_being_relabelled(
    tmp_path: Path,
) -> None:
    """A plan cannot serialize an external cwd as the project root."""
    external = tmp_path.parent / "validated-child-checkout"
    external.mkdir(exist_ok=True)
    unit = resolve_sync_unit("foo", "foo", external)
    with pytest.raises(SyncPlanError, match="escapes governing root"):
        build_sync_plan(
            tmp_path,
            [SyncPlanCandidate(module_id="foo", unit=unit)],
            ["foo"],
        )
