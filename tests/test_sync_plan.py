"""Focused contracts for the deterministic Agentic Sync V1 planner."""
from __future__ import annotations

from pathlib import Path

import pytest

from pdd.resolved_sync_unit import resolve_sync_unit
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


def test_validated_legacy_cwd_outside_plan_root_does_not_break_evidence(
    tmp_path: Path,
) -> None:
    """The issue dry-run adapter may provide an isolated validated checkout."""
    external = tmp_path.parent / "validated-child-checkout"
    external.mkdir(exist_ok=True)
    unit = resolve_sync_unit("foo", "foo", external)
    plan = build_sync_plan(
        tmp_path,
        [SyncPlanCandidate(module_id="foo", unit=unit)],
        ["foo"],
    )
    assert plan.to_dict()["candidates"][0]["governing_root"] == "."
