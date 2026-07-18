"""Focused contracts for the deterministic Agentic Sync V1 planner."""
from __future__ import annotations

import json
import copy
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.resolved_sync_unit import resolve_sync_unit
from pdd.agentic_sync import _load_fallback_scope_execution, _run_fallback_scope_sync
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
    for malformed in ([{}], [None], [1], [True], ["api/page", "api/page"]):
        with pytest.raises(SyncPlanError):
            apply_ambiguity_selection(plan, ["api/page", "web/page"], malformed)


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


def test_persisted_plan_recomputes_graph_and_rejects_digest_consistent_tampering(
    tmp_path: Path,
) -> None:
    backend = _candidate(tmp_path, "backend/service")
    frontend = _candidate(tmp_path, "frontend/profile", dependencies=("backend/service",))
    plan = build_sync_plan(tmp_path, [backend, frontend], ["frontend/profile"])
    scope = {
        "module_id_encoding": "pdd.module-id-list.v1",
        "module_ids": ["frontend/profile"],
        "sync_plan_digest": plan.sync_plan_digest,
        "selection_digest": selection_digest(["frontend/profile"]),
    }
    for mutate in (
        lambda document: document.__setitem__("dependency_order", ["frontend/profile", "backend/service"]),
        lambda document: document.__setitem__("sccs", [["backend/service", "frontend/profile"]]),
        lambda document: document["candidates"][0].__setitem__("mystery", True),
    ):
        document = copy.deepcopy(plan.to_dict())
        mutate(document)
        evidence = {
            "schema_version": "pdd.sync.scope-evidence.v1",
            "module_id_encoding": "pdd.module-id-list.v1",
            "selected_module_ids": list(plan.selected_module_ids),
            "sync_plan_digest": plan_digest(document),
            "selection_digest": plan.selection_digest,
            "sync_plan": document,
        }
        forged_scope = dict(scope, sync_plan_digest=evidence["sync_plan_digest"])
        with pytest.raises(SyncPlanError):
            validate_explicit_scope_evidence(forged_scope, evidence)


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


def test_fallback_scope_forces_one_agentic_child_flag(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A validated fallback cannot be downgraded by the original CLI mode."""
    candidate = _candidate(tmp_path, "frontend/profile")
    plan = build_sync_plan(tmp_path, [candidate], ["frontend/profile"])
    raw_scope = json.dumps(
        {
            "module_id_encoding": "pdd.module-id-list.v1",
            "module_ids": ["frontend/profile"],
            "sync_plan_digest": plan.sync_plan_digest,
            "selection_digest": plan.selection_digest,
        },
        sort_keys=True,
        separators=(",", ":"),
    )
    loaded = (
        plan.to_dict(),
        ("frontend/profile",),
        {"frontend/profile": tmp_path / "frontend"},
        {"frontend/profile": "profile"},
        {"frontend/profile": None},
        raw_scope,
    )
    runner = MagicMock()
    runner.run.return_value = (True, "synced", 0.0)
    with patch("pdd.agentic_sync._load_fallback_scope_execution", return_value=loaded), patch(
        "pdd.agentic_sync.AsyncSyncRunner", return_value=runner
    ) as runner_type:
        success, _message, _cost, _provider = _run_fallback_scope_sync(
            project_root=tmp_path,
            owner="owner",
            repo="repo",
            issue_number=1,
            issue_url="https://github.com/owner/repo/issues/1",
            verbose=False,
            quiet=True,
            budget=None,
            skip_verify=False,
            skip_tests=False,
            dry_run=False,
            agentic_mode=False,
            no_steer=True,
            max_attempts=None,
            timeout_adder=0.0,
            use_github_state=False,
            durable=False,
            durable_branch=None,
            no_resume=False,
            durable_max_parallel=None,
            strength=None,
            temperature=None,
            compressed_context=False,
            local=False,
        )

    assert success is True
    options = runner_type.call_args.kwargs["sync_options"]
    assert options["agentic"] is True
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_CHANGED_MODULES", raising=False)
    actual_runner = AsyncSyncRunner(
        basenames=["frontend/profile"],
        dep_graph={"frontend/profile": []},
        sync_options=options,
        github_info=None,
        quiet=True,
        module_cwds={"frontend/profile": tmp_path / "frontend"},
        module_targets={"frontend/profile": "profile"},
    )
    command = actual_runner._build_command("frontend/profile")
    assert command.count("--agentic") == 1
    child_env = actual_runner._build_env("/tmp/cost.csv")
    assert "PDD_CHANGED_MODULES" not in child_env
    assert child_env["PDD_EXPLICIT_SYNC_SCOPE_V1"] == raw_scope


def test_resume_requires_exact_frozen_selection_and_schedule(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Overlapping modules cannot inherit success from a different V1 run."""
    first = _candidate(tmp_path, "service/first")
    second = _candidate(tmp_path, "service/second")
    first_only = build_sync_plan(tmp_path, [first, second], ["service/first"])
    both = build_sync_plan(
        tmp_path, [first, second], ["service/first", "service/second"]
    )

    def options(plan):
        return {
            "sync_plan": plan.to_dict(),
            "sync_plan_digest": plan.sync_plan_digest,
            "selection_digest": plan.selection_digest,
            "execution_selected_module_ids": list(plan.selected_module_ids),
            "execution_dependency_order": list(plan.dependency_order),
        }

    monkeypatch.chdir(tmp_path)
    issue_url = "https://github.com/owner/repo/issues/99"
    source = AsyncSyncRunner(
        basenames=list(first_only.selected_module_ids),
        dep_graph={"service/first": []},
        sync_options=options(first_only),
        github_info=None,
        quiet=True,
        issue_url=issue_url,
    )
    source._record_result("service/first", True, 0.1, "")

    same = AsyncSyncRunner(
        basenames=list(first_only.selected_module_ids),
        dep_graph={"service/first": []},
        sync_options=options(first_only),
        github_info=None,
        quiet=True,
        issue_url=issue_url,
    )
    assert same.module_states["service/first"].status == "success"

    changed = AsyncSyncRunner(
        basenames=list(both.selected_module_ids),
        dep_graph={"service/first": [], "service/second": []},
        sync_options=options(both),
        github_info=None,
        quiet=True,
        issue_url=issue_url,
    )
    assert changed.module_states["service/first"].status == "pending"
    assert changed.module_states["service/second"].status == "pending"


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
    assert canonical_module_id(
        tmp_path, resolve_sync_unit("wrong-id", "job", nested)
    ) == "apps/worker/job"


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
