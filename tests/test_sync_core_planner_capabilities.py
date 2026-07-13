"""Tests for fail-closed command capabilities and repair planning."""

from pathlib import PurePosixPath

import pytest

from pdd.sync_core import (
    BaselineStatus,
    CandidateId,
    CapabilityError,
    CapabilityRegistry,
    InventoryStatus,
    RepairAction,
    RepairPolicy,
    SemanticStatus,
    SyncVerdict,
    plan_repair,
)
from pdd.sync_core.types import VerdictDetails


SUBJECT = CandidateId("repository-1", PurePosixPath("prompts/widget.prompt"), "prompt")


def _verdict(baseline, semantic, changed=(), missing=()):
    return SyncVerdict(
        SUBJECT,
        InventoryStatus.MANAGED,
        baseline,
        semantic,
        VerdictDetails(changed, "test verdict", missing),
    )


def test_reconcile_and_certify_are_strictly_read_only() -> None:
    registry = CapabilityRegistry.protected_defaults()
    assert registry.get("reconcile").read_only is True
    assert registry.get("certify").read_only is True
    with pytest.raises(CapabilityError, match="cannot write roles"):
        registry.authorize_writes("reconcile", {"fingerprint"})


def test_unknown_command_and_out_of_scope_write_fail_closed() -> None:
    registry = CapabilityRegistry.protected_defaults()
    with pytest.raises(CapabilityError, match="unknown"):
        registry.get("candidate-command")
    with pytest.raises(CapabilityError, match="cannot write roles"):
        registry.authorize_writes("baseline", {"code"})


def test_mutating_commands_require_transactions() -> None:
    registry = CapabilityRegistry.protected_defaults()
    for command in ("baseline", "sync", "update", "resolve", "trusted-validator"):
        assert registry.get(command).requires_transaction is True
    assert registry.get("baseline").may_reset_baseline is True
    assert registry.get("trusted-validator").may_issue_evidence is True


@pytest.mark.parametrize("role", ["prompt", "include", "manifest"])
def test_prompt_side_drift_can_only_plan_generation(role) -> None:
    verdict = _verdict(BaselineStatus.DRIFTED, SemanticStatus.UNKNOWN, (role,))
    plan = plan_repair(verdict, RepairPolicy())
    assert plan.action is RepairAction.SYNC_FROM_PROMPT
    assert plan.unattended is True
    assert plan.verdict is verdict


@pytest.mark.parametrize("role", ["code", "test", "example"])
def test_derived_drift_requires_reviewed_requirement_preserving_update(role) -> None:
    plan = plan_repair(
        _verdict(BaselineStatus.DRIFTED, SemanticStatus.UNKNOWN, (role,)),
        RepairPolicy(),
    )
    assert plan.action is RepairAction.UPDATE_PROMPT_REVIEW
    assert plan.unattended is False
    assert plan.review_required is True


def test_conflict_never_has_an_unattended_action() -> None:
    plan = plan_repair(
        _verdict(BaselineStatus.DRIFTED, SemanticStatus.CONFLICT, ("prompt", "code")),
        RepairPolicy(),
    )
    assert plan.action is RepairAction.RESOLVE_CONFLICT
    assert plan.unattended is False


def test_unbaselined_defaults_to_reviewed_unknown_baseline() -> None:
    plan = plan_repair(
        _verdict(BaselineStatus.UNBASELINED, SemanticStatus.UNKNOWN), RepairPolicy()
    )
    assert plan.action is RepairAction.BASELINE_RESET
    assert plan.review_required is True


def test_missing_artifact_is_restored_not_stamped() -> None:
    plan = plan_repair(
        _verdict(
            BaselineStatus.DRIFTED,
            SemanticStatus.FAILED,
            ("code",),
            ("code",),
        ),
        RepairPolicy(),
    )
    assert plan.action is RepairAction.RESTORE_REQUIRED
    assert plan.unattended is False
