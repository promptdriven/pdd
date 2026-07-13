"""Policy-preserving repair plans derived from canonical verdicts."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

from .types import BaselineStatus, InventoryStatus, SemanticStatus, SyncVerdict


class RepairAction(str, Enum):
    """Explicit operation that can move a unit toward synchronization."""

    NONE = "NONE"
    VALIDATE = "VALIDATE"
    SYNC_FROM_PROMPT = "SYNC_FROM_PROMPT"
    UPDATE_PROMPT_REVIEW = "UPDATE_PROMPT_REVIEW"
    RESOLVE_CONFLICT = "RESOLVE_CONFLICT"
    VERIFIED_REBUILD = "VERIFIED_REBUILD"
    BASELINE_RESET = "BASELINE_RESET"
    RESTORE_REQUIRED = "RESTORE_REQUIRED"
    REPAIR_VALIDATION = "REPAIR_VALIDATION"
    BLOCK = "BLOCK"


@dataclass(frozen=True)
class RepairPolicy:
    """Protected controls for the small set of unattended repair operations."""

    allow_prompt_side_generation: bool = True
    allow_verified_rebuild: bool = False


@dataclass(frozen=True)
class RepairPlan:
    """Allowed action without changing the classifier's source verdict."""

    verdict: SyncVerdict
    action: RepairAction
    unattended: bool
    review_required: bool
    reason: str


_PROMPT_ROLES = frozenset({"prompt", "include", "config", "architecture", "manifest"})


def _preflight_plan(
    verdict: SyncVerdict, policy: RepairPolicy
) -> RepairPlan | None:
    """Plan terminal inventory, corruption, missing, and baseline conditions."""
    if verdict.in_sync:
        return RepairPlan(verdict, RepairAction.NONE, False, False, "already in sync")
    if (
        verdict.inventory is InventoryStatus.INVALID
        or verdict.baseline is BaselineStatus.CORRUPT
    ):
        return RepairPlan(
            verdict, RepairAction.BLOCK, False, True, "invalid or corrupt state blocks repair"
        )
    if verdict.required_artifacts_missing:
        return RepairPlan(
            verdict,
            RepairAction.RESTORE_REQUIRED,
            False,
            True,
            "required artifacts must be restored or regenerated without stamping",
        )
    if verdict.baseline is BaselineStatus.UNBASELINED:
        action = (
            RepairAction.VERIFIED_REBUILD
            if policy.allow_verified_rebuild
            else RepairAction.BASELINE_RESET
        )
        return RepairPlan(
            verdict,
            action,
            False,
            True,
            "unbaselined state requires an audited reviewed transition",
        )
    return None


def _semantic_plan(verdict: SyncVerdict) -> RepairPlan | None:
    """Plan conflict, failed validation, and evidence-only transitions."""
    if verdict.semantic is SemanticStatus.CONFLICT:
        return RepairPlan(
            verdict,
            RepairAction.RESOLVE_CONFLICT,
            False,
            True,
            "simultaneous source and derived edits require explicit resolution",
        )
    if verdict.semantic is SemanticStatus.FAILED:
        return RepairPlan(
            verdict,
            RepairAction.REPAIR_VALIDATION,
            False,
            True,
            "failed validation cannot be accepted as a baseline",
        )
    if verdict.baseline is BaselineStatus.CURRENT:
        return RepairPlan(
            verdict,
            RepairAction.VALIDATE,
            True,
            False,
            "current bytes require complete trusted semantic evidence",
        )
    return None


def plan_repair(verdict: SyncVerdict, policy: RepairPolicy) -> RepairPlan:
    """Map a verdict to one safe action without accepting drift as synchronization."""
    plan = _preflight_plan(verdict, policy) or _semantic_plan(verdict)
    if plan is not None:
        return plan
    changed = set(verdict.changed_roles)
    if changed and changed.issubset(_PROMPT_ROLES):
        return RepairPlan(
            verdict,
            RepairAction.SYNC_FROM_PROMPT,
            policy.allow_prompt_side_generation,
            not policy.allow_prompt_side_generation,
            "prompt-side drift may regenerate derived artifacts under policy",
        )
    return RepairPlan(
        verdict,
        RepairAction.UPDATE_PROMPT_REVIEW,
        False,
        True,
        "derived-side drift requires requirement-preserving reviewed prompt update",
    )
