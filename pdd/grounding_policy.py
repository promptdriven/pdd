"""Optional grounding policy checks for critical modules."""
from __future__ import annotations

import os
from pathlib import Path
from typing import Any, Dict, List, Literal, Optional

import yaml
from pydantic import BaseModel, Field

Severity = Literal["error", "warning"]


class GroundingPolicy(BaseModel):
    require_review_for_critical_modules: bool = False
    require_pinned_examples_for: List[str] = Field(default_factory=list)


class PolicyViolation(BaseModel):
    code: str
    module: str
    message: str
    severity: Severity


def _default_policy_path() -> Path:
    pdd_path = os.environ.get("PDD_PATH")
    if pdd_path:
        return Path(pdd_path) / "grounding_policy.yaml"
    return Path.cwd() / ".pdd" / "grounding_policy.yaml"


def load_policy(path: Optional[str] = None) -> GroundingPolicy:
    """Load optional grounding policy YAML; return permissive defaults when missing."""
    policy_path = Path(path) if path else _default_policy_path()
    if not policy_path.is_file():
        return GroundingPolicy()

    try:
        raw = yaml.safe_load(policy_path.read_text(encoding="utf-8"))
    except (OSError, yaml.YAMLError):
        return GroundingPolicy()

    if not isinstance(raw, dict):
        return GroundingPolicy()

    grounding = raw.get("grounding")
    if not isinstance(grounding, dict):
        return GroundingPolicy()

    pinned_raw = grounding.get("require_pinned_examples_for") or []
    pinned: List[str] = []
    if isinstance(pinned_raw, list):
        for item in pinned_raw:
            if isinstance(item, str):
                slug = item.strip()
                if slug:
                    pinned.append(slug)

    require_review = grounding.get("require_review_for_critical_modules")
    return GroundingPolicy(
        require_review_for_critical_modules=bool(require_review),
        require_pinned_examples_for=pinned,
    )


def check(
    policy: GroundingPolicy,
    module: str,
    grounding: Dict[str, Any],
) -> List[PolicyViolation]:
    """Evaluate grounding evidence for a module slug against policy rules."""
    if module not in policy.require_pinned_examples_for:
        return []

    violations: List[PolicyViolation] = []
    mode = grounding.get("mode") if isinstance(grounding, dict) else None
    pinned = grounding.get("pinned") if isinstance(grounding, dict) else []
    reviewed = grounding.get("reviewed") if isinstance(grounding, dict) else None

    pinned_list = [str(item) for item in pinned] if isinstance(pinned, list) else []

    if mode == "unavailable":
        violations.append(
            PolicyViolation(
                code="grounding.unavailable_for_critical_module",
                module=module,
                message=(
                    f"Grounding is unavailable for critical module '{module}' "
                    "but policy requires cloud grounding evidence."
                ),
                severity="warning",
            )
        )

    if policy.require_review_for_critical_modules and reviewed is not True:
        violations.append(
            PolicyViolation(
                code="grounding.review_required",
                module=module,
                message=(
                    f"Critical module '{module}' requires reviewed grounding examples "
                    "but generation.grounding.reviewed is not true."
                ),
                severity="error",
            )
        )

    if module not in pinned_list:
        violations.append(
            PolicyViolation(
                code="grounding.pin_required",
                module=module,
                message=(
                    f"Critical module '{module}' must pin its grounding example "
                    f"but {module!r} is not listed in generation.grounding.pinned."
                ),
                severity="error",
            )
        )

    return violations
