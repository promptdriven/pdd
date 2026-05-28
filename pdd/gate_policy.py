"""YAML policy loader for ``pdd checkup gate``."""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

import yaml


@dataclass
class GateLimits:
    max_cost_usd: Optional[float] = None
    max_nondeterministic_context_items: int = 0


@dataclass
class GatePolicy:
    require: dict[str, bool] = field(default_factory=dict)
    allow: dict[str, bool] = field(default_factory=dict)
    limits: GateLimits = field(default_factory=GateLimits)
    path: Optional[Path] = None

    def requires(self, key: str) -> bool:
        return bool(self.require.get(key, False))

    def allows(self, key: str) -> bool:
        return bool(self.allow.get(key, True))

    def as_dict(self) -> dict[str, Any]:
        return {
            "require": dict(self.require),
            "allow": dict(self.allow),
            "limits": {
                "max_cost_usd": self.limits.max_cost_usd,
                "max_nondeterministic_context_items": (
                    self.limits.max_nondeterministic_context_items
                ),
            },
            "path": str(self.path) if self.path else None,
        }


_DEFAULT_REQUIRE = {
    "stories_pass": True,
    "verify_pass": True,
    "unit_tests_pass": True,
    "generated_outputs_fresh": True,
    "no_unchecked_critical_rules": True,
}

_DEFAULT_ALLOW = {
    "waivers": True,
    "story_only_rules": False,
    "skipped_verify": False,
    "skipped_tests": False,
}


def default_policy() -> GatePolicy:
    return GatePolicy(
        require=dict(_DEFAULT_REQUIRE),
        allow=dict(_DEFAULT_ALLOW),
        limits=GateLimits(max_cost_usd=20.0, max_nondeterministic_context_items=0),
    )


def load_policy(path: Optional[Path]) -> GatePolicy:
    policy = default_policy()
    if path is None:
        return policy
    if not path.is_file():
        raise FileNotFoundError(f"Policy file not found: {path}")
    data = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
    policy.path = path
    policy.require = {**policy.require, **dict(data.get("require") or {})}
    policy.allow = {**policy.allow, **dict(data.get("allow") or {})}
    limits = data.get("limits") or {}
    policy.limits = GateLimits(
        max_cost_usd=limits.get("max_cost_usd", policy.limits.max_cost_usd),
        max_nondeterministic_context_items=int(
            limits.get(
                "max_nondeterministic_context_items",
                policy.limits.max_nondeterministic_context_items,
            )
        ),
    )
    return policy
