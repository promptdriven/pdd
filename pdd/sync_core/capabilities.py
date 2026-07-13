"""Protected command mutation scopes and transaction requirements."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import PurePosixPath
from typing import Iterable


class CapabilityError(ValueError):
    """Raised when a command attempts an undeclared synchronization mutation."""


@dataclass(frozen=True, order=True)
class CommandCapability:
    """Protected read/write contract for one command or automation consumer."""

    command_id: str
    readable_roles: frozenset[str]
    writable_roles: frozenset[str]
    shared_resources: tuple[PurePosixPath, ...]
    requires_transaction: bool
    may_reset_baseline: bool = False
    may_issue_evidence: bool = False

    @property
    def read_only(self) -> bool:
        """Return whether the command is prohibited from all managed writes."""
        return not self.writable_roles


class CapabilityRegistry:
    """Immutable lookup and enforcement for protected command capabilities."""

    def __init__(self, capabilities: Iterable[CommandCapability]) -> None:
        entries = tuple(sorted(capabilities))
        self._entries = {entry.command_id: entry for entry in entries}
        if len(self._entries) != len(entries):
            raise CapabilityError("duplicate command capability ID")

    @classmethod
    def protected_defaults(cls) -> "CapabilityRegistry":
        """Return the canonical command scopes used by CLI and automation."""
        all_roles = frozenset(
            {"prompt", "include", "code", "example", "test", "fingerprint", "evidence"}
        )
        return cls(
            (
                CommandCapability("reconcile", all_roles, frozenset(), (), False),
                CommandCapability("certify", all_roles, frozenset(), (), False),
                CommandCapability(
                    "baseline",
                    all_roles,
                    frozenset({"fingerprint"}),
                    (),
                    True,
                    may_reset_baseline=True,
                ),
                CommandCapability(
                    "sync",
                    all_roles,
                    frozenset({"code", "example", "test", "fingerprint", "evidence"}),
                    (PurePosixPath("architecture.json"),),
                    True,
                ),
                CommandCapability(
                    "update",
                    all_roles,
                    frozenset({"prompt", "fingerprint", "evidence"}),
                    (PurePosixPath("architecture.json"),),
                    True,
                ),
                CommandCapability(
                    "resolve",
                    all_roles,
                    all_roles - {"include"},
                    (PurePosixPath("architecture.json"),),
                    True,
                ),
                CommandCapability(
                    "trusted-validator",
                    all_roles,
                    frozenset({"evidence"}),
                    (),
                    True,
                    may_issue_evidence=True,
                ),
            )
        )

    def get(self, command_id: str) -> CommandCapability:
        """Return one protected capability or fail closed for unknown commands."""
        try:
            return self._entries[command_id]
        except KeyError as exc:
            raise CapabilityError(f"unknown synchronization command: {command_id}") from exc

    def authorize_writes(self, command_id: str, roles: Iterable[str]) -> None:
        """Reject writes outside a command's protected role scope."""
        capability = self.get(command_id)
        requested = frozenset(roles)
        unauthorized = requested - capability.writable_roles
        if unauthorized:
            raise CapabilityError(
                f"{command_id} cannot write roles: {', '.join(sorted(unauthorized))}"
            )
        if requested and not capability.requires_transaction:
            raise CapabilityError(f"{command_id} has no transactional mutation scope")

    def digest(self) -> str:
        """Return a deterministic digest bound into manifests and evidence."""
        payload = [
            {
                "command_id": item.command_id,
                "readable_roles": sorted(item.readable_roles),
                "writable_roles": sorted(item.writable_roles),
                "shared_resources": [path.as_posix() for path in item.shared_resources],
                "requires_transaction": item.requires_transaction,
                "may_reset_baseline": item.may_reset_baseline,
                "may_issue_evidence": item.may_issue_evidence,
            }
            for item in sorted(self._entries.values())
        ]
        encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
        return hashlib.sha256(encoded).hexdigest()
