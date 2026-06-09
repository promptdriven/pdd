"""Interactive prompt-repair session contracts and Pi-backed implementation."""

from __future__ import annotations

import json
import shutil
import subprocess
import tempfile
from copy import deepcopy
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Protocol, Sequence


PromptSourceSetReport = Any

NON_APPROVING_PATCH_KINDS = frozenset({"skip", "custom_no_patch", "no_patch"})

_PI_MIN_NODE_MAJOR = 22
_PI_BRIDGE = Path(__file__).parent / "_pi_repair_bridge.js"


def _pi_available() -> bool:
    if shutil.which("node") is None:
        return False
    try:
        out = subprocess.check_output(["node", "--version"], text=True).strip()
        return int(out.lstrip("v").split(".")[0]) >= _PI_MIN_NODE_MAJOR
    except Exception:
        return False


@dataclass
class ApprovedPatch:
    """Typed repair patch approved by an interactive session."""

    kind: str
    target: Path
    anchor: dict[str, Any]
    replacement: str

    def __post_init__(self) -> None:
        self.target = Path(self.target)
        self.anchor = dict(self.anchor)


@dataclass
class RepairOption:
    """A repair option label/preview pair passed to Pi as context."""

    label: str
    preview: str
    patch: ApprovedPatch


class InteractiveRepairSession(Protocol):
    """Engine-agnostic protocol for interactive prompt-repair sessions.

    Lifecycle: seed the report, run the session, then read approved_patches.
    The session backend (Pi or fake) drives the entire interaction.
    """

    def seed(self, report: PromptSourceSetReport) -> None:
        """Seed the session with a prompt-source-set report."""

    def run(self) -> None:
        """Run the full interactive session. The backend drives the workflow."""

    def approved_patches(self) -> list[ApprovedPatch]:
        """Return typed approved patches collected during the session."""


class PiInteractiveSession:
    """Pi-backed interactive repair session via @earendil-works/pi-coding-agent.

    Invokes a Node.js bridge script that runs a Pi AgentSession. Pi drives the
    entire interactive workflow — QA, repair proposals, and user choices. Python
    only serialises the input report, starts the bridge, and reads the output.
    """

    def __init__(self, bridge: Path | None = None) -> None:
        self._report: PromptSourceSetReport | None = None
        self._patches: list[ApprovedPatch] = []
        self._bridge = bridge or _PI_BRIDGE

    @staticmethod
    def is_available() -> bool:
        return _pi_available()

    def seed(self, report: PromptSourceSetReport) -> None:
        self._report = report

    def run(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            ctx_path = Path(tmp) / "context.json"
            out_path = Path(tmp) / "output.json"
            ctx_path.write_text(json.dumps(self._report or {}))
            subprocess.run(
                ["node", str(self._bridge), str(ctx_path), str(out_path)],
                check=True,
            )
            result = json.loads(out_path.read_text())
        self._patches = [
            ApprovedPatch(**p)
            for p in result.get("approved_patches", [])
            if p.get("kind") not in NON_APPROVING_PATCH_KINDS
        ]

    def approved_patches(self) -> list[ApprovedPatch]:
        return [deepcopy(p) for p in self._patches]


class FakeInteractiveSession:
    """Deterministic in-memory repair session for unit tests."""

    def __init__(self, patches: Sequence[ApprovedPatch] | None = None) -> None:
        self.report: PromptSourceSetReport | None = None
        self._patches: list[ApprovedPatch] = list(patches or [])
        self.ran: bool = False

    def seed(self, report: PromptSourceSetReport) -> None:
        self.report = report

    def run(self) -> None:
        self.ran = True

    def approved_patches(self) -> list[ApprovedPatch]:
        return [deepcopy(p) for p in self._patches]
