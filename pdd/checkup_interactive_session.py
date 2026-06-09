"""Interactive prompt-repair session contracts and Pi-backed implementation."""

from __future__ import annotations

import json
import shutil
import subprocess
import tempfile
from copy import deepcopy
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Protocol, Sequence

import click
from pydantic import BaseModel, Field


PromptSourceSetReport = Any

NON_APPROVING_PATCH_KINDS = frozenset({"skip", "custom_no_patch", "no_patch"})

_PI_MIN_NODE_MAJOR = 22
_PI_PACKAGE = "@earendil-works/pi-coding-agent"
# Bridge uses ESM imports; must be .mjs so Node treats it as an ES module.
_PI_BRIDGE = Path(__file__).parent / "_pi_repair_bridge.mjs"


def _pi_available() -> bool:
    node = shutil.which("node")
    if node is None:
        return False
    try:
        ver = subprocess.check_output([node, "--version"], text=True).strip()
        if int(ver.lstrip("v").split(".")[0]) < _PI_MIN_NODE_MAJOR:
            return False
        # Verify the npm package is installed before claiming availability.
        subprocess.run(
            [node, "--input-type=module", "--eval",
             f"import('{_PI_PACKAGE}').then(()=>process.exit(0),()=>process.exit(1))"],
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            timeout=15,
        )
        return True
    except (subprocess.SubprocessError, OSError, ValueError):
        return False


@dataclass
class ApprovedPatch:
    """Typed repair patch approved by an interactive session."""

    kind: str
    target: Path
    anchor: dict[str, Any]
    replacement: str
    finding_id: str = field(default="")

    def __post_init__(self) -> None:
        self.target = Path(self.target)
        self.anchor = dict(self.anchor)


class InteractiveRepairSession(Protocol):
    """Engine-agnostic protocol for interactive prompt-repair sessions.

    Lifecycle: seed the report, run the session, then read approved_patches.
    The session backend (Pi, LLM, or fake) drives the entire interaction.
    """

    def seed(self, report: PromptSourceSetReport) -> None:
        """Seed the session with a prompt-source-set report."""

    def run(self) -> None:
        """Run the full interactive session. The backend drives the workflow."""

    def approved_patches(self) -> list[ApprovedPatch]:
        """Return typed approved patches collected during the session."""


# ---------------------------------------------------------------------------
# Private Pydantic models for LlmInteractiveSession proposal output
# ---------------------------------------------------------------------------

class _PatchProposal(BaseModel):
    kind: str = Field(description="Patch kind: vocab_definition, contract_rule, example_rewrite, or custom_rewrite")
    target: str = Field(description="Relative path to the prompt file to repair")
    anchor: dict[str, Any] = Field(description="Anchor locating the patch point, e.g. {section: 'R3'} or {pattern: 'old text'}")
    replacement: str = Field(description="Exact new text to insert or replace")
    label: str = Field(description="Short one-line label shown in the repair menu")
    rationale: str = Field(description="One sentence explaining why this patch fixes the finding")


class _ProposalSet(BaseModel):
    proposals: list[_PatchProposal] = Field(description="2-4 concrete repair patch proposals for the finding")


# ---------------------------------------------------------------------------
# Session implementations
# ---------------------------------------------------------------------------

class PiInteractiveSession:
    """Pi-backed interactive repair session via @earendil-works/pi-coding-agent.

    Invokes a Node.js bridge script that runs a Pi AgentSession. Pi drives the
    entire interactive workflow — QA, repair proposals, and user choices. Python
    only serialises the input report, starts the bridge, and reads the output.
    """

    def __init__(self, bridge: Path | None = None, timeout: float | None = None) -> None:
        self._report: PromptSourceSetReport | None = None
        self._patches: list[ApprovedPatch] = []
        self._bridge = bridge or _PI_BRIDGE
        self._timeout = timeout

    @staticmethod
    def is_available() -> bool:
        return _pi_available()

    def seed(self, report: PromptSourceSetReport) -> None:
        self._report = report

    def run(self) -> None:
        # Reset before each run so a failed call never leaves stale patches.
        self._patches = []
        # Resolve the absolute path at call time to avoid PATH-ordering races.
        node = shutil.which("node") or "node"
        _KNOWN_PATCH_FIELDS = frozenset({"kind", "target", "anchor", "replacement", "finding_id"})
        with tempfile.TemporaryDirectory() as tmp:
            ctx_path = Path(tmp) / "context.json"
            out_path = Path(tmp) / "output.json"
            ctx_path.write_text(json.dumps(self._report or {}), encoding="utf-8")
            subprocess.run(
                [node, str(self._bridge), str(ctx_path), str(out_path)],
                check=True,
                timeout=self._timeout,
            )
            if not out_path.exists():
                raise RuntimeError(
                    f"Pi bridge exited without writing output to {out_path}"
                )
            try:
                result = json.loads(out_path.read_text(encoding="utf-8"))
            except json.JSONDecodeError as exc:
                raise RuntimeError(
                    f"Pi bridge wrote invalid JSON to {out_path}: {exc}"
                ) from exc
        self._patches = [
            ApprovedPatch(**{k: p[k] for k in _KNOWN_PATCH_FIELDS if k in p})
            for p in result.get("approved_patches", [])
            if p.get("kind") not in NON_APPROVING_PATCH_KINDS
        ]

    def approved_patches(self) -> list[ApprovedPatch]:
        return [deepcopy(p) for p in self._patches]


class LlmInteractiveSession:
    """Real interactive repair session using llm_invoke + Click CLI prompts.

    Works without Node.js or the Pi package — uses whichever LLM pdd is
    configured with. Presents numbered patch menus; the user approves patches
    in their terminal.
    """

    def __init__(self, strength: float = 0.5) -> None:
        self._report: PromptSourceSetReport | None = None
        self._patches: list[ApprovedPatch] = []
        self._strength = strength

    def seed(self, report: PromptSourceSetReport) -> None:
        self._report = report

    def run(self) -> None:
        self._patches = []
        for finding in (self._report or {}).get("findings", []):
            self._patches.extend(self._handle_finding(finding))

    def _handle_finding(self, finding: dict[str, Any]) -> list[ApprovedPatch]:
        # Lazy import — avoids LiteLLM startup cost when this class isn't used.
        from pdd.llm_invoke import llm_invoke  # type: ignore[import]

        finding_id = str(finding.get("finding_id") or finding.get("id") or "?")
        summary = finding.get("summary") or finding.get("check") or ""

        click.echo(f"\n{'─' * 60}")
        click.echo(f"Finding {finding_id}: {summary}")
        click.echo("─" * 60)
        click.echo("Generating repair proposals…")

        try:
            result = llm_invoke(
                messages=[{"role": "user", "content": (
                    "Analyze this pdd prompt quality finding and propose concrete repair patches.\n\n"
                    f"Finding:\n{json.dumps(finding, indent=2)}\n\n"
                    "Propose 2–4 patches. Each patch must include the exact file path, "
                    "a precise anchor (section name, pattern, or line marker), and the "
                    "exact replacement text — write the actual new text, not a description."
                )}],
                strength=self._strength,
                temperature=0.0,
                output_pydantic=_ProposalSet,
            )
            proposal_set = result.get("result")
            if not isinstance(proposal_set, _ProposalSet) or not proposal_set.proposals:
                click.echo("  (no proposals generated — skipping)")
                return []
        except Exception as exc:
            click.echo(f"  LLM error: {exc} — skipping finding")
            return []

        for i, p in enumerate(proposal_set.proposals, 1):
            click.echo(f"\n  [{i}] {p.label}")
            click.echo(f"      File     : {p.target}")
            click.echo(f"      Rationale: {p.rationale}")
        click.echo("  [s] Skip this finding")

        approved: list[ApprovedPatch] = []
        while True:
            raw = click.prompt(
                "\nApprove patch(es) — enter number(s) separated by spaces, or s to skip",
                default="s",
            ).strip().lower()
            if raw == "s":
                break
            try:
                indices = [int(x) for x in raw.split()]
                if not all(1 <= idx <= len(proposal_set.proposals) for idx in indices):
                    click.echo(f"  Please enter numbers between 1 and {len(proposal_set.proposals)}")
                    continue
                for idx in indices:
                    p = proposal_set.proposals[idx - 1]
                    approved.append(ApprovedPatch(
                        kind=p.kind,
                        target=Path(p.target),
                        anchor=p.anchor,
                        replacement=p.replacement,
                        finding_id=finding_id,
                    ))
                break
            except ValueError:
                click.echo("  Please enter numbers or 's'")

        return approved

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


def make_session(strength: float = 0.5) -> InteractiveRepairSession:
    """Return the best available interactive session backend.

    Prefers PiInteractiveSession when Node >=22 and the Pi package are present;
    falls back to LlmInteractiveSession which uses pdd's configured LLM.
    """
    if PiInteractiveSession.is_available():
        return PiInteractiveSession()
    return LlmInteractiveSession(strength=strength)
