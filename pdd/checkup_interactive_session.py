"""Interactive prompt-repair session contracts for checkup workflows."""

from __future__ import annotations

from collections import deque
from copy import deepcopy
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Deque, Iterable, Mapping, Protocol, Sequence


PromptSourceSetReport = Any

NON_APPROVING_PATCH_KINDS = frozenset({"skip", "custom_no_patch", "no_patch"})


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
    """A repair option shown to a user or agent backend."""

    label: str
    preview: str
    patch: ApprovedPatch


class InteractiveRepairSession(Protocol):
    """Engine-agnostic protocol for interactive prompt-repair sessions."""

    def seed(self, report: PromptSourceSetReport) -> None:
        """Seed the session with a prompt-source-set report."""

    def present_finding(self, finding_id: str) -> list[RepairOption]:
        """Return repair options presented for one finding."""

    def ask(self, question: str) -> str:
        """Ask a free-form question and return the backend answer."""

    def record_choice(self, finding_id: str, option: RepairOption) -> None:
        """Record the selected option for a previously presented finding."""

    def approved_patches(self) -> list[ApprovedPatch]:
        """Return typed approved patches from recorded choices."""


class FakeInteractiveSession:
    """Deterministic in-memory repair session for unit tests."""

    def __init__(
        self,
        options_by_finding: Mapping[str, Sequence[RepairOption]] | None = None,
        answers: Iterable[str] | None = None,
    ) -> None:
        self.report: PromptSourceSetReport | None = None
        self.options_by_finding: dict[str, list[RepairOption]] = {
            finding_id: list(options)
            for finding_id, options in (options_by_finding or {}).items()
        }
        self.presented_options: dict[str, list[RepairOption]] = {}
        self.recorded_choices: list[tuple[str, RepairOption]] = []
        self.qa_transcript_summary: list[dict[str, str]] = []
        self._answers: Deque[str] = deque(answers or [])

    def seed(self, report: PromptSourceSetReport) -> None:
        """Store the report and import simple mapping-style finding options."""
        self.report = report
        if isinstance(report, Mapping):
            for finding in report.get("findings", []):
                if not isinstance(finding, Mapping):
                    continue
                finding_id = finding.get("id") or finding.get("finding_id")
                options = finding.get("options")
                if isinstance(finding_id, str) and isinstance(options, Sequence):
                    typed_options = [
                        option for option in options if isinstance(option, RepairOption)
                    ]
                    self.options_by_finding.setdefault(finding_id, typed_options)

    def present_finding(self, finding_id: str) -> list[RepairOption]:
        """Return a fresh list of options and remember what was shown."""
        options = list(self.options_by_finding.get(finding_id, []))
        self.presented_options[finding_id] = options
        return list(options)

    def ask(self, question: str) -> str:
        """Consume the next scripted answer or return an empty string."""
        answer = self._answers.popleft() if self._answers else ""
        self.qa_transcript_summary.append({"question": question, "answer": answer})
        return answer

    def record_choice(self, finding_id: str, option: RepairOption) -> None:
        """Record a choice only after that exact option has been presented."""
        presented = self.presented_options.get(finding_id)
        if presented is None or option not in presented:
            raise ValueError(
                f"repair option {option.label!r} was not presented for {finding_id!r}"
            )
        self.recorded_choices.append((finding_id, option))

    def approved_patches(self) -> list[ApprovedPatch]:
        """Return typed approving patches from recorded choices."""
        patches: list[ApprovedPatch] = []
        for _, option in self.recorded_choices:
            patch = option.patch
            if (
                isinstance(patch, ApprovedPatch)
                and patch.kind not in NON_APPROVING_PATCH_KINDS
            ):
                patches.append(deepcopy(patch))
        return patches
