from pathlib import Path

import pytest

from pdd.checkup_interactive_session import (
    ApprovedPatch,
    FakeInteractiveSession,
    RepairOption,
)


def _patch(kind: str = "vocab_definition") -> ApprovedPatch:
    return ApprovedPatch(
        kind=kind,
        target=Path("prompts/refund_python.prompt"),
        anchor={"finding_id": "finding-1", "line": 42},
        replacement="- Remaining refundable amount: captured minus refunded.",
    )


def _option(label: str = "A", kind: str = "vocab_definition") -> RepairOption:
    return RepairOption(
        label=label,
        preview="--- prompt\n+++ prompt\n@@\n+definition",
        patch=_patch(kind),
    )


def test_fake_session_presents_seeded_options_and_records_choice() -> None:
    option = _option()
    session = FakeInteractiveSession({"finding-1": [option]})
    session.seed({"findings": []})

    presented = session.present_finding("finding-1")
    assert presented == [option]

    session.record_choice("finding-1", option)
    assert session.recorded_choices == [("finding-1", option)]


def test_fake_session_rejects_unpresented_choices() -> None:
    option = _option()
    session = FakeInteractiveSession({"finding-1": [option]})

    with pytest.raises(ValueError, match="not presented"):
        session.record_choice("finding-1", option)

    session.present_finding("finding-1")
    other_option = _option("B")
    with pytest.raises(ValueError, match="not presented"):
        session.record_choice("finding-1", other_option)


def test_approved_patches_returns_only_typed_approving_patches() -> None:
    approving = _option("A", "contract_rule")
    skipped = _option("skip", "skip")
    custom_no_patch = _option("custom", "custom_no_patch")
    session = FakeInteractiveSession(
        {"finding-1": [approving, skipped, custom_no_patch]}
    )

    for option in session.present_finding("finding-1"):
        session.record_choice("finding-1", option)

    patches = session.approved_patches()
    assert patches == [approving.patch]
    assert all(isinstance(patch, ApprovedPatch) for patch in patches)
    assert all(patch.kind not in {"skip", "custom_no_patch"} for patch in patches)


def test_approved_patches_returns_a_fresh_copy() -> None:
    option = _option()
    session = FakeInteractiveSession({"finding-1": [option]})
    session.present_finding("finding-1")
    session.record_choice("finding-1", option)

    first = session.approved_patches()
    first[0].anchor["line"] = 99

    second = session.approved_patches()
    assert second[0].anchor["line"] == 42


def test_scripted_answers_are_consumed_and_summarized() -> None:
    session = FakeInteractiveSession(answers=["yes", "later"])

    assert session.ask("Apply patch?") == "yes"
    assert session.ask("Review next?") == "later"
    assert session.ask("Anything else?") == ""
    assert session.qa_transcript_summary == [
        {"question": "Apply patch?", "answer": "yes"},
        {"question": "Review next?", "answer": "later"},
        {"question": "Anything else?", "answer": ""},
    ]


def test_seed_can_import_mapping_style_findings() -> None:
    option = _option()
    session = FakeInteractiveSession()

    session.seed({"findings": [{"id": "finding-1", "options": [option]}]})

    assert session.present_finding("finding-1") == [option]
