from pathlib import Path

import pytest

from pdd.checkup_interactive_session import (
    ApprovedPatch,
    FakeInteractiveSession,
    InteractiveRepairSession,
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
        {
            "finding-approving": [approving],
            "finding-skip": [skipped],
            "finding-custom": [custom_no_patch],
        }
    )

    session.present_finding("finding-approving")
    session.record_choice("finding-approving", approving)
    session.present_finding("finding-skip")
    session.record_choice("finding-skip", skipped)
    session.present_finding("finding-custom")
    session.record_choice("finding-custom", custom_no_patch)

    patches = session.approved_patches()
    assert len(patches) == 1
    assert patches[0].kind == approving.patch.kind
    assert patches[0].finding_id == "finding-approving"
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


# ---------------------------------------------------------------------------
# ApprovedPatch dataclass coercions
# ---------------------------------------------------------------------------


def test_approved_patch_coerces_string_target_to_path() -> None:
    patch = ApprovedPatch(
        kind="vocab_definition",
        target="prompts/refund_python.prompt",  # type: ignore[arg-type]
        anchor={"finding_id": "f1", "line": 1},
        replacement="definition text",
    )
    assert isinstance(patch.target, Path)
    assert patch.target == Path("prompts/refund_python.prompt")


def test_approved_patch_anchor_is_copy_independent_of_input() -> None:
    original_anchor = {"finding_id": "f1", "line": 10}
    patch = ApprovedPatch(
        kind="vocab_definition",
        target=Path("prompts/foo.prompt"),
        anchor=original_anchor,
        replacement="y",
    )
    original_anchor["line"] = 99
    assert patch.anchor["line"] == 10, "Mutating the input dict must not affect the stored anchor"


# ---------------------------------------------------------------------------
# FakeInteractiveSession.seed() behaviour
# ---------------------------------------------------------------------------


def test_seed_non_mapping_report_stores_report_without_raising() -> None:
    session = FakeInteractiveSession()
    session.seed("plain string report")
    assert session.report == "plain string report"

    session2 = FakeInteractiveSession()
    session2.seed(None)
    assert session2.report is None

    session3 = FakeInteractiveSession()
    session3.seed([1, 2, 3])
    assert session3.report == [1, 2, 3]


def test_seed_imports_findings_using_finding_id_key() -> None:
    option = _option()
    session = FakeInteractiveSession()
    session.seed({"findings": [{"finding_id": "finding-x", "options": [option]}]})
    assert session.present_finding("finding-x") == [option]


def test_seed_does_not_overwrite_preexisting_options() -> None:
    original_option = _option("original")
    session = FakeInteractiveSession({"finding-1": [original_option]})

    seed_option = _option("seed")
    session.seed({"findings": [{"id": "finding-1", "options": [seed_option]}]})

    # setdefault must preserve the original — seed must not overwrite
    assert session.present_finding("finding-1") == [original_option]


# ---------------------------------------------------------------------------
# FakeInteractiveSession.present_finding() behaviour
# ---------------------------------------------------------------------------


def test_present_finding_returns_independent_list_each_call() -> None:
    option = _option()
    session = FakeInteractiveSession({"finding-1": [option]})

    result1 = session.present_finding("finding-1")
    result1.append(_option("extra"))  # mutate the returned list

    result2 = session.present_finding("finding-1")
    assert len(result2) == 1, "Mutating one call's returned list must not affect the next call"


def test_present_finding_returns_empty_list_for_unknown_finding() -> None:
    session = FakeInteractiveSession()
    assert session.present_finding("no-such-finding") == []


# ---------------------------------------------------------------------------
# FakeInteractiveSession.ask() queue exhaustion
# ---------------------------------------------------------------------------


def test_ask_returns_empty_string_when_answers_queue_is_empty() -> None:
    session = FakeInteractiveSession(answers=[])
    assert session.ask("Any question?") == ""
    # Transcript should record the empty answer
    assert session.qa_transcript_summary == [{"question": "Any question?", "answer": ""}]


# ---------------------------------------------------------------------------
# Multi-finding sessions and approved_patches() edge cases
# ---------------------------------------------------------------------------


def test_approved_patches_returns_empty_list_when_no_choices_recorded() -> None:
    session = FakeInteractiveSession()
    assert session.approved_patches() == []


def test_multi_finding_session_produces_ordered_approved_patches() -> None:
    opt1 = _option("A", "vocab_definition")
    opt2 = _option("B", "contract_rule")
    session = FakeInteractiveSession(
        {"finding-1": [opt1], "finding-2": [opt2]}
    )

    session.present_finding("finding-1")
    session.record_choice("finding-1", opt1)
    session.present_finding("finding-2")
    session.record_choice("finding-2", opt2)

    patches = session.approved_patches()
    assert len(patches) == 2
    assert patches[0].kind == opt1.patch.kind
    assert patches[1].kind == opt2.patch.kind


def test_record_choice_rejects_duplicate_finding_id() -> None:
    option = _option()
    session = FakeInteractiveSession({"finding-1": [option]})
    session.present_finding("finding-1")
    session.record_choice("finding-1", option)

    with pytest.raises(ValueError, match="already recorded"):
        session.record_choice("finding-1", option)


def test_approved_patches_stamps_finding_id_from_recorded_choice() -> None:
    option = _option()
    session = FakeInteractiveSession({"finding-1": [option]})
    session.present_finding("finding-1")
    session.record_choice("finding-1", option)

    patches = session.approved_patches()
    assert patches[0].finding_id == "finding-1"


def test_approved_patches_preserves_explicit_finding_id_on_patch() -> None:
    patch = _patch()
    patch.finding_id = "explicit-id"
    option = RepairOption(label="A", preview="preview", patch=patch)
    session = FakeInteractiveSession({"finding-1": [option]})
    session.present_finding("finding-1")
    session.record_choice("finding-1", option)

    assert session.approved_patches()[0].finding_id == "explicit-id"


def test_record_choice_rejects_stale_option_after_representing_finding() -> None:
    opt_a = _option("A")
    opt_b = _option("B")

    session = FakeInteractiveSession({"finding-1": [opt_a]})
    session.present_finding("finding-1")
    session.record_choice("finding-1", opt_a)

    # Replace available options and re-present
    session.options_by_finding["finding-1"] = [opt_b]
    session.present_finding("finding-1")

    # opt_a is no longer in the current presented set
    with pytest.raises(ValueError, match="not presented"):
        session.record_choice("finding-1", opt_a)

    # A second choice for the same finding is rejected even when newly presented
    with pytest.raises(ValueError, match="already recorded"):
        session.record_choice("finding-1", opt_b)
    assert len(session.recorded_choices) == 1


def test_approved_patches_excludes_no_patch_kind() -> None:
    no_patch_option = _option("skip", "no_patch")
    session = FakeInteractiveSession({"finding-1": [no_patch_option]})
    session.present_finding("finding-1")
    session.record_choice("finding-1", no_patch_option)
    assert session.approved_patches() == []


def test_approved_patches_deep_copy_is_independent_of_recorded_choice() -> None:
    option = _option()
    session = FakeInteractiveSession({"finding-1": [option]})
    session.present_finding("finding-1")
    session.record_choice("finding-1", option)

    patches = session.approved_patches()
    patches[0].anchor["line"] = 999  # mutate the copy

    # The recorded option's patch must be unaffected
    _, recorded_option = session.recorded_choices[0]
    assert recorded_option.patch.anchor["line"] == 42, (
        "approved_patches() must return deep copies that do not alias recorded option data"
    )


# ---------------------------------------------------------------------------
# Protocol conformance
# ---------------------------------------------------------------------------


def test_fake_session_satisfies_interactive_repair_session_protocol() -> None:
    """FakeInteractiveSession must structurally implement all InteractiveRepairSession methods."""
    # The type annotation is checked statically; runtime callable checks are belt-and-suspenders.
    session: InteractiveRepairSession = FakeInteractiveSession()
    assert callable(session.seed)
    assert callable(session.present_finding)
    assert callable(session.ask)
    assert callable(session.record_choice)
    assert callable(session.approved_patches)


# ---------------------------------------------------------------------------
# #1434 Hybrid scope: protocol layer only (no Pi/TTY backends in #1435)
# ---------------------------------------------------------------------------


def test_module_is_stdlib_only_contract() -> None:
    """#1435 protocol must not import click, pydantic, llm_invoke, or Pi bridge code."""
    import ast
    from pathlib import Path

    source = Path("pdd/checkup_interactive_session.py").read_text(encoding="utf-8")
    tree = ast.parse(source)
    imports = {
        (node.module or "")
        for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom) and node.module
    }
    forbidden = {"click", "pydantic", "pdd.llm_invoke", "pdd.llm_interactive_session"}
    assert not imports & forbidden
    assert "_pi_repair_bridge" not in source
    assert "llm_invoke" not in source


def test_docs_hybrid_python_owns_menus_and_apply() -> None:
    """Docs must align with #1434 Hybrid: Python owns menus/apply, not Pi."""
    from pathlib import Path

    doc = Path("docs/checkup_interactive_session.md").read_text(encoding="utf-8")
    assert "**Hybrid**" in doc or "Hybrid" in doc
    assert "Python always owns" in doc
    assert "numbered menus" in doc
    assert "`--apply` gating" in doc
    assert "do not delegate menus" in doc


def test_prompt_forbids_tty_pi_and_provider_calls() -> None:
    """Prompt contract must forbid TTY/Pi/provider backends in this module."""
    from pathlib import Path

    prompt = Path("pdd/prompts/checkup_interactive_session_python.prompt").read_text(
        encoding="utf-8"
    )
    assert "Use only the standard library." in prompt
    assert "MUST NOT prompt on TTY or Pi backends in this module." in prompt
    assert "MUST NOT call external providers." in prompt
    assert "implement Pi/TTY backends" in prompt
    assert "RepairOption.patch` must be non-optional" in prompt


def test_pdd_interface_conformance_allows_dataclass_exports() -> None:
    """Dataclass types must not be declared as functions with paren signatures."""
    import json
    import re
    from pathlib import Path

    from pdd.code_generator_main import _verify_pdd_interface_signatures

    prompt = Path("pdd/prompts/checkup_interactive_session_python.prompt").read_text(
        encoding="utf-8"
    )
    code = Path("pdd/checkup_interactive_session.py").read_text(encoding="utf-8")
    match = re.search(r"<pdd-interface>\s*(\{.*?\})\s*</pdd-interface>", prompt, re.S)
    assert match is not None
    interface = json.loads(match.group(1))
    function_names = {
        item["name"]
        for item in interface.get("module", {}).get("functions", [])
        if isinstance(item, dict) and item.get("name")
    }
    assert "ApprovedPatch" not in function_names
    assert "RepairOption" not in function_names

    _verify_pdd_interface_signatures(
        generated_code=code,
        prompt_content=prompt,
        prompt_name="checkup_interactive_session_python.prompt",
        output_path="pdd/checkup_interactive_session.py",
        architecture_entry={},
    )
