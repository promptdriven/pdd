"""Tests for deterministic local intent planning."""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from pdd.intent import (
    INTENT_PLAN_SCHEMA_VERSION,
    build_intent_plan,
    detected_technology_terms,
    intent_plan_to_dict,
    render_review_card,
)


def _write_pressure_architecture(root: Path) -> None:
    prompts = root / "prompts"
    prompts.mkdir(parents=True)
    (prompts / "pressure_trace_analyzer_python.prompt").write_text(
        "Analyze uploaded pressure traces.",
        encoding="utf-8",
    )
    (root / ".pddrc").write_text("version: '1.0'\n", encoding="utf-8")
    (root / "architecture.json").write_text(
        json.dumps(
            [
                {
                    "reason": "Detect pressure excursions for valve diagnosis.",
                    "description": "Highlights out-of-limit pressure intervals for test engineers.",
                    "dependencies": [],
                    "priority": 1,
                    "filename": "pressure_trace_analyzer_python.prompt",
                    "filepath": "src/pressure_trace_analyzer.py",
                    "tags": ["pressure", "trace", "diagnostics"],
                }
            ]
        ),
        encoding="utf-8",
    )


def _file_inventory(root: Path) -> set[str]:
    return {
        path.relative_to(root).as_posix()
        for path in root.rglob("*")
        if path.is_file()
    }


def test_existing_pdd_plan_preserves_request_and_finds_candidate(tmp_path: Path) -> None:
    _write_pressure_architecture(tmp_path)
    request = (
        "As a test engineer, highlight pressure intervals outside the permitted band. "
        "Never modify the uploaded samples. For example, show when a valve spike begins."
    )

    before = _file_inventory(tmp_path)
    plan = build_intent_plan(request, tmp_path, title="Pressure limits")

    assert plan.schema_version == INTENT_PLAN_SCHEMA_VERSION
    assert plan.project_kind == "existing_pdd"
    assert plan.scope_kind == "repository"
    assert plan.adoption_scenario == "existing_pdd_change"
    assert plan.recommended_workflow == "change_existing_pdd"
    assert plan.original_request == request
    assert len(plan.original_request_sha256) == 64
    assert plan.intent_id.startswith("pressure-limits-")
    assert plan.candidate_targets
    assert plan.candidate_targets[0].prompt_path == (
        "prompts/pressure_trace_analyzer_python.prompt"
    )
    assert "pressure" in plan.candidate_targets[0].matched_terms
    assert plan.must_preserve == ("Never modify the uploaded samples.",)
    assert plan.examples == (
        "For example, show when a valve spike begins.",
    )
    assert plan.story_recommended is True
    assert _file_inventory(tmp_path) == before


def test_structured_plan_reports_truthful_capabilities(tmp_path: Path) -> None:
    plan = build_intent_plan("Create a local calculator.", tmp_path)
    payload = intent_plan_to_dict(plan)

    assert payload["schema_version"] == "pdd.intent.plan.v1"
    assert payload["project"]["kind"] == "greenfield"
    assert payload["project"]["adoption_scenario"] == "new_project_design"
    assert payload["capabilities"] == {
        "planning": True,
        "apply": False,
        "writes_project_files": False,
        "requires_github": False,
        "invokes_llm": False,
    }


def test_conventional_project_routes_through_characterization(tmp_path: Path) -> None:
    (tmp_path / "app.py").write_text("print('existing')\n", encoding="utf-8")

    plan = build_intent_plan("Add CSV export.", tmp_path)

    assert plan.project_kind == "conventional_brownfield"
    assert plan.adoption_scenario == "existing_project_adoption"
    assert plan.recommended_workflow == "characterize_then_adopt"
    assert "characterized" in plan.open_decisions[0]


def test_existing_monorepo_subproject_is_scoped_locally(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    subproject = tmp_path / "services" / "billing"
    subproject.mkdir(parents=True)
    (subproject / "service.py").write_text("def charge(): ...\n", encoding="utf-8")
    sibling = tmp_path / "services" / "unrelated"
    sibling.mkdir(parents=True)
    (sibling / ".pddrc").write_text("version: '1.0'\n", encoding="utf-8")

    plan = build_intent_plan("Add invoice reconciliation.", subproject)

    assert plan.scope_kind == "subproject"
    assert plan.repository_root == str(tmp_path.resolve())
    assert plan.project_kind == "conventional_brownfield"
    assert plan.adoption_scenario == "existing_subproject_adoption"
    assert plan.pdd_signals == ()
    assert any("repository boundary" in item for item in plan.open_decisions)


def test_proposed_new_monorepo_subproject_need_not_exist(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    proposed = tmp_path / "services" / "new_analyzer"

    plan = build_intent_plan("Create a pressure analyzer.", proposed)

    assert plan.project_exists is False
    assert plan.scope_kind == "subproject"
    assert plan.project_kind == "greenfield"
    assert plan.adoption_scenario == "new_subproject_design"
    assert not proposed.exists()


def test_invalid_architecture_is_warning_not_crash(tmp_path: Path) -> None:
    (tmp_path / "architecture.json").write_text("{not-json", encoding="utf-8")

    plan = build_intent_plan("Improve checkout.", tmp_path)

    assert plan.project_kind == "existing_pdd"
    assert plan.candidate_targets == ()
    assert any("Could not read architecture.json" in warning for warning in plan.warnings)


def test_prompt_only_project_can_propose_candidate(tmp_path: Path) -> None:
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "invoice_reconciliation_python.prompt").write_text(
        "Reconcile invoices.", encoding="utf-8"
    )

    plan = build_intent_plan("Improve invoice reconciliation.", tmp_path)

    assert plan.project_kind == "existing_pdd"
    assert plan.candidate_targets[0].product_area == "Invoice Reconciliation"
    assert plan.candidate_targets[0].output_path is None


def test_no_token_match_does_not_fabricate_target(tmp_path: Path) -> None:
    _write_pressure_architecture(tmp_path)

    plan = build_intent_plan("Add multilingual checkout receipts.", tmp_path)

    assert plan.candidate_targets == ()
    assert any("No affected product area" in item for item in plan.open_decisions)


def test_generic_workflow_terms_do_not_select_unrelated_modules(
    tmp_path: Path,
) -> None:
    _write_pressure_architecture(tmp_path)

    plan = build_intent_plan(
        "Let an AI agent plan a project locally without a GitHub issue.",
        tmp_path,
    )

    assert plan.candidate_targets == ()


def test_multiword_product_intent_outranks_unrelated_internal_intent(
    tmp_path: Path,
) -> None:
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    for filename in ("intent_python.prompt", "agentic_split_step0_intent_LLM.prompt"):
        (prompts / filename).write_text("Contract.", encoding="utf-8")
    (tmp_path / "architecture.json").write_text(
        json.dumps(
            [
                {
                    "reason": "Plans ordinary-language product intent locally.",
                    "description": "The PDD intent planning front door.",
                    "dependencies": [],
                    "priority": 1,
                    "filename": "intent_python.prompt",
                    "filepath": "pdd/intent.py",
                    "tags": ["intent", "pdd-intent"],
                },
                {
                    "reason": "Records intent for an internal agentic split step.",
                    "description": "Step zero of the agentic split workflow.",
                    "dependencies": [],
                    "priority": 2,
                    "filename": "agentic_split_step0_intent_LLM.prompt",
                    "filepath": "pdd/agentic_split/step0_intent.py",
                    "tags": ["intent", "agentic-split"],
                },
            ]
        ),
        encoding="utf-8",
    )

    plan = build_intent_plan(
        "Use PDD intent to plan ordinary-language product intent.",
        tmp_path,
    )

    assert [target.prompt_path for target in plan.candidate_targets] == [
        "prompts/intent_python.prompt"
    ]


def test_review_card_uses_human_headings_and_disclaims_application(tmp_path: Path) -> None:
    plan = build_intent_plan("Create a calculator.", tmp_path)

    card = render_review_card(plan)

    for heading in (
        "What I heard:",
        "What will change:",
        "What must stay unchanged:",
        "Important examples:",
        "How we will prove it:",
        "Affected product areas:",
        "Open decisions:",
        "Story coverage:",
    ):
        assert heading in card
    assert "Planning only: no project files were changed" in card


@pytest.mark.parametrize("intent_text", ["", " ", "\n\t"])
def test_empty_intent_is_rejected(tmp_path: Path, intent_text: str) -> None:
    with pytest.raises(ValueError, match="must not be empty"):
        build_intent_plan(intent_text, tmp_path)


def test_existing_file_cannot_be_project_root(tmp_path: Path) -> None:
    path = tmp_path / "not-a-project"
    path.write_text("x", encoding="utf-8")

    with pytest.raises(ValueError, match="not a directory"):
        build_intent_plan("Do something.", path)


def test_function_words_do_not_manufacture_candidates(tmp_path: Path) -> None:
    """Filler words must not link a request to an unrelated product area."""
    prompts = tmp_path / "prompts"
    prompts.mkdir(parents=True)
    (prompts / "billing_totals_python.prompt").write_text("x", encoding="utf-8")
    (tmp_path / ".pddrc").write_text("version: '1.0'\n", encoding="utf-8")
    (tmp_path / "architecture.json").write_text(
        json.dumps(
            [
                {
                    "reason": "Step 11 of the workflow runs for each queued item.",
                    "description": "Handles every other retry while the queue drains.",
                    "filename": "billing_totals_python.prompt",
                    "filepath": "src/billing_totals.py",
                }
            ]
        ),
        encoding="utf-8",
    )

    plan = build_intent_plan(
        "Show a chart for each visitor so that every one of them has what they "
        "want, while the same layout is what it was before.",
        tmp_path,
    )

    assert plan.candidate_targets == ()


def test_docs_only_directory_warns_before_greenfield_generation(
    tmp_path: Path,
) -> None:
    """An existing directory holding only prose is not a blank project root."""
    (tmp_path / "notes.md").write_text("# Design notes\n", encoding="utf-8")
    (tmp_path / "README.md").write_text("# Overview\n", encoding="utf-8")

    plan = build_intent_plan("Add offline PDF export.", tmp_path)

    assert plan.project_kind == "greenfield"
    assert any("no recognized source" in item for item in plan.open_decisions)
    assert any("non-source files" in item for item in plan.warnings)


def test_empty_greenfield_root_stays_unwarned(tmp_path: Path) -> None:
    """The guard must not fire for a genuinely empty project root."""
    plan = build_intent_plan("Add offline PDF export.", tmp_path)

    assert plan.project_kind == "greenfield"
    assert not any("no recognized source" in item for item in plan.open_decisions)
    assert not any("non-source files" in item for item in plan.warnings)


def test_greenfield_without_a_named_technology_is_flagged(tmp_path: Path) -> None:
    """Planning must surface the undecided stack before apply is attempted."""
    plan = build_intent_plan("Create a calculator.", tmp_path / "new_project")

    assert plan.project_kind == "greenfield"
    assert detected_technology_terms(plan.original_request) == ()
    assert any("No language or runtime" in item for item in plan.open_decisions)
    assert any("cannot select a technology" in item for item in plan.warnings)


def test_named_technology_is_detected_and_not_flagged(tmp_path: Path) -> None:
    plan = build_intent_plan(
        "Create a calculator in Python using poetry.", tmp_path / "new_project"
    )

    assert detected_technology_terms(plan.original_request) == ("poetry", "python")
    assert not any("No language or runtime" in item for item in plan.open_decisions)
    assert not any("cannot select a technology" in item for item in plan.warnings)


def test_ambiguous_english_is_not_mistaken_for_a_technology() -> None:
    """A false positive would let generation start on an undecided stack."""
    assert detected_technology_terms("Go through the c and r columns.") == ()
