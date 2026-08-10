# pylint: disable=missing-module-docstring,missing-function-docstring
# pylint: disable=protected-access,line-too-long

from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.story_criteria import (
    AcceptanceCriterion,
    CriteriaEvaluation,
    CriterionVerdict,
    StoryCriteriaError,
    _CriteriaAssessment,
    _CriterionAssessment,
    changes_from_verdicts,
    evaluate_acceptance_criteria,
    evaluation_summary,
    parse_acceptance_criteria,
)


_CONTRACT = (
    "<!-- pdd-story-contract derived-from-story=\"../story__x.md\" -->\n\n"
    "# Contract: thing\n\n"
    "## Covers\n\n- R1: does the thing\n\n"
    "## Acceptance Criteria\n\n"
    "1. Given a valid CSV, when uploaded, then a summary report is shown.\n"
    "2. Given an empty CSV, when uploaded, then the upload is rejected\n"
    "   with a message naming the file.\n\n"
    "## Oracle\n\n- returned value shape\n"
)


# --------------------------------------------------------------------------
# parse_acceptance_criteria
# --------------------------------------------------------------------------


def test_parses_numbered_criteria_from_contract():
    criteria = parse_acceptance_criteria(_CONTRACT)

    assert [c.id for c in criteria] == ["AC1", "AC2"]
    assert criteria[0].text.startswith("Given a valid CSV")


def test_folds_continuation_lines_into_the_criterion_above():
    criteria = parse_acceptance_criteria(_CONTRACT)

    assert criteria[1].text == (
        "Given an empty CSV, when uploaded, then the upload is rejected "
        "with a message naming the file."
    )


def test_parses_bullet_criteria_from_a_legacy_story():
    story = (
        "# User Story: Legacy\n\n"
        "## Story\n\nAs a legacy user, I want math.\n\n"
        "## Acceptance Criteria\n\n"
        "- Basic addition works.\n"
        "- Division by zero is rejected.\n"
    )

    assert [c.text for c in parse_acceptance_criteria(story)] == [
        "Basic addition works.",
        "Division by zero is rejected.",
    ]


def test_stops_at_the_next_heading():
    criteria = parse_acceptance_criteria(_CONTRACT)

    assert all("returned value shape" not in c.text for c in criteria)


def test_returns_nothing_without_a_criteria_section():
    assert parse_acceptance_criteria("# Story\n\nJust prose, no criteria.\n") == []
    assert parse_acceptance_criteria("") == []


def test_returns_nothing_when_the_section_is_empty():
    assert parse_acceptance_criteria("## Acceptance Criteria\n\n## Oracle\n- x\n") == []


# --------------------------------------------------------------------------
# verdict folding: the model-independent half of the gate
# --------------------------------------------------------------------------


def _prompt(tmp_path: Path, body: str) -> Path:
    path = tmp_path / "upload_python.prompt"
    path.write_text(body, encoding="utf-8")
    return path


def _evaluate(tmp_path, assessments, prompt_body="The command MUST show a summary report after upload."):
    prompt_path = _prompt(tmp_path, prompt_body)
    criteria = parse_acceptance_criteria(_CONTRACT)
    response = {
        "result": _CriteriaAssessment(assessments=assessments),
        "cost": 0.03,
        "model_name": "test-model",
    }
    with (
        patch("pdd.story_criteria.load_prompt_template", return_value="TEMPLATE"),
        patch("pdd.story_criteria.preprocess", side_effect=lambda text, **_k: text),
        patch("pdd.story_criteria.llm_invoke", return_value=response),
    ):
        return evaluate_acceptance_criteria([prompt_path], "story text", criteria)


def test_satisfied_with_a_verbatim_citation_passes(tmp_path):
    evaluation = _evaluate(
        tmp_path,
        [
            _CriterionAssessment(
                criterion_id="AC1",
                status="satisfied",
                citation="MUST show a summary report after upload",
                prompt_name="upload_python.prompt",
            ),
            _CriterionAssessment(
                criterion_id="AC2",
                status="satisfied",
                citation="MUST show a summary report after upload",
            ),
        ],
    )

    assert evaluation.passed is True
    assert evaluation.complete is True
    assert all(v.citation_verified for v in evaluation.verdicts)
    assert evaluation.cost == 0.03
    assert evaluation.model == "test-model"


def test_only_unsatisfied_fails_the_story(tmp_path):
    evaluation = _evaluate(
        tmp_path,
        [
            _CriterionAssessment(
                criterion_id="AC1",
                status="unsatisfied",
                rationale="Nothing requires a summary report.",
            ),
            _CriterionAssessment(criterion_id="AC2", status="unclear"),
        ],
    )

    assert evaluation.passed is False
    assert [v.criterion_id for v in evaluation.unsatisfied] == ["AC1"]


def test_unclear_is_advisory_and_never_fails(tmp_path):
    """The core of issue #5: a hedging model must not fail a correct prompt set."""
    evaluation = _evaluate(
        tmp_path,
        [
            _CriterionAssessment(criterion_id="AC1", status="unclear"),
            _CriterionAssessment(criterion_id="AC2", status="unclear"),
        ],
    )

    assert evaluation.passed is True
    assert len(evaluation.unclear) == 2
    assert evaluation.unsatisfied == []


def test_satisfied_without_a_citation_degrades_to_unclear(tmp_path):
    evaluation = _evaluate(
        tmp_path,
        [
            _CriterionAssessment(criterion_id="AC1", status="satisfied", citation="yes"),
            _CriterionAssessment(criterion_id="AC2", status="satisfied", citation=""),
        ],
    )

    assert [v.status for v in evaluation.verdicts] == ["unclear", "unclear"]
    assert evaluation.passed is True


def test_unverifiable_citation_is_reported_but_still_passes(tmp_path):
    """Models paraphrase; a false alarm here would restore model-sensitivity."""
    evaluation = _evaluate(
        tmp_path,
        [
            _CriterionAssessment(
                criterion_id="AC1",
                status="satisfied",
                citation="the prompt requires a summary to be displayed",
            ),
            _CriterionAssessment(
                criterion_id="AC2",
                status="satisfied",
                citation="MUST show a summary report after upload",
            ),
        ],
    )

    assert evaluation.passed is True
    assert evaluation.verdicts[0].citation_verified is False
    assert evaluation.verdicts[1].citation_verified is True


def test_a_skipped_criterion_is_unevaluated_not_a_pass(tmp_path):
    """A short answer must leave the run incomplete, never silently green."""
    evaluation = _evaluate(
        tmp_path,
        [
            _CriterionAssessment(
                criterion_id="AC1",
                status="satisfied",
                citation="MUST show a summary report after upload",
            )
        ],
    )

    assert evaluation.passed is False
    assert evaluation.complete is False
    assert [v.criterion_id for v in evaluation.unevaluated] == ["AC2"]


def test_empty_assessment_list_fails_closed(tmp_path):
    evaluation = _evaluate(tmp_path, [])

    assert evaluation.passed is False
    assert len(evaluation.unevaluated) == 2


def test_unrecognized_status_becomes_unclear_never_satisfied(tmp_path):
    evaluation = _evaluate(
        tmp_path,
        [
            _CriterionAssessment(criterion_id="AC1", status="probably fine"),
            _CriterionAssessment(criterion_id="AC2", status=""),
        ],
    )

    assert [v.status for v in evaluation.verdicts] == ["unclear", "unclear"]


@pytest.mark.parametrize("raw_id", ["AC1", "ac1", "AC 1", "ac-1", "1", "criterion 1"])
def test_criterion_identifiers_are_matched_loosely(tmp_path, raw_id):
    evaluation = _evaluate(
        tmp_path,
        [
            _CriterionAssessment(
                criterion_id=raw_id,
                status="satisfied",
                citation="MUST show a summary report after upload",
            )
        ],
    )

    assert evaluation.verdicts[0].status == "satisfied"


def test_unknown_criterion_ids_are_dropped(tmp_path):
    evaluation = _evaluate(
        tmp_path,
        [
            _CriterionAssessment(criterion_id="AC9", status="unsatisfied"),
            _CriterionAssessment(criterion_id="not a criterion", status="unsatisfied"),
        ],
    )

    assert evaluation.unsatisfied == []
    assert len(evaluation.unevaluated) == 2


def test_duplicate_assessments_keep_the_first(tmp_path):
    evaluation = _evaluate(
        tmp_path,
        [
            _CriterionAssessment(criterion_id="AC1", status="unsatisfied"),
            _CriterionAssessment(
                criterion_id="AC1",
                status="satisfied",
                citation="MUST show a summary report after upload",
            ),
            _CriterionAssessment(criterion_id="AC2", status="unclear"),
        ],
    )

    assert evaluation.verdicts[0].status == "unsatisfied"


# --------------------------------------------------------------------------
# failure modes
# --------------------------------------------------------------------------


def test_malformed_result_raises_instead_of_passing(tmp_path):
    """A malformed response must not be reported as an empty (passing) verdict."""
    prompt_path = _prompt(tmp_path, "body")
    with (
        patch("pdd.story_criteria.load_prompt_template", return_value="TEMPLATE"),
        patch("pdd.story_criteria.preprocess", side_effect=lambda text, **_k: text),
        patch(
            "pdd.story_criteria.llm_invoke",
            return_value={"result": "not a model", "cost": 0.04, "model_name": "m"},
        ),
        pytest.raises(StoryCriteriaError) as excinfo,
    ):
        evaluate_acceptance_criteria(
            [prompt_path], "story", parse_acceptance_criteria(_CONTRACT)
        )

    assert excinfo.value.cost == 0.04


def test_missing_template_raises(tmp_path):
    prompt_path = _prompt(tmp_path, "body")
    with (
        patch("pdd.story_criteria.load_prompt_template", return_value=None),
        pytest.raises(StoryCriteriaError),
    ):
        evaluate_acceptance_criteria(
            [prompt_path], "story", parse_acceptance_criteria(_CONTRACT)
        )


def test_no_criteria_makes_no_llm_call():
    with patch("pdd.story_criteria.llm_invoke") as mock_invoke:
        evaluation = evaluate_acceptance_criteria([], "story", [])

    mock_invoke.assert_not_called()
    assert evaluation.verdicts == []
    assert evaluation.passed is False


# --------------------------------------------------------------------------
# adapters
# --------------------------------------------------------------------------


def test_changes_are_rendered_only_for_unsatisfied_criteria():
    verdicts = [
        CriterionVerdict("AC1", "shows a report", "satisfied", citation="x" * 20),
        CriterionVerdict(
            "AC2",
            "rejects empty files",
            "unsatisfied",
            prompt_name="upload_python.prompt",
            rationale="No rejection is required.",
        ),
        CriterionVerdict("AC3", "is fast", "unclear"),
    ]

    changes = changes_from_verdicts(verdicts)

    assert len(changes) == 1
    assert changes[0]["prompt_name"] == "upload_python.prompt"
    assert "AC2 is not satisfied" in changes[0]["change_instructions"]
    assert "No rejection is required." in changes[0]["change_instructions"]


def test_changes_fall_back_to_the_default_prompt_name():
    verdicts = [CriterionVerdict("AC1", "does a thing", "unsatisfied")]

    changes = changes_from_verdicts(verdicts, default_prompt_name="only_python.prompt")

    assert changes[0]["prompt_name"] == "only_python.prompt"


def test_evaluation_summary_counts_each_status():
    evaluation = CriteriaEvaluation(
        verdicts=[
            CriterionVerdict("AC1", "a", "satisfied"),
            CriterionVerdict("AC2", "b", "unsatisfied"),
            CriterionVerdict("AC3", "c", "unclear"),
            CriterionVerdict("AC4", "d", "unevaluated"),
        ]
    )

    assert evaluation_summary(evaluation) == (1, 1, 1, 1)


def test_verdict_serializes_to_a_json_safe_mapping():
    verdict = CriterionVerdict("AC1", "does a thing", "satisfied", citation="c" * 20)

    assert verdict.as_dict() == {
        "criterion_id": "AC1",
        "criterion_text": "does a thing",
        "status": "satisfied",
        "citation": "c" * 20,
        "prompt_name": "",
        "rationale": "",
        "citation_verified": False,
    }


def test_criterion_is_hashable_and_frozen():
    criterion = AcceptanceCriterion(id="AC1", text="does a thing")

    assert {criterion}
    with pytest.raises(Exception):
        criterion.text = "mutated"  # type: ignore[misc]
