"""Structural contracts for documentation-only CI fast paths."""

from pathlib import Path

import yaml


UNIT_WORKFLOW = Path(".github/workflows/unit-tests.yml")


def _unit_jobs() -> dict:
    workflow = yaml.safe_load(UNIT_WORKFLOW.read_text(encoding="utf-8"))
    return workflow["jobs"]


def test_docs_only_prs_keep_required_check_without_heavy_jobs() -> None:
    """Required status remains stable while expensive jobs skip documentation."""
    jobs = _unit_jobs()
    classifier = jobs["changes"]
    required = jobs["unit-tests"]

    assert classifier["outputs"]["code_changed"] == (
        "${{ steps.classify.outputs.code_changed }}"
    )
    classify = next(
        step for step in classifier["steps"]
        if step.get("name") == "Classify pull request paths"
    )
    assert "docs/*|*.md)" in classify["run"]
    assert 'git diff --name-only -z "$BASE_SHA" "$HEAD_SHA"' in classify["run"]

    heavy_jobs = (
        "full-unit-tests",
        "public-cli-regression",
        "story-regression",
        "package-preprocess-smoke",
        "repo-bloat-docker-e2e",
    )
    for job_id in heavy_jobs:
        assert jobs[job_id]["needs"] == "changes"
        assert "needs.changes.outputs.code_changed == 'true'" in jobs[job_id]["if"]

    assert required["name"] == "Run Unit Tests"
    assert required["needs"] == ["changes", "full-unit-tests"]
    assert "always()" in required["if"]
    gate = next(
        step for step in required["steps"]
        if step.get("name") == "Resolve required unit-test check"
    )
    assert 'if [ "$CLASSIFY_RESULT" != "success" ]' in gate["run"]
    assert 'if [ "$CODE_CHANGED" = "false" ]' in gate["run"]
    assert 'if [ "$FULL_RESULT" != "success" ]' in gate["run"]
