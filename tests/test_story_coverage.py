from __future__ import annotations

import json
from pathlib import Path

import jsonschema
import pytest

from pdd.story_coverage import (
    compute_story_coverage,
    emit_story_coverage,
    format_summary_line,
    write_story_coverage,
)


def _write_story(stories_dir: Path, slug: str) -> Path:
    path = stories_dir / f"story__{slug}.md"
    path.write_text("## Story\n\n## Acceptance Criteria\n- ok\n", encoding="utf-8")
    return path


def _write_story_test(tests_dir: Path, story_ref: str, name: str = "test_flow") -> Path:
    path = tests_dir / "test_story_flow.py"
    path.write_text(
        "import pytest\n"
        f"@pytest.mark.story({story_ref!r})\n"
        f"def {name}():\n"
        "    assert True\n",
        encoding="utf-8",
    )
    return path


def _story_coverage_schema() -> dict:
    schema_path = (
        Path(__file__).parents[1] / "pdd" / "schemas" / "story_coverage.schema.json"
    )
    return json.loads(schema_path.read_text(encoding="utf-8"))


def test_compute_story_coverage_counts_story_marked_tests(tmp_path: Path):
    stories = tmp_path / "user_stories"
    tests = tmp_path / "tests"
    stories.mkdir()
    tests.mkdir()
    _write_story(stories, "checkout_flow")
    _write_story(stories, "shipping_flow")
    _write_story_test(tests, "checkout_flow")

    coverage = compute_story_coverage(tmp_path, stories_dir=stories, tests_dir=tests)

    assert coverage.status == "not_applicable"
    assert coverage.story_count == 2
    assert coverage.story_backed_test_count == 1
    assert coverage.stories_covered == 0
    assert coverage.story_coverage_pct is None
    assert coverage.pass_rate is None
    assert coverage.passing_test_count == 0
    assert coverage.gap_stories == ["shipping_flow"]


def test_collection_only_does_not_report_failing_story_test_as_passing(tmp_path: Path):
    stories = tmp_path / "user_stories"
    tests = tmp_path / "tests"
    stories.mkdir()
    tests.mkdir()
    _write_story(stories, "broken")
    path = tests / "test_story_flow.py"
    path.write_text(
        "import pytest\n"
        "@pytest.mark.story('broken')\n"
        "def test_broken():\n"
        "    assert False\n",
        encoding="utf-8",
    )

    coverage = compute_story_coverage(tmp_path, stories_dir=stories, tests_dir=tests)

    assert coverage.status == "not_applicable"
    assert coverage.story_backed_test_count == 1
    assert coverage.stories_covered == 0
    assert coverage.pass_rate is None
    assert coverage.passing_test_count == 0


def test_story_file_marker_ref_normalizes_to_story_id(tmp_path: Path):
    stories = tmp_path / "user_stories"
    tests = tmp_path / "tests"
    stories.mkdir()
    tests.mkdir()
    _write_story(stories, "checkout_flow")
    _write_story_test(tests, "user_stories/story__checkout_flow.md")

    coverage = compute_story_coverage(tmp_path, stories_dir=stories, tests_dir=tests)

    assert coverage.stories_covered == 0
    assert coverage.orphan_tests == []


def test_zero_stories_is_not_applicable(tmp_path: Path):
    stories = tmp_path / "user_stories"
    tests = tmp_path / "tests"
    stories.mkdir()
    tests.mkdir()

    coverage = compute_story_coverage(tmp_path, stories_dir=stories, tests_dir=tests)

    assert coverage.status == "not_applicable"
    assert coverage.story_coverage_pct is None
    assert "not_applicable" in format_summary_line(coverage)


def test_write_story_coverage_writes_latest_and_run_snapshot(tmp_path: Path):
    stories = tmp_path / "user_stories"
    tests = tmp_path / "tests"
    stories.mkdir()
    tests.mkdir()
    _write_story(stories, "checkout_flow")
    _write_story_test(tests, "checkout_flow")
    coverage = compute_story_coverage(tmp_path, stories_dir=stories, tests_dir=tests)

    latest = write_story_coverage(coverage, tmp_path, run_id="run-123")

    assert latest == tmp_path / ".pdd" / "evidence" / "stories" / "coverage.latest.json"
    snapshot = tmp_path / ".pdd" / "evidence" / "stories" / "runs" / "run-123.json"
    assert snapshot.exists()
    assert json.loads(latest.read_text(encoding="utf-8"))["schema_version"] == 1
    assert json.loads(snapshot.read_text(encoding="utf-8"))["run_id"] == "run-123"


def test_story_coverage_schema_accepts_unavailable_pass_rate(tmp_path: Path):
    stories = tmp_path / "user_stories"
    tests = tmp_path / "tests"
    stories.mkdir()
    tests.mkdir()
    _write_story(stories, "checkout_flow")
    _write_story_test(tests, "checkout_flow")
    coverage = compute_story_coverage(tmp_path, stories_dir=stories, tests_dir=tests)

    jsonschema.validate(instance=coverage.to_dict(), schema=_story_coverage_schema())


def test_story_coverage_schema_rejects_percentage_pass_rate(tmp_path: Path):
    stories = tmp_path / "user_stories"
    tests = tmp_path / "tests"
    stories.mkdir()
    tests.mkdir()
    _write_story(stories, "checkout_flow")
    _write_story_test(tests, "checkout_flow")
    payload = compute_story_coverage(tmp_path, stories_dir=stories, tests_dir=tests).to_dict()
    payload["pass_rate"] = 100.0

    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(instance=payload, schema=_story_coverage_schema())


def test_emit_story_coverage_prints_and_appends_step_summary(tmp_path: Path, capsys, monkeypatch):
    stories = tmp_path / "user_stories"
    tests = tmp_path / "tests"
    stories.mkdir()
    tests.mkdir()
    _write_story(stories, "checkout_flow")
    _write_story_test(tests, "checkout_flow")
    summary = tmp_path / "summary.md"
    monkeypatch.setenv("GITHUB_STEP_SUMMARY", str(summary))

    coverage = emit_story_coverage(
        tmp_path,
        stories_dir=stories,
        tests_dir=tests,
        run_id="run-456",
    )

    line = (
        "story regression: not_applicable "
        "(1 collected story tests across 0/1 verified stories; pass-rate unavailable)"
    )
    assert coverage.run_id == "run-456"
    assert capsys.readouterr().out == line + "\n"
    assert line in summary.read_text(encoding="utf-8")
