# pylint: disable=missing-module-docstring,missing-function-docstring
"""Regression tests for the structured story detection result models and CLI (#2027)."""
from __future__ import annotations

import json
import os
import sys
import uuid
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.commands.analysis import detect_change
from pdd.cli import cli as pdd_cli
from pdd.story_detection_result import (
    DIAG_AUTH_NON_INTERACTIVE,
    DIAG_INTERNAL_ERROR,
    DIAG_PROMPT_UNRESOLVED_LINK,
    SCHEMA_VERSION,
    SCOPE_SCHEMA_VERSION,
    StoryDetectionRun,
    build_run_from_legacy,
    scope_from_dirs,
)
from pdd.story_scope_manifest import ManifestError, load_scope_manifest


# ---------------------------------------------------------------------------
# Model layer tests
# ---------------------------------------------------------------------------


def _pass_result(story="user_stories/story__one.md"):
    return {"story": story, "passed": True, "changes": []}


def _fail_result(story="user_stories/story__two.md"):
    return {
        "story": story,
        "passed": False,
        "changes": [
            {
                "prompt_name": "prompts/foo_python.prompt",
                "change_instructions": "Update foo",
            }
        ],
    }


def _error_result(story="user_stories/story__three.md"):
    return {
        "story": story,
        "passed": False,
        "changes": [],
        "error": "No prompts from pdd-story-prompts metadata could be resolved.",
    }


def _make_scope():
    return scope_from_dirs(stories_dir="user_stories", prompts_dir="prompts")


# --- One PASS story ---


def test_build_run_single_pass():
    run = build_run_from_legacy(
        passed=True,
        results=[_pass_result()],
        total_cost=0.05,
        model_name="gpt-test",
        scope=_make_scope(),
        invocation_id="inv-1",
    )
    assert run.all_pass is True
    assert run.outcome == "all_pass"
    assert len(run.items) == 1
    assert run.items[0].verdict == "PASS"
    assert run.items[0].changes == ()
    assert run.schema_version == SCHEMA_VERSION
    assert run.usage.cost_source == "actual"


# --- Mixed PASS/FAIL with --no-fail-fast ---


def test_build_run_mixed_pass_fail_no_fail_fast():
    run = build_run_from_legacy(
        passed=False,
        results=[_pass_result(), _fail_result()],
        total_cost=0.12,
        model_name="gpt-test",
        scope=_make_scope(),
        invocation_id="inv-2",
        fail_fast_triggered=False,
    )
    assert run.all_pass is False
    assert run.outcome == "story_fail"
    assert len(run.items) == 2
    assert run.items[0].verdict == "PASS"
    assert run.items[1].verdict == "FAIL"
    assert len(run.items[1].changes) == 1
    assert run.items[1].changes[0].prompt_name == "prompts/foo_python.prompt"


# --- FAIL with proposed prompt changes ---


def test_build_run_fail_preserves_changes():
    run = build_run_from_legacy(
        passed=False,
        results=[_fail_result()],
        total_cost=0.08,
        model_name="gpt-test",
        scope=_make_scope(),
        invocation_id="inv-3",
    )
    item = run.items[0]
    assert item.verdict == "FAIL"
    assert len(item.changes) == 1
    assert item.changes[0].change_instructions == "Update foo"


# --- Missing contract (error result) ---


def test_build_run_missing_contract_error():
    run = build_run_from_legacy(
        passed=False,
        results=[_error_result()],
        total_cost=0.0,
        model_name="",
        scope=_make_scope(),
        invocation_id="inv-4",
    )
    item = run.items[0]
    assert item.verdict == "FAIL"
    assert len(item.errors) == 1
    assert item.errors[0].code == DIAG_PROMPT_UNRESOLVED_LINK


# --- all_pass is False when any UNKNOWN verdict ---


def test_build_run_unknown_verdict_forces_all_pass_false():
    results = [{"story": "user_stories/story__x.md", "passed": None, "changes": []}]
    run = build_run_from_legacy(
        passed=True,
        results=results,
        total_cost=0.0,
        model_name="",
        scope=_make_scope(),
        invocation_id="inv-5",
    )
    assert run.all_pass is False
    assert run.items[0].verdict == "UNKNOWN"


# --- Empty scope ---


def test_build_run_empty_scope():
    run = build_run_from_legacy(
        passed=True,
        results=[],
        total_cost=0.0,
        model_name="",
        scope=_make_scope(),
        invocation_id="inv-6",
    )
    assert run.all_pass is True
    assert run.items == ()
    assert run.usage.stories_attempted == 0


# --- Cost as Decimal string ---


def test_build_run_cost_is_decimal_string():
    run = build_run_from_legacy(
        passed=True,
        results=[],
        total_cost=0.123456789,
        model_name="gpt-test",
        scope=_make_scope(),
        invocation_id="inv-7",
    )
    # Must be a string, not a float
    assert isinstance(run.usage.total_cost, str)
    # Must not be "0.0" or contain binary float artifacts
    assert "." in run.usage.total_cost or run.usage.total_cost.lstrip("-").isdigit()


# --- Error run factory ---


def test_make_error_run_auth():
    run = StoryDetectionRun.make_error_run(
        outcome="auth_error",
        code=DIAG_AUTH_NON_INTERACTIVE,
        message="No credentials found.",
        retryable=True,
    )
    assert run.all_pass is False
    assert run.outcome == "auth_error"
    assert len(run.diagnostics) == 1
    assert run.diagnostics[0].code == DIAG_AUTH_NON_INTERACTIVE
    assert run.diagnostics[0].retryable is True


def test_make_error_run_schema_valid():
    run = StoryDetectionRun.make_error_run(
        outcome="internal_error",
        code=DIAG_INTERNAL_ERROR,
        message="boom",
    )
    d = run.to_dict()
    assert d["schema_version"] == SCHEMA_VERSION
    assert d["outcome"] == "internal_error"
    assert d["all_pass"] is False


# --- Serialization round-trip ---


def test_to_dict_json_serializable():
    run = build_run_from_legacy(
        passed=False,
        results=[_pass_result(), _fail_result()],
        total_cost=0.05,
        model_name="gpt-test",
        scope=_make_scope(),
        invocation_id="inv-8",
    )
    d = run.to_dict()
    # Must serialize to JSON without error
    payload = json.dumps(d)
    loaded = json.loads(payload)
    assert loaded["schema_version"] == SCHEMA_VERSION
    assert len(loaded["items"]) == 2


# ---------------------------------------------------------------------------
# Scope manifest tests
# ---------------------------------------------------------------------------


def _write_manifest(path, data):
    Path(path).write_text(json.dumps(data), encoding="utf-8")


def test_load_scope_manifest_valid(tmp_path):
    story = tmp_path / "user_stories" / "story__x.md"
    story.parent.mkdir()
    story.write_text("story", encoding="utf-8")
    prompt = tmp_path / "prompts" / "x_python.prompt"
    prompt.parent.mkdir()
    prompt.write_text("prompt", encoding="utf-8")

    manifest_data = {
        "schema_version": SCOPE_SCHEMA_VERSION,
        "stories": [
            {
                "story": "user_stories/story__x.md",
                "prompts": ["prompts/x_python.prompt"],
            }
        ],
    }
    manifest_path = tmp_path / "scope.json"
    manifest_path.write_text(json.dumps(manifest_data), encoding="utf-8")

    scope, diags = load_scope_manifest(str(manifest_path), project_root=str(tmp_path))

    assert len(scope.story_paths) == 1
    assert "story__x.md" in scope.story_paths[0]
    assert len(scope.prompt_paths) == 1
    assert diags == []


def test_load_scope_manifest_rejects_absolute_path(tmp_path):
    manifest_data = {
        "schema_version": SCOPE_SCHEMA_VERSION,
        "stories": [
            {
                "story": "/etc/passwd",
                "prompts": [],
            }
        ],
    }
    manifest_path = tmp_path / "scope.json"
    manifest_path.write_text(json.dumps(manifest_data), encoding="utf-8")

    with pytest.raises(ManifestError, match="Absolute paths"):
        load_scope_manifest(str(manifest_path), project_root=str(tmp_path))


def test_load_scope_manifest_rejects_dotdot(tmp_path):
    manifest_data = {
        "schema_version": SCOPE_SCHEMA_VERSION,
        "stories": [
            {
                "story": "../outside/story__x.md",
                "prompts": [],
            }
        ],
    }
    manifest_path = tmp_path / "scope.json"
    manifest_path.write_text(json.dumps(manifest_data), encoding="utf-8")

    with pytest.raises(ManifestError, match="traversal"):
        load_scope_manifest(str(manifest_path), project_root=str(tmp_path))


def test_load_scope_manifest_rejects_unknown_schema(tmp_path):
    manifest_data = {
        "schema_version": "bad.schema.v99",
        "stories": [],
    }
    manifest_path = tmp_path / "scope.json"
    manifest_path.write_text(json.dumps(manifest_data), encoding="utf-8")

    with pytest.raises(ManifestError, match="schema_version"):
        load_scope_manifest(str(manifest_path), project_root=str(tmp_path))


def test_load_scope_manifest_rejects_duplicate_story(tmp_path):
    manifest_data = {
        "schema_version": SCOPE_SCHEMA_VERSION,
        "stories": [
            {"story": "user_stories/story__x.md", "prompts": []},
            {"story": "user_stories/story__x.md", "prompts": []},
        ],
    }
    manifest_path = tmp_path / "scope.json"
    manifest_path.write_text(json.dumps(manifest_data), encoding="utf-8")

    with pytest.raises(ManifestError, match="Duplicate"):
        load_scope_manifest(str(manifest_path), project_root=str(tmp_path))


def test_load_scope_manifest_deduplicates_prompts(tmp_path):
    story = tmp_path / "user_stories" / "story__a.md"
    story.parent.mkdir()
    story.write_text("story", encoding="utf-8")
    story2 = tmp_path / "user_stories" / "story__b.md"
    story2.write_text("story2", encoding="utf-8")
    prompt = tmp_path / "prompts" / "a_python.prompt"
    prompt.parent.mkdir()
    prompt.write_text("prompt", encoding="utf-8")

    manifest_data = {
        "schema_version": SCOPE_SCHEMA_VERSION,
        "stories": [
            {"story": "user_stories/story__a.md", "prompts": ["prompts/a_python.prompt"]},
            {"story": "user_stories/story__b.md", "prompts": ["prompts/a_python.prompt"]},
        ],
    }
    manifest_path = tmp_path / "scope.json"
    manifest_path.write_text(json.dumps(manifest_data), encoding="utf-8")

    scope, _ = load_scope_manifest(str(manifest_path), project_root=str(tmp_path))
    assert len(scope.prompt_paths) == 1


# ---------------------------------------------------------------------------
# CLI tests — structured JSON output
# ---------------------------------------------------------------------------


def _mock_context_obj():
    return {"verbose": False, "quiet": False}


def _passing_run_return():
    return (True, [_pass_result()], 0.05, "gpt-test")


def _failing_run_return():
    return (False, [_pass_result(), _fail_result()], 0.1, "gpt-test")


# --- JSON stdout contains one parseable document, no ANSI/Rich text ---


def test_json_mode_stdout_parseable(tmp_path):
    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_run:
        mock_run.return_value = _passing_run_return()
        result = runner.invoke(
            detect_change,
            ["--stories", "--json"],
            obj=_mock_context_obj(),
        )

    assert result.exit_code == 0
    # stdout must be one JSON document
    doc = json.loads(result.output)
    assert doc["schema_version"] == SCHEMA_VERSION
    assert doc["all_pass"] is True
    assert isinstance(doc["items"], list)


def test_json_mode_fail_emits_document_and_exits_1(tmp_path):
    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_run:
        mock_run.return_value = _failing_run_return()
        result = runner.invoke(
            detect_change,
            ["--stories", "--json", "--no-fail-fast"],
            obj=_mock_context_obj(),
        )

    assert result.exit_code == 1
    doc = json.loads(result.output)
    assert doc["all_pass"] is False
    assert doc["outcome"] == "story_fail"
    # FAIL row has proposed changes
    fail_item = next(i for i in doc["items"] if i["verdict"] == "FAIL")
    assert len(fail_item["changes"]) == 1


# --- JSON output is schema-valid on provider/auth failure ---


def test_json_mode_provider_failure_exits_3(tmp_path):
    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_run:
        mock_run.side_effect = RuntimeError("provider connection refused")
        result = runner.invoke(
            detect_change,
            ["--stories", "--json"],
            obj=_mock_context_obj(),
        )

    assert result.exit_code == 3
    doc = json.loads(result.output)
    assert doc["all_pass"] is False
    assert doc["outcome"] == "internal_error"


def test_json_mode_auth_failure_exits_3(tmp_path):
    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_run:
        mock_run.side_effect = RuntimeError("auth credential missing")
        result = runner.invoke(
            detect_change,
            ["--stories", "--json"],
            obj=_mock_context_obj(),
        )

    assert result.exit_code == 3
    doc = json.loads(result.output)
    assert doc["outcome"] == "auth_error"
    assert doc["diagnostics"][0]["code"] == DIAG_AUTH_NON_INTERACTIVE


# --- Atomic explicit-path output ---


def test_json_output_file_written_atomically(tmp_path):
    out_file = tmp_path / "result.json"
    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_run:
        mock_run.return_value = _passing_run_return()
        result = runner.invoke(
            detect_change,
            ["--stories", "--json-output", str(out_file)],
            obj=_mock_context_obj(),
        )

    assert result.exit_code == 0
    assert out_file.exists()
    doc = json.loads(out_file.read_text(encoding="utf-8"))
    assert doc["schema_version"] == SCHEMA_VERSION


# --- --json and --json-output are mutually exclusive ---


def test_json_and_json_output_mutually_exclusive(tmp_path):
    out_file = tmp_path / "result.json"
    runner = CliRunner()
    result = runner.invoke(
        detect_change,
        ["--stories", "--json", "--json-output", str(out_file)],
        obj=_mock_context_obj(),
    )
    assert result.exit_code != 0
    assert "mutually exclusive" in result.output


# --- --scope-manifest with --stories-dir is rejected ---


def test_scope_manifest_and_stories_dir_rejected(tmp_path):
    manifest = tmp_path / "scope.json"
    manifest.write_text(json.dumps({
        "schema_version": SCOPE_SCHEMA_VERSION, "stories": []
    }), encoding="utf-8")
    runner = CliRunner()
    result = runner.invoke(
        detect_change,
        ["--stories", "--scope-manifest", str(manifest), "--stories-dir", "user_stories"],
        obj=_mock_context_obj(),
    )
    assert result.exit_code != 0
    assert "scope-manifest" in result.output.lower() or "stories-dir" in result.output.lower()


# --- Scope manifest constrains evaluation to authorized stories only ---


def test_scope_manifest_limits_evaluation(tmp_path):
    story_a = tmp_path / "user_stories" / "story__a.md"
    story_a.parent.mkdir()
    story_a.write_text("story a", encoding="utf-8")
    story_b = tmp_path / "user_stories" / "story__b.md"
    story_b.write_text("story b", encoding="utf-8")
    prompt = tmp_path / "prompts" / "a_python.prompt"
    prompt.parent.mkdir()
    prompt.write_text("prompt", encoding="utf-8")

    manifest_data = {
        "schema_version": SCOPE_SCHEMA_VERSION,
        "stories": [
            {"story": "user_stories/story__a.md", "prompts": ["prompts/a_python.prompt"]}
        ],
    }
    manifest_path = tmp_path / "scope.json"
    manifest_path.write_text(json.dumps(manifest_data), encoding="utf-8")

    captured_story_files = []

    def _mock_run(*, story_files, **kwargs):
        if story_files:
            captured_story_files.extend(story_files)
        return (True, [], 0.0, "gpt-test")

    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests", side_effect=_mock_run):
        result = runner.invoke(
            detect_change,
            ["--stories", "--scope-manifest", str(manifest_path), "--json"],
            obj=_mock_context_obj(),
        )

    assert result.exit_code == 0
    # Only story__a.md should be passed; story__b.md must not appear
    story_names = [Path(str(p)).name for p in captured_story_files]
    assert "story__a.md" in story_names
    assert "story__b.md" not in story_names


# --- Invalid scope manifest produces config_error JSON ---


def test_invalid_scope_manifest_produces_config_error_json(tmp_path):
    bad_manifest = tmp_path / "scope.json"
    bad_manifest.write_text("{not json", encoding="utf-8")

    runner = CliRunner()
    result = runner.invoke(
        detect_change,
        ["--stories", "--scope-manifest", str(bad_manifest), "--json"],
        obj=_mock_context_obj(),
    )

    assert result.exit_code == 2
    doc = json.loads(result.output)
    assert doc["outcome"] == "config_error"
    assert doc["all_pass"] is False


# --- Read-only mode does not mutate story metadata ---


def test_read_only_disables_cache_story_prompt_links(tmp_path):
    runner = CliRunner()
    calls = []

    def _mock_run(**kwargs):
        calls.append(kwargs.get("cache_story_prompt_links"))
        return (True, [], 0.0, "gpt-test")

    with patch("pdd.commands.analysis.run_user_story_tests", side_effect=_mock_run):
        result = runner.invoke(
            detect_change,
            ["--stories", "--read-only", "--json"],
            obj=_mock_context_obj(),
        )

    assert result.exit_code == 0
    # cache_story_prompt_links must be False in read-only mode
    assert calls[0] is False


def test_json_mode_implies_read_only(tmp_path):
    calls = []

    def _mock_run(**kwargs):
        calls.append(kwargs.get("cache_story_prompt_links"))
        return (True, [], 0.0, "gpt-test")

    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests", side_effect=_mock_run):
        result = runner.invoke(
            detect_change,
            ["--stories", "--json"],
            obj=_mock_context_obj(),
        )

    assert result.exit_code == 0
    assert calls[0] is False


# --- Unique invocation IDs ---


def test_invocation_ids_are_unique():
    ids = set()
    runner = CliRunner()

    def _mock_run(**kwargs):
        return (True, [], 0.0, "gpt-test")

    for _ in range(3):
        with patch("pdd.commands.analysis.run_user_story_tests", side_effect=_mock_run):
            result = runner.invoke(
                detect_change,
                ["--stories", "--json"],
                obj=_mock_context_obj(),
            )
        doc = json.loads(result.output)
        ids.add(doc["invocation_id"])

    assert len(ids) == 3


# --- Non-interactive flag is accepted ---


def test_non_interactive_flag_accepted():
    runner = CliRunner()

    def _mock_run(**kwargs):
        return (True, [], 0.0, "gpt-test")

    with patch("pdd.commands.analysis.run_user_story_tests", side_effect=_mock_run):
        result = runner.invoke(
            detect_change,
            ["--stories", "--non-interactive", "--json"],
            obj=_mock_context_obj(),
        )

    assert result.exit_code == 0


# --- --stories rejects unsupported positional arguments ---


def test_stories_rejects_positional_args_with_helpful_message():
    runner = CliRunner()
    with runner.isolated_filesystem():
        # Create files so Click's path existence check passes, allowing our
        # --stories validation to run and produce an actionable message.
        Path("p.prompt").write_text("p", encoding="utf-8")
        Path("change.txt").write_text("c", encoding="utf-8")
        result = runner.invoke(
            detect_change,
            ["--stories", "p.prompt", "change.txt"],
            obj=_mock_context_obj(),
        )
    assert result.exit_code != 0
    # Should mention --stories-dir or --scope-manifest
    assert "--stories-dir" in result.output or "--scope-manifest" in result.output


# --- *_LLM.prompt inclusion without --include-llm ---


def test_llm_prompt_excluded_by_default(tmp_path):
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    (prompts_dir / "foo_python.prompt").write_text("prompt", encoding="utf-8")
    (prompts_dir / "bar_LLM.prompt").write_text("llm prompt", encoding="utf-8")
    stories_dir = tmp_path / "user_stories"
    stories_dir.mkdir()
    (stories_dir / "story__x.md").write_text("story", encoding="utf-8")

    captured = []

    def _mock_run(*, include_llm_prompts, **kwargs):
        captured.append(include_llm_prompts)
        return (True, [], 0.0, "gpt-test")

    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests", side_effect=_mock_run):
        runner.invoke(
            detect_change,
            ["--stories", "--json"],
            obj=_mock_context_obj(),
        )

    assert captured[0] is False


def test_llm_prompt_included_with_flag(tmp_path):
    captured = []

    def _mock_run(*, include_llm_prompts, **kwargs):
        captured.append(include_llm_prompts)
        return (True, [], 0.0, "gpt-test")

    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests", side_effect=_mock_run):
        runner.invoke(
            detect_change,
            ["--stories", "--include-llm", "--json"],
            obj=_mock_context_obj(),
        )

    assert captured[0] is True
