from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import pytest

from pdd.user_story_tests import (
    discover_prompt_files,
    discover_story_files,
    run_user_story_fix,
    run_user_story_tests,
)


def test_user_story_tests_no_stories(tmp_path):
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    (prompts_dir / "foo_python.prompt").write_text("prompt", encoding="utf-8")

    passed, results, cost, model = run_user_story_tests(
        prompts_dir=str(prompts_dir),
        stories_dir=str(tmp_path / "user_stories"),
        quiet=True,
    )

    assert passed is True
    assert results == []
    assert cost == 0.0
    assert model == ""


def test_user_story_tests_detect_pass(tmp_path):
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    (prompts_dir / "foo_python.prompt").write_text("prompt", encoding="utf-8")
    story = stories_dir / "story__happy_path.md"
    story.write_text("As a user...", encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        mock_detect.return_value = ([], 0.25, "gpt-test")
        passed, results, cost, model = run_user_story_tests(
            prompts_dir=str(prompts_dir),
            stories_dir=str(stories_dir),
            quiet=True,
        )

    assert passed is True
    assert results[0]["passed"] is True
    assert cost == 0.25
    assert model == "gpt-test"


def test_user_story_tests_detect_fail(tmp_path):
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    (prompts_dir / "foo_python.prompt").write_text("prompt", encoding="utf-8")
    story = stories_dir / "story__failure.md"
    story.write_text("As a user...", encoding="utf-8")

    changes = [{"prompt_name": "foo_python.prompt", "change_instructions": "Add support"}]

    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        mock_detect.return_value = (changes, 0.5, "gpt-test")
        passed, results, cost, model = run_user_story_tests(
            prompts_dir=str(prompts_dir),
            stories_dir=str(stories_dir),
            quiet=True,
        )

    assert passed is False
    assert results[0]["passed"] is False
    assert results[0]["changes"] == changes
    assert cost == 0.5
    assert model == "gpt-test"


def test_discover_prompt_files_excludes_llm_by_default(tmp_path):
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    (prompts_dir / "foo_python.prompt").write_text("prompt", encoding="utf-8")
    (prompts_dir / "bar_llm.prompt").write_text("prompt", encoding="utf-8")

    results = discover_prompt_files(str(prompts_dir))

    assert len(results) == 1
    assert results[0].name == "foo_python.prompt"


def test_discover_prompt_files_includes_llm(tmp_path):
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    (prompts_dir / "foo_python.prompt").write_text("prompt", encoding="utf-8")
    (prompts_dir / "bar_llm.prompt").write_text("prompt", encoding="utf-8")

    results = discover_prompt_files(str(prompts_dir), include_llm=True)

    assert {p.name for p in results} == {"foo_python.prompt", "bar_llm.prompt"}


def test_discover_story_files_filters_prefix(tmp_path):
    stories_dir = tmp_path / "user_stories"
    stories_dir.mkdir()
    (stories_dir / "story__one.md").write_text("story", encoding="utf-8")
    (stories_dir / "not_a_story.md").write_text("story", encoding="utf-8")

    results = discover_story_files(str(stories_dir))

    assert [p.name for p in results] == ["story__one.md"]


def test_user_story_tests_fail_fast(tmp_path):
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    (prompts_dir / "foo_python.prompt").write_text("prompt", encoding="utf-8")
    (stories_dir / "story__one.md").write_text("story", encoding="utf-8")
    (stories_dir / "story__two.md").write_text("story", encoding="utf-8")

    changes = [{"prompt_name": "foo_python.prompt", "change_instructions": "Add support"}]

    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        mock_detect.return_value = (changes, 0.5, "gpt-test")
        passed, results, cost, model = run_user_story_tests(
            prompts_dir=str(prompts_dir),
            stories_dir=str(stories_dir),
            quiet=True,
            fail_fast=True,
        )

    assert passed is False
    assert len(results) == 1
    assert mock_detect.call_count == 1
    assert cost == 0.5
    assert model == "gpt-test"


def test_user_story_fix_happy_path(tmp_path):
    prompts_dir = tmp_path / "prompts" / "sub"
    src_dir = tmp_path / "src" / "sub"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir(parents=True)
    src_dir.mkdir(parents=True)
    stories_dir.mkdir()

    prompt_path = prompts_dir / "calc_python.prompt"
    prompt_path.write_text("prompt", encoding="utf-8")
    code_path = src_dir / "calc.py"
    code_path.write_text("code", encoding="utf-8")
    story_path = stories_dir / "story__calc.md"
    story_path.write_text("story", encoding="utf-8")

    ctx = SimpleNamespace(obj={})

    with patch("pdd.user_story_tests.discover_prompt_files") as mock_discover, \
         patch("pdd.user_story_tests.detect_change") as mock_detect, \
         patch("pdd.change_main.change_main") as mock_change, \
         patch("pdd.user_story_tests.run_user_story_tests") as mock_story_tests:
        mock_discover.return_value = [prompt_path]
        mock_detect.return_value = ([{"prompt_name": "calc_python.prompt"}], 0.1, "detect-model")
        mock_change.return_value = (f"Modified prompt saved to {prompt_path}", 0.2, "change-model")
        mock_story_tests.return_value = (True, [], 0.3, "verify-model")

        success, message, cost, model, changed_files = run_user_story_fix(
            ctx=ctx,
            story_file=str(story_path),
            prompts_dir=str(tmp_path / "prompts"),
            quiet=True,
        )

    assert success is True, message
    assert message == "User story prompts updated successfully."
    assert cost == pytest.approx(0.6)
    assert model == "verify-model"
    assert changed_files == [str(prompt_path)]
    assert ctx.obj.get("skip_user_stories") is None
    mock_change.assert_called_once()
    assert mock_change.call_args[1]["input_code"] == str(code_path)


def test_user_story_fix_treats_plain_error_message_as_failure(tmp_path):
    prompts_dir = tmp_path / "prompts" / "sub"
    src_dir = tmp_path / "src" / "sub"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir(parents=True)
    src_dir.mkdir(parents=True)
    stories_dir.mkdir()

    prompt_path = prompts_dir / "calc_python.prompt"
    prompt_path.write_text("prompt", encoding="utf-8")
    code_path = src_dir / "calc.py"
    code_path.write_text("code", encoding="utf-8")
    story_path = stories_dir / "story__calc.md"
    story_path.write_text("story", encoding="utf-8")

    ctx = SimpleNamespace(obj={})

    with patch("pdd.user_story_tests.discover_prompt_files") as mock_discover, \
         patch("pdd.user_story_tests.detect_change") as mock_detect, \
         patch("pdd.change_main.change_main") as mock_change, \
         patch("pdd.user_story_tests.run_user_story_tests") as mock_story_tests:
        mock_discover.return_value = [prompt_path]
        mock_detect.return_value = ([{"prompt_name": "calc_python.prompt"}], 0.1, "detect-model")
        mock_change.return_value = ("Error during prompt modification: failure", 0.2, "change-model")

        success, message, cost, model, changed_files = run_user_story_fix(
            ctx=ctx,
            story_file=str(story_path),
            prompts_dir=str(tmp_path / "prompts"),
            quiet=True,
        )

    assert success is False
    assert "Error during prompt modification: failure" in message
    assert cost == pytest.approx(0.3)
    assert model == "change-model"
    assert changed_files == []
    assert ctx.obj.get("skip_user_stories") is None
    mock_story_tests.assert_not_called()
    assert mock_change.call_args[1]["input_code"] == str(code_path)
