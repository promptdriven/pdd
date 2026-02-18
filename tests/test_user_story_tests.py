from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import pytest

from pdd.user_story_tests import (
    cache_story_prompt_links,
    discover_prompt_files,
    discover_story_files,
    generate_user_story,
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


def test_user_story_tests_uses_story_prompt_metadata_subset(tmp_path):
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    prompt_one = prompts_dir / "one_python.prompt"
    prompt_two = prompts_dir / "two_python.prompt"
    prompt_one.write_text("prompt one", encoding="utf-8")
    prompt_two.write_text("prompt two", encoding="utf-8")
    story = stories_dir / "story__subset.md"
    story.write_text(
        "<!-- pdd-story-prompts: one_python.prompt -->\n\nAs a user...",
        encoding="utf-8",
    )

    captured_prompt_inputs = []

    def fake_detect(prompt_paths, *_args, **_kwargs):
        captured_prompt_inputs.append(prompt_paths)
        return ([], 0.1, "gpt-test")

    with patch("pdd.user_story_tests.detect_change", side_effect=fake_detect):
        passed, results, cost, model = run_user_story_tests(
            prompts_dir=str(prompts_dir),
            stories_dir=str(stories_dir),
            quiet=True,
        )

    assert passed is True
    assert results[0]["passed"] is True
    assert cost == 0.1
    assert model == "gpt-test"
    assert captured_prompt_inputs == [[str(prompt_one)]]


def test_user_story_tests_unresolved_story_metadata_fails(tmp_path):
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    (prompts_dir / "one_python.prompt").write_text("prompt one", encoding="utf-8")
    story = stories_dir / "story__bad_metadata.md"
    story.write_text(
        "<!-- pdd-story-prompts: missing_python.prompt -->\n\nAs a user...",
        encoding="utf-8",
    )

    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        passed, results, cost, model = run_user_story_tests(
            prompts_dir=str(prompts_dir),
            stories_dir=str(stories_dir),
            quiet=True,
        )

    assert passed is False
    assert results[0]["passed"] is False
    assert "No prompts from pdd-story-prompts metadata could be resolved." in results[0]["error"]
    assert cost == 0.0
    assert model == ""
    mock_detect.assert_not_called()


def test_user_story_tests_caches_story_prompt_links(tmp_path):
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    (prompts_dir / "one_python.prompt").write_text("prompt one", encoding="utf-8")
    (prompts_dir / "two_python.prompt").write_text("prompt two", encoding="utf-8")
    story = stories_dir / "story__cache_links.md"
    story.write_text("As a user...", encoding="utf-8")

    changes = [{"prompt_name": "one_python.prompt", "change_instructions": "Change one"}]

    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        mock_detect.return_value = (changes, 0.2, "gpt-test")
        passed, results, cost, model = run_user_story_tests(
            prompts_dir=str(prompts_dir),
            stories_dir=str(stories_dir),
            quiet=True,
            cache_story_prompt_links=True,
        )

    assert passed is False
    assert results[0]["passed"] is False
    assert cost == 0.2
    assert model == "gpt-test"
    updated_story = story.read_text(encoding="utf-8")
    assert "<!-- pdd-story-prompts: one_python.prompt -->" in updated_story


def test_cache_story_prompt_links_updates_metadata(tmp_path):
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    (prompts_dir / "one_python.prompt").write_text("prompt one", encoding="utf-8")
    (prompts_dir / "two_python.prompt").write_text("prompt two", encoding="utf-8")
    story = stories_dir / "story__new.md"
    story.write_text("As a user...", encoding="utf-8")

    changes = [{"prompt_name": "two_python.prompt", "change_instructions": "Change two"}]

    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        mock_detect.return_value = (changes, 0.4, "gpt-test")
        success, message, cost, model, linked_prompts = cache_story_prompt_links(
            story_file=str(story),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert message == "Story prompt metadata linked."
    assert cost == 0.4
    assert model == "gpt-test"
    assert linked_prompts == ["two_python.prompt"]
    updated_story = story.read_text(encoding="utf-8")
    assert "<!-- pdd-story-prompts: two_python.prompt -->" in updated_story


def test_cache_story_prompt_links_skips_existing_valid_metadata(tmp_path):
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    (prompts_dir / "one_python.prompt").write_text("prompt one", encoding="utf-8")
    story = stories_dir / "story__existing.md"
    story.write_text(
        "<!-- pdd-story-prompts: one_python.prompt -->\n\nAs a user...",
        encoding="utf-8",
    )

    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        success, message, cost, model, linked_prompts = cache_story_prompt_links(
            story_file=str(story),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert message == "Story already contains prompt metadata."
    assert cost == 0.0
    assert model == ""
    assert linked_prompts == ["one_python.prompt"]
    mock_detect.assert_not_called()


def test_cache_story_prompt_links_missing_story_fails(tmp_path):
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    (prompts_dir / "one_python.prompt").write_text("prompt one", encoding="utf-8")

    success, message, cost, model, linked_prompts = cache_story_prompt_links(
        story_file=str(tmp_path / "user_stories" / "story__missing.md"),
        prompts_dir=str(prompts_dir),
    )

    assert success is False
    assert "User story file not found" in message
    assert cost == 0.0
    assert model == ""
    assert linked_prompts == []


def test_generate_user_story_creates_story_file_and_links(tmp_path):
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_two = prompts_dir / "notify_python.prompt"
    prompt_one.write_text("Handle file uploads.", encoding="utf-8")
    prompt_two.write_text("Send notifications.", encoding="utf-8")

    changes = [{"prompt_name": "notify_python.prompt", "change_instructions": "Refine scope"}]
    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        mock_detect.return_value = (changes, 0.2, "gpt-test")
        success, message, cost, model, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt_one), str(prompt_two)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert "Generated story file:" in message
    assert "auto-detected" in message
    assert cost == 0.2
    assert model == "gpt-test"
    assert linked_prompts == ["notify_python.prompt"]
    output_path = Path(story_file)
    assert output_path.exists()
    story_text = output_path.read_text(encoding="utf-8")
    assert story_text.startswith("# User Story:")
    assert "<!-- pdd-story-prompts: notify_python.prompt -->" in story_text
    assert "## Story" in story_text
    assert "## Prompt Scope" in story_text
    assert "## Acceptance Criteria" in story_text


def test_generate_user_story_falls_back_to_input_links_when_detection_empty(tmp_path):
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_two = prompts_dir / "notify_python.prompt"
    prompt_one.write_text("Handle file uploads.", encoding="utf-8")
    prompt_two.write_text("Send notifications.", encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        mock_detect.return_value = ([], 0.15, "gpt-test")
        success, message, cost, model, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt_one), str(prompt_two)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert "linked from prompt inputs" in message
    assert cost == 0.15
    assert model == "gpt-test"
    assert linked_prompts == ["upload_python.prompt", "notify_python.prompt"]
    story_text = Path(story_file).read_text(encoding="utf-8")
    assert "<!-- pdd-story-prompts:" in story_text
    assert "upload_python.prompt" in story_text
    assert "notify_python.prompt" in story_text


def test_generate_user_story_missing_prompt_fails(tmp_path):
    success, message, cost, model, story_file, linked_prompts = generate_user_story(
        prompt_files=[str(tmp_path / "prompts" / "missing.prompt")],
        stories_dir=str(tmp_path / "user_stories"),
    )

    assert success is False
    assert "Prompt file not found" in message
    assert cost == 0.0
    assert model == ""
    assert story_file == ""
    assert linked_prompts == []


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


def test_user_story_fix_uses_pdd_src_dir_override(tmp_path, monkeypatch):
    prompts_dir = tmp_path / "prompts" / "sub"
    src_dir = tmp_path / "custom_src" / "sub"
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

    monkeypatch.setenv("PDD_SRC_DIR", str(tmp_path / "custom_src"))

    ctx = SimpleNamespace(obj={})

    with patch("pdd.user_story_tests.discover_prompt_files") as mock_discover, \
         patch("pdd.user_story_tests.detect_change") as mock_detect, \
         patch("pdd.change_main.change_main") as mock_change, \
         patch("pdd.user_story_tests.run_user_story_tests") as mock_story_tests:
        mock_discover.return_value = [prompt_path]
        mock_detect.return_value = ([{"prompt_name": "calc_python.prompt"}], 0.1, "detect-model")
        mock_change.return_value = (f"Modified prompt saved to {prompt_path}", 0.2, "change-model")
        mock_story_tests.return_value = (True, [], 0.3, "verify-model")

        success, _, _, _, changed_files = run_user_story_fix(
            ctx=ctx,
            story_file=str(story_path),
            prompts_dir=str(tmp_path / "prompts"),
            quiet=True,
        )

    assert success is True
    assert changed_files == [str(prompt_path)]
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
