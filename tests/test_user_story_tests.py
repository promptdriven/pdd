# pylint: disable=missing-module-docstring,missing-function-docstring
# pylint: disable=use-implicit-booleaness-not-comparison,unused-variable
# pylint: disable=too-many-locals,line-too-long,too-many-lines

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


def test_user_story_tests_caches_story_prompt_links_when_detection_is_empty(tmp_path):
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    (prompts_dir / "one_python.prompt").write_text("prompt one", encoding="utf-8")
    (prompts_dir / "two_python.prompt").write_text("prompt two", encoding="utf-8")
    story = stories_dir / "story__cache_on_pass.md"
    story.write_text("As a user...", encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        mock_detect.return_value = ([], 0.1, "gpt-test")
        passed, results, cost, model = run_user_story_tests(
            prompts_dir=str(prompts_dir),
            stories_dir=str(stories_dir),
            quiet=True,
            cache_story_prompt_links=True,
        )

    assert passed is True
    assert results[0]["passed"] is True
    assert cost == 0.1
    assert model == "gpt-test"
    updated_story = story.read_text(encoding="utf-8")
    assert "<!-- pdd-story-prompts:" in updated_story
    assert "one_python.prompt" in updated_story
    assert "two_python.prompt" in updated_story


def test_run_user_story_tests_accepts_deprecated_link_story_prompt_metadata(tmp_path):
    """PR #820: link_story_prompt_metadata remains a deprecated alias for main API."""
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    (prompts_dir / "one_python.prompt").write_text("prompt one", encoding="utf-8")
    story = stories_dir / "story__deprecated_kwarg.md"
    story.write_text("As a user...", encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        mock_detect.return_value = ([], 0.1, "gpt-test")
        with pytest.warns(DeprecationWarning, match="link_story_prompt_metadata"):
            passed, results, cost, model = run_user_story_tests(
                prompts_dir=str(prompts_dir),
                stories_dir=str(stories_dir),
                quiet=True,
                link_story_prompt_metadata=True,
            )

    assert passed is True
    assert results[0]["passed"] is True
    assert "<!-- pdd-story-prompts:" in story.read_text(encoding="utf-8")


def test_run_user_story_tests_cache_kwarg_wins_over_deprecated_alias(tmp_path):
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    (prompts_dir / "one_python.prompt").write_text("prompt one", encoding="utf-8")
    story = stories_dir / "story__kwarg_precedence.md"
    story.write_text("As a user...", encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        mock_detect.return_value = ([], 0.0, "")
        with pytest.warns(DeprecationWarning):
            run_user_story_tests(
                prompts_dir=str(prompts_dir),
                stories_dir=str(stories_dir),
                quiet=True,
                cache_story_prompt_links=True,
                link_story_prompt_metadata=False,
            )

    assert "<!-- pdd-story-prompts:" in story.read_text(encoding="utf-8")


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


def test_cache_story_prompt_links_empty_detection_uses_story_text_refs(tmp_path):
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    (prompts_dir / "one_python.prompt").write_text("prompt one", encoding="utf-8")
    (prompts_dir / "two_python.prompt").write_text("prompt two", encoding="utf-8")
    story = stories_dir / "story__refs.md"
    story.write_text(
        "## Prompt Scope\n- Use `two_python.prompt` for notifications.\n",
        encoding="utf-8",
    )

    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        mock_detect.return_value = ([], 0.4, "gpt-test")
        success, message, cost, model, linked_prompts = cache_story_prompt_links(
            story_file=str(story),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert message == "Story prompt metadata linked from story content."
    assert cost == 0.4
    assert model == "gpt-test"
    assert linked_prompts == ["two_python.prompt"]
    updated_story = story.read_text(encoding="utf-8")
    assert "<!-- pdd-story-prompts: two_python.prompt -->" in updated_story


def test_cache_story_prompt_links_empty_detection_falls_back_to_full_prompt_set(tmp_path):
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    (prompts_dir / "one_python.prompt").write_text("prompt one", encoding="utf-8")
    (prompts_dir / "two_python.prompt").write_text("prompt two", encoding="utf-8")
    story = stories_dir / "story__full_set.md"
    story.write_text("As a user...", encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        mock_detect.return_value = ([], 0.4, "gpt-test")
        success, message, cost, model, linked_prompts = cache_story_prompt_links(
            story_file=str(story),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert message == "Story prompt metadata linked to full prompt set."
    assert cost == 0.4
    assert model == "gpt-test"
    assert linked_prompts == ["one_python.prompt", "two_python.prompt"]
    updated_story = story.read_text(encoding="utf-8")
    assert "<!-- pdd-story-prompts:" in updated_story
    assert "one_python.prompt" in updated_story
    assert "two_python.prompt" in updated_story


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

    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.user_story_tests._llm_generate_story_markdown",
        return_value=(_LLM_STORY_MD, 0.05, "story-model"),
    ):
        success, message, cost, model, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt_one), str(prompt_two)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert "Generated story file:" in message
    assert "linked from prompt inputs" in message
    assert cost == pytest.approx(0.05)
    assert model == "story-model"
    assert linked_prompts == ["upload_python.prompt", "notify_python.prompt"]
    mock_detect.assert_not_called()
    output_path = Path(story_file)
    assert output_path.exists()
    story_text = output_path.read_text(encoding="utf-8")
    assert story_text.startswith("<!-- pdd-story-prompts:")
    assert "upload_python.prompt" in story_text
    assert "notify_python.prompt" in story_text
    assert "## Covers" in story_text
    assert "## Story" in story_text
    assert "## Context" in story_text
    assert "## Acceptance Criteria" in story_text
    assert "## Oracle" in story_text
    assert "## Non-Oracle" in story_text
    assert "## Negative Cases" in story_text
    assert "## Prompt Scope" not in story_text
    assert "<persona>" not in story_text
    assert "<behavior>" not in story_text
    assert "scoped prompt capabilities" not in story_text
    assert "As a data analyst, I can upload a CSV file" in story_text
    assert "scoped prompt capabilities" not in story_text


def test_generate_user_story_links_prompt_inputs_without_detection(tmp_path):
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_two = prompts_dir / "notify_python.prompt"
    prompt_one.write_text("Handle file uploads.", encoding="utf-8")
    prompt_two.write_text("Send notifications.", encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.user_story_tests._llm_generate_story_markdown",
        return_value=(_LLM_STORY_MD, 0.05, "story-model"),
    ):
        success, message, cost, model, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt_one), str(prompt_two)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert "linked from prompt inputs" in message
    assert cost == pytest.approx(0.05)
    assert model == "story-model"
    assert linked_prompts == ["upload_python.prompt", "notify_python.prompt"]
    mock_detect.assert_not_called()
    story_text = Path(story_file).read_text(encoding="utf-8")
    assert "<!-- pdd-story-prompts:" in story_text
    assert "upload_python.prompt" in story_text
    assert "notify_python.prompt" in story_text


def test_generate_user_story_uses_input_links_when_detection_raises(tmp_path):
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt = prompts_dir / "offline_python.prompt"
    prompt.write_text("Generate an offline-safe report.", encoding="utf-8")

    with patch(
        "pdd.user_story_tests._llm_generate_story_markdown",
        return_value=(_LLM_STORY_MD, 0.05, "story-model"),
    ), patch("pdd.user_story_tests.detect_change") as mock_detect:
        mock_detect.side_effect = RuntimeError("provider unavailable")
        success, message, cost, model, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert "linked from prompt inputs" in message
    assert cost == pytest.approx(0.05)
    assert model == "story-model"
    assert linked_prompts == ["offline_python.prompt"]
    mock_detect.assert_not_called()
    story_text = Path(story_file).read_text(encoding="utf-8")
    assert "<!-- pdd-story-prompts: offline_python.prompt -->" in story_text
    assert "As a data analyst, I can upload a CSV file" in story_text


def test_generate_user_story_derives_unit_test_ready_details_from_prompt(tmp_path):
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt = prompts_dir / "csv_report_python.prompt"
    prompt.write_text(
        "\n".join(
            [
                "Build a CSV report workflow.",
                "- Accept only .csv uploads with a header row.",
                "- Return row_count and column_names in the summary.",
                "- MUST NOT log raw uploaded cell values.",
            ]
        ),
        encoding="utf-8",
    )

    csv_story = _LLM_STORY_MD.replace(
        "As a data analyst, I can upload a CSV file and view a summary report",
        "As a data analyst, I can upload a CSV file with a header row and view row_count and column_names",
    ).replace(
        "Rejecting a valid CSV",
        "Logging raw uploaded cell values",
    )
    with patch(
        "pdd.user_story_tests._llm_generate_story_markdown",
        return_value=(csv_story, 0.05, "story-model"),
    ), patch("pdd.user_story_tests.detect_change") as mock_detect:
        success, _, _, _, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert linked_prompts == ["csv_report_python.prompt"]
    mock_detect.assert_not_called()
    story_text = Path(story_file).read_text(encoding="utf-8")
    assert "As a data analyst" in story_text
    assert "header row" in story_text
    assert "row_count and column_names" in story_text
    assert "Logging raw uploaded cell values" in story_text
    assert "<persona>" not in story_text
    assert "List forbidden outcomes" not in story_text


def test_generate_user_story_seeds_covers_and_negative_cases(tmp_path):
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()

    fixture_path = Path(__file__).resolve().parent / "fixtures" / "contract_rules_python.prompt"
    prompt_content = fixture_path.read_text(encoding="utf-8")

    prompt_one = prompts_dir / "contract_rules_python.prompt"
    prompt_one.write_text(prompt_content, encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.user_story_tests._llm_generate_story_markdown",
        return_value=(_LLM_STORY_MD, 0.05, "story-model"),
    ):
        success, _, _, _, story_file, _ = generate_user_story(
            prompt_files=[str(prompt_one)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    mock_detect.assert_not_called()
    story_text = Path(story_file).read_text(encoding="utf-8")
    assert "- R1: Upload returns a summary report" in story_text
    assert "## Negative Cases" in story_text


def test_generate_user_story_multi_prompt_seeds_cross_module(tmp_path):
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()

    fixture_path = Path(__file__).resolve().parent / "fixtures" / "contract_rules_python.prompt"
    prompt_content = fixture_path.read_text(encoding="utf-8")

    prompt_one = prompts_dir / "contract_rules_python.prompt"
    prompt_one.write_text(prompt_content, encoding="utf-8")
    prompt_two = prompts_dir / "other_python.prompt"
    prompt_two.write_text("Handle other stuff.", encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.user_story_tests._llm_generate_story_markdown",
        return_value=(_LLM_STORY_MD, 0.05, "story-model"),
    ):
        success, _, _, _, story_file, _ = generate_user_story(
            prompt_files=[str(prompt_one), str(prompt_two)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    mock_detect.assert_not_called()
    story_text = Path(story_file).read_text(encoding="utf-8")
    assert "- R1: Upload returns a summary report" in story_text


_LLM_STORY_MD = (
    "# User Story: Upload CSV\n\n"
    "## Covers\n\n- R1: Upload returns a summary report\n\n"
    "## Story\n\n"
    "As a data analyst, I can upload a CSV file and view a summary report, "
    "so that I can quickly understand my data.\n\n"
    "## Context\n\n- `prompts/upload_python.prompt`: CSV upload + summary\n\n"
    "## Acceptance Criteria\n\n"
    "1. Given a valid CSV, when uploaded, then a summary report is shown.\n\n"
    "## Oracle\n\n- returned value shape\n\n"
    "## Non-Oracle\n\n- internal helper names\n\n"
    "## Negative Cases\n\n- Rejecting a valid CSV\n\n"
    "## Non-Goals\n\n- Editing the CSV\n\n"
    "## Notes\n\n- n/a\n"
)


_CONTEXT_AUDIT_PROMPT_BASE = "\n".join(
    [
        "<pdd-reason>Reports per-source token attribution for a hydrated prompt so users can audit context-window cost before generation.</pdd-reason>",
        "",
        "% Goal",
        "Write the `pdd/commands/context_audit.py` module.",
        "",
        "% Requirements",
        "1. Define a Click command named `context_audit` with a required `prompt_path` argument.",
        "2. Provide options `--model`, `--json`, and `--threshold`.",
        "3. Preprocess the prompt file; do NOT make an LLM call.",
        "4. Detect dynamic tags such as `<shell>` and `<web>` and emit warnings.",
        "5. Attribute tokens per source segment, including `prompt_body` and one row per resolved include.",
    ]
)


_CONTEXT_AUDIT_PROMPT_AGGREGATE_ONLY = "\n".join(
    [
        "<pdd-reason>Reports only aggregate token totals for a hydrated prompt so users can audit context-window cost before generation, without per-source attribution.</pdd-reason>",
        "",
        "% Goal",
        "Write the `pdd/commands/context_audit.py` module.",
        "",
        "% Requirements",
        "1. Define a Click command named `context_audit` with a required `prompt_path` argument.",
        "2. Provide options `--model`, `--json`, and `--threshold`.",
        "3. Preprocess the prompt file; do NOT make an LLM call.",
        "4. Detect dynamic tags such as `<shell>` and `<web>` and emit warnings.",
        "5. Report only aggregate token totals, without per-source attribution rows.",
    ]
)


_CONTEXT_AUDIT_STORY_MD = (
    "# User Story: Context Audit\n\n"
    "## Covers\n\n"
    "- context_audit_python.prompt: CLI users can run `pdd context-audit <prompt_path>` "
    "to see per-source token attribution before generation.\n"
    "- context_audit_python.prompt: The command supports `--json`, `--model`, and "
    "`--threshold` behavior without making an LLM call.\n\n"
    "## Story\n\n"
    "As a CLI user, I can audit a hydrated prompt's per-source token usage before "
    "generation, so that I can identify which prompt body, include, test, example, "
    "or grounding source consumes the context window.\n\n"
    "## Context\n\n"
    "- `context_audit_python.prompt` defines the `pdd context-audit <prompt_path>` "
    "command, JSON output, threshold exit behavior, dynamic-tag warnings, and "
    "the no-LLM-call requirement.\n\n"
    "## Acceptance Criteria\n\n"
    "1. Given a prompt with includes, when I run `pdd context-audit <prompt_path>`, "
    "then the output reports token rows per source rather than only aggregate totals.\n"
    "2. Given `--json` is passed, when the audit completes, then stdout is a JSON "
    "object with `total_tokens`, `context_limit`, `percent_used`, `model`, `rows`, "
    "`warnings`, and `threshold_exceeded`.\n"
    "3. Given the threshold percentage is exceeded, when `--threshold` is nonzero, "
    "then the command exits with code 2.\n"
    "4. Given dynamic tags such as `<shell>` or `<web>` are present, when they are "
    "not expanded, then warning entries are reported without making an LLM call.\n\n"
    "## Oracle\n\n"
    "These details matter for pass/fail:\n"
    "- Per-source attribution rows are present for prompt body and resolved includes.\n"
    "- Aggregate-only token totals are not sufficient.\n"
    "- `--json`, `--model`, and `--threshold` behavior matches the prompt.\n"
    "- The command does not make an LLM call for local auditing.\n\n"
    "## Non-Oracle\n\n"
    "These details should not matter:\n"
    "- Private helper names.\n"
    "- Table styling.\n"
    "- Internal ordering beyond sorting rows by token count.\n\n"
    "## Negative Cases\n\n"
    "- Reporting only aggregate totals with no per-source attribution.\n"
    "- Calling an LLM during context audit.\n"
    "- Silently ignoring dynamic tags without warnings.\n\n"
    "## Non-Goals\n\n"
    "- Generating code from the audited prompt.\n"
    "- Fetching cloud grounding data locally.\n\n"
    "## Notes\n\n"
    "- This story should fail validation if the prompt changes from per-source "
    "token attribution to aggregate-only token totals.\n"
)


def test_generate_user_story_uses_llm_output(tmp_path):
    """Issue #1356: the story body is authored by the LLM from the prompt
    content, and the pdd-story-prompts metadata is still stitched in."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_one.write_text(
        "Users can upload a CSV file and view a summary report.", encoding="utf-8"
    )

    fake_llm = {"result": _LLM_STORY_MD, "cost": 0.05, "model_name": "story-model"}
    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.llm_invoke.llm_invoke", return_value=fake_llm
    ) as mock_llm:
        success, message, cost, model, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt_one)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert mock_llm.called
    story_text = Path(story_file).read_text(encoding="utf-8")
    # LLM-authored narrative is present (not the deterministic placeholder).
    assert "As a data analyst, I can upload a CSV file" in story_text
    assert "<persona>" not in story_text
    assert "## Acceptance Criteria" in story_text
    # Metadata stitched deterministically even though the LLM did not emit it.
    assert story_text.startswith("<!-- pdd-story-prompts:")
    assert "upload_python.prompt" in story_text
    assert "linked from prompt inputs" in message
    assert cost == pytest.approx(0.05)
    assert model == "story-model"
    assert linked_prompts == ["upload_python.prompt"]
    mock_detect.assert_not_called()


def test_generate_user_story_context_audit_story_protects_per_source_attribution(tmp_path):
    """Regression for PR #1387 as a prompt input: the generated story must
    capture concrete requirements that make aggregate-only prompt drift fail."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "context_audit_python.prompt"
    prompt_one.write_text(_CONTEXT_AUDIT_PROMPT_BASE, encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.user_story_tests._llm_generate_story_markdown",
        return_value=(_CONTEXT_AUDIT_STORY_MD, 0.05, "story-model"),
    ):
        success, _, _, _, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt_one)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert linked_prompts == ["context_audit_python.prompt"]
    mock_detect.assert_not_called()
    story_text = Path(story_file).read_text(encoding="utf-8")
    assert "per-source token attribution" in story_text
    assert "Aggregate-only token totals are not sufficient" in story_text
    assert "`--json`, `--model`, and `--threshold`" in story_text
    assert "does not make an LLM call" in story_text
    assert "<pdd-reason>" not in story_text
    assert "\"type\": \"cli\"" not in story_text


def test_run_user_story_tests_fails_for_harmful_context_audit_prompt_change(tmp_path):
    """A generated story must fail validation when the prompt drifts from
    per-source attribution to aggregate-only totals."""
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    prompt_one = prompts_dir / "context_audit_python.prompt"
    prompt_one.write_text(_CONTEXT_AUDIT_PROMPT_AGGREGATE_ONLY, encoding="utf-8")
    story = stories_dir / "story__context_audit.md"
    story.write_text(
        "<!-- pdd-story-prompts: context_audit_python.prompt -->\n\n"
        f"{_CONTEXT_AUDIT_STORY_MD}",
        encoding="utf-8",
    )

    harmful_changes = [
        {
            "prompt_name": "context_audit_python.prompt",
            "change_instructions": (
                "Restore per-source token attribution rows; aggregate-only "
                "token totals violate the generated user story."
            ),
        }
    ]
    captured_prompt_inputs = []

    def fake_detect(prompt_paths, story_content, *_args, **_kwargs):
        captured_prompt_inputs.append(prompt_paths)
        prompt_text = Path(prompt_paths[0]).read_text(encoding="utf-8")
        assert "Report only aggregate token totals" in prompt_text
        assert "per-source token attribution" in story_content
        assert "Aggregate-only token totals are not sufficient" in story_content
        return harmful_changes, 0.2, "gpt-test"

    with patch("pdd.user_story_tests.detect_change", side_effect=fake_detect):
        passed, results, cost, model = run_user_story_tests(
            prompts_dir=str(prompts_dir),
            stories_dir=str(stories_dir),
            quiet=True,
            fail_fast=True,
        )

    assert passed is False
    assert results == [
        {
            "story": str(story),
            "passed": False,
            "changes": harmful_changes,
        }
    ]
    assert captured_prompt_inputs == [[str(prompt_one)]]
    assert cost == pytest.approx(0.2)
    assert model == "gpt-test"


def test_generate_user_story_fails_when_llm_errors(tmp_path):
    """When the provider call fails (no key / offline / error), generation
    fails instead of writing a deterministic substitute story."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_one.write_text("Handle file uploads.", encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.llm_invoke.llm_invoke", side_effect=RuntimeError("no provider key")
    ):
        success, message, cost, model, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt_one)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is False
    assert "requires a valid LLM-authored story" in message
    assert cost == 0.0
    assert model == ""
    assert story_file == ""
    assert linked_prompts == []
    mock_detect.assert_not_called()
    assert not (tmp_path / "user_stories").exists()


def test_generate_user_story_fails_when_llm_output_malformed(tmp_path):
    """LLM output missing a required section is rejected without writing a
    deterministic substitute story."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_one.write_text("Handle file uploads.", encoding="utf-8")

    # Missing '## Acceptance Criteria'.
    malformed = "# User Story: x\n\n## Story\n\nAs a user, I can do things.\n"
    bad_llm = {"result": malformed, "cost": 0.05, "model_name": "story-model"}
    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.llm_invoke.llm_invoke", return_value=bad_llm
    ):
        success, message, cost, model, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt_one)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is False
    assert "requires a valid LLM-authored story" in message
    assert cost == pytest.approx(0.05)
    assert model == "story-model"
    assert story_file == ""
    assert linked_prompts == []
    mock_detect.assert_not_called()
    assert not (tmp_path / "user_stories").exists()


def test_generate_user_story_rejects_llm_story_missing_canonical_sections(tmp_path):
    """Issue #1356: an LLM story carrying only `## Story` and
    `## Acceptance Criteria` is incomplete and must be rejected without writing
    a deterministic substitute story."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_one.write_text("Handle file uploads.", encoding="utf-8")

    # Only '## Story' + '## Acceptance Criteria' — every other canonical
    # section (Covers, Context, Oracle, Non-Oracle, Negative Cases, Non-Goals,
    # Notes) is missing, so this must not be written as-is.
    incomplete = (
        "# User Story: Upload\n\n"
        "## Story\n\n"
        "As a user, I can upload a file, so that I get a report.\n\n"
        "## Acceptance Criteria\n\n"
        "1. Given a file, when uploaded, then a report appears.\n"
    )
    bad_llm = {"result": incomplete, "cost": 0.05, "model_name": "story-model"}
    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.llm_invoke.llm_invoke", return_value=bad_llm
    ):
        success, message, cost, model, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt_one)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is False
    assert "requires a valid LLM-authored story" in message
    assert cost == pytest.approx(0.05)
    assert model == "story-model"
    assert story_file == ""
    assert linked_prompts == []
    mock_detect.assert_not_called()
    assert not (tmp_path / "user_stories").exists()


def test_generate_user_story_fails_when_llm_output_contains_placeholders(tmp_path):
    """LLM output containing template placeholders is rejected without fallback."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_one.write_text("Handle file uploads.", encoding="utf-8")

    placeholder_story = (
        "# User Story: Placeholder\n\n"
        "## Story\n\n"
        "As a <persona>, I can <capability>, so that <benefit>.\n\n"
        "## Acceptance Criteria\n\n"
        "1. Given <state>, when <action>, then <detail>.\n"
    )
    bad_llm = {"result": placeholder_story, "cost": 0.05, "model_name": "story-model"}
    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.llm_invoke.llm_invoke", return_value=bad_llm
    ):
        success, message, cost, model, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt_one)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is False
    assert "requires a valid LLM-authored story" in message
    assert cost == pytest.approx(0.05)
    assert model == "story-model"
    assert story_file == ""
    assert linked_prompts == []
    mock_detect.assert_not_called()
    assert not (tmp_path / "user_stories").exists()


def test_legacy_minimal_story_passes_validation(tmp_path):
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    prompt_one = prompts_dir / "math_python.prompt"
    prompt_one.write_text("Math operations.", encoding="utf-8")

    story_path = stories_dir / "story__legacy.md"
    story_path.write_text(
        "# User Story: Legacy Math Flow\n\n"
        "<!-- pdd-story-prompts: math_python.prompt -->\n\n"
        "## Story\n"
        "As a legacy user, I want basic math to work.\n\n"
        "## Acceptance Criteria\n"
        "- Basic addition works.\n",
        encoding="utf-8",
    )

    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        mock_detect.return_value = ([], 0.1, "gpt-legacy")
        success, results, cost, model = run_user_story_tests(
            prompts_dir=str(prompts_dir),
            stories_dir=str(stories_dir),
        )

    assert success is True
    assert len(results) == 1
    assert results[0]["passed"] is True


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
         patch("pdd.user_story_tests.get_extension", return_value=".py"), \
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
         patch("pdd.user_story_tests.get_extension", return_value=".py"), \
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
         patch("pdd.user_story_tests.get_extension", return_value=".py"), \
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
