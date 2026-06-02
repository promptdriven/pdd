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

    changes = [{"prompt_name": "notify_python.prompt", "change_instructions": "Refine scope"}]
    # Force the deterministic fallback (LLM unavailable) so this exercises the
    # template path it asserts on.
    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.user_story_tests._llm_generate_story_markdown", return_value=(None, 0.0, "")
    ):
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
    assert story_text.startswith("<!-- pdd-story-prompts:")
    assert "<!-- pdd-story-prompts: notify_python.prompt -->" in story_text
    assert "## Covers" in story_text
    assert "## Story" in story_text
    assert "## Context" in story_text
    assert "## Acceptance Criteria" in story_text
    assert "## Oracle" in story_text
    assert "## Non-Oracle" in story_text
    assert "## Negative Cases" in story_text
    assert "## Prompt Scope" not in story_text
    assert "- R1: Add contract rule IDs here after contracts are authored." in story_text


def test_generate_user_story_falls_back_to_input_links_when_detection_empty(tmp_path):
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_two = prompts_dir / "notify_python.prompt"
    prompt_one.write_text("Handle file uploads.", encoding="utf-8")
    prompt_two.write_text("Send notifications.", encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.user_story_tests._llm_generate_story_markdown", return_value=(None, 0.0, "")
    ):
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


def test_generate_user_story_seeds_covers_and_negative_cases(tmp_path):
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()

    fixture_path = Path(__file__).resolve().parent / "fixtures" / "contract_rules_python.prompt"
    prompt_content = fixture_path.read_text(encoding="utf-8")

    prompt_one = prompts_dir / "contract_rules_python.prompt"
    prompt_one.write_text(prompt_content, encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.user_story_tests._llm_generate_story_markdown", return_value=(None, 0.0, "")
    ):
        mock_detect.return_value = ([], 0.1, "gpt-test")
        success, _, _, _, story_file, _ = generate_user_story(
            prompt_files=[str(prompt_one)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    story_text = Path(story_file).read_text(encoding="utf-8")
    assert "- R1: Positive amount" in story_text
    assert "- R2: Remaining balance" in story_text
    assert "- R3: No provider call before validation" in story_text
    assert "Call the payment provider for requests rejected by R1 or R2." in story_text


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
        "pdd.user_story_tests._llm_generate_story_markdown", return_value=(None, 0.0, "")
    ):
        mock_detect.return_value = ([], 0.1, "gpt-test")
        success, _, _, _, story_file, _ = generate_user_story(
            prompt_files=[str(prompt_one), str(prompt_two)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    story_text = Path(story_file).read_text(encoding="utf-8")
    assert "- prompts/contract_rules_python.prompt#R1: Positive amount" in story_text
    assert "- prompts/contract_rules_python.prompt#R2: Remaining balance" in story_text


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
        mock_detect.return_value = ([], 0.1, "detect-model")
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
    # Cost includes both the story-generation call and the linking call.
    assert cost == pytest.approx(0.15)


def test_generate_user_story_falls_back_when_llm_errors(tmp_path):
    """When the provider call fails (no key / offline / error), generation falls
    back to the deterministic template so `pdd test` still produces a story."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_one.write_text("Handle file uploads.", encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.llm_invoke.llm_invoke", side_effect=RuntimeError("no provider key")
    ):
        mock_detect.return_value = ([], 0.1, "detect-model")
        success, _, _, _, story_file, _ = generate_user_story(
            prompt_files=[str(prompt_one)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    story_text = Path(story_file).read_text(encoding="utf-8")
    # Deterministic template placeholder is present.
    assert "As a <persona>," in story_text
    assert story_text.startswith("<!-- pdd-story-prompts:")


def test_generate_user_story_falls_back_when_llm_output_malformed(tmp_path):
    """LLM output missing a required section is rejected in favor of the
    deterministic template (keeps stories structurally valid)."""
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
        mock_detect.return_value = ([], 0.1, "detect-model")
        success, _, _, _, story_file, _ = generate_user_story(
            prompt_files=[str(prompt_one)],
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    story_text = Path(story_file).read_text(encoding="utf-8")
    assert "As a <persona>," in story_text  # fell back to template
    assert "I can do things." not in story_text


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
