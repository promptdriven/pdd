# pylint: disable=missing-module-docstring,missing-function-docstring
# pylint: disable=use-implicit-booleaness-not-comparison,unused-variable
# pylint: disable=too-many-locals,line-too-long,too-many-lines

from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import pytest

from pdd.user_story_tests import (
    _contract_path_for_story,
    _story_content_hash,
    cache_story_prompt_links,
    discover_prompt_files,
    discover_story_files,
    generate_user_story,
    resolve_issue_source,
    run_user_story_fix,
    run_user_story_tests,
    sync_user_story_contract,
)


# Issue #1356: stories are authored from the ISSUE, never the prompt. Tests use a
# deterministic, offline local issue markdown file as the issue source so they
# make no network/gh call. `_write_issue` returns the path to pass as --issue.
_DEFAULT_ISSUE_BODY = (
    "# Issue: Upload CSV and view a summary report\n\n"
    "## Summary\n"
    "Users can upload a CSV file and view a summary report.\n\n"
    "## Acceptance Criteria\n"
    "- Given a valid CSV, when uploaded, then a summary report is shown.\n"
)


def _write_issue(tmp_path, body=_DEFAULT_ISSUE_BODY, name="issue.md"):
    issue_path = tmp_path / name
    issue_path.write_text(body, encoding="utf-8")
    return str(issue_path)


@pytest.fixture(autouse=True)
def _stub_contract_llm():
    """Stub the contract LLM call for the whole module so generation tests never
    hit the network. The real contract WRITER still runs, so a contract file is
    produced from ``_CONTRACT_MD``. Tests that assert issue-specific contract
    content override this with their own ``_llm_generate_story_contract`` patch."""
    with patch(
        "pdd.user_story_tests._llm_generate_story_contract",
        return_value=(_CONTRACT_MD, 0.0, "contract-model"),
    ):
        yield


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


def test_user_story_tests_resolves_cwd_relative_metadata_with_absolute_prompts_dir(
    tmp_path, monkeypatch
):
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()
    monkeypatch.chdir(tmp_path)

    prompt_path = prompts_dir / "foo_python.prompt"
    prompt_path.write_text("prompt", encoding="utf-8")
    story = stories_dir / "story__cwd_relative_metadata.md"
    story.write_text(
        "<!-- pdd-story-prompts: prompts/foo_python.prompt -->\n\nAs a user...",
        encoding="utf-8",
    )

    captured_prompt_inputs = []

    def fake_detect(prompt_paths, *_args, **_kwargs):
        captured_prompt_inputs.append(prompt_paths)
        return ([], 0.1, "gpt-test")

    with patch("pdd.user_story_tests.detect_change", side_effect=fake_detect):
        passed, results, cost, model = run_user_story_tests(
            prompts_dir=str(prompts_dir.resolve()),
            stories_dir=str(stories_dir),
            quiet=True,
        )

    assert passed is True
    assert results[0]["passed"] is True
    assert cost == 0.1
    assert model == "gpt-test"
    assert captured_prompt_inputs == [[str(prompt_path)]]


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
            issue=_write_issue(tmp_path),
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert "Generated story file:" in message
    assert "linked from prompt inputs" in message
    assert "Generated contract file:" in message
    assert cost == pytest.approx(0.05)
    assert model == "story-model"
    assert linked_prompts == ["upload_python.prompt", "notify_python.prompt"]
    mock_detect.assert_not_called()
    output_path = Path(story_file)
    assert output_path.exists()
    story_text = output_path.read_text(encoding="utf-8")
    # The HUMAN story file holds only the metadata link + the one-sentence Story.
    assert story_text.startswith("<!-- pdd-story-prompts:")
    assert "upload_python.prompt" in story_text
    assert "notify_python.prompt" in story_text
    assert "## Story" in story_text
    assert "As a data analyst, I can upload a CSV file" in story_text
    # Contract sections must NOT be in the human file (they live in the contract).
    assert "## Covers" not in story_text
    assert "## Acceptance Criteria" not in story_text
    assert "<persona>" not in story_text
    # The CONTRACT file is a separate sibling under contracts/.
    contract_path = output_path.parent / "contracts" / (
        output_path.name[len("story__"):-len(".md")] + ".contract.md"
    )
    assert contract_path.exists()
    contract_text = contract_path.read_text(encoding="utf-8")
    assert "pdd-story-contract" in contract_text
    assert 'issue-ref=' in contract_text
    assert "story-hash=" in contract_text
    assert "## Covers" in contract_text
    assert "## Acceptance Criteria" in contract_text
    assert "## Candidate Prompts" in contract_text


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
            issue=_write_issue(tmp_path),
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
            issue=_write_issue(tmp_path),
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


def test_generate_user_story_derives_unit_test_ready_details_from_issue(tmp_path):
    """The story carries concrete, unit-test-ready details. Those details come
    from the issue/LLM, not from the prompt: the prompt body here is deliberately
    vague, yet the generated story is specific."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt = prompts_dir / "csv_report_python.prompt"
    # Deliberately vague prompt: it does NOT mention header rows, row_count, or
    # column_names. If story content leaked from the prompt, the asserts below
    # would fail.
    prompt.write_text("Build a CSV report workflow.", encoding="utf-8")

    issue_src = _write_issue(
        tmp_path,
        body=(
            "# Issue: CSV report\n\n"
            "Accept only .csv uploads with a header row. Return row_count and "
            "column_names in the summary. MUST NOT log raw uploaded cell values.\n"
        ),
    )

    csv_story = (
        "# User Story: CSV report\n\n"
        "## Story\n\n"
        "As a data analyst, I can upload a CSV file with a header row and view "
        "row_count and column_names, so that I can quickly understand my data.\n"
    )
    csv_contract = _CONTRACT_MD.replace(
        "- Rejecting a valid CSV",
        "- Logging raw uploaded cell values",
    )
    with patch(
        "pdd.user_story_tests._llm_generate_story_markdown",
        return_value=(csv_story, 0.05, "story-model"),
    ), patch(
        "pdd.user_story_tests._llm_generate_story_contract",
        return_value=(csv_contract, 0.02, "contract-model"),
    ), patch("pdd.user_story_tests.detect_change") as mock_detect:
        success, _, _, _, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt)],
            issue=issue_src,
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert linked_prompts == ["csv_report_python.prompt"]
    mock_detect.assert_not_called()
    # The human Story carries the issue-derived capability detail (not the prompt's).
    story_text = Path(story_file).read_text(encoding="utf-8")
    assert "As a data analyst" in story_text
    assert "header row" in story_text
    assert "row_count and column_names" in story_text
    assert "<persona>" not in story_text
    # The forbidden behavior is an issue-derived contract Negative Case.
    contract_path = _contract_path_for_story(Path(story_file))
    contract_text = contract_path.read_text(encoding="utf-8")
    assert "Logging raw uploaded cell values" in contract_text
    assert "List forbidden outcomes" not in contract_text


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
            issue=_write_issue(tmp_path),
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    mock_detect.assert_not_called()
    # Covers/Negative Cases live in the generated contract, not the human story.
    contract_text = _contract_path_for_story(Path(story_file)).read_text(encoding="utf-8")
    assert "- R1: Upload returns a summary report" in contract_text
    assert "## Negative Cases" in contract_text


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
            issue=_write_issue(tmp_path),
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    mock_detect.assert_not_called()
    contract_text = _contract_path_for_story(Path(story_file)).read_text(encoding="utf-8")
    assert "- R1: Upload returns a summary report" in contract_text


# Two-file model: the human-verified Story file holds ONLY the one-sentence
# Story; the machine-checkable contract lives in a separate file.
_LLM_STORY_MD = (
    "# User Story: Upload CSV\n\n"
    "## Story\n\n"
    "As a data analyst, I can upload a CSV file and view a summary report, "
    "so that I can quickly understand my data.\n"
)

# Default contract body returned by the stubbed contract LLM call. The real
# contract WRITER still runs, so generation tests produce a real contract file
# under user_stories/contracts/ with this body + the derived-from header.
_CONTRACT_MD = (
    "## Covers\n\n- R1: Upload returns a summary report\n\n"
    "## Context\n\n- `prompts/upload_python.prompt`: CSV upload + summary\n\n"
    "## Acceptance Criteria\n\n"
    "1. Given a valid CSV, when uploaded, then a summary report is shown.\n\n"
    "## Oracle\n\n- returned value shape\n\n"
    "## Non-Oracle\n\n- internal helper names\n\n"
    "## Negative Cases\n\n- Rejecting a valid CSV\n\n"
    "## Non-Goals\n\n- Editing the CSV\n\n"
    "## Candidate Prompts\n\n- `upload_python.prompt` — implements CSV upload (primary)\n\n"
    "## Notes\n\n- n/a\n"
)


# PR #1387 renamed `pdd context-audit` to `pdd context` and made the default
# output a Claude-Code `/context`-style usage box (the raw attribution table
# moved behind `--table`). These fixtures model that command as a prompt input so
# the issue-derived story can be exercised against both the faithful prompt and a
# harmful aggregate-only mutation.
_CONTEXT_PROMPT_BASE = "\n".join(
    [
        "<pdd-reason>Reports per-source token attribution for a hydrated prompt so users can audit context-window cost before generation, displayed by default as a Claude-Code /context-style usage box.</pdd-reason>",
        "",
        "% Goal",
        "Write the `pdd/commands/context.py` module.",
        "",
        "% Requirements",
        "1. Define a Click command named `context` with a required `prompt_path` argument.",
        "2. Provide options `--model`, `--json`, `--table`, and `--threshold`.",
        "3. Preprocess the prompt file; do NOT make an LLM call.",
        "4. Detect dynamic tags such as `<shell>` and `<web>` and emit warnings.",
        "5. Attribute tokens per source segment, including `prompt_body` and one row per resolved include.",
        "6. By default render a Claude-Code `/context`-style usage box with an "
        "`Estimated usage by category` breakdown (one line per source); `--table` "
        "shows the raw per-source attribution table.",
    ]
)


_CONTEXT_PROMPT_AGGREGATE_ONLY = "\n".join(
    [
        "<pdd-reason>Reports only aggregate token totals for a hydrated prompt so users can audit context-window cost before generation, without per-source attribution or a usage-box breakdown.</pdd-reason>",
        "",
        "% Goal",
        "Write the `pdd/commands/context.py` module.",
        "",
        "% Requirements",
        "1. Define a Click command named `context` with a required `prompt_path` argument.",
        "2. Provide options `--model`, `--json`, `--table`, and `--threshold`.",
        "3. Preprocess the prompt file; do NOT make an LLM call.",
        "4. Detect dynamic tags such as `<shell>` and `<web>` and emit warnings.",
        "5. Report only aggregate token totals, without per-source attribution rows.",
        "6. Render only the aggregate total; omit the per-source `Estimated usage by "
        "category` breakdown from the usage box.",
    ]
)


# Context-window example split into the two-file model: a plain human Story and a
# separate per-source contract. The durable, regression-catching signal
# (per-source breakdown vs aggregate-only) lives in the contract; the Story is a
# single readable sentence with no brand comparison.
_CONTEXT_HUMAN_STORY = (
    "# User Story: Audit context-window usage by source\n\n"
    "## Story\n\n"
    "As a CLI user, I can see how many tokens each part of my prompt uses before "
    "generating, so that I can find and trim what consumes the context window.\n"
)

_CONTEXT_CONTRACT_MD = (
    "## Covers\n\n"
    "- context_python.prompt: CLI users can run `pdd context <prompt_path>` to see "
    "per-source token attribution rendered as a usage box with a per-source "
    "`Estimated usage by category` breakdown before generation.\n"
    "- context_python.prompt: The command supports `--table`, `--json`, `--model`, and "
    "`--threshold` behavior without making an LLM call.\n\n"
    "## Context\n\n"
    "- `context_python.prompt` defines the `pdd context <prompt_path>` command, the "
    "default per-source usage box, the `--table` attribution table, JSON "
    "output, threshold exit behavior, dynamic-tag warnings, and the no-LLM-call "
    "requirement.\n\n"
    "## Acceptance Criteria\n\n"
    "1. Given a prompt with includes, when I run `pdd context <prompt_path>`, then "
    "the default output is a usage box whose "
    "`Estimated usage by category` breakdown reports token rows per source rather "
    "than only an aggregate total.\n"
    "2. Given `--table` is passed, when the audit completes, then the per-source "
    "attribution table is shown with rows ordered largest-token-consumer first.\n"
    "3. Given `--json` is passed, when the audit completes, then stdout is a JSON "
    "object with `total_tokens`, `context_limit`, `percent_used`, `model`, `rows`, "
    "`warnings`, and `threshold_exceeded`.\n"
    "4. Given the threshold percentage is exceeded, when `--threshold` is nonzero, "
    "then the command exits with code 2.\n"
    "5. Given dynamic tags such as `<shell>` or `<web>` are present, when they are "
    "not expanded, then warning entries are reported without making an LLM call.\n\n"
    "## Oracle\n\n"
    "These details matter for pass/fail:\n"
    "- The default output is a usage box with a "
    "per-source `Estimated usage by category` breakdown.\n"
    "- Per-source attribution rows are present for prompt body and resolved includes.\n"
    "- Aggregate-only token totals are not sufficient.\n"
    "- `--table`, `--json`, `--model`, and `--threshold` behavior matches the prompt.\n"
    "- The command does not make an LLM call for local auditing.\n\n"
    "## Non-Oracle\n\n"
    "These details should not matter:\n"
    "- The exact glyphs used in the usage box and the grid dimensions.\n"
    "- Private helper names.\n"
    "- Table styling.\n"
    "- Resemblance to any specific third-party tool's UI.\n"
    "- Internal ordering beyond sorting rows by token count.\n\n"
    "## Negative Cases\n\n"
    "- Reporting only an aggregate total with no per-source attribution.\n"
    "- Dropping the per-source breakdown when rendering the usage box.\n"
    "- Calling an LLM during the deterministic context audit.\n"
    "- Silently ignoring dynamic tags without warnings.\n\n"
    "## Non-Goals\n\n"
    "- Generating code from the audited prompt.\n"
    "- Fetching cloud grounding data locally.\n\n"
    "## Candidate Prompts\n\n"
    "- `context_python.prompt` — implements the context-window usage command (primary)\n\n"
    "## Notes\n\n"
    "- This story should fail validation if the prompt changes from per-source "
    "token attribution to aggregate-only token totals, or removes the default "
    "per-source usage-box breakdown.\n"
)


def test_generate_user_story_uses_llm_output(tmp_path):
    """Issue #1356: the story body is authored by the LLM from the ISSUE, and
    the pdd-story-prompts metadata linking the prompt is still stitched in."""
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
            issue=_write_issue(tmp_path),
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert mock_llm.called
    story_text = Path(story_file).read_text(encoding="utf-8")
    # LLM-authored narrative is present (not the deterministic placeholder).
    assert "As a data analyst, I can upload a CSV file" in story_text
    assert "<persona>" not in story_text
    # Acceptance criteria live in the generated contract, not the human story.
    assert "## Acceptance Criteria" not in story_text
    assert "## Acceptance Criteria" in _contract_path_for_story(
        Path(story_file)
    ).read_text(encoding="utf-8")
    # Metadata stitched deterministically even though the LLM did not emit it.
    assert story_text.startswith("<!-- pdd-story-prompts:")
    assert "upload_python.prompt" in story_text
    assert "linked from prompt inputs" in message
    assert cost == pytest.approx(0.05)
    assert model == "story-model"
    assert linked_prompts == ["upload_python.prompt"]
    mock_detect.assert_not_called()


def test_generate_user_story_context_story_protects_per_source_attribution(tmp_path):
    """Regression for PR #1387 (`pdd context`) as a prompt input: the generated
    story must capture concrete requirements -- the `/context`-style usage box and
    per-source attribution -- that make aggregate-only prompt drift fail."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "context_python.prompt"
    prompt_one.write_text(_CONTEXT_PROMPT_BASE, encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.user_story_tests._llm_generate_story_markdown",
        return_value=(_CONTEXT_HUMAN_STORY, 0.05, "story-model"),
    ), patch(
        "pdd.user_story_tests._llm_generate_story_contract",
        return_value=(_CONTEXT_CONTRACT_MD, 0.02, "contract-model"),
    ):
        success, _, _, _, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt_one)],
            issue=_write_issue(tmp_path),
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert linked_prompts == ["context_python.prompt"]
    mock_detect.assert_not_called()
    story_text = Path(story_file).read_text(encoding="utf-8")
    contract_text = _contract_path_for_story(Path(story_file)).read_text(encoding="utf-8")
    # The concrete, regression-catching requirements live in the CONTRACT.
    assert "per-source token attribution" in contract_text
    assert "Aggregate-only token totals are not sufficient" in contract_text
    # The regression-catching signal is the observable structure (a per-source
    # usage-box breakdown vs an aggregate-only total), not a brand comparison.
    assert "Estimated usage by category" in contract_text
    assert "usage box" in contract_text
    assert "`--table`, `--json`, `--model`, and `--threshold`" in contract_text
    assert "does not make an LLM call" in contract_text
    # Durability: neither file pins acceptance to a specific external tool's UI.
    # A future redesign (or a different best-in-class tool) must not make this
    # story falsely fail, so no Claude Code / Codex / Copilot brand comparison.
    for text in (story_text, contract_text):
        assert "Claude" not in text
        assert "Codex" not in text
        assert "Copilot" not in text
    assert "<pdd-reason>" not in story_text
    assert "\"type\": \"cli\"" not in story_text


def test_run_user_story_tests_passes_then_fails_for_harmful_context_prompt_change(tmp_path):
    """Show the same `pdd context` story passing the original prompt and failing
    after a harmful aggregate-only prompt mutation that drops the usage box."""
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    prompt_one = prompts_dir / "context_python.prompt"
    prompt_one.write_text(_CONTEXT_PROMPT_BASE, encoding="utf-8")
    # Two-file model: the human Story plus its sibling contract. Validation
    # combines them into the detect oracle, so the per-source requirements that
    # catch the regression live in the contract.
    story = stories_dir / "story__context.md"
    story.write_text(
        "<!-- pdd-story-prompts: context_python.prompt -->\n\n"
        f"{_CONTEXT_HUMAN_STORY}",
        encoding="utf-8",
    )
    contract = _contract_path_for_story(story)
    contract.parent.mkdir(parents=True, exist_ok=True)
    contract.write_text(_CONTEXT_CONTRACT_MD, encoding="utf-8")

    harmful_changes = [
        {
            "prompt_name": "context_python.prompt",
            "change_instructions": (
                "Restore the per-source `Estimated usage by category` breakdown; "
                "aggregate-only token totals violate the generated user story."
            ),
        }
    ]
    captured_prompt_inputs = []
    detect_trace = []

    def fake_detect(prompt_paths, story_content, *_args, **_kwargs):
        captured_prompt_inputs.append(prompt_paths)
        prompt_text = Path(prompt_paths[0]).read_text(encoding="utf-8")
        assert "per-source token attribution" in story_content
        assert "Aggregate-only token totals are not sufficient" in story_content
        if "Attribute tokens per source segment" in prompt_text:
            detect_trace.append("PASS: original prompt still requires per-source attribution")
            return [], 0.1, "gpt-test"
        if "Report only aggregate token totals" in prompt_text:
            detect_trace.append("FAIL: mutated prompt reports aggregate-only totals")
            return harmful_changes, 0.2, "gpt-test"
        raise AssertionError("test fixture prompt must be original or aggregate-only mutation")

    with patch("pdd.user_story_tests.detect_change", side_effect=fake_detect):
        baseline_passed, baseline_results, baseline_cost, baseline_model = run_user_story_tests(
            prompts_dir=str(prompts_dir),
            stories_dir=str(stories_dir),
            quiet=True,
            fail_fast=True,
        )
        prompt_one.write_text(_CONTEXT_PROMPT_AGGREGATE_ONLY, encoding="utf-8")
        mutated_passed, mutated_results, mutated_cost, mutated_model = run_user_story_tests(
            prompts_dir=str(prompts_dir),
            stories_dir=str(stories_dir),
            quiet=True,
            fail_fast=True,
        )

    assert baseline_passed is True
    assert baseline_results == [
        {
            "story": str(story),
            "passed": True,
            "changes": [],
        }
    ]
    assert baseline_cost == pytest.approx(0.1)
    assert baseline_model == "gpt-test"

    assert mutated_passed is False
    assert mutated_results == [
        {
            "story": str(story),
            "passed": False,
            "changes": harmful_changes,
        }
    ]
    assert captured_prompt_inputs == [[str(prompt_one)], [str(prompt_one)]]
    assert detect_trace == [
        "PASS: original prompt still requires per-source attribution",
        "FAIL: mutated prompt reports aggregate-only totals",
    ]
    assert mutated_cost == pytest.approx(0.2)
    assert mutated_model == "gpt-test"


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
            issue=_write_issue(tmp_path),
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
    """LLM output missing the required `## Story` heading is rejected without
    writing a deterministic substitute story."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_one.write_text("Handle file uploads.", encoding="utf-8")

    # No '## Story' heading at all — not a valid human story.
    malformed = "# User Story: x\n\nThis prose has no Story section heading.\n"
    bad_llm = {"result": malformed, "cost": 0.05, "model_name": "story-model"}
    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.llm_invoke.llm_invoke", return_value=bad_llm
    ):
        success, message, cost, model, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt_one)],
            issue=_write_issue(tmp_path),
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


def test_generate_user_story_accepts_minimal_human_story(tmp_path):
    """The human story file is intentionally tiny: a title + the `## Story`
    sentence is a COMPLETE, valid human story (the contract carries everything
    else). This is the inverse of the old single-file rule that required every
    canonical section in one file."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_one.write_text("Handle file uploads.", encoding="utf-8")

    minimal = (
        "# User Story: Upload\n\n"
        "## Story\n\n"
        "As a user, I can upload a file, so that I get a report.\n"
    )
    good_llm = {"result": minimal, "cost": 0.05, "model_name": "story-model"}
    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.llm_invoke.llm_invoke", return_value=good_llm
    ):
        success, message, cost, model, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt_one)],
            issue=_write_issue(tmp_path),
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert Path(story_file).exists()
    assert linked_prompts == ["upload_python.prompt"]
    mock_detect.assert_not_called()
    # The contract is still produced (via the autouse stub).
    assert _contract_path_for_story(Path(story_file)).exists()


def test_generate_writes_two_files_human_story_and_contract(tmp_path):
    """Generation writes a tiny human Story file plus a sibling AI contract under
    contracts/, with a derived-from header linking them and a Candidate Prompts
    list. The human file is the only thing a person verifies."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_one.write_text("Handle file uploads.", encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change"), patch(
        "pdd.user_story_tests._llm_generate_story_markdown",
        return_value=(_LLM_STORY_MD, 0.05, "story-model"),
    ):
        success, _, _, _, story_file, _ = generate_user_story(
            prompt_files=[str(prompt_one)],
            issue=_write_issue(tmp_path),
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    story_path = Path(story_file)
    # Human file: only one ## section (the Story); the contract sections are NOT here.
    story_text = story_path.read_text(encoding="utf-8")
    level2 = [ln.strip() for ln in story_text.splitlines() if ln.startswith("## ")]
    assert level2 == ["## Story"]

    # Contract file is a sibling under contracts/<slug>.contract.md.
    contract_path = story_path.parent / "contracts" / "upload.contract.md"
    assert contract_path == _contract_path_for_story(story_path)
    assert contract_path.exists()
    contract_text = contract_path.read_text(encoding="utf-8")
    # Derived-from header links the contract back to the human Story for sync.
    assert "pdd-story-contract" in contract_text
    assert 'derived-from-story="../story__upload.md"' in contract_text
    assert "story-hash=" in contract_text
    # Contract carries the machine-checkable sections + candidate prompts.
    for section in (
        "## Covers", "## Acceptance Criteria", "## Oracle",
        "## Negative Cases", "## Candidate Prompts",
    ):
        assert section in contract_text


def test_generate_contract_failure_is_non_blocking(tmp_path):
    """If the contract step fails, the human Story is still written (it is the
    source of truth); the message notes the contract can be generated later."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_one.write_text("Handle file uploads.", encoding="utf-8")

    with patch("pdd.user_story_tests.detect_change"), patch(
        "pdd.user_story_tests._llm_generate_story_markdown",
        return_value=(_LLM_STORY_MD, 0.05, "story-model"),
    ), patch(
        "pdd.user_story_tests._llm_generate_story_contract",
        return_value=(None, 0.0, "contract-model"),
    ):
        success, message, _, _, story_file, _ = generate_user_story(
            prompt_files=[str(prompt_one)],
            issue=_write_issue(tmp_path),
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert Path(story_file).exists()
    assert "Contract generation was skipped" in message
    assert not _contract_path_for_story(Path(story_file)).exists()


def test_sync_regenerates_contract_when_story_changes(tmp_path):
    """Editing the human Story re-aligns the contract (regenerated from the edited
    Story + the issue recorded in the contract header). An unchanged Story is a
    no-op."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_one.write_text("Handle file uploads.", encoding="utf-8")
    issue_src = _write_issue(tmp_path)

    with patch("pdd.user_story_tests.detect_change"), patch(
        "pdd.user_story_tests._llm_generate_story_markdown",
        return_value=(_LLM_STORY_MD, 0.05, "story-model"),
    ):
        _, _, _, _, story_file, _ = generate_user_story(
            prompt_files=[str(prompt_one)],
            issue=issue_src,
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    story_path = Path(story_file)
    contract_path = _contract_path_for_story(story_path)
    original_hash = _story_content_hash(story_path.read_text(encoding="utf-8"))
    assert f'story-hash="{original_hash}"' in contract_path.read_text(encoding="utf-8")

    # Unchanged Story -> sync is a no-op (no regeneration).
    changed, msg, _, _, _ = sync_user_story_contract(
        str(story_path), prompts_dir=str(prompts_dir)
    )
    assert changed is False
    assert "already aligned" in msg

    # Human edits the Story -> contract is regenerated to align with the new text.
    edited = story_path.read_text(encoding="utf-8").replace(
        "view a summary report", "view a summary report and download it as JSON"
    )
    story_path.write_text(edited, encoding="utf-8")
    new_hash = _story_content_hash(edited)
    assert new_hash != original_hash

    with patch(
        "pdd.user_story_tests._llm_generate_story_contract",
        return_value=(_CONTRACT_MD, 0.02, "contract-model"),
    ):
        changed, msg, _, _, _ = sync_user_story_contract(
            str(story_path), prompts_dir=str(prompts_dir)
        )
    assert changed is True
    assert "Regenerated contract" in msg
    assert f'story-hash="{new_hash}"' in contract_path.read_text(encoding="utf-8")


def test_validation_uses_story_plus_contract_as_oracle(tmp_path):
    """detect_change receives the human Story AND its contract combined."""
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()
    (prompts_dir / "upload_python.prompt").write_text("uploads", encoding="utf-8")

    story = stories_dir / "story__upload.md"
    story.write_text(
        "<!-- pdd-story-prompts: upload_python.prompt -->\n\n" + _LLM_STORY_MD,
        encoding="utf-8",
    )
    contract = _contract_path_for_story(story)
    contract.parent.mkdir(parents=True, exist_ok=True)
    contract.write_text(_CONTRACT_MD, encoding="utf-8")

    seen = {}

    def fake_detect(prompt_paths, oracle, *_a, **_k):
        seen["oracle"] = oracle
        return [], 0.1, "gpt-test"

    with patch("pdd.user_story_tests.detect_change", side_effect=fake_detect):
        passed, _, _, _ = run_user_story_tests(
            prompts_dir=str(prompts_dir), stories_dir=str(stories_dir), quiet=True
        )

    assert passed is True
    # The oracle must contain both the human Story sentence and a contract section.
    assert "As a data analyst, I can upload a CSV file" in seen["oracle"]
    assert "## Acceptance Criteria" in seen["oracle"]


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
            issue=_write_issue(tmp_path),
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
        issue=_write_issue(tmp_path),
        stories_dir=str(tmp_path / "user_stories"),
    )

    assert success is False
    assert "Prompt file not found" in message
    assert cost == 0.0
    assert model == ""
    assert story_file == ""
    assert linked_prompts == []


def test_generate_user_story_requires_issue(tmp_path):
    """Issue #1356: without an issue source, generation fails with a clear
    message and makes no LLM call -- it must not fall back to prompt-derived
    authoring."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_one.write_text("Handle file uploads.", encoding="utf-8")

    with patch("pdd.llm_invoke.llm_invoke") as mock_llm, patch(
        "pdd.user_story_tests._llm_generate_story_markdown"
    ) as mock_author:
        success, message, cost, model, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt_one)],
            issue=None,
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is False
    assert "derives the story from a GitHub issue" in message
    assert "--issue" in message
    assert story_file == ""
    assert linked_prompts == []
    mock_llm.assert_not_called()
    mock_author.assert_not_called()
    assert not (tmp_path / "user_stories").exists()


def test_generate_user_story_authors_from_issue_not_prompt(tmp_path):
    """Independence guarantee: the LLM that authors the story receives the
    ISSUE text and never the prompt body. This is what keeps the story an
    independent TDD oracle."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    # A unique marker that must NEVER reach the story-authoring LLM.
    prompt_one.write_text(
        "PROMPT_ONLY_MARKER_should_not_leak_into_story", encoding="utf-8"
    )

    issue_src = _write_issue(
        tmp_path,
        body=(
            "# Issue: Upload CSV\n\n"
            "ISSUE_MARKER_must_drive_the_story. Users can upload a CSV file and "
            "view a summary report.\n"
        ),
    )

    captured = {}

    def fake_llm(*, prompt, input_json, **_kwargs):
        captured["input_json"] = input_json
        return {"result": _LLM_STORY_MD, "cost": 0.05, "model_name": "story-model"}

    with patch("pdd.user_story_tests.detect_change") as mock_detect, patch(
        "pdd.llm_invoke.llm_invoke", side_effect=fake_llm
    ) as mock_llm:
        success, message, cost, model, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt_one)],
            issue=issue_src,
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is True
    assert mock_llm.called
    payload = "".join(str(v) for v in captured["input_json"].values())
    # The issue text reaches the author...
    assert "ISSUE_MARKER_must_drive_the_story" in payload
    # ...but the prompt body must NOT.
    assert "PROMPT_ONLY_MARKER_should_not_leak_into_story" not in payload
    # The prompt is still linked for validation/regeneration.
    assert linked_prompts == ["upload_python.prompt"]
    mock_detect.assert_not_called()


def test_generate_user_story_fails_when_issue_unresolvable(tmp_path):
    """A garbage issue source that is neither a file, a URL, nor a number fails
    generation before any LLM call."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_one = prompts_dir / "upload_python.prompt"
    prompt_one.write_text("Handle file uploads.", encoding="utf-8")

    with patch("pdd.llm_invoke.llm_invoke") as mock_llm:
        success, message, cost, model, story_file, linked_prompts = generate_user_story(
            prompt_files=[str(prompt_one)],
            issue="not-a-real-issue-source",
            stories_dir=str(tmp_path / "user_stories"),
            prompts_dir=str(prompts_dir),
        )

    assert success is False
    assert "Could not resolve issue source" in message
    assert story_file == ""
    assert linked_prompts == []
    mock_llm.assert_not_called()
    assert not (tmp_path / "user_stories").exists()


def test_resolve_issue_source_local_markdown_file(tmp_path):
    issue_path = tmp_path / "issue.md"
    issue_path.write_text(
        "# Add a context command\n\nBody text here.\n", encoding="utf-8"
    )

    title, body, ref = resolve_issue_source(str(issue_path))

    assert title == "Add a context command"
    assert "Body text here." in body
    assert ref == "issue.md"


def test_resolve_issue_source_github_url_uses_gh(tmp_path):
    with patch(
        "pdd.user_story_tests._fetch_issue_via_gh",
        return_value=("Issue title", "Issue body"),
    ) as mock_fetch:
        title, body, ref = resolve_issue_source(
            "https://github.com/promptdriven/pdd/issues/789"
        )

    mock_fetch.assert_called_once_with("promptdriven/pdd", "789")
    assert title == "Issue title"
    assert body == "Issue body"
    assert ref == "promptdriven/pdd#789"


def test_resolve_issue_source_pull_url_uses_gh(tmp_path):
    with patch(
        "pdd.user_story_tests._fetch_issue_via_gh",
        return_value=("PR title", "PR body"),
    ) as mock_fetch:
        title, body, ref = resolve_issue_source(
            "https://github.com/promptdriven/pdd/pull/1387"
        )

    mock_fetch.assert_called_once_with("promptdriven/pdd", "1387")
    assert ref == "promptdriven/pdd#1387"


def test_resolve_issue_source_bare_number_infers_repo(tmp_path):
    with patch(
        "pdd.user_story_tests._infer_repo_slug", return_value="promptdriven/pdd"
    ) as mock_repo, patch(
        "pdd.user_story_tests._fetch_issue_via_gh",
        return_value=("T", "B"),
    ) as mock_fetch:
        title, body, ref = resolve_issue_source("#1356")

    mock_repo.assert_called_once()
    mock_fetch.assert_called_once_with("promptdriven/pdd", "1356")
    assert ref == "promptdriven/pdd#1356"


def test_resolve_issue_source_unresolvable_returns_none(tmp_path):
    assert resolve_issue_source("") == (None, None, None)
    assert resolve_issue_source("not-a-source") == (None, None, None)
    # A number with no inferable repo cannot be resolved.
    with patch("pdd.user_story_tests._infer_repo_slug", return_value=None):
        assert resolve_issue_source("123") == (None, None, None)
    # gh failure surfaces as unresolved.
    with patch("pdd.user_story_tests._fetch_issue_via_gh", return_value=None):
        assert resolve_issue_source(
            "https://github.com/promptdriven/pdd/issues/1"
        ) == (None, None, None)


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


def test_user_story_fix_detect_and_change_are_contract_aware(tmp_path):
    """Regression for PR #1501 review item 4: the repair path must detect AND
    change against the human Story PLUS its generated contract, not the tiny
    story file alone. Otherwise `pdd fix user_stories/story__x.md` drops the
    contract's acceptance criteria/oracle and can no-op or under-specify."""
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
    story_path.write_text("## Story\nAs a user I want calc.\n", encoding="utf-8")
    contract_path = _contract_path_for_story(story_path)
    contract_path.parent.mkdir(parents=True, exist_ok=True)
    contract_text = (
        "## Acceptance Criteria\n1. CONTRACT_ONLY_CRITERION must hold.\n"
    )
    contract_path.write_text(contract_text, encoding="utf-8")

    detected_oracle = {}
    change_prompt_contents = {}

    def fake_detect_change(prompts, change_description, *args, **kwargs):
        detected_oracle["text"] = change_description
        return ([{"prompt_name": "calc_python.prompt"}], 0.1, "detect-model")

    def fake_change_main(**kwargs):
        change_prompt_contents["text"] = Path(
            kwargs["change_prompt_file"]
        ).read_text(encoding="utf-8")
        return (f"Modified prompt saved to {prompt_path}", 0.2, "change-model")

    ctx = SimpleNamespace(obj={})

    with patch("pdd.user_story_tests.discover_prompt_files", return_value=[prompt_path]), \
         patch("pdd.user_story_tests.detect_change", side_effect=fake_detect_change), \
         patch("pdd.user_story_tests.get_extension", return_value=".py"), \
         patch("pdd.change_main.change_main", side_effect=fake_change_main), \
         patch("pdd.user_story_tests.run_user_story_tests", return_value=(True, [], 0.3, "verify-model")):
        success, message, cost, model, changed_files = run_user_story_fix(
            ctx=ctx,
            story_file=str(story_path),
            prompts_dir=str(tmp_path / "prompts"),
            quiet=True,
        )

    assert success is True, message
    # detect_change saw the combined oracle (story + contract criterion).
    assert "CONTRACT_ONLY_CRITERION" in detected_oracle["text"]
    assert "As a user I want calc." in detected_oracle["text"]
    # change_main received the combined oracle on disk, not just the story file.
    assert "CONTRACT_ONLY_CRITERION" in change_prompt_contents["text"]
    assert "As a user I want calc." in change_prompt_contents["text"]


def test_user_story_fix_without_contract_passes_story_directly(tmp_path):
    """When no contract exists, the story file is the full oracle and is passed
    to change_main directly (no temp file indirection)."""
    prompts_dir = tmp_path / "prompts" / "sub"
    src_dir = tmp_path / "src" / "sub"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir(parents=True)
    src_dir.mkdir(parents=True)
    stories_dir.mkdir()

    prompt_path = prompts_dir / "calc_python.prompt"
    prompt_path.write_text("prompt", encoding="utf-8")
    (src_dir / "calc.py").write_text("code", encoding="utf-8")
    story_path = stories_dir / "story__calc.md"
    story_path.write_text("## Story\nplain story\n", encoding="utf-8")

    ctx = SimpleNamespace(obj={})

    with patch("pdd.user_story_tests.discover_prompt_files", return_value=[prompt_path]), \
         patch("pdd.user_story_tests.detect_change",
               return_value=([{"prompt_name": "calc_python.prompt"}], 0.1, "detect-model")), \
         patch("pdd.user_story_tests.get_extension", return_value=".py"), \
         patch("pdd.change_main.change_main",
               return_value=(f"Modified prompt saved to {prompt_path}", 0.2, "change-model")) as mock_change, \
         patch("pdd.user_story_tests.run_user_story_tests", return_value=(True, [], 0.3, "verify-model")):
        success, *_ = run_user_story_fix(
            ctx=ctx,
            story_file=str(story_path),
            prompts_dir=str(tmp_path / "prompts"),
            quiet=True,
        )

    assert success is True
    # No contract => change_main is handed the story path itself.
    assert mock_change.call_args[1]["change_prompt_file"] == str(story_path)


# Issue #1873 — diagnostic failure output


def test_failure_diagnostic_output_quiet_false(tmp_path, capsys, monkeypatch):
    """R1: full diagnostic block appears on failure when quiet=False."""
    monkeypatch.chdir(tmp_path)
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    prompt_path = prompts_dir / "foo_python.prompt"
    prompt_path.write_text("prompt", encoding="utf-8")
    story = stories_dir / "story__failure.md"
    story.write_text("As a user...", encoding="utf-8")

    changes = [
        {"prompt_name": "foo_python.prompt", "change_instructions": "Add support for X"}
    ]

    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        mock_detect.return_value = (changes, 0.5, "gpt-test")
        passed, results, _cost, _model = run_user_story_tests(
            prompts_dir="prompts",
            stories_dir="user_stories",
            quiet=False,
        )

    assert passed is False
    captured = capsys.readouterr()
    # Normalize output: rprint may wrap long paths across lines.
    out = captured.out.replace("\n", "")
    assert "FAIL" in out
    assert "user_stories/story__failure.md" in out
    assert "Linked prompts:" in out
    assert "prompts/foo_python.prompt" in out
    assert "Missing or stale behavior:" in out
    assert "prompts/foo_python.prompt: Add support for X" in out
    assert "Next step:" in out
    assert "pdd fix user_stories/story__failure.md" in out


def test_failure_diagnostic_output_quiet_true(tmp_path, capsys, monkeypatch):
    """R2: diagnostic block is suppressed when quiet=True."""
    monkeypatch.chdir(tmp_path)
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    prompt_path = prompts_dir / "foo_python.prompt"
    prompt_path.write_text("prompt", encoding="utf-8")
    story = stories_dir / "story__failure.md"
    story.write_text("As a user...", encoding="utf-8")

    changes = [
        {"prompt_name": "foo_python.prompt", "change_instructions": "Add support for X"}
    ]

    with patch("pdd.user_story_tests.detect_change") as mock_detect:
        mock_detect.return_value = (changes, 0.5, "gpt-test")
        passed, results, _cost, _model = run_user_story_tests(
            prompts_dir="prompts",
            stories_dir="user_stories",
            quiet=True,
        )

    assert passed is False
    captured = capsys.readouterr()
    out = captured.out
    assert "Linked prompts:" not in out
    assert "Missing or stale behavior:" not in out
    assert "Next step:" not in out


def test_failure_diagnostic_metadata_resolution_failure(tmp_path, capsys, monkeypatch):
    """R1 metadata-resolution path: diagnostic block uses error message when no prompts resolved."""
    monkeypatch.chdir(tmp_path)
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()

    prompt_path = prompts_dir / "foo_python.prompt"
    prompt_path.write_text("prompt", encoding="utf-8")
    story = stories_dir / "story__noprompts.md"
    story.write_text(
        "As a user...\n<!-- pdd-story-prompts: nonexistent_python.prompt -->\n",
        encoding="utf-8",
    )

    passed, results, _cost, _model = run_user_story_tests(
        prompts_dir="prompts",
        stories_dir="user_stories",
        quiet=False,
    )

    assert passed is False
    assert (
        results[0]["error"]
        == "No prompts from pdd-story-prompts metadata could be resolved."
    )
    captured = capsys.readouterr()
    # Normalize output: rprint may wrap long paths across lines.
    out = captured.out.replace("\n", "")
    assert "FAIL" in out
    assert "Linked prompts:" in out
    assert "none resolved from pdd-story-prompts metadata" in out
    assert "unresolved: nonexistent_python.prompt" in out
    assert "Missing or stale behavior:" in out
    assert "Next step:" in out
    assert "pdd fix user_stories/story__noprompts.md" in out


def test_failure_diagnostic_output_preserves_rich_markup_characters(
    tmp_path, capsys, monkeypatch
):
    """Diagnostic paths and instructions must not be parsed as Rich markup."""
    monkeypatch.chdir(tmp_path)
    prompt_dir = tmp_path / "prompts" / "frontend" / "app" / "[tenant]" / "queues"
    stories_dir = tmp_path / "user_stories"
    prompt_dir.mkdir(parents=True)
    stories_dir.mkdir()

    prompt_path = prompt_dir / "page_TypeScriptReact.prompt"
    prompt_path.write_text("Render tenant queue page.", encoding="utf-8")
    story = stories_dir / "story__tenant_queue.md"
    story.write_text(
        "As an operator, I can inspect tenant queue state.\n"
        "<!-- pdd-story-prompts: prompts/frontend/app/[tenant]/queues/page_TypeScriptReact.prompt -->\n",
        encoding="utf-8",
    )

    changes = [
        {
            "prompt_name": "page_TypeScriptReact.prompt",
            "change_instructions": "Guarantee app/[tenant]/queues shows slot state.",
        }
    ]

    with patch(
        "pdd.user_story_tests.detect_change",
        return_value=(changes, 0.5, "gpt-test"),
    ):
        passed, _results, _cost, _model = run_user_story_tests(
            prompts_dir="prompts",
            stories_dir="user_stories",
            quiet=False,
        )

    assert passed is False
    out = capsys.readouterr().out.replace("\n", "")
    assert "prompts/frontend/app/[tenant]/queues/page_TypeScriptReact.prompt" in out
    assert "app/[tenant]/queues shows slot state" in out
    assert "pdd fix user_stories/story__tenant_queue.md" in out


def test_cache_story_prompt_links_honors_explicit_prompts(tmp_path, monkeypatch):
    """Explicit --prompt inputs must all be linked, without an LLM call.

    Regression for `pdd story link STORY --prompt a --prompt b` dropping
    prompts whenever the story text happened to reference one of them (the
    story's own metadata comment counts as such a reference).
    """
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    prompt_a = prompts / "demo_python.prompt"
    prompt_b = prompts / "demo2_python.prompt"
    prompt_a.write_text("Demo prompt A.", encoding="utf-8")
    prompt_b.write_text("Demo prompt B.", encoding="utf-8")

    stories = tmp_path / "user_stories"
    stories.mkdir()
    story = stories / "story__demo.md"
    story.write_text(
        "<!-- pdd-story-prompts: demo_python.prompt -->\n\n"
        "# User Story: demo\n\n"
        "## Story\n"
        "As a user, I can run the demo, so that I see a response.\n",
        encoding="utf-8",
    )

    def _no_llm(*_args, **_kwargs):
        raise AssertionError("explicit prompt links must not call detect_change")

    monkeypatch.setattr("pdd.user_story_tests.detect_change", _no_llm)

    success, message, cost, _model, linked_refs = cache_story_prompt_links(
        story_file=str(story),
        prompts_dir=str(prompts),
        prompt_files=[prompt_a, prompt_b],
        force_relink=True,
    )

    assert success, message
    assert cost == 0.0
    assert linked_refs == ["demo2_python.prompt", "demo_python.prompt"]
    metadata_line = story.read_text(encoding="utf-8").splitlines()[0]
    assert "demo2_python.prompt" in metadata_line
    assert "demo_python.prompt" in metadata_line
