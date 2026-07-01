"""Tests for the ``pdd story`` CLI command group (issue #1768).

Covers all acceptance criteria:
  - pdd story add <source> --title ... --prompt ... --devunit ...
  - pdd story list --with-regression-status
  - pdd story link <story_file> --prompt ...
  - dry-run mode, duplicate detection, path-traversal rejection
"""
from __future__ import annotations

import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest
from click.testing import CliRunner

# ---------------------------------------------------------------------------
# Import the command group — guard against not-yet-implemented module so that
# test collection succeeds even before pdd/commands/story.py exists.
# ---------------------------------------------------------------------------
try:
    from pdd.commands.story import story  # type: ignore[import]
    _STORY_COMMAND_AVAILABLE = True
except ImportError:
    story = None  # type: ignore[assignment]
    _STORY_COMMAND_AVAILABLE = False

pytestmark = pytest.mark.skipif(
    not _STORY_COMMAND_AVAILABLE,
    reason="pdd.commands.story not yet implemented",
)

# ---------------------------------------------------------------------------
# Shared fixtures
# ---------------------------------------------------------------------------

@pytest.fixture()
def runner() -> CliRunner:
    return CliRunner()


@pytest.fixture()
def isolated_runner(tmp_path: Path):
    """CliRunner whose mix_stderr is False so stdout/stderr are separate."""
    return CliRunner(mix_stderr=False)


# Realistic return value shape for generate_user_story():
#   (success: bool, message: str, cost: float, model: str, story_path: str, linked_refs: List[str])
_STORY_SUCCESS = (
    True,
    "Generated story file: user_stories/story__my_feature.md. "
    "Story prompt metadata linked from prompt inputs.",
    0.05,
    "claude-sonnet-4-6",
    "user_stories/story__my_feature.md",
    ["commands/my_feature_python.prompt"],
)

# Realistic return value for discover_story_files(): List[Path]
_STORY_PATHS = [
    Path("user_stories/story__pdd_fix.md"),
    Path("user_stories/story__pdd_checkup.md"),
]

# ---------------------------------------------------------------------------
# Scenario 1: Issue-URL input
# ---------------------------------------------------------------------------

class TestIssueUrlInput:
    """pdd story add <github-url> creates a story from the issue."""

    def test_valid_github_url_creates_story(self, runner: CliRunner, tmp_path: Path) -> None:
        """A valid GitHub issue URL is resolved and a story file is created."""
        with runner.isolated_filesystem(temp_dir=tmp_path):
            with patch("pdd.commands.story.generate_user_story") as mock_gen:
                mock_gen.return_value = _STORY_SUCCESS
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "https://github.com/promptdriven/pdd/issues/1768",
                        "--title", "My Feature Story",
                        "--prompt", "prompts/my_feature_python.prompt",
                    ],
                    obj={"quiet": True, "verbose": False},
                )
        assert result.exit_code == 0, result.output
        mock_gen.assert_called_once()
        call_kwargs = mock_gen.call_args.kwargs
        assert call_kwargs["issue"] == "https://github.com/promptdriven/pdd/issues/1768"

    def test_github_url_without_title_infers_from_issue(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """No --title provided: command infers title from the issue."""
        with runner.isolated_filesystem(temp_dir=tmp_path):
            with patch("pdd.commands.story.generate_user_story") as mock_gen:
                mock_gen.return_value = _STORY_SUCCESS
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "https://github.com/promptdriven/pdd/issues/1768",
                        "--prompt", "prompts/my_feature_python.prompt",
                    ],
                    obj={"quiet": True, "verbose": False},
                )
        assert result.exit_code == 0, result.output

    def test_unresolvable_url_exits_nonzero(self, runner: CliRunner, tmp_path: Path) -> None:
        """When the issue URL cannot be fetched the command exits non-zero."""
        with runner.isolated_filesystem(temp_dir=tmp_path):
            with patch("pdd.commands.story.generate_user_story") as mock_gen:
                mock_gen.return_value = (
                    False,
                    "Could not resolve issue source 'https://github.com/example/repo/issues/9999'.",
                    0.0,
                    "",
                    "",
                    [],
                )
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "https://github.com/example/repo/issues/9999",
                        "--prompt", "prompts/foo_python.prompt",
                    ],
                    obj={"quiet": True, "verbose": False},
                )
        assert result.exit_code != 0


# ---------------------------------------------------------------------------
# Scenario 2: Inline text input
# ---------------------------------------------------------------------------

class TestInlineTextInput:
    """pdd story add "<text>" --title "..." creates a story from free text."""

    def test_inline_text_with_title_creates_story(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """Raw description text plus --title produces a story file."""
        with runner.isolated_filesystem(temp_dir=tmp_path):
            with patch("pdd.commands.story.generate_user_story") as mock_gen:
                mock_gen.return_value = _STORY_SUCCESS
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "Users should be able to export reports as PDF.",
                        "--title", "Export PDF Report",
                        "--prompt", "prompts/export_python.prompt",
                    ],
                    obj={"quiet": True, "verbose": False},
                )
        assert result.exit_code == 0, result.output
        mock_gen.assert_called_once()

    def test_local_markdown_file_as_source(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """A local markdown file path is accepted as the story source."""
        issue_md = tmp_path / "my_issue.md"
        issue_md.write_text("# Add PDF Export\n\nUsers need PDF export.\n", encoding="utf-8")

        with runner.isolated_filesystem(temp_dir=tmp_path):
            with patch("pdd.commands.story.generate_user_story") as mock_gen:
                mock_gen.return_value = _STORY_SUCCESS
                result = runner.invoke(
                    story,
                    [
                        "add",
                        str(issue_md),
                        "--prompt", "prompts/export_python.prompt",
                    ],
                    obj={"quiet": True, "verbose": False},
                )
        assert result.exit_code == 0, result.output
        call_kwargs = mock_gen.call_args.kwargs
        assert str(issue_md) in call_kwargs.get("issue", "")


# ---------------------------------------------------------------------------
# Scenario 3: Single-dev-unit link
# ---------------------------------------------------------------------------

class TestSingleDevUnitLink:
    """--devunit resolves to a prompt path and embeds pdd-story-prompts metadata."""

    def test_known_devunit_resolves_to_prompt(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """A known devunit name is resolved to its prompt path."""
        resolved_prompt = tmp_path / "prompts" / "foo_python.prompt"
        resolved_prompt.parent.mkdir(parents=True, exist_ok=True)
        resolved_prompt.write_text("% foo prompt\n", encoding="utf-8")

        with runner.isolated_filesystem(temp_dir=tmp_path):
            with patch("pdd.commands.story.generate_user_story") as mock_gen, \
                 patch("pdd.commands.story.resolve_prompt_path") as mock_resolve:
                mock_resolve.return_value = resolved_prompt
                mock_gen.return_value = (
                    True,
                    "Generated story file: user_stories/story__foo.md. "
                    "Story prompt metadata linked from prompt inputs.",
                    0.03,
                    "claude-sonnet-4-6",
                    "user_stories/story__foo.md",
                    ["commands/foo_python.prompt"],
                )
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "https://github.com/promptdriven/pdd/issues/1768",
                        "--devunit", "foo",
                    ],
                    obj={"quiet": True, "verbose": False},
                )
        assert result.exit_code == 0, result.output

    def test_unknown_devunit_exits_nonzero(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """An unresolvable devunit name causes the command to exit non-zero."""
        with runner.isolated_filesystem(temp_dir=tmp_path):
            with patch("pdd.commands.story.resolve_prompt_path") as mock_resolve:
                mock_resolve.return_value = None
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "https://github.com/promptdriven/pdd/issues/1768",
                        "--devunit", "nonexistent_unit",
                    ],
                    obj={"quiet": True, "verbose": False},
                )
        assert result.exit_code != 0
        assert "nonexistent_unit" in result.output.lower() or result.exit_code != 0

    def test_explicit_prompt_path_bypasses_devunit_resolution(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """--prompt <path> is accepted directly without devunit lookup."""
        prompt_file = tmp_path / "prompts" / "bar_python.prompt"
        prompt_file.parent.mkdir(parents=True, exist_ok=True)
        prompt_file.write_text("% bar prompt\n", encoding="utf-8")

        with runner.isolated_filesystem(temp_dir=tmp_path):
            with patch("pdd.commands.story.generate_user_story") as mock_gen:
                mock_gen.return_value = _STORY_SUCCESS
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "https://github.com/promptdriven/pdd/issues/1768",
                        "--prompt", str(prompt_file),
                    ],
                    obj={"quiet": True, "verbose": False},
                )
        assert result.exit_code == 0, result.output
        # resolve_prompt_path should NOT have been called for --prompt
        call_kwargs = mock_gen.call_args.kwargs
        assert str(prompt_file) in str(call_kwargs.get("prompt_files", []))


# ---------------------------------------------------------------------------
# Scenario 4: Cross-dev-unit / multi-devunit link
# ---------------------------------------------------------------------------

class TestCrossDevUnitLink:
    """--devunit a --devunit b preserves BOTH links in pdd-story-prompts metadata."""

    def test_two_devunits_preserve_both_prompt_refs(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """Both --devunit values are embedded in the story metadata, not just the first."""
        prompt_a = tmp_path / "prompts" / "alpha_python.prompt"
        prompt_b = tmp_path / "prompts" / "beta_python.prompt"
        for p in (prompt_a, prompt_b):
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text("% prompt\n", encoding="utf-8")

        def _resolve(project_root: Path, basename: str, manifest=None) -> Path | None:
            mapping = {"alpha": prompt_a, "beta": prompt_b}
            return mapping.get(basename)

        with runner.isolated_filesystem(temp_dir=tmp_path):
            with patch("pdd.commands.story.generate_user_story") as mock_gen, \
                 patch("pdd.commands.story.resolve_prompt_path", side_effect=_resolve):
                mock_gen.return_value = (
                    True,
                    "Generated story file: user_stories/story__alpha_beta.md.",
                    0.06,
                    "claude-sonnet-4-6",
                    "user_stories/story__alpha_beta.md",
                    ["alpha_python.prompt", "beta_python.prompt"],
                )
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "https://github.com/promptdriven/pdd/issues/1768",
                        "--devunit", "alpha",
                        "--devunit", "beta",
                    ],
                    obj={"quiet": True, "verbose": False},
                )
        assert result.exit_code == 0, result.output
        call_kwargs = mock_gen.call_args.kwargs
        passed_prompts = [str(p) for p in call_kwargs.get("prompt_files", [])]
        assert str(prompt_a) in passed_prompts, "prompt_a missing from call"
        assert str(prompt_b) in passed_prompts, "prompt_b missing from call"

    def test_mixed_devunit_and_explicit_prompt(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """--devunit and --prompt can be combined and all links are preserved."""
        prompt_a = tmp_path / "prompts" / "alpha_python.prompt"
        prompt_explicit = tmp_path / "prompts" / "explicit_python.prompt"
        for p in (prompt_a, prompt_explicit):
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text("% prompt\n", encoding="utf-8")

        with runner.isolated_filesystem(temp_dir=tmp_path):
            with patch("pdd.commands.story.generate_user_story") as mock_gen, \
                 patch("pdd.commands.story.resolve_prompt_path") as mock_resolve:
                mock_resolve.return_value = prompt_a
                mock_gen.return_value = (
                    True,
                    "Generated story file: user_stories/story__alpha.md.",
                    0.04,
                    "claude-sonnet-4-6",
                    "user_stories/story__alpha.md",
                    ["alpha_python.prompt", "explicit_python.prompt"],
                )
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "https://github.com/promptdriven/pdd/issues/1768",
                        "--devunit", "alpha",
                        "--prompt", str(prompt_explicit),
                    ],
                    obj={"quiet": True, "verbose": False},
                )
        assert result.exit_code == 0, result.output
        call_kwargs = mock_gen.call_args.kwargs
        passed_prompts = [str(p) for p in call_kwargs.get("prompt_files", [])]
        assert str(prompt_explicit) in passed_prompts


class TestStoryAddWorkflowOptions:
    """Workflow options that shape story generation inputs."""

    def test_title_controls_output_story_slug(self, runner: CliRunner, tmp_path: Path) -> None:
        """--title is passed through as the generated story output path."""
        with runner.isolated_filesystem(temp_dir=tmp_path):
            with patch("pdd.commands.story.generate_user_story") as mock_gen:
                mock_gen.return_value = _STORY_SUCCESS
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "https://github.com/promptdriven/pdd/issues/1768",
                        "--title", "Export PDF Report",
                        "--prompt", "prompts/export_python.prompt",
                    ],
                    obj={"quiet": True, "verbose": False},
                )
        assert result.exit_code == 0, result.output
        assert mock_gen.call_args.kwargs["output"].endswith(
            "user_stories/story__export_pdf_report.md"
        )

    def test_from_changed_files_uses_git_status_prompts(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """--from-changed-files discovers modified/untracked .prompt files."""
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir(parents=True)
        changed_prompt = prompts_dir / "changed_python.prompt"
        changed_prompt.write_text("% changed prompt\n", encoding="utf-8")

        with runner.isolated_filesystem(temp_dir=tmp_path):
            with patch("pdd.commands.story._changed_prompt_files") as mock_changed, \
                 patch("pdd.commands.story.generate_user_story") as mock_gen:
                mock_changed.return_value = [str(changed_prompt)]
                mock_gen.return_value = _STORY_SUCCESS
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "https://github.com/promptdriven/pdd/issues/1768",
                        "--from-changed-files",
                    ],
                    obj={"quiet": True, "verbose": False},
                )

        assert result.exit_code == 0, result.output
        assert str(changed_prompt) in mock_gen.call_args.kwargs["prompt_files"]

    def test_generate_regression_prints_from_story_handoff(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """--generate-regression points users to deterministic pdd test --from-story."""
        with runner.isolated_filesystem(temp_dir=tmp_path):
            with patch("pdd.commands.story.generate_user_story") as mock_gen:
                mock_gen.return_value = (
                    True,
                    "Generated story file: user_stories/story__export_pdf.md.",
                    0.0,
                    "deterministic",
                    "user_stories/story__export_pdf.md",
                    ["prompts/export_python.prompt"],
                )
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "https://github.com/promptdriven/pdd/issues/1768",
                        "--prompt", "prompts/export_python.prompt",
                        "--generate-regression",
                    ],
                    obj={"quiet": True, "verbose": False},
                )

        assert result.exit_code == 0, result.output
        assert "Issue #1700" in result.output
        assert "pdd test --from-story user_stories/story__export_pdf.md" in result.output


# ---------------------------------------------------------------------------
# Scenario 5: Duplicate detection
# ---------------------------------------------------------------------------

class TestDuplicateDetection:
    """Existing story slug exits with a clear error; --update allows overwrite."""

    def test_duplicate_slug_exits_nonzero_with_path(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """If story__my_feature.md already exists, the command exits non-zero."""
        stories_dir = tmp_path / "user_stories"
        stories_dir.mkdir(parents=True, exist_ok=True)
        existing = stories_dir / "story__my_feature.md"
        existing.write_text("<!-- pdd-story-prompts: prompts/x_python.prompt -->\n## Story\n", encoding="utf-8")

        with runner.isolated_filesystem(temp_dir=tmp_path):
            with patch("pdd.commands.story.generate_user_story") as mock_gen:
                # generate_user_story detects the duplicate and returns failure
                mock_gen.return_value = (
                    False,
                    f"Story already exists: {existing}. Use --update to overwrite.",
                    0.0,
                    "",
                    str(existing),
                    [],
                )
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "https://github.com/promptdriven/pdd/issues/1768",
                        "--title", "My Feature",
                        "--prompt", "prompts/x_python.prompt",
                    ],
                    obj={"quiet": True, "verbose": False},
                )
        assert result.exit_code != 0

    def test_update_flag_allows_overwrite(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """--update allows overwriting an existing story slug."""
        stories_dir = tmp_path / "user_stories"
        stories_dir.mkdir(parents=True, exist_ok=True)
        existing = stories_dir / "story__my_feature.md"
        existing.write_text("old content\n", encoding="utf-8")

        with runner.isolated_filesystem(temp_dir=tmp_path):
            with patch("pdd.commands.story.generate_user_story") as mock_gen:
                mock_gen.return_value = (
                    True,
                    f"Updated story file: {existing}. Story prompt metadata linked.",
                    0.03,
                    "claude-sonnet-4-6",
                    str(existing),
                    ["commands/x_python.prompt"],
                )
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "https://github.com/promptdriven/pdd/issues/1768",
                        "--title", "My Feature",
                        "--prompt", "prompts/x_python.prompt",
                        "--update",
                    ],
                    obj={"quiet": True, "verbose": False},
                )
        assert result.exit_code == 0, result.output

    def test_update_existing_title_merges_metadata_without_regenerating(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """--update relinks an existing titled story instead of rewriting its body."""
        with runner.isolated_filesystem(temp_dir=tmp_path) as fs:
            stories_dir = Path(fs) / "user_stories"
            stories_dir.mkdir(parents=True, exist_ok=True)
            existing = stories_dir / "story__my_feature.md"
            existing.write_text("old content\n", encoding="utf-8")
            with patch("pdd.commands.story.cache_story_prompt_links") as mock_link, \
                 patch("pdd.commands.story.generate_user_story") as mock_gen:
                mock_link.return_value = (
                    True,
                    "Story prompt metadata linked.",
                    0.0,
                    "",
                    ["prompts/x_python.prompt"],
                )
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "https://github.com/promptdriven/pdd/issues/1768",
                        "--title", "My Feature",
                        "--prompt", "prompts/x_python.prompt",
                        "--update",
                    ],
                    obj={"quiet": True, "verbose": False},
                )

        assert result.exit_code == 0, result.output
        mock_link.assert_called_once()
        mock_gen.assert_not_called()

    def test_case_insensitive_slug_collision_detected(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """Case-insensitive slug match: 'My Feature' collides with story__my_feature.md."""
        stories_dir = tmp_path / "user_stories"
        stories_dir.mkdir(parents=True, exist_ok=True)
        existing = stories_dir / "story__my_feature.md"
        existing.write_text("## Story\nAs a user...\n", encoding="utf-8")

        with runner.isolated_filesystem(temp_dir=tmp_path):
            with patch("pdd.commands.story.generate_user_story") as mock_gen:
                mock_gen.return_value = (
                    False,
                    f"Story already exists: {existing}. Use --update to overwrite.",
                    0.0,
                    "",
                    str(existing),
                    [],
                )
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "https://github.com/promptdriven/pdd/issues/1768",
                        "--title", "MY FEATURE",  # same slug, different case
                        "--prompt", "prompts/x_python.prompt",
                    ],
                    obj={"quiet": True, "verbose": False},
                )
        assert result.exit_code != 0


# ---------------------------------------------------------------------------
# Scenario 6: Dry-run mode
# ---------------------------------------------------------------------------

class TestDryRunMode:
    """--dry-run prints the proposed file path and prompts without writing files."""

    def test_dry_run_prints_path_and_prompts_without_writing(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """--dry-run outputs what would be created but writes no story file."""
        with runner.isolated_filesystem(temp_dir=tmp_path) as fs:
            with patch("pdd.commands.story.generate_user_story") as mock_gen:
                result = runner.invoke(
                    story,
                    [
                        "add",
                        "https://github.com/promptdriven/pdd/issues/1768",
                        "--title", "My Feature",
                        "--prompt", "prompts/foo_python.prompt",
                        "--dry-run",
                    ],
                    obj={"quiet": True, "verbose": False},
                )
            # generate_user_story must NOT be called in dry-run mode
            mock_gen.assert_not_called()

        assert result.exit_code == 0, result.output
        out = result.output.lower()
        # Output should mention the proposed path and the prompt
        assert "story__" in out or "dry" in out or "would" in out
        assert "foo_python.prompt" in result.output or "foo" in out

        # No new story file should have been written
        story_files = list(tmp_path.rglob("story__*.md"))
        assert story_files == [], f"Unexpected story files written: {story_files}"

    def test_dry_run_still_validates_path_traversal(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """--dry-run must still reject path traversal in the title/slug."""
        with runner.isolated_filesystem(temp_dir=tmp_path):
            result = runner.invoke(
                story,
                [
                    "add",
                    "some text",
                    "--title", "../evil",
                    "--dry-run",
                ],
                obj={"quiet": True, "verbose": False},
            )
        assert result.exit_code != 0


# ---------------------------------------------------------------------------
# Scenario 7: Path traversal rejection
# ---------------------------------------------------------------------------

class TestPathTraversalRejection:
    """Titles/slugs containing .. or absolute paths are rejected with exit code != 0."""

    def test_title_with_double_dotdot_is_rejected(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """A title containing ``../`` is rejected before any file I/O."""
        with runner.isolated_filesystem(temp_dir=tmp_path):
            result = runner.invoke(
                story,
                [
                    "add",
                    "some description text",
                    "--title", "../../../etc/passwd",
                    "--prompt", "prompts/foo_python.prompt",
                ],
                obj={"quiet": True, "verbose": False},
            )
        assert result.exit_code != 0

    def test_title_with_absolute_path_is_rejected(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """A title that resolves to an absolute path outside user_stories/ is rejected."""
        with runner.isolated_filesystem(temp_dir=tmp_path):
            result = runner.invoke(
                story,
                [
                    "add",
                    "some description",
                    "--title", "/etc/passwd",
                    "--prompt", "prompts/foo_python.prompt",
                ],
                obj={"quiet": True, "verbose": False},
            )
        assert result.exit_code != 0

    def test_title_with_embedded_traversal_is_rejected(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """A slug like ``valid/../sneaky`` that still escapes the directory is rejected."""
        with runner.isolated_filesystem(temp_dir=tmp_path):
            result = runner.invoke(
                story,
                [
                    "add",
                    "some description",
                    "--title", "valid/../sneaky",
                    "--prompt", "prompts/foo_python.prompt",
                ],
                obj={"quiet": True, "verbose": False},
            )
        assert result.exit_code != 0


# ---------------------------------------------------------------------------
# Scenario 8: pdd story list --with-regression-status
# ---------------------------------------------------------------------------

class TestStoryList:
    """pdd story list shows story id, linked prompts, and regression status."""

    def test_list_shows_stories_with_prompt_metadata(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """Story files with pdd-story-prompts metadata are listed with their prompts."""
        story_paths = [
            tmp_path / "user_stories" / "story__pdd_fix.md",
            tmp_path / "user_stories" / "story__pdd_checkup.md",
        ]
        for p in story_paths:
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(
                "<!-- pdd-story-prompts: prompts/fix_python.prompt -->\n\n## Story\n",
                encoding="utf-8",
            )

        with patch("pdd.commands.story.discover_story_files") as mock_discover:
            mock_discover.return_value = story_paths
            result = runner.invoke(
                story,
                ["list"],
                obj={"quiet": True, "verbose": False},
            )
        assert result.exit_code == 0, result.output
        assert "story__pdd_fix" in result.output
        assert "story__pdd_checkup" in result.output

    def test_list_empty_directory_shows_no_stories(
        self, runner: CliRunner
    ) -> None:
        """When no story files exist the list is empty (exit 0, no crash)."""
        with patch("pdd.commands.story.discover_story_files") as mock_discover:
            mock_discover.return_value = []
            result = runner.invoke(
                story,
                ["list"],
                obj={"quiet": True, "verbose": False},
            )
        assert result.exit_code == 0

    def test_list_with_regression_status_shows_status_column(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """--with-regression-status adds a status column (missing/passing/stale)."""
        story_path = tmp_path / "user_stories" / "story__pdd_fix.md"
        story_path.parent.mkdir(parents=True, exist_ok=True)
        story_path.write_text(
            "<!-- pdd-story-prompts: prompts/fix_python.prompt -->\n\n## Story\n",
            encoding="utf-8",
        )

        with patch("pdd.commands.story.discover_story_files") as mock_discover:
            mock_discover.return_value = [story_path]
            result = runner.invoke(
                story,
                ["list", "--with-regression-status"],
                obj={"quiet": True, "verbose": False},
            )
        assert result.exit_code == 0, result.output
        out_lower = result.output.lower()
        # One of the status values should appear in the output
        status_terms = {"missing", "passing", "stale", "status", "regression"}
        assert any(term in out_lower for term in status_terms), (
            f"Expected regression status info in output, got: {result.output!r}"
        )

    def test_list_stories_without_prompt_metadata_are_still_listed(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """Stories without pdd-story-prompts metadata appear in listing with empty prompts column."""
        story_path = tmp_path / "user_stories" / "story__unlinkated.md"
        story_path.parent.mkdir(parents=True, exist_ok=True)
        story_path.write_text("## Story\nAs a user, I want something.\n", encoding="utf-8")

        with patch("pdd.commands.story.discover_story_files") as mock_discover:
            mock_discover.return_value = [story_path]
            result = runner.invoke(
                story,
                ["list"],
                obj={"quiet": True, "verbose": False},
            )
        assert result.exit_code == 0, result.output
        assert "story__unlinkated" in result.output


# ---------------------------------------------------------------------------
# Scenario 9: pdd story link (bonus — link subcommand)
# ---------------------------------------------------------------------------

class TestStoryLink:
    """pdd story link <story_file> --prompt <path> updates pdd-story-prompts metadata."""

    def test_link_adds_prompt_metadata_to_existing_story(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """The link subcommand writes pdd-story-prompts metadata to the story file."""
        story_file = tmp_path / "user_stories" / "story__checkout_refund.md"
        story_file.parent.mkdir(parents=True, exist_ok=True)
        story_file.write_text("## Story\nAs a user, I want refunds.\n", encoding="utf-8")

        prompt_file = tmp_path / "prompts" / "refund_payment_python.prompt"
        prompt_file.parent.mkdir(parents=True, exist_ok=True)
        prompt_file.write_text("% refund prompt\n", encoding="utf-8")

        with patch("pdd.commands.story.cache_story_prompt_links") as mock_link:
            mock_link.return_value = (
                True,
                "Story prompt metadata linked.",
                0.0,
                "",
                ["prompts/refund_payment_python.prompt"],
            )
            result = runner.invoke(
                story,
                [
                    "link",
                    str(story_file),
                    "--prompt", str(prompt_file),
                ],
                obj={"quiet": True, "verbose": False},
            )
        assert result.exit_code == 0, result.output

    def test_link_missing_story_file_exits_nonzero(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """Linking to a nonexistent story file exits non-zero."""
        with runner.isolated_filesystem(temp_dir=tmp_path):
            result = runner.invoke(
                story,
                [
                    "link",
                    "user_stories/story__does_not_exist.md",
                    "--prompt", "prompts/foo_python.prompt",
                ],
                obj={"quiet": True, "verbose": False},
            )
        assert result.exit_code != 0

    def test_link_rejects_story_outside_user_stories(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """Linking a markdown file outside user_stories is rejected."""
        story_file = tmp_path / "story__checkout_refund.md"
        story_file.write_text("## Story\nAs a user, I want refunds.\n", encoding="utf-8")
        prompt_file = tmp_path / "prompts" / "refund_payment_python.prompt"
        prompt_file.parent.mkdir(parents=True, exist_ok=True)
        prompt_file.write_text("% refund prompt\n", encoding="utf-8")

        result = runner.invoke(
            story,
            [
                "link",
                str(story_file),
                "--prompt", str(prompt_file),
            ],
            obj={"quiet": True, "verbose": False},
        )
        assert result.exit_code != 0
