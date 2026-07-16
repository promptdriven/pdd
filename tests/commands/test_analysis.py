import os
import json
import sys
import subprocess
import click
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
from click.testing import CliRunner
from pdd.commands.analysis import detect_change, conflicts, bug, crash, trace
from pdd.cli import cli as pdd_cli
from pdd.user_story_tests import run_user_story_tests

# -----------------------------------------------------------------------------
# Fixtures
# -----------------------------------------------------------------------------


@pytest.fixture
def runner():
    """Fixture for Click CliRunner."""
    return CliRunner()


@pytest.fixture
def mock_context_obj():
    """Fixture for the context object expected by the commands."""
    return {"verbose": False, "quiet": False}


# -----------------------------------------------------------------------------
# Tests for 'detect' command
# -----------------------------------------------------------------------------


def test_detect_change_success(runner, mock_context_obj):
    """Test 'detect' command with valid arguments."""
    with patch("pdd.commands.analysis.detect_change_main") as mock_main:
        # Setup mock return
        mock_main.return_value = ([], 0.0, "gpt-4")

        with runner.isolated_filesystem():
            # Create dummy files
            with open("p1.prompt", "w") as f:
                f.write("content")
            with open("p2.prompt", "w") as f:
                f.write("content")
            with open("change.txt", "w") as f:
                f.write("change")

            result = runner.invoke(
                detect_change,
                ["p1.prompt", "p2.prompt", "change.txt", "--output", "out.csv"],
                obj=mock_context_obj,
            )

            assert result.exit_code == 0

            # Verify detect_change_main was called correctly
            # The last file is the change file, others are prompt files
            args, kwargs = mock_main.call_args
            assert kwargs["prompt_files"] == ["p1.prompt", "p2.prompt"]
            assert kwargs["change_file"] == "change.txt"
            assert kwargs["output"] == "out.csv"


def test_detect_change_insufficient_args(runner, mock_context_obj):
    """Test 'detect' command fails with fewer than 2 files."""
    with runner.isolated_filesystem():
        with open("p1.prompt", "w") as f:
            f.write("content")

        result = runner.invoke(detect_change, ["p1.prompt"], obj=mock_context_obj)

        assert result.exit_code != 0
        assert "Requires at least one PROMPT_FILE and one CHANGE_FILE" in result.output


# -----------------------------------------------------------------------------
# Tests for 'detect --stories' mode
# -----------------------------------------------------------------------------


def test_detect_stories_success(runner, mock_context_obj):
    """Test 'detect --stories' invokes user story runner with defaults."""
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            True,
            [{"story": "s", "passed": True}],
            0.1,
            "gpt-4",
        )
        result = runner.invoke(detect_change, ["--stories"], obj=mock_context_obj)

        assert result.exit_code == 0
        args, kwargs = mock_runner.call_args
        assert kwargs["prompts_dir"] is None
        assert kwargs["stories_dir"] is None
        assert kwargs["include_llm_prompts"] is False
        assert kwargs["fail_fast"] is True
        assert kwargs["cache_story_prompt_links"] is True


def test_detect_stories_options(runner, mock_context_obj):
    """Test 'detect --stories' forwards options."""
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (True, [], 0.0, "gpt-4")
        result = runner.invoke(
            detect_change,
            [
                "--stories",
                "--stories-dir",
                "stories",
                "--prompts-dir",
                "prompts",
                "--include-llm",
                "--no-fail-fast",
            ],
            obj=mock_context_obj,
        )

        assert result.exit_code == 0
        args, kwargs = mock_runner.call_args
        assert kwargs["prompts_dir"] == "prompts"
        assert kwargs["stories_dir"] == "stories"
        assert kwargs["include_llm_prompts"] is True
        assert kwargs["fail_fast"] is False
        assert kwargs["cache_story_prompt_links"] is True


def test_detect_stories_rejects_files(runner, mock_context_obj):
    """Test '--stories' mode rejects prompt/change positional arguments."""
    with runner.isolated_filesystem():
        with open("p1.prompt", "w") as f:
            f.write("content")
        with open("change.txt", "w") as f:
            f.write("change")
        result = runner.invoke(
            detect_change,
            ["--stories", "p1.prompt", "change.txt"],
            obj=mock_context_obj,
        )

    assert result.exit_code != 0
    assert "does not accept PROMPT_FILES/CHANGE_FILE arguments" in result.output


def test_detect_stories_rejects_output_option(runner, mock_context_obj):
    """Test '--stories' mode rejects detect CSV output flag."""
    result = runner.invoke(
        detect_change, ["--stories", "--output", "out.csv"], obj=mock_context_obj
    )

    assert result.exit_code != 0
    assert "--output is not supported with --stories" in result.output


def _failed_story_result():
    return [
        {
            "story": "/tmp/issue1872_stories/story__provider_queue_dashboard.md",
            "passed": False,
            "prompt_files": ["prompts/provider_queue_dashboard.prompt"],
            "changes_list": [{"change": "provider queue dashboard prompt drifted"}],
        },
        {
            "story": "/tmp/issue1872_stories/story__provider_subscription_queue.md",
            "passed": False,
            "prompt_files": ["prompts/provider_subscription_queue.prompt"],
            "changes_list": [{"change": "provider subscription queue prompt drifted"}],
        },
    ]


def test_issue_1872_reproduction_failed_story_exits_nonzero():
    """A story validation FAIL must make the top-level CLI fail."""
    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            False,
            _failed_story_result(),
            0.046212,
            "gemini/gemini-2.5-flash",
        )

        result = runner.invoke(
            pdd_cli,
            ["--no-core-dump", "detect", "--stories", "--no-fail-fast"],
        )

    assert result.exit_code == 1
    assert "gemini/gemini-2.5-flash" in result.output


def test_issue_1872_reproduction_fatal_story_exception_exits_nonzero():
    """Fatal provider/auth/LLM failures in story mode must fail the CLI."""
    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.side_effect = RuntimeError("provider auth failed")

        result = runner.invoke(pdd_cli, ["--no-core-dump", "detect", "--stories"])

    assert result.exit_code == 1
    assert "Error during 'detect' command" in result.output
    assert "provider auth failed" in result.output


def test_issue_1872_reproduction_passing_stories_exit_zero():
    """All-passing story validation remains a successful CLI run."""
    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            True,
            [
                {
                    "story": "/tmp/issue1872_stories/story__provider_availability_routing.md",
                    "passed": True,
                    "prompt_files": ["prompts/provider_availability_routing.prompt"],
                    "changes_list": [],
                }
            ],
            0.01,
            "gemini/gemini-2.5-flash",
        )

        result = runner.invoke(pdd_cli, ["--no-core-dump", "detect", "--stories"])

    assert result.exit_code == 0
    assert "gemini/gemini-2.5-flash" in result.output


def test_detect_stories_failed_result_direct_command_exits_nonzero(
    runner, mock_context_obj
):
    """The direct detect command should also signal failed story validation."""
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            False,
            _failed_story_result(),
            0.046212,
            "gemini/gemini-2.5-flash",
        )

        result = runner.invoke(
            detect_change,
            ["--stories", "--no-fail-fast"],
            obj=mock_context_obj,
        )

    assert result.exit_code == 1


def test_detect_stories_failed_result_top_level_exits_nonzero():
    """A mocked failed story result should fail through the registered CLI."""
    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            False,
            _failed_story_result(),
            0.046212,
            "gemini/gemini-2.5-flash",
        )

        result = runner.invoke(
            pdd_cli,
            ["--no-core-dump", "detect", "--stories", "--no-fail-fast"],
        )

    assert result.exit_code == 1


def test_detect_stories_passing_result_top_level_exits_zero():
    """Passing story mode remains successful through the registered CLI."""
    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            True,
            [{"story": "/tmp/issue1872_stories/story__ok.md", "passed": True}],
            0.01,
            "gemini/gemini-2.5-flash",
        )

        result = runner.invoke(pdd_cli, ["--no-core-dump", "detect", "--stories"])

    assert result.exit_code == 0


def test_detect_stories_fatal_exception_top_level_exits_nonzero():
    """Handled story-mode exceptions should still produce a failing process."""
    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.side_effect = RuntimeError("provider auth failed")

        result = runner.invoke(pdd_cli, ["--no-core-dump", "detect", "--stories"])

    assert result.exit_code == 1
    assert "provider auth failed" in result.output


def test_detect_stories_evidence_written_before_failed_story_exit(
    runner, mock_context_obj
):
    """Failed story runs should write evidence before exiting non-zero."""
    with (
        patch("pdd.commands.analysis.run_user_story_tests") as mock_runner,
        patch("pdd.commands.analysis.write_evidence_manifest") as mock_evidence,
    ):
        mock_runner.return_value = (
            False,
            _failed_story_result(),
            0.046212,
            "gemini/gemini-2.5-flash",
        )

        result = runner.invoke(
            detect_change,
            ["--stories", "--evidence"],
            obj=mock_context_obj,
        )

    mock_evidence.assert_called_once()
    assert mock_evidence.call_args.kwargs["command"] == "pdd detect --stories"
    assert mock_evidence.call_args.kwargs["validation"] == {"detect_stories": "failed"}
    assert result.exit_code == 1


def test_conflicts_handled_exception_top_level_exits_nonzero():
    """A representative handled-exception path should fail via result callback."""
    runner = CliRunner()
    with runner.isolated_filesystem():
        with open("p1.prompt", "w") as handle:
            handle.write("prompt 1")
        with open("p2.prompt", "w") as handle:
            handle.write("prompt 2")
        with patch("pdd.commands.analysis.conflicts_main") as mock_conflicts:
            mock_conflicts.side_effect = RuntimeError("conflicts provider failed")

            result = runner.invoke(
                pdd_cli,
                ["--no-core-dump", "conflicts", "p1.prompt", "p2.prompt"],
            )

    assert result.exit_code == 1
    assert "Error during 'conflicts' command" in result.output
    assert "conflicts provider failed" in result.output


def test_detect_help_and_output_behavior_describe_story_output_contract():
    """Runtime help and runtime rejection should agree on story output behavior."""
    runner = CliRunner()

    help_result = runner.invoke(pdd_cli, ["detect", "--help"])
    reject_result = runner.invoke(
        pdd_cli,
        ["--no-core-dump", "detect", "--stories", "--output", "out.csv"],
    )

    assert help_result.exit_code == 0
    assert "--output" in help_result.output
    assert "not supported with --stories" in help_result.output
    assert "--evidence" in help_result.output
    assert reject_result.exit_code != 0
    assert "--output is not supported with --stories" in reject_result.output


def _structured_story_scope(tmp_path):
    stories = tmp_path / "stories"
    prompts = tmp_path / "prompts"
    contracts = stories / "contracts"
    contracts.mkdir(parents=True)
    prompts.mkdir()
    story = stories / "story__ok.md"
    story.write_text(
        "<!-- pdd-story-prompts: prompts/a.prompt -->\n## Story\nOK", encoding="utf-8"
    )
    (contracts / "ok.contract.md").write_text("## Oracle\nOK", encoding="utf-8")
    (prompts / "a.prompt").write_text("prompt", encoding="utf-8")
    return stories, prompts, story


def _separate_stream_runner() -> CliRunner:
    """Return a runner with independent stderr across supported Click versions."""
    try:
        return CliRunner(mix_stderr=False)
    except TypeError:
        # Click 8.2+ removed the option and captures stderr separately by
        # default; retain compatibility with the older test runner as well.
        return CliRunner()


def test_detect_stories_json_stdout_is_single_versioned_document(tmp_path, monkeypatch):
    """Machine stdout MUST contain only the v1 document and imply safe policies."""
    stories, prompts, story = _structured_story_scope(tmp_path)
    monkeypatch.setenv("PDD_AUTO_UPDATE", "false")
    monkeypatch.delenv("PDD_FORCE", raising=False)
    monkeypatch.delenv("PDD_ALLOW_INTERACTIVE", raising=False)
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:

        def assert_noninteractive(**_kwargs):
            assert os.environ["PDD_FORCE"] == "1"
            assert os.environ["PDD_ALLOW_INTERACTIVE"] == "0"
            return (
                True,
                [{"story": str(story), "passed": True, "changes": []}],
                0.125,
                "model-safe",
            )

        mock_runner.side_effect = assert_noninteractive
        result = CliRunner().invoke(
            pdd_cli,
            [
                "--no-core-dump",
                "detect",
                "--stories",
                "--stories-dir",
                str(stories),
                "--prompts-dir",
                str(prompts),
                "--json",
            ],
        )

    assert result.exit_code == 0
    payload = json.loads(result.output)
    assert payload["schema_version"] == "pdd.detect.stories.v1"
    assert payload["outcome"] == "PASS"
    assert payload["all_pass"] is True
    assert payload["results"][0]["verdict"] == "PASS"
    assert payload["usage"]["cost_usd"] == "0.125"
    assert mock_runner.call_args.kwargs["cache_story_prompt_links"] is False
    assert mock_runner.call_args.kwargs["quiet"] is True
    assert "PDD_FORCE" not in os.environ
    assert "PDD_ALLOW_INTERACTIVE" not in os.environ


def test_structured_story_json_captures_evaluator_stdout(tmp_path):
    """Provider/Rich chatter must never prefix or corrupt machine JSON."""
    stories, prompts, story = _structured_story_scope(tmp_path)

    def noisy_runner(**_kwargs):
        print("provider secret diagnostic")
        print("provider stderr secret", file=sys.stderr)
        from rich import print as rich_print

        rich_print("provider rich secret")
        return (
            True,
            [{"story": str(story), "passed": True, "changes": []}],
            0.0,
            "model-safe",
        )

    with patch("pdd.commands.analysis.run_user_story_tests", side_effect=noisy_runner):
        result = _separate_stream_runner().invoke(
            detect_change,
            [
                "--stories",
                "--stories-dir",
                str(stories),
                "--prompts-dir",
                str(prompts),
                "--json",
            ],
            obj={},
        )

    assert result.exit_code == 0
    assert json.loads(result.stdout)["schema_version"] == "pdd.detect.stories.v1"
    assert "provider secret" not in result.stdout
    assert "provider secret" not in result.stderr
    assert "provider rich secret" not in result.stdout
    assert "provider rich secret" not in result.stderr
    assert "redirected to stderr" in result.stderr


def test_structured_story_json_mixed_capture_keeps_stdout_machine_safe(tmp_path):
    """Click's merged test stream must not turn the stderr marker into JSON text."""
    stories, prompts, story = _structured_story_scope(tmp_path)

    def noisy_runner(**_kwargs):
        print("provider diagnostic")
        return (
            True,
            [{"story": str(story), "passed": True, "changes": []}],
            0.0,
            "model-safe",
        )

    with patch("pdd.commands.analysis.run_user_story_tests", side_effect=noisy_runner):
        result = CliRunner().invoke(
            detect_change,
            [
                "--stories",
                "--stories-dir",
                str(stories),
                "--prompts-dir",
                str(prompts),
                "--json",
            ],
            obj={},
        )

    assert result.exit_code == 0
    assert json.loads(result.stdout)["schema_version"] == "pdd.detect.stories.v1"


def test_structured_story_json_restores_dynamic_rich_stream(tmp_path):
    """A machine invocation must not retain its transient CliRunner stream."""
    stories, prompts, story = _structured_story_scope(tmp_path)
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            True,
            [{"story": str(story), "passed": True, "changes": []}],
            0.0,
            "model-safe",
        )
        result = CliRunner().invoke(
            detect_change,
            [
                "--stories",
                "--stories-dir",
                str(stories),
                "--prompts-dir",
                str(prompts),
                "--json",
            ],
            obj={},
        )

    assert result.exit_code == 0

    from rich import get_console
    from pdd.core.errors import console as error_console

    assert get_console()._file is None
    assert error_console._file is None

    @click.command()
    def emit_rich_output():
        from rich import print as rich_print

        rich_print("after-machine-invocation")

    follow_up = CliRunner().invoke(emit_rich_output, [])
    assert follow_up.exit_code == 0
    assert "after-machine-invocation" in follow_up.output


def test_detect_stories_json_failure_is_complete_before_exit_one(tmp_path, monkeypatch):
    """A semantic FAIL MUST remain distinguishable from infrastructure failure."""
    stories, prompts, story = _structured_story_scope(tmp_path)
    monkeypatch.setenv("PDD_AUTO_UPDATE", "false")
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            False,
            [
                {
                    "story": str(story),
                    "passed": False,
                    "changes": [{"instruction": "tighten"}],
                }
            ],
            0.2,
            "model-safe",
        )
        result = CliRunner().invoke(
            detect_change,
            [
                "--stories",
                "--stories-dir",
                str(stories),
                "--prompts-dir",
                str(prompts),
                "--json",
            ],
            obj={"quiet": False},
        )

    assert result.exit_code == 1
    payload = json.loads(result.output)
    assert payload["outcome"] == "STORY_FAILURE"
    assert payload["results"][0]["changes"] == [{"instruction": "tighten"}]


def test_detect_stories_incomplete_scope_is_infrastructure_exit_three(tmp_path):
    stories, prompts, story = _structured_story_scope(tmp_path)
    second = stories / "story__second.md"
    second.write_text("## Story\nSecond", encoding="utf-8")
    (stories / "contracts" / "second.contract.md").write_text(
        "## Oracle\nSecond", encoding="utf-8"
    )
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            False,
            [{"story": str(story), "passed": False, "changes": []}],
            0.1,
            "model-safe",
        )
        result = CliRunner().invoke(
            detect_change,
            [
                "--stories",
                "--stories-dir",
                str(stories),
                "--prompts-dir",
                str(prompts),
                "--json",
            ],
            obj={},
        )
    assert result.exit_code == 3
    payload = json.loads(result.output)
    assert payload["outcome"] == "INCOMPLETE"
    assert payload["results"][1]["verdict"] == "UNKNOWN"


def test_detect_stories_json_provider_failure_is_structured_exit_three(tmp_path):
    stories, prompts, _story = _structured_story_scope(tmp_path)
    with patch(
        "pdd.commands.analysis.run_user_story_tests",
        side_effect=RuntimeError("secret token value"),
    ):
        result = CliRunner().invoke(
            detect_change,
            [
                "--stories",
                "--stories-dir",
                str(stories),
                "--prompts-dir",
                str(prompts),
                "--json",
            ],
            obj={},
        )
    assert result.exit_code == 3
    payload = json.loads(result.output)
    assert payload["outcome"] == "INFRASTRUCTURE_ERROR"
    assert payload["errors"][0]["code"] == "provider:UNAVAILABLE"
    assert "secret token value" not in result.output


def test_top_level_json_preserves_infrastructure_exit_three(tmp_path, monkeypatch):
    stories, prompts, _story = _structured_story_scope(tmp_path)
    monkeypatch.setenv("PDD_AUTO_UPDATE", "false")
    with patch(
        "pdd.commands.analysis.run_user_story_tests",
        side_effect=TimeoutError("provider secret timed out"),
    ):
        result = CliRunner().invoke(
            pdd_cli,
            [
                "--no-core-dump",
                "detect",
                "--stories",
                "--stories-dir",
                str(stories),
                "--prompts-dir",
                str(prompts),
                "--json",
            ],
        )
    assert result.exit_code == 3
    assert json.loads(result.output)["errors"][0]["code"] == "provider:TIMEOUT"
    assert "provider secret" not in result.output


def test_top_level_structured_json_suppresses_core_dump_without_flag(
    tmp_path, monkeypatch
):
    """The early machine-mode detector must protect stdout/core-dump paths."""
    stories, prompts, _story = _structured_story_scope(tmp_path)
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_AUTO_UPDATE", "false")
    with patch(
        "pdd.commands.analysis.run_user_story_tests",
        side_effect=RuntimeError("provider secret failure"),
    ):
        result = CliRunner().invoke(
            pdd_cli,
            [
                "detect",
                "--stories",
                "--stories-dir",
                str(stories),
                "--prompts-dir",
                str(prompts),
                "--json",
            ],
        )

    assert result.exit_code == 3
    assert json.loads(result.stdout)["outcome"] == "INFRASTRUCTURE_ERROR"
    assert "provider secret" not in result.stdout
    assert not (tmp_path / ".pdd" / "core_dumps").exists()


def test_detect_stories_json_empty_scope_is_config_exit_two(tmp_path):
    stories = tmp_path / "stories"
    prompts = tmp_path / "prompts"
    stories.mkdir()
    prompts.mkdir()
    result = CliRunner().invoke(
        detect_change,
        [
            "--stories",
            "--stories-dir",
            str(stories),
            "--prompts-dir",
            str(prompts),
            "--json",
        ],
        obj={},
    )
    assert result.exit_code == 2
    assert json.loads(result.output)["errors"][0]["code"] == "scope:EMPTY"


def test_detect_stories_json_output_is_atomic_and_silent(tmp_path):
    stories, prompts, story = _structured_story_scope(tmp_path)
    destination = tmp_path / "result.json"
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            True,
            [{"story": str(story), "passed": True, "changes": []}],
            0.0,
            "model-safe",
        )
        result = CliRunner().invoke(
            detect_change,
            [
                "--stories",
                "--stories-dir",
                str(stories),
                "--prompts-dir",
                str(prompts),
                "--json-output",
                str(destination),
            ],
            obj={},
        )
    assert result.exit_code == 0
    assert result.output == ""
    assert json.loads(destination.read_text(encoding="utf-8"))["all_pass"] is True


def test_structured_mode_must_not_enable_story_link_mutation(tmp_path):
    stories, prompts, _story = _structured_story_scope(tmp_path)
    result = CliRunner().invoke(
        detect_change,
        [
            "--stories",
            "--stories-dir",
            str(stories),
            "--prompts-dir",
            str(prompts),
            "--json",
            "--cache-story-links",
        ],
        obj={},
    )
    assert result.exit_code == 2
    assert "MUST use --read-only" in result.output


def test_structured_mode_rejects_story_symlink_escape(tmp_path):
    stories, prompts, _story = _structured_story_scope(tmp_path)
    outside = tmp_path / "outside-story.md"
    outside.write_text("## Story\noutside", encoding="utf-8")
    escaped = stories / "story__escaped.md"
    escaped.symlink_to(outside)
    result = CliRunner().invoke(
        detect_change,
        [
            "--stories",
            "--stories-dir",
            str(stories),
            "--prompts-dir",
            str(prompts),
            "--json",
        ],
        obj={},
    )
    assert result.exit_code == 2
    assert json.loads(result.output)["errors"][0]["code"] == "scope:PATH_ESCAPE"


def test_structured_mode_does_not_evaluate_prompt_symlink_outside_scope(tmp_path):
    stories, prompts, story = _structured_story_scope(tmp_path)
    outside = tmp_path / "outside.prompt"
    outside.write_text("outside", encoding="utf-8")
    escaped = prompts / "outside.prompt"
    escaped.symlink_to(outside)
    story.write_text(
        "<!-- pdd-story-prompts: prompts/outside.prompt -->\n## Story\nOK",
        encoding="utf-8",
    )
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            False,
            [{"story": str(story), "passed": False, "changes": []}],
            0.0,
            "model-safe",
        )
        result = CliRunner().invoke(
            detect_change,
            [
                "--stories",
                "--stories-dir",
                str(stories),
                "--prompts-dir",
                str(prompts),
                "--json",
            ],
            obj={},
        )
    assert result.exit_code == 3
    assert mock_runner.call_args.kwargs["prompt_files"] == [prompts / "a.prompt"]
    assert (
        json.loads(result.output)["results"][0]["errors"][0]["code"]
        == "prompt:OUTSIDE_SCOPE"
    )


def _write_scope_manifest(tmp_path, *, prompt_ref="prompts/a.prompt"):
    stories, prompts, story = _structured_story_scope(tmp_path)
    manifest = tmp_path / "scope.json"
    manifest.write_text(
        json.dumps(
            {
                "schema_version": "pdd.detect.stories.scope.v1",
                "stories": [
                    {
                        "story": "stories/story__ok.md",
                        "contract": "stories/contracts/ok.contract.md",
                        "prompts": [prompt_ref],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    return stories, prompts, story, manifest


def test_scope_manifest_preserves_exact_scope_and_rejects_discovery(tmp_path, monkeypatch):
    """Manifest mode passes only explicitly authorized files to the evaluator."""
    stories, prompts, story, manifest = _write_scope_manifest(tmp_path)
    (stories / "story__extra.md").write_text("## Story\nExtra", encoding="utf-8")
    (stories / "contracts" / "extra.contract.md").write_text(
        "## Oracle\nExtra", encoding="utf-8"
    )
    (prompts / "unrelated.prompt").write_text("unrelated", encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            True,
            [{"story": str(story), "passed": True, "changes": []}],
            0.0,
            "model-safe",
        )
        result = CliRunner().invoke(
            detect_change,
            ["--stories", "--scope-manifest", str(manifest), "--json"],
            obj={},
        )
    assert result.exit_code == 0
    assert mock_runner.call_args.kwargs["story_files"] == [story]
    assert mock_runner.call_args.kwargs["prompt_files"] == [prompts / "a.prompt"]
    payload = json.loads(result.output)
    assert payload["scope"]["stories"] == ["stories/story__ok.md"]
    assert payload["scope"]["prompts"] == ["prompts/a.prompt"]
    assert payload["scope"]["contracts"] == ["stories/contracts/ok.contract.md"]


def test_scope_manifest_allows_shared_prompt_across_distinct_stories(
    tmp_path, monkeypatch
):
    """One prompt may be authorized by multiple story contracts exactly once."""
    stories, prompts, story, manifest = _write_scope_manifest(tmp_path)
    second_story = stories / "story__second.md"
    second_contract = stories / "contracts" / "second.contract.md"
    second_story.write_text(
        "<!-- pdd-story-prompts: prompts/a.prompt -->\n## Story\nSecond",
        encoding="utf-8",
    )
    second_contract.write_text("## Oracle\nSecond", encoding="utf-8")
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["stories"].append(
        {
            "story": "stories/story__second.md",
            "contract": "stories/contracts/second.contract.md",
            "prompts": ["prompts/a.prompt"],
        }
    )
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            True,
            [
                {"story": str(story), "passed": True, "changes": []},
                {"story": str(second_story), "passed": True, "changes": []},
            ],
            0.0,
            "model-safe",
        )
        result = CliRunner().invoke(
            detect_change,
            ["--stories", "--scope-manifest", str(manifest), "--json"],
            obj={},
        )

    assert result.exit_code == 0
    assert mock_runner.call_args.kwargs["story_files"] == [story, second_story]
    assert mock_runner.call_args.kwargs["prompt_files"] == [prompts / "a.prompt"]
    assert mock_runner.call_args.kwargs["contract_files"] == {
        story: stories / "contracts" / "ok.contract.md",
        second_story: second_contract,
    }
    document = json.loads(result.output)
    assert document["scope"]["prompts"] == ["prompts/a.prompt"]


def test_source_cli_subprocess_emits_structured_story_results_without_mutation(
    tmp_path,
):
    """The source entrypoint preserves the structured story CLI boundary end to end."""
    stories, prompts, story, manifest = _write_scope_manifest(tmp_path)
    second_story = stories / "story__second.md"
    second_story.write_text(
        "<!-- pdd-story-prompts: prompts/a.prompt -->\n## Story\nSecond",
        encoding="utf-8",
    )
    second_contract = stories / "contracts" / "second.contract.md"
    second_contract.write_text("## Oracle\nSecond", encoding="utf-8")
    manifest_payload = json.loads(manifest.read_text(encoding="utf-8"))
    manifest_payload["stories"].append(
        {
            "story": "stories/story__second.md",
            "contract": "stories/contracts/second.contract.md",
            "prompts": ["prompts/a.prompt"],
        }
    )
    manifest.write_text(json.dumps(manifest_payload), encoding="utf-8")

    hooks = tmp_path / "hooks"
    hooks.mkdir()
    (hooks / "sitecustomize.py").write_text(
        """
import os

import pdd.commands.analysis as analysis


def _controlled_story_runner(*, story_files=None, **_kwargs):
    mode = os.environ["PDD_SUBPROCESS_STORY_MODE"]
    if mode == "provider":
        raise RuntimeError("provider credentials unavailable")
    passed = mode == "pass"
    return (
        passed,
        [{"story": str(path), "passed": passed, "changes": []}
         for path in story_files or []],
        0.0,
        "subprocess-model",
    )


analysis.run_user_story_tests = _controlled_story_runner
""".lstrip(),
        encoding="utf-8",
    )
    source_root = Path(__file__).resolve().parents[2]
    environment = os.environ.copy()
    environment["PYTHONPATH"] = os.pathsep.join([str(hooks), str(source_root)])
    environment["PDD_AUTO_UPDATE"] = "false"
    environment["PDD_FORCE_LOCAL"] = "1"
    environment["LITELLM_CACHE_DISABLE"] = "1"

    def invoke(mode, *extra):
        return subprocess.run(
            [
                sys.executable,
                "-m",
                "pdd.cli",
                "--no-core-dump",
                "detect",
                "--stories",
                "--scope-manifest",
                str(manifest),
                *extra,
            ],
            cwd=tmp_path,
            env={**environment, "PDD_SUBPROCESS_STORY_MODE": mode},
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )

    def project_bytes():
        return {
            path.relative_to(tmp_path): path.read_bytes()
            for path in tmp_path.rglob("*")
            if path.is_file() and hooks not in path.parents
        }

    before = project_bytes()
    passed = invoke("pass", "--json")
    assert passed.returncode == 0, passed.stderr
    passed_document = json.loads(passed.stdout)
    assert passed_document["outcome"] == "PASS"
    assert passed_document["scope"]["prompts"] == ["prompts/a.prompt"]
    assert len(passed_document["results"]) == 2
    assert project_bytes() == before

    failed = invoke("fail", "--json")
    assert failed.returncode == 1, failed.stderr
    failed_document = json.loads(failed.stdout)
    assert failed_document["outcome"] == "STORY_FAILURE"
    assert failed_document["all_pass"] is False
    unavailable = invoke("provider", "--json")
    assert unavailable.returncode == 3, unavailable.stderr
    unavailable_document = json.loads(unavailable.stdout)
    assert unavailable_document["outcome"] == "INFRASTRUCTURE_ERROR"
    assert unavailable_document["errors"][0]["code"] == (
        "auth:NON_INTERACTIVE_CREDENTIALS_MISSING"
    )

    output = tmp_path / "structured-result.json"
    output.write_text("previous partial content", encoding="utf-8")
    atomic = invoke("pass", "--json-output", str(output))
    assert atomic.returncode == 0, atomic.stderr
    assert atomic.stdout == ""
    assert json.loads(output.read_text(encoding="utf-8"))["outcome"] == "PASS"
    assert not list(tmp_path.glob(f".{output.name}.*"))


def test_scope_manifest_plain_mode_is_read_only_and_noninteractive(tmp_path, monkeypatch):
    stories, prompts, story, manifest = _write_scope_manifest(tmp_path)
    monkeypatch.chdir(tmp_path)
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            True,
            [{"story": str(story), "passed": True, "changes": []}],
            0.0,
            "model-safe",
        )
        result = CliRunner().invoke(
            detect_change,
            ["--stories", "--scope-manifest", str(manifest)],
            obj={},
        )
    assert result.exit_code == 0
    assert mock_runner.call_args.kwargs["cache_story_prompt_links"] is False


def test_scope_manifest_plain_mode_fails_closed_on_metadata_mismatch(tmp_path, monkeypatch):
    stories, prompts, story, manifest = _write_scope_manifest(tmp_path)
    story.write_text("## Story\nNo prompt metadata", encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            True,
            [{"story": str(story), "passed": True, "changes": []}],
            0.0,
            "model-safe",
        )
        result = CliRunner().invoke(
            detect_change,
            ["--stories", "--scope-manifest", str(manifest)],
            obj={},
        )
    assert result.exit_code == 3
    mock_runner.assert_not_called()


def test_scope_manifest_rejects_per_story_metadata_swap_before_dispatch(
    tmp_path, monkeypatch
):
    """A mismatched story must not spend budget evaluating another prompt."""
    stories, prompts, first_story, manifest = _write_scope_manifest(tmp_path)
    second_story = stories / "story__second.md"
    second_contract = stories / "contracts" / "second.contract.md"
    second_story.write_text(
        "<!-- pdd-story-prompts: prompts/b.prompt -->\n## Story\nSecond",
        encoding="utf-8",
    )
    second_contract.write_text("## Oracle\nSecond", encoding="utf-8")
    (prompts / "b.prompt").write_text("prompt b", encoding="utf-8")
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["stories"].append(
        {
            "story": "stories/story__second.md",
            "contract": "stories/contracts/second.contract.md",
            "prompts": ["prompts/b.prompt"],
        }
    )
    # The first story now names the second story's authorized prompt.  Before
    # the preflight guard, the evaluator received b.prompt for both stories
    # and only emitted MANIFEST_MISMATCH after those provider calls.
    first_story.write_text(
        "<!-- pdd-story-prompts: prompts/b.prompt -->\n## Story\nFirst",
        encoding="utf-8",
    )
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        result = CliRunner().invoke(
            detect_change,
            ["--stories", "--scope-manifest", str(manifest), "--json"],
            obj={},
        )

    assert result.exit_code == 3
    mock_runner.assert_not_called()
    document = json.loads(result.output)
    assert document["outcome"] == "INCOMPLETE"
    assert document["errors"][0]["code"] == "scope:MANIFEST_MISMATCH"


@pytest.mark.parametrize(
    ("field", "value", "error_code"),
    [
        ("story", "../outside.md", "scope:PATH_ESCAPE"),
        ("story", "/tmp/outside.md", "scope:PATH_ESCAPE"),
    ],
)
def test_scope_manifest_rejects_traversal_and_absolute_paths(
    tmp_path, monkeypatch, field, value, error_code
):
    _stories, _prompts, _story, manifest = _write_scope_manifest(tmp_path)
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["stories"][0][field] = value
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    result = CliRunner().invoke(
        detect_change,
        ["--stories", "--scope-manifest", str(manifest), "--json"],
        obj={},
    )
    assert result.exit_code == 2
    assert json.loads(result.output)["errors"][0]["code"] == error_code


def test_scope_manifest_rejects_duplicate_prompt_and_symlink_escape(tmp_path, monkeypatch):
    stories, prompts, _story, manifest = _write_scope_manifest(tmp_path)
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["stories"][0]["prompts"] = ["prompts/a.prompt", "prompts/a.prompt"]
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    duplicate = CliRunner().invoke(
        detect_change,
        ["--stories", "--scope-manifest", str(manifest), "--json"],
        obj={},
    )
    assert duplicate.exit_code == 2
    assert json.loads(duplicate.output)["errors"][0]["code"] == "scope:DUPLICATE_PROMPT"

    outside = tmp_path / "outside.prompt"
    outside.write_text("outside", encoding="utf-8")
    escaped = prompts / "escaped.prompt"
    escaped.symlink_to(outside)
    payload["stories"][0]["prompts"] = ["prompts/escaped.prompt"]
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    symlink = CliRunner().invoke(
        detect_change,
        ["--stories", "--scope-manifest", str(manifest), "--json"],
        obj={},
    )
    assert symlink.exit_code == 2
    assert json.loads(symlink.output)["errors"][0]["code"] == "scope:PATH_ESCAPE"

    alias = tmp_path / "alias"
    alias.symlink_to(stories, target_is_directory=True)
    payload["stories"][0]["prompts"] = ["prompts/a.prompt"]
    payload["stories"][0]["story"] = "alias/story__ok.md"
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    parent_symlink = CliRunner().invoke(
        detect_change,
        ["--stories", "--scope-manifest", str(manifest), "--json"],
        obj={},
    )
    assert parent_symlink.exit_code == 2
    assert (
        json.loads(parent_symlink.output)["errors"][0]["code"]
        == "scope:PATH_ESCAPE"
    )


def test_scope_manifest_rejects_unknown_fields(tmp_path, monkeypatch):
    _stories, _prompts, _story, manifest = _write_scope_manifest(tmp_path)
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["unexpected"] = True
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    result = CliRunner().invoke(
        detect_change,
        ["--stories", "--scope-manifest", str(manifest), "--json"],
        obj={},
    )
    assert result.exit_code == 2
    assert json.loads(result.output)["errors"][0]["code"] == "scope:MANIFEST_UNKNOWN_FIELD"

    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["stories"][0]["unexpected"] = True
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    entry_result = CliRunner().invoke(
        detect_change,
        ["--stories", "--scope-manifest", str(manifest), "--json"],
        obj={},
    )
    assert entry_result.exit_code == 2
    assert (
        json.loads(entry_result.output)["errors"][0]["code"]
        == "scope:MANIFEST_UNKNOWN_FIELD"
    )


def test_scope_manifest_rejects_duplicate_json_keys_and_empty_prompt_sets(
    tmp_path, monkeypatch
):
    _stories, _prompts, _story, manifest = _write_scope_manifest(tmp_path)
    manifest.write_text(
        '{"schema_version":"pdd.detect.stories.scope.v1",'
        '"schema_version":"pdd.detect.stories.scope.v1", "stories": []}',
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)
    duplicate = CliRunner().invoke(
        detect_change,
        ["--stories", "--scope-manifest", str(manifest), "--json"],
        obj={},
    )
    assert duplicate.exit_code == 2
    assert (
        json.loads(duplicate.output)["errors"][0]["code"]
        == "scope:MANIFEST_DUPLICATE_KEY"
    )

    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["stories"] = [
        {
            "story": "stories/story__ok.md",
            "contract": "stories/contracts/ok.contract.md",
            "prompts": [],
        }
    ]
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    empty = CliRunner().invoke(
        detect_change,
        ["--stories", "--scope-manifest", str(manifest), "--json"],
        obj={},
    )
    assert empty.exit_code == 2
    assert json.loads(empty.output)["errors"][0]["code"] == "scope:MANIFEST_PROMPTS"


def test_scope_manifest_custom_contract_is_used_by_evaluator(tmp_path, monkeypatch):
    """The manifest contract path must be the oracle passed to detection."""
    stories, prompts, story, manifest = _write_scope_manifest(tmp_path)
    custom_contract = tmp_path / "contracts" / "custom.contract.md"
    custom_contract.parent.mkdir()
    custom_contract.write_text("CUSTOM ACCEPTANCE", encoding="utf-8")
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["stories"][0]["contract"] = "contracts/custom.contract.md"
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    seen = {}

    def fake_detect(prompt_paths, oracle, strength, temperature, time, verbose):
        seen["oracle"] = oracle
        return [], 0.0, "model-safe"

    with patch("pdd.user_story_tests.detect_change", side_effect=fake_detect):
        result = run_user_story_tests(
            prompts_dir=str(tmp_path),
            stories_dir=str(tmp_path),
            story_files=[story],
            prompt_files=[prompts / "a.prompt"],
            contract_files={story.resolve(): custom_contract.resolve()},
            quiet=True,
        )
    assert result[0] is True
    assert "CUSTOM ACCEPTANCE" in seen["oracle"]


def test_scope_manifest_is_rejected_for_standard_detect_mode(tmp_path):
    manifest = tmp_path / "scope.json"
    manifest.write_text("{}", encoding="utf-8")
    prompt = tmp_path / "prompt.prompt"
    change = tmp_path / "change.py"
    prompt.write_text("prompt", encoding="utf-8")
    change.write_text("change", encoding="utf-8")
    result = CliRunner().invoke(
        detect_change,
        [str(prompt), str(change), "--scope-manifest", str(manifest)],
        obj={},
    )
    assert result.exit_code == 2
    assert "require --stories" in result.output


# -----------------------------------------------------------------------------
# Tests for 'conflicts' command
# -----------------------------------------------------------------------------


def test_conflicts_success(runner, mock_context_obj):
    """Test 'conflicts' command with valid arguments."""
    with patch("pdd.commands.analysis.conflicts_main") as mock_main:
        mock_main.return_value = ([], 0.0, "gpt-4")

        with runner.isolated_filesystem():
            with open("p1.prompt", "w") as f:
                f.write("c")
            with open("p2.prompt", "w") as f:
                f.write("c")

            result = runner.invoke(
                conflicts, ["p1.prompt", "p2.prompt"], obj=mock_context_obj
            )

            assert result.exit_code == 0
            mock_main.assert_called_once()
            assert mock_main.call_args[1]["prompt1"] == "p1.prompt"
            assert mock_main.call_args[1]["prompt2"] == "p2.prompt"


# -----------------------------------------------------------------------------
# Tests for 'bug' command
# -----------------------------------------------------------------------------


def test_bug_agentic_success(runner, mock_context_obj):
    """Test 'bug' command in default agentic mode."""
    with patch("pdd.commands.analysis.run_agentic_bug") as mock_agentic:
        # Mock return: success, message, cost, model, changed_files
        mock_agentic.return_value = (True, "Fixed", 0.5, "gpt-4", ["file.py"])

        result = runner.invoke(
            bug, ["https://github.com/issues/1"], obj=mock_context_obj
        )

        assert result.exit_code == 0
        mock_agentic.assert_called_once()
        assert mock_agentic.call_args[1]["issue_url"] == "https://github.com/issues/1"


def test_bug_agentic_failure_exit_code_1(runner, mock_context_obj):
    """Test 'bug' agentic mode exits with code 1 when workflow fails (issue #593).

    pdd bug must not exit 0 on failure so CI and 'pdd bug && pdd fix' can detect failure.
    The command signals failure via click.exceptions.Exit(1); CliRunner captures that as result.exit_code.
    """
    with patch("pdd.commands.analysis.run_agentic_bug") as mock_agentic:
        mock_agentic.return_value = (
            False,
            "Issue not found or API error: Failed to fetch issue: gh: Not Found (HTTP 404)",
            0.0,
            "",
            [],
        )

        result = runner.invoke(
            bug,
            ["https://github.com/promptdriven/pdd/issues/99999"],
            obj=mock_context_obj,
        )

        mock_agentic.assert_called_once()
        assert result.exit_code == 1


def test_bug_agentic_wrong_args(runner, mock_context_obj):
    """Test 'bug' agentic mode fails with wrong number of arguments."""
    result = runner.invoke(bug, ["arg1", "arg2"], obj=mock_context_obj)
    assert result.exit_code != 0
    assert "Agentic mode requires exactly one argument" in result.output


def test_bug_clean_restart_rejects_non_issue_url(runner, mock_context_obj):
    """--clean-restart should only run with a GitHub issue URL."""
    with patch("pdd.commands.analysis.run_agentic_bug") as mock_agentic:
        result = runner.invoke(
            bug,
            ["--clean-restart", "not-a-url"],
            obj=mock_context_obj,
        )

    assert result.exit_code == 2
    assert "--clean-restart can only be used" in result.output
    mock_agentic.assert_not_called()


def test_bug_manual_success(runner, mock_context_obj):
    """Test 'bug' command in manual mode."""
    with patch("pdd.commands.analysis.bug_main") as mock_main:
        mock_main.return_value = ("test code", 0.1, "gpt-4")

        with runner.isolated_filesystem():
            # Create 5 dummy files
            files = ["p.prompt", "c.py", "prog.py", "curr.txt", "des.txt"]
            for f in files:
                with open(f, "w") as fh:
                    fh.write("content")

            args = ["--manual"] + files + ["--language", "Python"]
            result = runner.invoke(bug, args, obj=mock_context_obj)

            assert result.exit_code == 0
            mock_main.assert_called_once()
            kwargs = mock_main.call_args[1]
            assert kwargs["prompt_file"] == "p.prompt"
            assert kwargs["code_file"] == "c.py"
            assert kwargs["program_file"] == "prog.py"
            assert kwargs["current_output"] == "curr.txt"
            assert kwargs["desired_output"] == "des.txt"
            assert kwargs["language"] == "Python"


def test_bug_manual_missing_file(runner, mock_context_obj):
    """Test 'bug' manual mode fails if a file does not exist."""
    with runner.isolated_filesystem():
        # Only create 4 files
        files = ["p.prompt", "c.py", "prog.py", "curr.txt"]
        for f in files:
            with open(f, "w") as fh:
                fh.write("content")

        # Pass a 5th non-existent file
        args = ["--manual"] + files + ["missing.txt"]
        result = runner.invoke(bug, args, obj=mock_context_obj)

        assert result.exit_code != 0
        assert "File does not exist" in result.output


def test_bug_manual_wrong_arg_count(runner, mock_context_obj):
    """Test 'bug' manual mode fails with wrong number of arguments."""
    with runner.isolated_filesystem():
        args = ["--manual", "f1"]
        result = runner.invoke(bug, args, obj=mock_context_obj)
        assert result.exit_code != 0
        assert "Manual mode requires 5 arguments" in result.output


# -----------------------------------------------------------------------------
# Tests for 'crash' command
# -----------------------------------------------------------------------------


def test_crash_success(runner, mock_context_obj):
    """Test 'crash' command with valid arguments."""
    with patch("pdd.commands.analysis.crash_main") as mock_main:
        # success, final_code, final_program, attempts, cost, model
        mock_main.return_value = (True, "code", "prog", 1, 0.1, "gpt-4")

        with runner.isolated_filesystem():
            files = ["p.prompt", "c.py", "prog.py", "err.log"]
            for f in files:
                with open(f, "w") as fh:
                    fh.write("content")

            args = files + ["--loop", "--budget", "10.0"]
            result = runner.invoke(crash, args, obj=mock_context_obj)

            assert result.exit_code == 0
            mock_main.assert_called_once()
            kwargs = mock_main.call_args[1]
            assert kwargs["prompt_file"] == "p.prompt"
            assert kwargs["error_file"] == "err.log"
            assert kwargs["loop"] is True
            assert kwargs["budget"] == 10.0


# -----------------------------------------------------------------------------
# Tests for 'trace' command
# -----------------------------------------------------------------------------


def test_trace_success(runner, mock_context_obj):
    """Test 'trace' command with valid arguments."""
    with patch("pdd.commands.analysis.trace_main") as mock_main:
        mock_main.return_value = (10, 0.05, "gpt-4")

        with runner.isolated_filesystem():
            with open("p.prompt", "w") as f:
                f.write("content")
            with open("c.py", "w") as f:
                f.write("content")

            result = runner.invoke(
                trace, ["p.prompt", "c.py", "15"], obj=mock_context_obj
            )

            assert result.exit_code == 0
            mock_main.assert_called_once()
            assert mock_main.call_args[1]["code_line"] == 15


# -----------------------------------------------------------------------------
# Tests for Error Handling
# -----------------------------------------------------------------------------


def test_generic_exception_handling(runner, mock_context_obj):
    """Test that exceptions are caught and passed to handle_error."""
    with (
        patch("pdd.commands.analysis.detect_change_main") as mock_main,
        patch("pdd.commands.analysis.handle_error") as mock_handle_error,
    ):
        # Simulate an unexpected error
        mock_main.side_effect = ValueError("Something went wrong")

        with runner.isolated_filesystem():
            with open("p1.prompt", "w") as f:
                f.write("c")
            with open("p2.prompt", "w") as f:
                f.write("c")
            with open("change.txt", "w") as f:
                f.write("c")

            result = runner.invoke(
                detect_change,
                ["p1.prompt", "p2.prompt", "change.txt"],
                obj=mock_context_obj,
            )

            assert result.exit_code == 0
            mock_handle_error.assert_called_once()
            assert isinstance(mock_handle_error.call_args[0][0], ValueError)
            assert mock_handle_error.call_args[0][1] == "detect"


# -----------------------------------------------------------------------------
# Additional Tests (Fixed to pass context object)
# -----------------------------------------------------------------------------


@patch("pdd.commands.analysis.detect_change_main")
def test_detect_change_success_v2(mock_main, runner, mock_context_obj):
    """Test that detect command parses arguments correctly and calls the main logic."""
    mock_main.return_value = (["result"], 0.5, "gpt-4")
    with runner.isolated_filesystem():
        with open("prompt1.txt", "w") as f:
            f.write("p1")
        with open("prompt2.txt", "w") as f:
            f.write("p2")
        with open("change.txt", "w") as f:
            f.write("change")
        result = runner.invoke(
            detect_change,
            ["prompt1.txt", "prompt2.txt", "change.txt", "--output", "out.csv"],
            obj=mock_context_obj,
        )
        assert result.exit_code == 0
        args, kwargs = mock_main.call_args
        assert kwargs["prompt_files"] == ["prompt1.txt", "prompt2.txt"]
        assert kwargs["change_file"] == "change.txt"
        assert kwargs["output"] == "out.csv"


def test_detect_change_not_enough_args_v2(runner, mock_context_obj):
    """Test that detect command fails if fewer than 2 files are provided."""
    with runner.isolated_filesystem():
        with open("file1.txt", "w") as f:
            f.write("content")
        result = runner.invoke(detect_change, ["file1.txt"], obj=mock_context_obj)
        assert result.exit_code != 0
        assert "Requires at least one PROMPT_FILE and one CHANGE_FILE" in result.output


@patch("pdd.commands.analysis.detect_change_main")
@patch("pdd.commands.analysis.handle_error")
def test_detect_change_exception_handling_v2(
    mock_handle_error, mock_main, runner, mock_context_obj
):
    """Test that generic exceptions are caught and handled."""
    mock_main.side_effect = Exception("Boom")
    with runner.isolated_filesystem():
        with open("p.txt", "w") as f:
            f.write("p")
        with open("c.txt", "w") as f:
            f.write("c")
        result = runner.invoke(detect_change, ["p.txt", "c.txt"], obj=mock_context_obj)
        assert mock_handle_error.called
        assert "Boom" in str(mock_handle_error.call_args[0][0])


@patch("pdd.commands.analysis.conflicts_main")
def test_conflicts_success_v2(mock_main, runner, mock_context_obj):
    """Test conflicts command success path."""
    mock_main.return_value = ([], 0.1, "gpt-4")
    with runner.isolated_filesystem():
        with open("p1.txt", "w") as f:
            f.write("content")
        with open("p2.txt", "w") as f:
            f.write("content")
        result = runner.invoke(
            conflicts, ["p1.txt", "p2.txt", "--output", "res.csv"], obj=mock_context_obj
        )
        assert result.exit_code == 0
        args, kwargs = mock_main.call_args
        assert kwargs["prompt1"] == "p1.txt"
        assert kwargs["prompt2"] == "p2.txt"
        assert kwargs["output"] == "res.csv"


@patch("pdd.commands.analysis.run_agentic_bug")
def test_bug_agentic_mode_v2(mock_agentic, runner, mock_context_obj):
    """Test bug command in default agentic mode (URL)."""
    mock_agentic.return_value = (True, "Fixed", 1.0, "gpt-4", [])
    result = runner.invoke(
        bug,
        [
            "https://github.com/user/repo/issues/1",
            "--timeout-adder",
            "5.0",
            "--no-github-state",
        ],
        obj=mock_context_obj,
    )
    assert result.exit_code == 0
    args, kwargs = mock_agentic.call_args
    assert kwargs["issue_url"] == "https://github.com/user/repo/issues/1"
    assert kwargs["timeout_adder"] == 5.0
    assert kwargs["use_github_state"] is False


@patch("pdd.commands.analysis.run_agentic_bug")
def test_bug_agentic_mode_failure(mock_agentic, runner, mock_context_obj):
    """Test bug command exits with 1 when agentic workflow fails (issue #593)."""
    mock_agentic.return_value = (False, "Workflow failed", 0.0, "", [])
    result = runner.invoke(
        bug, ["https://github.com/user/repo/issues/593"], obj=mock_context_obj
    )
    assert result.exit_code == 1


def test_bug_agentic_mode_missing_arg_v2(runner, mock_context_obj):
    """Test bug command fails in agentic mode without URL."""
    result = runner.invoke(bug, [], obj=mock_context_obj)
    assert result.exit_code != 0
    assert "Agentic mode requires exactly one argument" in result.output


@patch("pdd.commands.analysis.bug_main")
def test_bug_manual_mode_success_v2(mock_bug_main, runner, mock_context_obj):
    """Test bug command in manual mode with 5 files."""
    mock_bug_main.return_value = ("TestCode", 0.5, "gpt-4")
    with runner.isolated_filesystem():
        files = ["p.txt", "c.py", "prog.py", "curr.txt", "des.txt"]
        for f in files:
            with open(f, "w") as fh:
                fh.write("content")
        result = runner.invoke(
            bug, ["--manual", "--language", "Java"] + files, obj=mock_context_obj
        )
        assert result.exit_code == 0
        args, kwargs = mock_bug_main.call_args
        assert kwargs["prompt_file"] == "p.txt"
        assert kwargs["code_file"] == "c.py"
        assert kwargs["program_file"] == "prog.py"
        assert kwargs["current_output"] == "curr.txt"
        assert kwargs["desired_output"] == "des.txt"
        assert kwargs["language"] == "Java"


def test_bug_manual_mode_wrong_arg_count_v2(runner, mock_context_obj):
    """Test bug command manual mode fails with wrong number of args."""
    with runner.isolated_filesystem():
        with open("f1.txt", "w") as f:
            f.write("x")
        result = runner.invoke(bug, ["--manual", "f1.txt"], obj=mock_context_obj)
        assert result.exit_code != 0
        assert "Manual mode requires 5 arguments" in result.output


def test_bug_manual_mode_file_not_found_v2(runner, mock_context_obj):
    """Test bug command manual mode fails if files don't exist."""
    with runner.isolated_filesystem():
        result = runner.invoke(
            bug, ["--manual", "a", "b", "c", "d", "e"], obj=mock_context_obj
        )
        assert result.exit_code != 0
        assert "File does not exist" in result.output


@patch("pdd.commands.analysis.crash_main")
def test_crash_success_v2(mock_crash_main, runner, mock_context_obj):
    """Test crash command success path."""
    mock_crash_main.return_value = (True, "code", "prog", 2, 1.5, "gpt-4")
    with runner.isolated_filesystem():
        files = ["prompt.txt", "code.py", "prog.py", "err.txt"]
        for f in files:
            with open(f, "w") as fh:
                fh.write("x")
        result = runner.invoke(
            crash, files + ["--loop", "--max-attempts", "5"], obj=mock_context_obj
        )
        assert result.exit_code == 0
        args, kwargs = mock_crash_main.call_args
        assert kwargs["prompt_file"] == "prompt.txt"
        assert kwargs["code_file"] == "code.py"
        assert kwargs["program_file"] == "prog.py"
        assert kwargs["error_file"] == "err.txt"
        assert kwargs["loop"] is True
        assert kwargs["max_attempts"] == 5


@patch("pdd.commands.analysis.trace_main")
def test_trace_success_v2(mock_trace_main, runner, mock_context_obj):
    """Test trace command success path."""
    mock_trace_main.return_value = ("Line 10", 0.2, "gpt-4")
    with runner.isolated_filesystem():
        with open("p.txt", "w") as f:
            f.write("p")
        with open("c.py", "w") as f:
            f.write("c")
        result = runner.invoke(trace, ["p.txt", "c.py", "42"], obj=mock_context_obj)
        assert result.exit_code == 0
        args, kwargs = mock_trace_main.call_args
        assert kwargs["prompt_file"] == "p.txt"
        assert kwargs["code_file"] == "c.py"
        assert kwargs["code_line"] == 42


def test_trace_invalid_int_v2(runner, mock_context_obj):
    """Test trace command fails if line number is not an int."""
    with runner.isolated_filesystem():
        with open("p.txt", "w") as f:
            f.write("p")
        with open("c.py", "w") as f:
            f.write("c")
        result = runner.invoke(
            trace, ["p.txt", "c.py", "not-an-int"], obj=mock_context_obj
        )
        assert result.exit_code != 0
        assert "Invalid value for 'CODE_LINE'" in result.output


"""
Test Plan for pdd/commands/analysis.py

1.  **Scope**: This module implements CLI commands (`detect`, `conflicts`, `bug`, `crash`, `trace`) using the `click` library. It acts as an interface layer, parsing arguments, validating inputs, and dispatching execution to underlying logic functions (e.g., `detect_change_main`, `bug_main`).

2.  **Testing Strategy**:
    *   **Unit Tests**: The primary strategy. We will use `click.testing.CliRunner` to simulate CLI execution. This ensures that argument parsing, option handling, and custom validation logic (like the manual file checks in `bug`) work correctly.
    *   **Mocking**: We will mock the underlying "main" functions (e.g., `detect_change_main`) to isolate the CLI layer. We verify that these functions are called with the expected arguments.
    *   **Isolation**: Each test will run in an isolated filesystem (using `runner.isolated_filesystem()`) to handle file existence checks without polluting the real filesystem.

3.  **Z3 Formal Verification**:
    *   **Assessment**: The code primarily consists of imperative glue code, argument parsing, and function dispatch. It does not contain complex algorithmic logic, mathematical constraints, or state machine transitions that benefit significantly from SMT solving.
    *   **Decision**: Z3 is not applicable for this specific module. The logic is best verified through direct functional testing of the CLI interface.

4.  **Test Cases**:
    *   **`detect`**:
        *   Verify success with >= 2 files.
        *   Verify failure with < 2 files.
        *   Verify exception handling (generic exceptions caught and handled).
    *   **`conflicts`**:
        *   Verify success with 2 valid files.
    *   **`bug`**:
        *   **Agentic Mode**: Verify success with 1 URL argument. Verify failure with wrong arg count.
        *   **Manual Mode**: Verify success with 5 valid files. Verify failure with missing files or directories. Verify failure with wrong arg count.
    *   **`crash`**:
        *   Verify success with 4 valid files. Check parameter passing (loop, budget, etc.).
    *   **`trace`**:
        *   Verify success with valid files and line number.

"""

import os
import pytest
from unittest.mock import MagicMock, patch
from click.testing import CliRunner
from pdd.commands.analysis import detect_change, conflicts, bug, crash, trace

# -----------------------------------------------------------------------------
# Fixtures
# -----------------------------------------------------------------------------


@pytest.fixture
def runner():
    """Returns a Click CLI runner."""
    return CliRunner()


@pytest.fixture
def mock_context_obj():
    """Mock context object usually passed via click.obj."""
    return {"verbose": True, "quiet": False}


# -----------------------------------------------------------------------------
# Tests for 'detect' command
# -----------------------------------------------------------------------------


def test_detect_change_success(runner):
    """Test 'detect' command with valid arguments."""
    with runner.isolated_filesystem():
        # Setup
        with open("prompt1.txt", "w") as f:
            f.write("p1")
        with open("prompt2.txt", "w") as f:
            f.write("p2")
        with open("change.txt", "w") as f:
            f.write("change")

        # Mock the underlying main function
        with patch("pdd.commands.analysis.detect_change_main") as mock_main:
            mock_main.return_value = (["result"], 1.0, "gpt-4")

            result = runner.invoke(
                detect_change, ["prompt1.txt", "prompt2.txt", "change.txt"]
            )

            assert result.exit_code == 0
            mock_main.assert_called_once()

            # Verify args parsing: last file is change_file, rest are prompt_files
            call_kwargs = mock_main.call_args[1]
            assert call_kwargs["change_file"] == "change.txt"
            assert call_kwargs["prompt_files"] == ["prompt1.txt", "prompt2.txt"]


def test_detect_change_insufficient_args(runner):
    """Test 'detect' fails if fewer than 2 files are provided."""
    with runner.isolated_filesystem():
        with open("file1.txt", "w") as f:
            f.write("content")

        result = runner.invoke(detect_change, ["file1.txt"])

        assert result.exit_code != 0
        assert "Requires at least one PROMPT_FILE and one CHANGE_FILE" in result.output


def test_detect_change_exception_handling(runner):
    """Test that generic exceptions are handled via handle_error."""
    with runner.isolated_filesystem():
        with open("p.txt", "w") as f:
            f.write("p")
        with open("c.txt", "w") as f:
            f.write("c")

        with patch(
            "pdd.commands.analysis.detect_change_main", side_effect=ValueError("Boom")
        ):
            with patch("pdd.commands.analysis.handle_error") as mock_handle_error:
                result = runner.invoke(detect_change, ["p.txt", "c.txt"])

                # Should exit cleanly (return None) but handle_error should be called
                assert result.exit_code == 0
                mock_handle_error.assert_called_once()
                assert "Boom" in str(mock_handle_error.call_args[0][0])


# -----------------------------------------------------------------------------
# Tests for 'conflicts' command
# -----------------------------------------------------------------------------


def test_conflicts_success(runner):
    """Test 'conflicts' command with valid files."""
    with runner.isolated_filesystem():
        with open("p1.txt", "w") as f:
            f.write("content")
        with open("p2.txt", "w") as f:
            f.write("content")

        with patch("pdd.commands.analysis.conflicts_main") as mock_main:
            mock_main.return_value = ([], 0.5, "gpt-4")

            result = runner.invoke(
                conflicts, ["p1.txt", "p2.txt", "--output", "out.csv"]
            )

            assert result.exit_code == 0
            mock_main.assert_called_once()
            assert mock_main.call_args[1]["prompt1"] == "p1.txt"
            assert mock_main.call_args[1]["prompt2"] == "p2.txt"
            assert mock_main.call_args[1]["output"] == "out.csv"


# -----------------------------------------------------------------------------
# Tests for 'bug' command
# -----------------------------------------------------------------------------


def test_bug_agentic_mode_success(runner):
    """Test 'bug' in default agentic mode (URL argument)."""
    with patch("pdd.commands.analysis.run_agentic_bug") as mock_agentic:
        mock_agentic.return_value = (True, "Fixed", 1.0, "gpt-4", [])

        result = runner.invoke(
            bug, ["https://github.com/user/repo/issues/1", "--timeout-adder", "5.0"]
        )

        assert result.exit_code == 0
        mock_agentic.assert_called_once()
        assert (
            mock_agentic.call_args[1]["issue_url"]
            == "https://github.com/user/repo/issues/1"
        )
        assert mock_agentic.call_args[1]["timeout_adder"] == 5.0
        assert mock_agentic.call_args[1]["use_github_state"] is True


def test_bug_agentic_mode_no_github_state(runner):
    """Test 'bug' agentic mode with --no-github-state flag."""
    with patch("pdd.commands.analysis.run_agentic_bug") as mock_agentic:
        mock_agentic.return_value = (True, "Fixed", 1.0, "gpt-4", [])

        result = runner.invoke(bug, ["https://github.com/u/r/i/1", "--no-github-state"])

        assert result.exit_code == 0
        assert mock_agentic.call_args[1]["use_github_state"] is False


def test_bug_agentic_mode_clean_restart(runner):
    """Test 'bug' agentic mode forwards --clean-restart."""
    with patch("pdd.commands.analysis.run_agentic_bug") as mock_agentic:
        mock_agentic.return_value = (True, "Fixed", 1.0, "gpt-4", [])

        result = runner.invoke(
            bug, ["https://github.com/u/r/issues/1", "--clean-restart"]
        )

        assert result.exit_code == 0
        assert mock_agentic.call_args[1]["clean_restart"] is True


def test_bug_manual_mode_success(runner):
    """Test 'bug' in manual mode with 5 valid files."""
    with runner.isolated_filesystem():
        files = ["prompt.txt", "code.py", "prog.py", "curr.txt", "des.txt"]
        for f in files:
            with open(f, "w") as fh:
                fh.write("content")

        with patch("pdd.commands.analysis.bug_main") as mock_main:
            mock_main.return_value = ("TestCode", 1.0, "gpt-4")

            args = ["--manual"] + files + ["--language", "Java"]
            result = runner.invoke(bug, args)

            assert result.exit_code == 0
            mock_main.assert_called_once()
            kwargs = mock_main.call_args[1]
            assert kwargs["prompt_file"] == "prompt.txt"
            assert kwargs["code_file"] == "code.py"
            assert kwargs["language"] == "Java"


def test_bug_manual_mode_wrong_arg_count(runner):
    """Test 'bug --manual' fails if not exactly 5 arguments."""
    with runner.isolated_filesystem():
        result = runner.invoke(bug, ["--manual", "file1", "file2"])
        assert result.exit_code != 0
        assert "Manual mode requires 5 arguments" in result.output


def test_bug_manual_mode_file_not_found(runner):
    """Test 'bug --manual' fails if a file does not exist."""
    with runner.isolated_filesystem():
        # Create only 4 files
        files = ["f1", "f2", "f3", "f4"]
        for f in files:
            with open(f, "w") as fh:
                fh.write(".")

        # Pass 5 args, last one missing
        args = ["--manual"] + files + ["missing_file"]
        result = runner.invoke(bug, args)

        assert result.exit_code != 0
        assert "File does not exist: missing_file" in result.output


def test_bug_manual_mode_directory_error(runner):
    """Test 'bug --manual' fails if an argument is a directory."""
    with runner.isolated_filesystem():
        os.mkdir("mydir")
        files = ["f1", "f2", "f3", "f4"]
        for f in files:
            with open(f, "w") as fh:
                fh.write(".")

        args = ["--manual"] + files + ["mydir"]
        result = runner.invoke(bug, args)

        assert result.exit_code != 0
        assert "Path is a directory" in result.output


# -----------------------------------------------------------------------------
# Tests for 'crash' command
# -----------------------------------------------------------------------------


def test_crash_success(runner):
    """Test 'crash' command with valid arguments."""
    with runner.isolated_filesystem():
        files = ["prompt.txt", "code.py", "prog.py", "err.txt"]
        for f in files:
            with open(f, "w") as fh:
                fh.write(".")

        with patch("pdd.commands.analysis.crash_main") as mock_main:
            # success, final_code, final_program, attempts, total_cost, model_name
            mock_main.return_value = (True, "code", "prog", 2, 0.5, "gpt-4")

            result = runner.invoke(crash, files + ["--loop", "--max-attempts", "5"])

            assert result.exit_code == 0
            mock_main.assert_called_once()
            kwargs = mock_main.call_args[1]
            assert kwargs["prompt_file"] == "prompt.txt"
            assert kwargs["loop"] is True
            assert kwargs["max_attempts"] == 5


# -----------------------------------------------------------------------------
# Tests for 'trace' command
# -----------------------------------------------------------------------------


def test_trace_success(runner):
    """Test 'trace' command with valid arguments."""
    with runner.isolated_filesystem():
        with open("prompt.txt", "w") as f:
            f.write(".")
        with open("code.py", "w") as f:
            f.write(".")

        with patch("pdd.commands.analysis.trace_main") as mock_main:
            mock_main.return_value = ("Line 10", 0.1, "gpt-4")

            result = runner.invoke(trace, ["prompt.txt", "code.py", "42"])

            assert result.exit_code == 0
            mock_main.assert_called_once()
            kwargs = mock_main.call_args[1]
            assert kwargs["prompt_file"] == "prompt.txt"
            assert kwargs["code_line"] == 42
