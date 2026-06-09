"""
E2E & Integration tests for issue #1201.

Verifies that output paths configured in .pddrc (generate_output_path, test_output_path,
example_output_path) and overrides from architecture.json (filepath) are honored
consistently and symmetrically across Click CLI commands and sync orchestration.
"""

import json
import os
import click
import pytest
from pathlib import Path
from click.testing import CliRunner
from unittest.mock import patch, MagicMock

from pdd.commands.maintenance import sync
from pdd.sync_determine_operation import get_pdd_file_paths, SyncDecision


@pytest.fixture
def base_ctx_obj():
    """Standard ctx.obj dict for CLI tests."""
    return {
        "strength": 0.5,
        "temperature": 0.0,
        "time": 0.25,
        "verbose": False,
        "force": True,
        "quiet": False,
        "output_cost": None,
        "review_examples": False,
        "local": True,
        "context": None,
    }


def _make_cli(command, ctx_obj):
    """Build a throwaway Click group with the given command attached."""
    @click.group()
    @click.pass_context
    def cli(ctx):
        ctx.ensure_object(dict)
        ctx.obj = dict(ctx_obj)
    cli.add_command(command)
    return cli


class TestE2EIssue1201OutputPaths:
    """E2E/Integration: Verify output paths are consistently honored across pipeline layers."""

    @pytest.fixture
    def setup_project(self, tmp_path):
        """Creates a temporary project with consistent custom output paths configured."""
        # Create directories
        (tmp_path / "prompts").mkdir(parents=True, exist_ok=True)
        (tmp_path / "src_custom").mkdir(parents=True, exist_ok=True)
        (tmp_path / "tests_custom").mkdir(parents=True, exist_ok=True)
        (tmp_path / "examples_custom").mkdir(parents=True, exist_ok=True)

        # Write .pddrc
        pddrc = tmp_path / ".pddrc"
        pddrc.write_text("""version: "1.0"
contexts:
  default:
    paths: ["**"]
    defaults:
      prompts_dir: "prompts/"
      generate_output_path: "src_custom/"
      test_output_path: "tests_custom/"
      example_output_path: "examples_custom/"
      default_language: "python"
""")

        # Write architecture.json with custom filepath for module
        arch_json = tmp_path / "architecture.json"
        arch_json.write_text(json.dumps({
            "modules": [
                {
                    "filename": "custom_widget_python.prompt",
                    "filepath": "custom_widget.py"
                }
            ]
        }))

        # Create prompt file
        prompt_file = tmp_path / "prompts" / "custom_widget_python.prompt"
        prompt_file.write_text("Generate custom widget module")

        return tmp_path

    def test_e2e_cli_sync_resolves_and_passes_correct_paths(self, setup_project, base_ctx_obj, monkeypatch):
        """
        Verify that invoking 'pdd sync' command with CliRunner resolves correct dirs
        from .pddrc and passes them to the sync_orchestration layer.
        """
        monkeypatch.chdir(setup_project)
        runner = CliRunner()
        cli = _make_cli(sync, base_ctx_obj)

        mock_result = {"success": True, "total_cost": 0.1, "model_name": "gpt-4", "summary": "Sync OK."}

        with patch("pdd.sync_main.sync_orchestration", return_value=mock_result) as mock_sync_orch:
            result = runner.invoke(cli, ["sync", "custom_widget"], catch_exceptions=False)

            assert result.exit_code == 0
            mock_sync_orch.assert_called_once()
            kw = mock_sync_orch.call_args.kwargs

            # Check that code_dir, tests_dir, examples_dir resolved from .pddrc are passed correctly
            assert Path(kw["code_dir"]).resolve() == (setup_project / "src_custom").resolve()
            assert Path(kw["tests_dir"]).resolve() == (setup_project / "tests_custom").resolve()
            assert Path(kw["examples_dir"]).resolve() == (setup_project / "examples_custom").resolve()

    def test_e2e_path_resolution_symmetry_for_custom_widget(self, setup_project, monkeypatch):
        """
        Integration: Verify get_pdd_file_paths resolves symmetric and expected paths
        using BOTH .pddrc defaults and architecture.json overrides under the hood.
        """
        monkeypatch.chdir(setup_project)

        paths = get_pdd_file_paths(
            basename="custom_widget",
            language="python",
            prompts_dir="prompts"
        )

        code_path = paths["code"]
        test_path = paths["test"]
        example_path = paths["example"]

        # 1. Code path must honor the directory 'src_custom' from .pddrc AND
        #    preserve the file name 'custom_widget.py' from architecture.json.
        assert code_path.parent.name == "src_custom"
        assert code_path.name == "custom_widget.py"

        # 2. Test path must honor 'tests_custom' from .pddrc
        assert test_path.parent.name == "tests_custom"
        assert test_path.name == "test_custom_widget.py"

        # 3. Example path must honor 'examples_custom' from .pddrc
        assert example_path.parent.name == "examples_custom"
        assert example_path.name == "custom_widget_example.py"

    def test_e2e_sync_orchestration_path_flow(self, setup_project, monkeypatch):
        """
        Integration: Verify that sync_orchestration internal path resolution flow (when called
        directly) accesses the exact same resolved paths from the fix.
        """
        monkeypatch.chdir(setup_project)

        from pdd.sync_orchestration import sync_orchestration

        # We patch sync_determine_operation to return 'nothing', letting the sync worker
        # finish instantly and cleanly without any LLM interactions or lock/TUI issues,
        # but completely exercising the path resolution and initialization code of sync_orchestration.
        mock_decision = SyncDecision(operation='nothing', reason='Complete')

        with patch("pdd.sync_orchestration.sync_determine_operation", return_value=mock_decision), \
             patch("pdd.sync_orchestration.get_pdd_file_paths", wraps=get_pdd_file_paths) as mock_get_paths:

            # Execute sync_orchestration directly in quiet/headless mode
            result = sync_orchestration(
                basename="custom_widget",
                language="python",
                prompts_dir="prompts",
                quiet=True
            )

            # 1. Verify get_pdd_file_paths was indeed called and returned correct paths
            mock_get_paths.assert_called_once()

            # 2. Verify that sync_orchestration returned successfully
            assert result["success"] is True

            # 3. Verify final_state paths returned by sync_orchestration
            final_state = result["final_state"]
            code_path = Path(final_state["code"]["path"])
            test_path = Path(final_state["test"]["path"])
            example_path = Path(final_state["example"]["path"])

            # Code path honors .pddrc src_custom/ and architecture.json name
            assert code_path.parent.name == "src_custom"
            assert code_path.name == "custom_widget.py"

            # Test/example honor .pddrc subdirectories
            assert test_path.parent.name == "tests_custom"
            assert example_path.parent.name == "examples_custom"


class TestIssue551SyncOrchestratorCanonicalExtensions:
    """E2E regression tests for issue #551 (reopened): YAML/Markdown sync paths use canonical extensions.

    The bug: `get_pdd_file_paths` in `sync_determine_operation.py` used a local `get_extension`
    helper that returned raw language names (``yaml``, ``markdown``) instead of canonical
    CSV-backed extensions (``.yml``, ``.md``).  Because `sync_orchestration` exposes those paths
    in ``final_state`` and sync decision logic checks those exact paths for existence,
    canonical artifacts were treated as missing — triggering an indefinite regeneration loop.

    The fix (commit 89a2eba) updated `get_extension` to perform a CSV lookup first so
    YAML → ``.yml`` and Markdown → ``.md``.

    These tests verify that the fix holds end-to-end through the sync orchestration layer.
    """

    @pytest.fixture
    def yaml_project(self, tmp_path):
        """Minimal YAML project: architecture.json says ci.yml, prompt file present."""
        (tmp_path / "prompts").mkdir()
        (tmp_path / "examples").mkdir()
        (tmp_path / "tests").mkdir()
        (tmp_path / "architecture.json").write_text(json.dumps({
            "modules": [{"filename": "ci_YAML.prompt", "filepath": "ci.yml"}]
        }))
        (tmp_path / "prompts" / "ci_YAML.prompt").write_text("Generate CI workflow.\n")
        return tmp_path

    @pytest.fixture
    def markdown_project(self, tmp_path):
        """Minimal Markdown project: architecture.json says manifest.md, prompt file present."""
        (tmp_path / "prompts").mkdir()
        (tmp_path / "examples").mkdir()
        (tmp_path / "tests").mkdir()
        (tmp_path / "architecture.json").write_text(json.dumps({
            "modules": [{"filename": "manifest_Markdown.prompt", "filepath": "manifest.md"}]
        }))
        (tmp_path / "prompts" / "manifest_Markdown.prompt").write_text("Generate manifest.\n")
        return tmp_path

    def test_sync_orchestration_yaml_final_state_uses_yml_extension(self, yaml_project, monkeypatch):
        """
        sync_orchestration for a YAML module must expose ``.yml`` paths in final_state.

        Before the fix get_extension('YAML') returned 'yaml', so final_state exposed
        ``.yaml`` paths even though the actual code file was ``.yml``.
        """
        monkeypatch.chdir(yaml_project)
        from pdd.sync_orchestration import sync_orchestration

        mock_decision = SyncDecision(operation="nothing", reason="all synced")
        with patch("pdd.sync_orchestration.sync_determine_operation", return_value=mock_decision), \
             patch("pdd.sync_orchestration.get_pdd_file_paths", wraps=get_pdd_file_paths) as mock_paths:
            result = sync_orchestration(
                basename="ci",
                language="YAML",
                prompts_dir="prompts",
                quiet=True,
            )

        assert result["success"] is True
        mock_paths.assert_called()

        final = result["final_state"]
        example_path = Path(final["example"]["path"])
        test_path = Path(final["test"]["path"])

        assert example_path.suffix == ".yml", (
            f"Bug #551: sync_orchestration final_state example path uses "
            f"{example_path.suffix!r} instead of canonical '.yml'. "
            f"Full path: {example_path}"
        )
        assert test_path.suffix == ".yml", (
            f"Bug #551: sync_orchestration final_state test path uses "
            f"{test_path.suffix!r} instead of canonical '.yml'. "
            f"Full path: {test_path}"
        )
        assert example_path.name == "ci_example.yml"
        assert test_path.name == "test_ci.yml"

    def test_sync_orchestration_markdown_final_state_uses_md_extension(self, markdown_project, monkeypatch):
        """
        sync_orchestration for a Markdown module must expose ``.md`` paths in final_state,
        not ``.markdown``.
        """
        monkeypatch.chdir(markdown_project)
        from pdd.sync_orchestration import sync_orchestration

        mock_decision = SyncDecision(operation="nothing", reason="all synced")
        with patch("pdd.sync_orchestration.sync_determine_operation", return_value=mock_decision), \
             patch("pdd.sync_orchestration.get_pdd_file_paths", wraps=get_pdd_file_paths) as mock_paths:
            result = sync_orchestration(
                basename="manifest",
                language="Markdown",
                prompts_dir="prompts",
                quiet=True,
            )

        assert result["success"] is True
        mock_paths.assert_called()

        final = result["final_state"]
        example_path = Path(final["example"]["path"])
        test_path = Path(final["test"]["path"])

        assert example_path.suffix == ".md", (
            f"Bug #551: sync_orchestration final_state example path uses "
            f"{example_path.suffix!r} instead of canonical '.md'. "
            f"Full path: {example_path}"
        )
        assert test_path.suffix == ".md", (
            f"Bug #551: sync_orchestration final_state test path uses "
            f"{test_path.suffix!r} instead of canonical '.md'. "
            f"Full path: {test_path}"
        )
        assert example_path.name == "manifest_example.md"
        assert test_path.name == "test_manifest.md"

    def test_yaml_canonical_artifacts_prevent_regeneration_loop(self, tmp_path, monkeypatch):
        """
        Regression: when ci_example.yml and test_ci.yml already exist and are current,
        sync must recognize them (operation='nothing') rather than treating them as missing.

        Bug #551 caused get_pdd_file_paths to return ``.yaml`` paths while the canonical
        artifacts were ``.yml``, so the example/test were always seen as missing and sync
        re-generated them indefinitely.
        """
        monkeypatch.chdir(tmp_path)
        (tmp_path / "prompts").mkdir()
        (tmp_path / "examples").mkdir()
        (tmp_path / "tests").mkdir()
        (tmp_path / "architecture.json").write_text(json.dumps({
            "modules": [{"filename": "ci_YAML.prompt", "filepath": "ci.yml"}]
        }))
        (tmp_path / "prompts" / "ci_YAML.prompt").write_text("Generate CI workflow.\n")
        (tmp_path / "ci.yml").write_text("name: ci\non: push\njobs: {}\n")
        (tmp_path / "examples" / "ci_example.yml").write_text("name: ci-example\n")
        (tmp_path / "tests" / "test_ci.yml").write_text("name: ci-test\n")

        paths = get_pdd_file_paths("ci", "YAML", "prompts")

        assert paths["example"].suffix == ".yml", (
            f"Bug #551: get_pdd_file_paths returned example path with suffix "
            f"{paths['example'].suffix!r} instead of '.yml'. "
            "The pre-existing ci_example.yml would be treated as missing."
        )
        assert paths["test"].suffix == ".yml", (
            f"Bug #551: get_pdd_file_paths returned test path with suffix "
            f"{paths['test'].suffix!r} instead of '.yml'. "
            "The pre-existing test_ci.yml would be treated as missing."
        )
        assert paths["example"].exists(), (
            f"Canonical example file {paths['example']} should exist — "
            "if get_pdd_file_paths returns a .yaml path instead, it will be treated "
            "as missing and trigger an infinite re-generation loop."
        )
        assert paths["test"].exists(), (
            f"Canonical test file {paths['test']} should exist — "
            "if get_pdd_file_paths returns a .yaml path instead, it will be treated "
            "as missing and trigger an infinite re-generation loop."
        )

    def test_cli_sync_yaml_resolves_to_orchestration_with_yaml_language(
        self, yaml_project, base_ctx_obj, monkeypatch
    ):
        """
        CLI smoke-test: ``pdd sync ci --language YAML`` reaches sync_orchestration
        with language='YAML' so that path derivation uses the canonical extension.
        """
        monkeypatch.chdir(yaml_project)
        runner = CliRunner()
        cli = _make_cli(sync, base_ctx_obj)

        captured: dict = {}

        def _capturing_orchestration(**kwargs):
            captured.update(kwargs)
            return {
                "success": True,
                "total_cost": 0.0,
                "model_name": "stub",
                "summary": "OK",
            }

        with patch("pdd.sync_main.sync_orchestration", side_effect=_capturing_orchestration):
            result = runner.invoke(cli, ["sync", "ci"], catch_exceptions=False)

        assert result.exit_code == 0, f"CLI exited {result.exit_code}:\n{result.output}"
        assert captured.get("language", "").lower() == "yaml", (
            f"sync_orchestration received language={captured.get('language')!r}, expected 'yaml' (YAML)"
        )
