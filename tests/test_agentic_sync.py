"""Tests for pdd.agentic_sync module."""
from __future__ import annotations

import json
import os
import tempfile
from pathlib import Path
from typing import Any, Dict, List
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_sync import (
    _apply_architecture_corrections,
    _detect_modules_from_branch_diff,
    _filter_already_synced,
    _find_project_root,
    _is_catchall_match,
    _is_github_issue_url,
    _llm_fix_dry_run_failure,
    _load_architecture_json,
    _parse_llm_response,
    _resolve_module_cwd,
    _run_dry_run_validation,
    _run_single_dry_run,
    run_agentic_sync,
)
from pdd.agentic_sync_runner import build_dep_graph_from_architecture


# ---------------------------------------------------------------------------
# _is_github_issue_url
# ---------------------------------------------------------------------------

class TestIsGithubIssueUrl:
    def test_full_https_url(self):
        assert _is_github_issue_url("https://github.com/owner/repo/issues/123")

    def test_url_without_scheme(self):
        assert _is_github_issue_url("github.com/owner/repo/issues/42")

    def test_www_prefix(self):
        assert _is_github_issue_url("https://www.github.com/owner/repo/issues/1")

    def test_not_a_url(self):
        assert not _is_github_issue_url("my_module")

    def test_github_pr_not_issue(self):
        assert not _is_github_issue_url("https://github.com/owner/repo/pull/123")

    def test_partial_url(self):
        assert not _is_github_issue_url("github.com/owner/repo")

    def test_empty_string(self):
        assert not _is_github_issue_url("")


# ---------------------------------------------------------------------------
# _parse_llm_response
# ---------------------------------------------------------------------------

class TestParseLlmResponse:
    def test_basic_modules_and_valid_deps(self):
        response = (
            'MODULES_TO_SYNC: ["llm_invoke", "sync_main"]\n\n'
            "DEPS_VALID: true\n"
        )
        modules, valid, corrections = _parse_llm_response(response)
        assert modules == ["llm_invoke", "sync_main"]
        assert valid is True
        assert corrections == []

    def test_modules_with_single_quotes(self):
        response = "MODULES_TO_SYNC: ['foo', 'bar']\n\nDEPS_VALID: true\n"
        modules, valid, _ = _parse_llm_response(response)
        assert modules == ["foo", "bar"]
        assert valid is True

    def test_deps_invalid_with_corrections(self):
        response = (
            'MODULES_TO_SYNC: ["api_orders"]\n\n'
            "DEPS_VALID: false\n\n"
            "DEPS_CORRECTIONS:\n"
            '[{"filename": "api_orders_Python.prompt", '
            '"dependencies": ["models_Python.prompt"]}]\n'
        )
        modules, valid, corrections = _parse_llm_response(response)
        assert modules == ["api_orders"]
        assert valid is False
        assert len(corrections) == 1
        assert corrections[0]["filename"] == "api_orders_Python.prompt"

    def test_no_modules_found(self):
        response = "I could not identify any modules.\nDEPS_VALID: true\n"
        modules, valid, _ = _parse_llm_response(response)
        assert modules == []
        assert valid is True

    def test_malformed_corrections_json(self):
        response = (
            'MODULES_TO_SYNC: ["foo"]\n'
            "DEPS_VALID: false\n"
            "DEPS_CORRECTIONS:\n"
            "not valid json\n"
        )
        modules, valid, corrections = _parse_llm_response(response)
        assert modules == ["foo"]
        assert valid is False
        assert corrections == []

    def test_deps_valid_case_insensitive(self):
        response = 'MODULES_TO_SYNC: ["a"]\nDEPS_VALID: True\n'
        _, valid, _ = _parse_llm_response(response)
        assert valid is True

        response2 = 'MODULES_TO_SYNC: ["a"]\nDEPS_VALID: FALSE\n'
        _, valid2, _ = _parse_llm_response(response2)
        assert valid2 is False


# ---------------------------------------------------------------------------
# _apply_architecture_corrections
# ---------------------------------------------------------------------------

class TestApplyArchitectureCorrections:
    def test_applies_corrections(self, tmp_path):
        arch_path = tmp_path / "architecture.json"
        architecture = [
            {"filename": "foo_python.prompt", "dependencies": ["bar_python.prompt"]},
            {"filename": "bar_python.prompt", "dependencies": []},
        ]
        arch_path.write_text(json.dumps(architecture))

        corrections = [
            {"filename": "foo_python.prompt", "dependencies": ["bar_python.prompt", "baz_python.prompt"]},
        ]

        result = _apply_architecture_corrections(arch_path, architecture, corrections, quiet=True)
        assert result[0]["dependencies"] == ["bar_python.prompt", "baz_python.prompt"]

        # Verify file was written
        saved = json.loads(arch_path.read_text())
        assert saved[0]["dependencies"] == ["bar_python.prompt", "baz_python.prompt"]

    def test_skips_unknown_filenames(self, tmp_path):
        arch_path = tmp_path / "architecture.json"
        architecture = [{"filename": "foo_python.prompt", "dependencies": []}]
        arch_path.write_text(json.dumps(architecture))

        corrections = [
            {"filename": "nonexistent_python.prompt", "dependencies": ["x_python.prompt"]},
        ]

        result = _apply_architecture_corrections(arch_path, architecture, corrections, quiet=True)
        assert result[0]["dependencies"] == []


# ---------------------------------------------------------------------------
# build_dep_graph_from_architecture
# ---------------------------------------------------------------------------

class TestBuildDepGraphFromArchitecture:
    def test_basic_graph(self, tmp_path):
        arch = [
            {"filename": "api_python.prompt", "dependencies": ["models_python.prompt"]},
            {"filename": "models_python.prompt", "dependencies": []},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))

        graph = build_dep_graph_from_architecture(arch_path, ["api", "models"])
        assert graph["api"] == ["models"]
        assert graph["models"] == []

    def test_filters_to_target_basenames(self, tmp_path):
        arch = [
            {"filename": "api_python.prompt", "dependencies": ["models_python.prompt", "utils_python.prompt"]},
            {"filename": "models_python.prompt", "dependencies": []},
            {"filename": "utils_python.prompt", "dependencies": []},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))

        # Only targeting api and models, not utils
        graph = build_dep_graph_from_architecture(arch_path, ["api", "models"])
        assert "models" in graph["api"]
        assert "utils" not in graph.get("api", [])

    def test_missing_file_returns_empty_deps(self, tmp_path):
        arch_path = tmp_path / "architecture.json"
        # File doesn't exist
        graph = build_dep_graph_from_architecture(arch_path, ["foo", "bar"])
        assert graph == {"foo": [], "bar": []}

    def test_self_dependency_excluded(self, tmp_path):
        arch = [
            {"filename": "foo_python.prompt", "dependencies": ["foo_python.prompt"]},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))

        graph = build_dep_graph_from_architecture(arch_path, ["foo"])
        assert graph["foo"] == []


# ---------------------------------------------------------------------------
# _load_architecture_json
# ---------------------------------------------------------------------------

class TestLoadArchitectureJson:
    def test_loads_valid_file(self, tmp_path):
        data = [{"filename": "test_python.prompt", "dependencies": []}]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(data))

        result, path = _load_architecture_json(tmp_path)
        assert result is not None
        assert len(result) == 1
        assert path == arch_path

    def test_returns_none_for_missing(self, tmp_path):
        result, path = _load_architecture_json(tmp_path)
        assert result is None

    def test_returns_none_for_invalid_json(self, tmp_path):
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text("not json")

        result, _ = _load_architecture_json(tmp_path)
        assert result is None

    def test_returns_none_for_non_list(self, tmp_path):
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text('{"key": "value"}')

        result, _ = _load_architecture_json(tmp_path)
        assert result is None


# ---------------------------------------------------------------------------
# _find_project_root
# ---------------------------------------------------------------------------

class TestFindProjectRoot:
    def test_finds_git_root(self, tmp_path):
        (tmp_path / ".git").mkdir()
        sub = tmp_path / "a" / "b"
        sub.mkdir(parents=True)

        root = _find_project_root(sub)
        assert root == tmp_path

    def test_finds_pddrc_root(self, tmp_path):
        (tmp_path / ".pddrc").touch()
        sub = tmp_path / "deep" / "nested"
        sub.mkdir(parents=True)

        root = _find_project_root(sub)
        assert root == tmp_path

    def test_returns_start_if_no_markers(self, tmp_path):
        sub = tmp_path / "orphan"
        sub.mkdir()
        root = _find_project_root(sub)
        assert root == sub


# ---------------------------------------------------------------------------
# run_agentic_sync integration (mocked)
# ---------------------------------------------------------------------------

class TestRunAgenticSync:
    @patch("pdd.agentic_sync._check_gh_cli", return_value=False)
    def test_fails_without_gh_cli(self, mock_gh):
        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True
        )
        assert not success
        assert "gh" in msg.lower()

    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_fails_with_invalid_url(self, mock_gh):
        success, msg, cost, model = run_agentic_sync(
            "not-a-url", quiet=True
        )
        assert not success
        assert "Invalid" in msg

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch("pdd.agentic_sync.build_dep_graph_from_architecture", return_value={"foo": []})
    @patch("pdd.agentic_sync.load_prompt_template", return_value="template {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_full_flow_success(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        mock_load_prompt,
        mock_build_graph,
        mock_dry_run,
        mock_branch_diff,
        mock_runner_cls,
    ):
        # Setup mocks
        issue_data = {"title": "Test", "body": "Fix foo", "comments_url": ""}
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (
            [{"filename": "foo_python.prompt", "dependencies": []}],
            Path("/tmp/architecture.json"),
        )
        mock_agentic_task.return_value = (
            True,
            'MODULES_TO_SYNC: ["foo"]\nDEPS_VALID: true',
            0.05,
            "anthropic",
        )
        mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, [], 0.0)

        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 1 modules synced successfully", 0.10)
        mock_runner_cls.return_value = mock_runner

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        assert success
        assert cost == pytest.approx(0.15)
        assert model == "anthropic"
        mock_runner.run.assert_called_once()

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch("pdd.agentic_sync.build_dep_graph_from_architecture")
    @patch("pdd.agentic_sync.load_prompt_template", return_value="template {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_strips_language_suffix_from_llm_basenames(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        mock_load_prompt,
        mock_build_graph,
        mock_dry_run,
        mock_branch_diff,
        mock_runner_cls,
    ):
        """LLM returns basenames with language suffix; they should be stripped."""
        issue_data = {"title": "Test", "body": "Fix models", "comments_url": ""}
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (
            [
                {"filename": "crm_models_Python.prompt", "dependencies": []},
                {"filename": "api_orders_Python.prompt", "dependencies": ["crm_models_Python.prompt"]},
            ],
            Path("/tmp/architecture.json"),
        )
        # LLM returns basenames WITH language suffixes (as found in architecture.json filenames)
        mock_agentic_task.return_value = (
            True,
            'MODULES_TO_SYNC: ["crm_models_Python", "api_orders_Python"]\nDEPS_VALID: true',
            0.05,
            "anthropic",
        )
        mock_build_graph.return_value = {"crm_models": ["api_orders"], "api_orders": []}
        mock_dry_run.return_value = (True, {"crm_models": Path("/tmp"), "api_orders": Path("/tmp")}, [], 0.0)

        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 2 modules synced successfully", 0.20)
        mock_runner_cls.return_value = mock_runner

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        assert success
        # Verify stripped basenames were passed to build_dep_graph_from_architecture
        call_args = mock_build_graph.call_args
        assert sorted(call_args[0][1]) == ["api_orders", "crm_models"]
        # Verify stripped basenames were passed to AsyncSyncRunner
        runner_kwargs = mock_runner_cls.call_args[1]
        assert sorted(runner_kwargs["basenames"]) == ["api_orders", "crm_models"]


# ---------------------------------------------------------------------------
# _resolve_module_cwd
# ---------------------------------------------------------------------------

class TestResolveModuleCwd:
    def _write_pddrc(self, path: Path, contexts: Dict[str, Any]) -> None:
        """Helper to write a .pddrc file."""
        import yaml
        config = {"contexts": contexts}
        path.write_text(yaml.dump(config))

    def test_module_found_in_root_pddrc(self, tmp_path):
        """Module matched by root .pddrc returns project root."""
        self._write_pddrc(tmp_path / ".pddrc", {
            "myctx": {
                "defaults": {"prompts_dir": "prompts/mymod"},
                "paths": ["src/mymod/**"],
            },
        })
        result = _resolve_module_cwd("mymod/widget", tmp_path)
        assert result == tmp_path

    def test_module_found_in_subdirectory_pddrc(self, tmp_path):
        """Module found in subdirectory .pddrc returns that subdirectory."""
        # No root .pddrc — so subdirectory scanning is used
        # Subdirectory has a matching context
        sub = tmp_path / "examples" / "hello"
        sub.mkdir(parents=True)
        self._write_pddrc(sub / ".pddrc", {
            "hello_ctx": {
                "defaults": {"prompts_dir": "prompts/greeting"},
                "paths": ["src/**"],
            },
        })
        result = _resolve_module_cwd("greeting/hi", tmp_path)
        assert result == sub

    def test_module_not_found_falls_back_to_root(self, tmp_path):
        """Module not in any .pddrc falls back to project root."""
        self._write_pddrc(tmp_path / ".pddrc", {
            "other": {
                "defaults": {"prompts_dir": "prompts/other"},
                "paths": ["src/other/**"],
            },
        })
        result = _resolve_module_cwd("nonexistent_mod", tmp_path)
        assert result == tmp_path

    def test_no_pddrc_falls_back_to_root(self, tmp_path):
        """No .pddrc files at all returns project root."""
        result = _resolve_module_cwd("anything", tmp_path)
        assert result == tmp_path

    def test_deepest_match_wins(self, tmp_path):
        """When multiple subdirs match, the deepest one wins."""
        # Depth 1 match
        sub1 = tmp_path / "level1"
        sub1.mkdir()
        self._write_pddrc(sub1 / ".pddrc", {
            "ctx1": {
                "defaults": {"prompts_dir": "prompts/shared"},
                "paths": ["src/**"],
            },
        })
        # Depth 2 match (deeper)
        sub2 = sub1 / "level2"
        sub2.mkdir()
        self._write_pddrc(sub2 / ".pddrc", {
            "ctx2": {
                "defaults": {"prompts_dir": "prompts/shared"},
                "paths": ["src/**"],
            },
        })
        result = _resolve_module_cwd("shared/mod", tmp_path)
        assert result == sub2

    def test_catchall_subdirectory_skipped(self, tmp_path):
        """Subdirectory with catch-all '**' pattern should NOT match unrelated modules."""
        # Subdirectory with catch-all pattern
        sub = tmp_path / "test_debug2"
        sub.mkdir()
        self._write_pddrc(sub / ".pddrc", {
            "test_ctx": {
                "paths": ["**"],
            },
        })
        # Module that doesn't belong to test_debug2
        result = _resolve_module_cwd("bug_main", tmp_path)
        # Should fall back to project root, not test_debug2
        assert result == tmp_path

    def test_catchall_star_subdirectory_skipped(self, tmp_path):
        """Subdirectory with catch-all '*' pattern should NOT match unrelated modules."""
        sub = tmp_path / "some_subdir"
        sub.mkdir()
        self._write_pddrc(sub / ".pddrc", {
            "catch_all": {
                "paths": ["*"],
            },
        })
        result = _resolve_module_cwd("any_module", tmp_path)
        assert result == tmp_path

    def test_specific_subdirectory_match_still_works(self, tmp_path):
        """Subdirectory with specific path pattern should still match correctly."""
        sub = tmp_path / "frontend"
        sub.mkdir()
        self._write_pddrc(sub / ".pddrc", {
            "components": {
                "paths": ["components/**"],
            },
        })
        result = _resolve_module_cwd("components/button", tmp_path)
        assert result == sub


# ---------------------------------------------------------------------------
# _is_catchall_match
# ---------------------------------------------------------------------------

class TestIsCatchallMatch:
    def test_catchall_double_star(self):
        """Pattern '**' is a catch-all."""
        config = {"contexts": {"ctx": {"paths": ["**"]}}}
        assert _is_catchall_match("any_module", config) is True

    def test_catchall_single_star(self):
        """Pattern '*' is a catch-all."""
        config = {"contexts": {"ctx": {"paths": ["*"]}}}
        assert _is_catchall_match("any_module", config) is True

    def test_specific_pattern_not_catchall(self):
        """Pattern 'src/**' is specific, not a catch-all."""
        config = {"contexts": {"ctx": {"paths": ["src/**"]}}}
        assert _is_catchall_match("src/widget", config) is False

    def test_prompts_dir_match_not_catchall(self):
        """Match via prompts_dir is always specific."""
        config = {"contexts": {"ctx": {"defaults": {"prompts_dir": "prompts/mymod"}, "paths": []}}}
        assert _is_catchall_match("mymod/widget", config) is False

    def test_default_context_ignored(self):
        """Default context is skipped."""
        config = {"contexts": {"default": {"paths": ["**"]}}}
        assert _is_catchall_match("any_module", config) is True  # no non-default match

    def test_no_match_at_all(self):
        """No matching pattern at all returns True (specificity 0)."""
        config = {"contexts": {"ctx": {"paths": ["frontend/**"]}}}
        assert _is_catchall_match("backend_api", config) is True


# ---------------------------------------------------------------------------
# _run_single_dry_run
# ---------------------------------------------------------------------------

class TestRunSingleDryRun:
    @patch("pdd.agentic_sync.subprocess.run")
    @patch("pdd.agentic_sync._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_successful_dry_run(self, mock_find, mock_run):
        mock_run.return_value = MagicMock(returncode=0, stderr="", stdout="")
        ok, err = _run_single_dry_run("my_module", Path("/project"))
        assert ok is True
        assert err == ""
        # Verify command includes --dry-run
        cmd = mock_run.call_args[0][0]
        assert "--dry-run" in cmd
        assert "my_module" in cmd

    @patch("pdd.agentic_sync.subprocess.run")
    @patch("pdd.agentic_sync._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_failed_dry_run(self, mock_find, mock_run):
        mock_run.return_value = MagicMock(
            returncode=1, stderr="Error: prompt not found", stdout=""
        )
        ok, err = _run_single_dry_run("bad_module", Path("/project"))
        assert ok is False
        assert "prompt not found" in err

    @patch("pdd.agentic_sync.subprocess.run")
    @patch("pdd.agentic_sync._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_timeout(self, mock_find, mock_run):
        mock_run.side_effect = __import__("subprocess").TimeoutExpired(
            cmd="pdd", timeout=60
        )
        ok, err = _run_single_dry_run("slow_module", Path("/project"))
        assert ok is False
        assert "timed out" in err.lower()


# ---------------------------------------------------------------------------
# _run_dry_run_validation
# ---------------------------------------------------------------------------

class TestRunDryRunValidation:
    @patch("pdd.agentic_sync._run_single_dry_run")
    @patch("pdd.agentic_sync._resolve_module_cwd")
    def test_all_pass_programmatic(self, mock_resolve, mock_dry_run):
        """All modules pass programmatic dry-run."""
        project_root = Path("/project")
        mock_resolve.return_value = project_root
        mock_dry_run.return_value = (True, "")

        all_valid, cwds, errors, cost = _run_dry_run_validation(
            ["mod_a", "mod_b"], project_root, quiet=True
        )
        assert all_valid is True
        assert cwds == {"mod_a": project_root, "mod_b": project_root}
        assert errors == []
        assert cost == 0.0

    @patch("pdd.agentic_sync._llm_fix_dry_run_failure")
    @patch("pdd.agentic_sync._run_single_dry_run")
    @patch("pdd.agentic_sync._resolve_module_cwd")
    def test_programmatic_fails_llm_succeeds(self, mock_resolve, mock_dry_run, mock_llm):
        """Programmatic fails, LLM fallback succeeds."""
        project_root = Path("/project")
        llm_cwd = Path("/project/sub")
        mock_resolve.return_value = project_root
        mock_dry_run.return_value = (False, "prompt not found")
        mock_llm.return_value = (True, llm_cwd, 0.02, "")

        all_valid, cwds, errors, cost = _run_dry_run_validation(
            ["mod_x"], project_root, quiet=True
        )
        assert all_valid is True
        assert cwds == {"mod_x": llm_cwd}
        assert errors == []
        assert cost == pytest.approx(0.02)

    @patch("pdd.agentic_sync._llm_fix_dry_run_failure")
    @patch("pdd.agentic_sync._run_single_dry_run")
    @patch("pdd.agentic_sync._resolve_module_cwd")
    def test_both_fail(self, mock_resolve, mock_dry_run, mock_llm):
        """Both programmatic and LLM fail."""
        project_root = Path("/project")
        mock_resolve.return_value = project_root
        mock_dry_run.return_value = (False, "prompt not found")
        mock_llm.return_value = (False, None, 0.01, "LLM could not resolve")

        all_valid, cwds, errors, cost = _run_dry_run_validation(
            ["mod_y"], project_root, quiet=True
        )
        assert all_valid is False
        assert "mod_y" in errors[0]
        assert cost == pytest.approx(0.01)


# ---------------------------------------------------------------------------
# _filter_already_synced
# ---------------------------------------------------------------------------

class TestFilterAlreadySynced:
    """Tests for fingerprint-based pre-filtering of already-synced modules."""

    @patch("pdd.agentic_sync.sync_determine_operation")
    @patch("pdd.agentic_sync._detect_languages_with_context")
    @patch("pdd.agentic_sync._load_pddrc_config")
    @patch("pdd.agentic_sync._find_pddrc_file")
    def test_nothing_operation_filtered_out(self, mock_pddrc_file, mock_config, mock_detect, mock_determine):
        """Module with operation='nothing' gets filtered out."""
        cwd = Path("/project")
        mock_pddrc_file.return_value = cwd / ".pddrc"
        mock_config.return_value = {"contexts": {"default": {"defaults": {"prompts_dir": "prompts"}}}}
        mock_detect.return_value = {"python": Path("prompts/mod_a_python.prompt")}

        decision = MagicMock()
        decision.operation = "nothing"
        mock_determine.return_value = decision

        result = _filter_already_synced(["mod_a"], {"mod_a": cwd}, quiet=True)
        assert result == []

    @patch("pdd.agentic_sync.sync_determine_operation")
    @patch("pdd.agentic_sync._detect_languages_with_context")
    @patch("pdd.agentic_sync._load_pddrc_config")
    @patch("pdd.agentic_sync._find_pddrc_file")
    def test_generate_operation_kept(self, mock_pddrc_file, mock_config, mock_detect, mock_determine):
        """Module with operation='generate' stays in the list."""
        cwd = Path("/project")
        mock_pddrc_file.return_value = cwd / ".pddrc"
        mock_config.return_value = {"contexts": {"default": {"defaults": {"prompts_dir": "prompts"}}}}
        mock_detect.return_value = {"python": Path("prompts/mod_b_python.prompt")}

        decision = MagicMock()
        decision.operation = "generate"
        mock_determine.return_value = decision

        result = _filter_already_synced(["mod_b"], {"mod_b": cwd}, quiet=True)
        assert result == ["mod_b"]

    @patch("pdd.agentic_sync.sync_determine_operation")
    @patch("pdd.agentic_sync._detect_languages_with_context")
    @patch("pdd.agentic_sync._load_pddrc_config")
    @patch("pdd.agentic_sync._find_pddrc_file")
    def test_mixed_modules(self, mock_pddrc_file, mock_config, mock_detect, mock_determine):
        """Mix of synced and unsynced modules — only unsynced remain."""
        cwd = Path("/project")
        mock_pddrc_file.return_value = cwd / ".pddrc"
        mock_config.return_value = {"contexts": {"default": {"defaults": {"prompts_dir": "prompts"}}}}
        mock_detect.return_value = {"python": Path("prompts/x_python.prompt")}

        nothing_decision = MagicMock()
        nothing_decision.operation = "nothing"
        generate_decision = MagicMock()
        generate_decision.operation = "generate"

        mock_determine.side_effect = [nothing_decision, generate_decision]

        result = _filter_already_synced(
            ["synced_mod", "needs_work_mod"],
            {"synced_mod": cwd, "needs_work_mod": cwd},
            quiet=True,
        )
        assert result == ["needs_work_mod"]

    def test_missing_cwd_keeps_module(self):
        """Module without resolved cwd stays in the list."""
        result = _filter_already_synced(["mod_x"], {}, quiet=True)
        assert result == ["mod_x"]

    @patch("pdd.agentic_sync._find_pddrc_file")
    def test_language_discovery_failure_keeps_module(self, mock_pddrc_file):
        """If language discovery raises an exception, module stays in the list."""
        mock_pddrc_file.side_effect = Exception("pddrc read error")

        result = _filter_already_synced(
            ["mod_err"], {"mod_err": Path("/project")}, quiet=True
        )
        assert result == ["mod_err"]

    @patch("pdd.agentic_sync.sync_determine_operation")
    @patch("pdd.agentic_sync._detect_languages_with_context")
    @patch("pdd.agentic_sync._load_pddrc_config")
    @patch("pdd.agentic_sync._find_pddrc_file")
    def test_fingerprint_check_exception_keeps_module(self, mock_pddrc_file, mock_config, mock_detect, mock_determine):
        """If sync_determine_operation raises, module stays in the list."""
        cwd = Path("/project")
        mock_pddrc_file.return_value = cwd / ".pddrc"
        mock_config.return_value = {"contexts": {"default": {"defaults": {"prompts_dir": "prompts"}}}}
        mock_detect.return_value = {"python": Path("prompts/mod_c_python.prompt")}
        mock_determine.side_effect = Exception("hash computation error")

        result = _filter_already_synced(["mod_c"], {"mod_c": cwd}, quiet=True)
        assert result == ["mod_c"]

    @patch("pdd.agentic_sync._detect_languages_with_context")
    @patch("pdd.agentic_sync._load_pddrc_config")
    @patch("pdd.agentic_sync._find_pddrc_file")
    def test_no_languages_found_keeps_module(self, mock_pddrc_file, mock_config, mock_detect):
        """Module with no detected languages stays in the list."""
        cwd = Path("/project")
        mock_pddrc_file.return_value = cwd / ".pddrc"
        mock_config.return_value = {"contexts": {"default": {"defaults": {"prompts_dir": "prompts"}}}}
        mock_detect.return_value = {}

        result = _filter_already_synced(["mod_d"], {"mod_d": cwd}, quiet=True)
        assert result == ["mod_d"]

    @patch("pdd.agentic_sync.sync_determine_operation")
    @patch("pdd.agentic_sync._detect_languages_with_context")
    @patch("pdd.agentic_sync._load_pddrc_config")
    @patch("pdd.agentic_sync._find_pddrc_file")
    def test_multi_language_any_needs_work_keeps_module(self, mock_pddrc_file, mock_config, mock_detect, mock_determine):
        """If any language needs work, the module stays."""
        cwd = Path("/project")
        mock_pddrc_file.return_value = cwd / ".pddrc"
        mock_config.return_value = {"contexts": {"default": {"defaults": {"prompts_dir": "prompts"}}}}
        mock_detect.return_value = {
            "python": Path("prompts/mod_e_python.prompt"),
            "typescript": Path("prompts/mod_e_typescript.prompt"),
        }

        nothing_decision = MagicMock()
        nothing_decision.operation = "nothing"
        fix_decision = MagicMock()
        fix_decision.operation = "fix"

        mock_determine.side_effect = [nothing_decision, fix_decision]

        result = _filter_already_synced(["mod_e"], {"mod_e": cwd}, quiet=True)
        assert result == ["mod_e"]

    @patch("pdd.agentic_sync.sync_determine_operation")
    @patch("pdd.agentic_sync._detect_languages_with_context")
    @patch("pdd.agentic_sync._load_pddrc_config")
    @patch("pdd.agentic_sync._find_pddrc_file")
    def test_all_filtered_returns_empty(self, mock_pddrc_file, mock_config, mock_detect, mock_determine):
        """When all modules are already synced, returns empty list."""
        cwd = Path("/project")
        mock_pddrc_file.return_value = cwd / ".pddrc"
        mock_config.return_value = {"contexts": {"default": {"defaults": {"prompts_dir": "prompts"}}}}
        mock_detect.return_value = {"python": Path("prompts/x_python.prompt")}

        decision = MagicMock()
        decision.operation = "nothing"
        mock_determine.return_value = decision

        result = _filter_already_synced(
            ["mod_1", "mod_2", "mod_3"],
            {"mod_1": cwd, "mod_2": cwd, "mod_3": cwd},
            quiet=True,
        )
        assert result == []


# ---------------------------------------------------------------------------
# Tests for _parse_llm_response deduplication
# ---------------------------------------------------------------------------

class TestParseLlmResponseDedup:
    """Tests that _parse_llm_response deduplicates modules in the LLM output."""

    def test_exact_duplicates_removed(self):
        """LLM returns the same module name twice — dedup removes the second."""
        response = 'MODULES_TO_SYNC: ["recruiting_config", "recruiting_config", "recruiting_chat"]\nDEPS_VALID: true'
        modules, deps_valid, _ = _parse_llm_response(response)
        assert modules == ["recruiting_config", "recruiting_chat"]

    def test_no_duplicates_unchanged(self):
        """When all modules are unique, list is returned as-is."""
        response = 'MODULES_TO_SYNC: ["mod_a", "mod_b", "mod_c"]\nDEPS_VALID: true'
        modules, deps_valid, _ = _parse_llm_response(response)
        assert modules == ["mod_a", "mod_b", "mod_c"]

    def test_preserves_order(self):
        """Dedup preserves first-occurrence order."""
        response = 'MODULES_TO_SYNC: ["c", "a", "b", "a", "c"]\nDEPS_VALID: true'
        modules, _, _ = _parse_llm_response(response)
        assert modules == ["c", "a", "b"]


# ---------------------------------------------------------------------------
# Tests for post-suffix-stripping deduplication
# ---------------------------------------------------------------------------

class TestPostStrippingDedup:
    """Tests that modules are deduplicated after language suffix removal.

    The LLM may return both "recruiting_config_Python" and "recruiting_config"
    which are different strings but both map to "recruiting_config" after
    suffix stripping.
    """

    def test_suffix_stripping_creates_duplicates(self):
        """Two different LLM entries that converge to the same basename after stripping."""
        from pdd.sync_order import extract_module_from_include

        # Simulate the stripping + dedup logic from run_agentic_sync lines 718-722
        raw_modules = ["recruiting_config_Python", "recruiting_config", "recruiting_chat_Python"]
        stripped = []
        for m in raw_modules:
            s = extract_module_from_include(m + ".prompt")
            stripped.append(s if s else m)
        result = list(dict.fromkeys(stripped))

        assert result == ["recruiting_config", "recruiting_chat"]

    def test_no_convergence_no_dedup(self):
        """Different modules stay separate after stripping."""
        from pdd.sync_order import extract_module_from_include

        raw_modules = ["recruiting_config_Python", "recruiting_config_yaml_YAML", "recruiting_chat_Python"]
        stripped = []
        for m in raw_modules:
            s = extract_module_from_include(m + ".prompt")
            stripped.append(s if s else m)
        result = list(dict.fromkeys(stripped))

        assert result == ["recruiting_config", "recruiting_config_yaml", "recruiting_chat"]

    def test_preserves_order_after_stripping(self):
        """First occurrence wins when duplicates appear after stripping."""
        from pdd.sync_order import extract_module_from_include

        raw_modules = ["recruiting_chat_Python", "recruiting_config", "recruiting_config_Python"]
        stripped = []
        for m in raw_modules:
            s = extract_module_from_include(m + ".prompt")
            stripped.append(s if s else m)
        result = list(dict.fromkeys(stripped))

        assert result == ["recruiting_chat", "recruiting_config"]


# ---------------------------------------------------------------------------
# _detect_modules_from_branch_diff
# ---------------------------------------------------------------------------

class TestDetectModulesFromBranchDiff:
    """Test git diff-based module detection for pdd sync with issue URLs."""

    def test_returns_basenames_from_changed_prompts(self):
        """When branch has changed prompt files, return their basenames."""
        diff_output = (
            "prompts/agentic_e2e_fix_orchestrator_python.prompt\n"
            "prompts/ci_validation_python.prompt\n"
            "prompts/commands/fix_python.prompt\n"
        )
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            result = _detect_modules_from_branch_diff(Path("/fake/project"))
        assert result == [
            "agentic_e2e_fix_orchestrator",
            "ci_validation",
            "commands/fix",
        ]

    def test_returns_empty_list_on_main_branch(self):
        """When on main/master, no diff is possible — return empty list."""
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=0, stdout="main\n", stderr=""
            )
            result = _detect_modules_from_branch_diff(Path("/fake/project"))
        assert result == []

    def test_returns_empty_list_when_no_prompts_changed(self):
        """When branch has changes but no prompt files, return empty list."""
        diff_output = "pdd/agentic_common.py\ntests/test_agentic_common.py\n"
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            result = _detect_modules_from_branch_diff(Path("/fake/project"))
        assert result == []

    def test_filters_non_prompt_files_from_diff(self):
        """Only .prompt files are considered, not other changed files."""
        diff_output = (
            "prompts/ci_validation_python.prompt\n"
            "pdd/ci_validation.py\n"
            "tests/test_ci_validation.py\n"
            "architecture.json\n"
        )
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            result = _detect_modules_from_branch_diff(Path("/fake/project"))
        assert result == ["ci_validation"]

    def test_excludes_llm_prompt_templates(self):
        """LLM prompt templates (ending in _LLM.prompt) are not syncable modules."""
        diff_output = (
            "prompts/ci_validation_python.prompt\n"
            "prompts/agentic_e2e_fix_step10_ci_validation_LLM.prompt\n"
        )
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            result = _detect_modules_from_branch_diff(Path("/fake/project"))
        assert result == ["ci_validation"]

    def test_returns_empty_list_when_git_fails(self):
        """When git command fails (not a git repo, etc.), return empty list."""
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = FileNotFoundError("git not found")
            result = _detect_modules_from_branch_diff(Path("/fake/project"))
        assert result == []

    def test_deduplicates_basenames(self):
        """If same basename appears multiple times, deduplicate."""
        diff_output = (
            "prompts/ci_validation_python.prompt\n"
            "prompts/ci_validation_javascript.prompt\n"
        )
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            result = _detect_modules_from_branch_diff(Path("/fake/project"))
        assert result == ["ci_validation"]

    def test_handles_nested_prompt_paths(self):
        """Prompts in subdirectories like commands/ get correct basenames."""
        diff_output = (
            "prompts/commands/fix_python.prompt\n"
            "prompts/commands/sync_python.prompt\n"
        )
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            result = _detect_modules_from_branch_diff(Path("/fake/project"))
        assert result == ["commands/fix", "commands/sync"]


class TestBranchDiffSkipsLlm:
    """Verify run_agentic_sync uses branch diff and skips LLM when modules found."""

    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_skips_llm_when_branch_diff_finds_modules(
        self, mock_cli, mock_gh, mock_llm, mock_diff, mock_dry_run
    ):
        """When branch diff returns modules, LLM should not be called."""
        mock_diff.return_value = ["ci_validation", "agentic_common"]
        mock_gh.return_value = (True, json.dumps({
            "title": "test", "body": "test body", "comments_url": ""
        }))
        mock_dry_run.return_value = (True, {}, [], 0.0)

        with patch("pdd.agentic_sync._find_project_root", return_value=Path("/fake")), \
             patch("pdd.agentic_sync._load_architecture_json", return_value=([], Path("/fake/architecture.json"))), \
             patch("pdd.agentic_sync.AsyncSyncRunner") as mock_runner:
            mock_runner_inst = MagicMock()
            mock_runner_inst.run.return_value = (True, "ok", 0.5)
            mock_runner.return_value = mock_runner_inst

            run_agentic_sync(
                "https://github.com/owner/repo/issues/822",
                quiet=True,
            )

        mock_llm.assert_not_called()

    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_falls_back_to_llm_when_branch_diff_empty(
        self, mock_cli, mock_gh, mock_llm, mock_diff, mock_dry_run
    ):
        """When branch diff returns empty, LLM identification should be used."""
        mock_diff.return_value = []
        mock_gh.return_value = (True, json.dumps({
            "title": "test", "body": "test body", "comments_url": ""
        }))
        mock_llm.return_value = (
            True,
            'MODULES_TO_SYNC: ["ci_validation"]\nDEPS_VALID: true',
            0.50,
            "gpt-4",
        )
        mock_dry_run.return_value = (True, {}, [], 0.0)

        with patch("pdd.agentic_sync._find_project_root", return_value=Path("/fake")), \
             patch("pdd.agentic_sync._load_architecture_json", return_value=([], Path("/fake/architecture.json"))), \
             patch("pdd.agentic_sync.load_prompt_template", return_value="template {issue_content} {architecture_json}"), \
             patch("pdd.agentic_sync.AsyncSyncRunner") as mock_runner:
            mock_runner_inst = MagicMock()
            mock_runner_inst.run.return_value = (True, "ok", 0.5)
            mock_runner.return_value = mock_runner_inst

            run_agentic_sync(
                "https://github.com/owner/repo/issues/822",
                quiet=True,
            )

        mock_llm.assert_called_once()
