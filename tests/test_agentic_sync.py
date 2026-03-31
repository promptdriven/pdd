"""Tests for pdd.agentic_sync module."""
from __future__ import annotations

import json
import os
import subprocess
import tempfile
from pathlib import Path
from typing import Any, Dict, List
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_sync import (
    _apply_architecture_corrections,
    _augment_architecture_from_pr_branch,
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
        # Runner now includes initial_cost (0.05) + per-module (0.10) = 0.15
        mock_runner.run.return_value = (True, "All 1 modules synced successfully", 0.15)
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

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch("pdd.agentic_sync.build_dep_graph_from_architecture", return_value={"foo": []})
    @patch("pdd.agentic_sync.load_prompt_template", return_value="template {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_initial_cost_passed_to_runner(
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
        """Issue #745: LLM module analysis cost must be passed as initial_cost to AsyncSyncRunner."""
        issue_data = {"title": "Test", "body": "Fix foo", "comments_url": ""}
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (
            [{"filename": "foo_python.prompt", "dependencies": []}],
            Path("/tmp/architecture.json"),
        )
        # LLM module identification costs 0.07
        mock_agentic_task.return_value = (
            True,
            'MODULES_TO_SYNC: ["foo"]\nDEPS_VALID: true',
            0.07,
            "anthropic",
        )
        mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, [], 0.0)

        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 1 modules synced successfully", 0.10)
        mock_runner_cls.return_value = mock_runner

        run_agentic_sync("https://github.com/owner/repo/issues/1", quiet=True)

        # Verify initial_cost was passed to AsyncSyncRunner constructor
        runner_kwargs = mock_runner_cls.call_args[1]
        assert "initial_cost" in runner_kwargs
        assert runner_kwargs["initial_cost"] == pytest.approx(0.07)


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

    def test_preserves_context_prefix_for_multi_context_prompts(self):
        """Prompts under context-specific dirs like prompts/frontend/ preserve the full path.

        When pdd_cloud has multiple contexts (frontend, backend, etc.), the diff
        output contains paths like 'prompts/frontend/app/dashboard/page_TypescriptReact.prompt'.
        The basename must include the context prefix ('frontend/app/dashboard/page') so that
        pdd sync can resolve the correct .pddrc context. Stripping to just 'page' causes
        sync to pick the wrong context or fail with 'No prompt files found'.

        Regression test for GitHub issue promptdriven/pdd_cloud#826.
        """
        diff_output = (
            "prompts/frontend/app/dashboard/page_TypescriptReact.prompt\n"
            "prompts/frontend/components/layout/Sidebar_TypescriptReact.prompt\n"
            "prompts/frontend/components/dashboard/GitHubAppCTA_TypescriptReact.prompt\n"
            "prompts/backend/utils/credit_helpers_python.prompt\n"
        )
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="change/issue-836\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            result = _detect_modules_from_branch_diff(Path("/fake/project"))
        assert result == [
            "frontend/app/dashboard/page",
            "frontend/components/layout/Sidebar",
            "frontend/components/dashboard/GitHubAppCTA",
            "backend/utils/credit_helpers",
        ]

    def test_handles_extension_prompts_with_nested_prompts_dir(self):
        """Prompts under extension dirs like extensions/github_pdd_app/prompts/ are handled.

        Extension prompts have a different structure: the 'prompts/' directory is nested
        inside the extension, not at the repo root. The function should still extract
        correct basenames relative to the prompts/ directory.
        """
        diff_output = (
            "extensions/github_pdd_app/prompts/pdd_executor_Python.prompt\n"
            "extensions/github_pdd_app/prompts/solving_orchestrator_Python.prompt\n"
        )
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="change/issue-838\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            result = _detect_modules_from_branch_diff(Path("/fake/project"))
        assert result == ["pdd_executor", "solving_orchestrator"]


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


# ---------------------------------------------------------------------------
# _filter_invalid_basenames — pre-validation against architecture.json
# (Prevents LLM-hallucinated basenames from blocking the entire sync)
# ---------------------------------------------------------------------------

from pdd.agentic_sync import _filter_invalid_basenames


class TestFilterInvalidBasenames:
    def test_filters_out_hallucinated_basenames(self):
        """Basenames not in architecture.json should be removed."""
        architecture = [
            {"filename": "agentic_e2e_fix_step1_unit_tests_LLM.prompt"},
            {"filename": "agentic_bug_orchestrator_python.prompt"},
        ]
        modules = [
            "agentic_bug_orchestrator",
            "agentic_e2e_fix_step1_understand",  # hallucinated
            "agentic_e2e_fix_step8_review",      # hallucinated
        ]

        valid, invalid = _filter_invalid_basenames(modules, architecture)

        assert "agentic_bug_orchestrator" in valid
        assert "agentic_e2e_fix_step1_understand" in invalid
        assert "agentic_e2e_fix_step8_review" in invalid
        assert len(valid) == 1
        assert len(invalid) == 2

    def test_keeps_all_valid_basenames(self):
        """All basenames that exist in architecture.json should be kept."""
        architecture = [
            {"filename": "mod_a_python.prompt"},
            {"filename": "mod_b_python.prompt"},
        ]
        modules = ["mod_a", "mod_b"]

        valid, invalid = _filter_invalid_basenames(modules, architecture)

        assert valid == ["mod_a", "mod_b"]
        assert invalid == []

    def test_matches_llm_prompt_basenames(self):
        """LLM prompts (ending in _LLM) should also match."""
        architecture = [
            {"filename": "agentic_bug_step10_verify_LLM.prompt"},
        ]
        modules = ["agentic_bug_step10_verify"]

        valid, invalid = _filter_invalid_basenames(modules, architecture)

        assert valid == ["agentic_bug_step10_verify"]
        assert invalid == []

    def test_returns_all_when_no_architecture(self):
        """If architecture is None, can't validate — keep all modules."""
        modules = ["mod_a", "hallucinated_mod"]

        valid, invalid = _filter_invalid_basenames(modules, None)

        assert valid == ["mod_a", "hallucinated_mod"]
        assert invalid == []

    def test_preserves_order(self):
        """Valid basenames should maintain their original order."""
        architecture = [
            {"filename": "mod_c_python.prompt"},
            {"filename": "mod_a_python.prompt"},
            {"filename": "mod_b_python.prompt"},
        ]
        modules = ["mod_b", "mod_a", "mod_c"]

        valid, invalid = _filter_invalid_basenames(modules, architecture)

        assert valid == ["mod_b", "mod_a", "mod_c"]

    def test_accepts_path_qualified_basenames_from_branch_diff(self):
        """Bug #571: _detect_modules_from_branch_diff returns basenames with
        directory prefixes like 'frontend/app/settings/github/page', but
        architecture.json only has 'page' (from 'page_TypescriptReact.prompt').
        The filter must accept path-qualified basenames when their tail matches."""
        architecture = [
            {"filename": "page_TypescriptReact.prompt"},
            {"filename": "BoardConfigPanel_TypescriptReact.prompt"},
        ]
        modules = [
            "frontend/app/settings/github/page",
            "frontend/components/github/BoardConfigPanel",
        ]

        valid, invalid = _filter_invalid_basenames(modules, architecture)

        assert "frontend/app/settings/github/page" in valid, (
            "Bug #571: path-qualified 'page' rejected despite 'page' being a known basename"
        )
        assert "frontend/components/github/BoardConfigPanel" in valid
        assert invalid == []

    def test_rejects_path_qualified_basenames_that_dont_match(self):
        """Path-qualified basenames where the tail doesn't match should still be rejected."""
        architecture = [
            {"filename": "page_TypescriptReact.prompt"},
        ]
        modules = ["frontend/app/settings/github/nonexistent"]

        valid, invalid = _filter_invalid_basenames(modules, architecture)

        assert valid == []
        assert "frontend/app/settings/github/nonexistent" in invalid

    def test_mixed_exact_and_path_qualified_basenames(self):
        """Both exact basenames and path-qualified basenames should be accepted."""
        architecture = [
            {"filename": "page_TypescriptReact.prompt"},
            {"filename": "agentic_bug_orchestrator_python.prompt"},
        ]
        modules = [
            "agentic_bug_orchestrator",                    # exact match
            "frontend/app/settings/github/page",           # path-qualified
            "hallucinated_module",                          # invalid
        ]

        valid, invalid = _filter_invalid_basenames(modules, architecture)

        assert "agentic_bug_orchestrator" in valid
        assert "frontend/app/settings/github/page" in valid
        assert "hallucinated_module" in invalid
        assert len(valid) == 2
        assert len(invalid) == 1

    def test_rejects_ambiguous_tail_match(self):
        """When multiple architecture entries share the same basename (e.g.
        commands/auth and server/routes/auth both extract to 'auth'),
        a path-qualified name like 'commands/auth' must NOT tail-match
        because it's ambiguous which module it refers to."""
        architecture = [
            {"filename": "auth_python.prompt"},   # could be commands/auth
            {"filename": "auth_python.prompt"},   # could be server/routes/auth
            {"filename": "cli_python.prompt"},    # unique basename
        ]
        modules = [
            "commands/auth",        # ambiguous — 'auth' appears twice
            "core/cli",             # unambiguous — 'cli' appears once
        ]

        valid, invalid = _filter_invalid_basenames(modules, architecture)

        assert "commands/auth" in invalid, (
            "Ambiguous tail-match should be rejected when basename appears multiple times"
        )
        assert "core/cli" in valid, (
            "Unambiguous tail-match should still be accepted"
        )


# ---------------------------------------------------------------------------
# BUG: The identify-modules prompt references "the current issue number" but
# never receives it. The LLM can't match origin fields without knowing which
# issue it's working on. Two things must be true:
#   1. The prompt template contains {issue_number} as a format placeholder
#   2. run_agentic_sync passes issue_number to .format() so the LLM sees it
# ---------------------------------------------------------------------------

class TestIdentifyModulesPromptReceivesIssueNumber:
    """The identify-modules LLM prompt must include the issue number so the
    LLM can match architecture.json origin fields against the current issue."""

    def test_prompt_template_contains_issue_number_placeholder(self):
        """The real prompt file must have {issue_number} as a format placeholder."""
        prompt_path = Path(__file__).resolve().parent.parent / "pdd" / "prompts" / "agentic_sync_identify_modules_LLM.prompt"
        assert prompt_path.exists(), f"Prompt file not found at {prompt_path}"
        template = prompt_path.read_text()
        assert "{issue_number}" in template, (
            "Prompt template must contain {issue_number} placeholder so the LLM "
            "knows which issue it's working on (needed for origin field matching)"
        )

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch("pdd.agentic_sync.build_dep_graph_from_architecture", return_value={"foo": []})
    @patch("pdd.agentic_sync.load_prompt_template",
           return_value="Issue #{issue_number}\n{issue_content}\n{architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_format_call_passes_issue_number(
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
        """run_agentic_sync must pass issue_number to .format() so the
        rendered prompt contains the actual number (e.g., '746'), not a
        raw '{issue_number}' placeholder."""
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
        mock_runner.run.return_value = (True, "All 1 modules synced", 0.10)
        mock_runner_cls.return_value = mock_runner

        run_agentic_sync(
            "https://github.com/owner/repo/issues/746", quiet=True
        )

        # The prompt passed to run_agentic_task must contain "746"
        prompt_arg = mock_agentic_task.call_args[1].get(
            "instruction", mock_agentic_task.call_args[0][0]
            if mock_agentic_task.call_args[0] else ""
        )
        assert "Issue #746" in prompt_arg, (
            "The rendered prompt must contain the issue number (746) so the LLM "
            f"can match origin fields. Got prompt starting with: {prompt_arg[:200]}"
        )


# ---------------------------------------------------------------------------
# _augment_architecture_from_pr_branch (Issue #733: new modules from PR branch)
# ---------------------------------------------------------------------------

class TestAugmentArchitectureFromPrBranch:
    """When running pdd sync from main for an issue with a PR, architecture.json
    should be augmented with entries from the PR branch so that newly created
    modules (like embed_retrieve) are not filtered out by _filter_invalid_basenames."""

    def test_adds_new_entries_from_pr_branch(self, tmp_path):
        """New entries in the PR branch's architecture.json should be merged."""
        local_arch = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py"},
        ]
        pr_branch_arch = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py"},
            {"filename": "embed_retrieve_python.prompt", "filepath": "pdd/embed_retrieve.py"},
        ]
        with patch("pdd.agentic_sync.subprocess.run") as mock_sub:
            mock_sub.return_value.returncode = 0
            mock_sub.return_value.stdout = json.dumps(pr_branch_arch)
            result = _augment_architecture_from_pr_branch(local_arch, tmp_path, 733)

        filenames = [e["filename"] for e in result]
        assert "foo_python.prompt" in filenames
        assert "embed_retrieve_python.prompt" in filenames

    def test_does_not_duplicate_existing_entries(self, tmp_path):
        """Entries already in local architecture should not be duplicated."""
        local_arch = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py", "reason": "local version"},
        ]
        pr_branch_arch = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py", "reason": "pr version"},
        ]
        with patch("pdd.agentic_sync.subprocess.run") as mock_sub:
            mock_sub.return_value.returncode = 0
            mock_sub.return_value.stdout = json.dumps(pr_branch_arch)
            result = _augment_architecture_from_pr_branch(local_arch, tmp_path, 733)

        assert len(result) == 1
        # Local version should be preserved, not overwritten
        assert result[0]["reason"] == "local version"

    def test_returns_original_when_no_pr_branch(self, tmp_path):
        """When the PR branch doesn't exist, return architecture unchanged."""
        local_arch = [
            {"filename": "foo_python.prompt"},
        ]
        with patch("pdd.agentic_sync.subprocess.run") as mock_sub:
            mock_sub.side_effect = subprocess.CalledProcessError(128, "git show")
            result = _augment_architecture_from_pr_branch(local_arch, tmp_path, 999)

        assert result == local_arch

    def test_returns_original_when_architecture_is_none(self, tmp_path):
        """When local architecture is None, return None unchanged."""
        result = _augment_architecture_from_pr_branch(None, tmp_path, 733)
        assert result is None

    def test_handles_malformed_pr_branch_json(self, tmp_path):
        """Gracefully handles invalid JSON from the PR branch."""
        local_arch = [{"filename": "foo_python.prompt"}]
        with patch("pdd.agentic_sync.subprocess.run") as mock_sub:
            mock_sub.return_value.returncode = 0
            mock_sub.return_value.stdout = "not valid json"
            result = _augment_architecture_from_pr_branch(local_arch, tmp_path, 733)

        assert result == local_arch
