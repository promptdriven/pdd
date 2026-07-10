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

# Cap per-test runtime for this real-LLM heavy module. Individual hot tests
# may carry their own @pytest.mark.timeout override.
pytestmark = pytest.mark.timeout(450)

from pdd.agentic_sync import (
    _apply_architecture_corrections,
    _analyze_global_sync_modules,
    _architecture_module_basenames,
    _architecture_sync_modules,
    _augment_architecture_from_pr_branch,
    _build_scoped_global_dep_graph,
    _branch_diff_is_runtime_llm_only,
    _detect_modules_from_branch_diff,
    _filter_already_synced,
    _find_project_root,
    _is_catchall_match,
    _is_github_issue_url,
    _is_runtime_llm_template,
    _llm_fix_dry_run_failure,
    _load_architecture_json,
    _parse_llm_response,
    _print_global_sync_plan,
    _resolve_module_cwd,
    _run_dry_run_validation,
    _run_single_dry_run,
    GlobalSyncAnalysis,
    GlobalSyncModule,
    run_agentic_sync,
    run_global_sync,
    _IDENTIFY_MODULES_MAX_CHARS,
    _build_identify_issue_content,
    _compact_architecture_for_identification,
    _filter_low_signal_comments,
    _is_low_signal_comment,
    _normalize_modules_for_sync,
    _parse_changed_modules_env,
    _truncate_head_tail,
)
from pdd.agentic_common import build_agentic_task_instruction
from pdd.agentic_sync_runner import (
    DepGraphFromArchitectureResult,
    build_dep_graph_from_architecture,
)


def _global_module(
    basename: str,
    root: Path,
    *,
    key: str | None = None,
    arch_name: str = "architecture.json",
    entry: Dict[str, Any] | None = None,
) -> GlobalSyncModule:
    arch_path = root / arch_name
    return GlobalSyncModule(
        key=key or basename,
        basename=basename,
        cwd=arch_path.parent,
        architecture_path=arch_path,
        entry=entry or {"filename": f"{basename}_python.prompt", "dependencies": []},
    )


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
# _is_runtime_llm_template
# ---------------------------------------------------------------------------

class TestIsRuntimeLlmTemplate:
    def test_bare_llm_basename(self):
        assert _is_runtime_llm_template("agentic_sync_identify_modules_LLM")

    def test_llm_prompt_filename(self):
        # Issue #1396: classifier must accept the *_LLM.prompt filename form
        # so the strip step in run_agentic_sync (which appends ".prompt") and
        # any caller that passes raw FILES_MODIFIED entries are both handled.
        assert _is_runtime_llm_template("agentic_sync_identify_modules_LLM.prompt")

    def test_path_qualified_llm_prompt(self):
        assert _is_runtime_llm_template(
            "pdd/prompts/agentic_sync_identify_modules_LLM.prompt"
        )

    def test_path_qualified_bare_llm(self):
        assert _is_runtime_llm_template(
            "pdd/prompts/agentic_sync_identify_modules_LLM"
        )

    def test_lowercase_llm_not_classified(self):
        # Case-sensitive: lowercase ``llm`` is a legitimate basename token.
        assert not _is_runtime_llm_template("call_llm")
        assert not _is_runtime_llm_template("call_llm.prompt")

    def test_non_llm_basename(self):
        assert not _is_runtime_llm_template("agentic_sync_identify_modules")
        assert not _is_runtime_llm_template("agentic_sync_identify_modules_python")

    def test_empty_string(self):
        assert not _is_runtime_llm_template("")


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

        result = _apply_architecture_corrections(
            tmp_path, corrections, architecture, quiet=True
        )
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

        result = _apply_architecture_corrections(
            tmp_path, corrections, architecture, quiet=True
        )
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

        result = build_dep_graph_from_architecture(arch_path, ["api", "models"])
        assert result.graph["api"] == ["models"]
        assert result.graph["models"] == []

    def test_filters_to_target_basenames(self, tmp_path):
        arch = [
            {"filename": "api_python.prompt", "dependencies": ["models_python.prompt", "utils_python.prompt"]},
            {"filename": "models_python.prompt", "dependencies": []},
            {"filename": "utils_python.prompt", "dependencies": []},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))

        # Only targeting api and models, not utils
        result = build_dep_graph_from_architecture(arch_path, ["api", "models"])
        assert "models" in result.graph["api"]
        assert "utils" not in result.graph.get("api", [])
        assert any("utils" in w and "not in the sync target set" in w for w in result.warnings)

    def test_missing_file_returns_empty_deps(self, tmp_path):
        arch_path = tmp_path / "architecture.json"
        # File doesn't exist
        result = build_dep_graph_from_architecture(arch_path, ["foo", "bar"])
        assert result.graph == {"foo": [], "bar": []}

    def test_self_dependency_excluded(self, tmp_path):
        arch = [
            {"filename": "foo_python.prompt", "dependencies": ["foo_python.prompt"]},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))

        result = build_dep_graph_from_architecture(arch_path, ["foo"])
        assert result.graph["foo"] == []

    def test_preserves_subdirectory_basenames(self, tmp_path):
        arch = [
            {"filename": "commands/maintenance_python.prompt", "dependencies": ["agentic_sync_python.prompt"]},
            {"filename": "agentic_sync_python.prompt", "dependencies": []},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))

        result = build_dep_graph_from_architecture(
            arch_path,
            ["commands/maintenance", "agentic_sync"],
        )

        assert result.graph["commands/maintenance"] == ["agentic_sync"]
        assert result.graph["agentic_sync"] == []

    def test_preserves_dependencies_for_path_qualified_targets(self, tmp_path):
        """Regression for #1382: branch-diff targets may be code paths."""
        arch = [
            {
                "filename": "config_Python.prompt",
                "filepath": "src/config.py",
                "dependencies": [],
            },
            {
                "filename": "models_Python.prompt",
                "filepath": "src/models.py",
                "dependencies": ["config_Python.prompt"],
            },
            {
                "filename": "firestore_client_Python.prompt",
                "filepath": "src/clients/firestore_client.py",
                "dependencies": ["config_Python.prompt", "models_Python.prompt"],
            },
            {
                "filename": "solving_orchestrator_Python.prompt",
                "filepath": "src/services/solving_orchestrator.py",
                "dependencies": [
                    "config_Python.prompt",
                    "models_Python.prompt",
                    "firestore_client_Python.prompt",
                ],
            },
            {
                "filename": "worker_app_Python.prompt",
                "filepath": "src/worker_app.py",
                "dependencies": [
                    "config_Python.prompt",
                    "models_Python.prompt",
                    "firestore_client_Python.prompt",
                ],
            },
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))

        result = build_dep_graph_from_architecture(
            arch_path,
            [
                "src/clients/firestore_client",
                "src/config",
                "src/models",
                "src/services/solving_orchestrator",
                "src/worker_app",
            ],
        )

        assert result.graph == {
            "src/config": [],
            "src/models": ["src/config"],
            "src/clients/firestore_client": ["src/config", "src/models"],
            "src/services/solving_orchestrator": [
                "src/config",
                "src/models",
                "src/clients/firestore_client",
            ],
            "src/worker_app": [
                "src/config",
                "src/models",
                "src/clients/firestore_client",
            ],
        }
        assert result.warnings == []


# ---------------------------------------------------------------------------
# Global sync helpers
# ---------------------------------------------------------------------------

class TestGlobalSyncHelpers:
    def test_architecture_module_basenames_preserves_subdirectories_and_skips_llm(self):
        architecture = [
            {"filename": "agentic_sync_python.prompt"},
            {"filename": "commands/maintenance_python.prompt"},
            {"filename": "agentic_change_step1_duplicate_LLM.prompt"},
            {"filename": "commands/maintenance_python.prompt"},
        ]

        result = _architecture_module_basenames(architecture)

        assert result == ["agentic_sync", "commands/maintenance"]

    @patch("pdd.agentic_sync.sync_determine_operation")
    @patch("pdd.agentic_sync._detect_languages_with_context")
    def test_analyze_global_sync_modules_collects_stale_modules(
        self, mock_detect_lang, mock_determine, tmp_path
    ):
        mock_detect_lang.return_value = {"python": tmp_path / "prompts/foo_python.prompt"}
        nothing = MagicMock()
        nothing.operation = "nothing"
        nothing.reason = "clean"
        nothing.estimated_cost = 0.0
        generate = MagicMock()
        generate.operation = "generate"
        generate.reason = "prompt changed"
        generate.estimated_cost = 1.25
        mock_determine.side_effect = [nothing, generate]

        analysis = _analyze_global_sync_modules(
            [
                _global_module("clean_mod", tmp_path),
                _global_module("stale_mod", tmp_path),
            ],
            tmp_path,
            quiet=True,
        )

        assert analysis.modules_to_sync == ["stale_mod"]
        assert analysis.estimated_cost == pytest.approx(1.25)
        assert "stale_mod" in analysis.module_operations
        assert all(call.kwargs["read_only"] is True for call in mock_determine.call_args_list)

    @patch("pdd.agentic_sync.sync_determine_operation")
    @patch("pdd.agentic_sync._detect_languages_with_context")
    def test_analyze_global_sync_modules_treats_all_synced_as_noop(
        self, mock_detect_lang, mock_determine, tmp_path
    ):
        mock_detect_lang.return_value = {"python": tmp_path / "prompts/foo_python.prompt"}
        decision = MagicMock()
        decision.operation = "all_synced"
        decision.reason = "workflow already complete"
        decision.estimated_cost = 0.0
        mock_determine.return_value = decision

        analysis = _analyze_global_sync_modules(
            [_global_module("complete_mod", tmp_path)],
            tmp_path,
            quiet=True,
        )

        assert analysis.modules_to_sync == []
        assert analysis.estimated_cost == 0.0

    @patch("pdd.agentic_sync.sync_determine_operation")
    @patch("pdd.agentic_sync._detect_languages_with_context")
    def test_analyze_global_sync_modules_runs_readonly_check_from_resolved_cwd(
        self, mock_detect_lang, mock_determine, tmp_path
    ):
        import yaml

        nested_dir = tmp_path / "pkg"
        nested_dir.mkdir()
        (nested_dir / ".pddrc").write_text(
            yaml.dump({
                "contexts": {
                    "pkg": {
                        "paths": ["src/**"],
                        "defaults": {"prompts_dir": "prompts/src"},
                    },
                },
            }),
            encoding="utf-8",
        )
        mock_detect_lang.return_value = {
            "python": nested_dir / "prompts/src/mod_python.prompt"
        }

        seen_cwds = []

        def _fake_determine(**_kwargs):
            seen_cwds.append(Path.cwd())
            decision = MagicMock()
            decision.operation = "nothing"
            decision.reason = "clean"
            decision.estimated_cost = 0.0
            return decision

        mock_determine.side_effect = _fake_determine

        _analyze_global_sync_modules(
            [_global_module("src/mod", nested_dir)],
            tmp_path,
            quiet=True,
        )

        assert seen_cwds == [nested_dir]

    @patch("pdd.agentic_sync.sync_determine_operation")
    @patch("pdd.agentic_sync._detect_languages_with_context")
    def test_analyze_global_sync_modules_skips_non_tier1_operations(
        self, mock_detect_lang, mock_determine, tmp_path
    ):
        mock_detect_lang.return_value = {
            "python": tmp_path / "prompts/foo_python.prompt"
        }
        decision = MagicMock()
        decision.operation = "fix"
        decision.reason = "tests failing"
        decision.estimated_cost = 3.0
        mock_determine.return_value = decision

        analysis = _analyze_global_sync_modules(
            [_global_module("needs_fix", tmp_path)],
            tmp_path,
            quiet=True,
        )

        assert analysis.modules_to_sync == []
        assert analysis.estimated_cost == 0.0
        assert any("outside Tier 1" in entry for entry in analysis.skipped_modules)

    def test_scoped_global_dep_graph_separates_duplicate_basenames(self, tmp_path):
        root_arch = tmp_path / "architecture.json"
        nested_arch = tmp_path / "examples" / "demo" / "architecture.json"
        nested_arch.parent.mkdir(parents=True)
        root_report = _global_module(
            "report",
            tmp_path,
            key="report",
            entry={"filename": "report_python.prompt", "dependencies": []},
        )
        nested_models = _global_module(
            "models",
            nested_arch.parent,
            key="examples/demo:models",
            arch_name="architecture.json",
            entry={"filename": "models_python.prompt", "dependencies": []},
        )
        nested_report = GlobalSyncModule(
            key="examples/demo:report",
            basename="report",
            cwd=nested_arch.parent,
            architecture_path=nested_arch,
            entry={
                "filename": "report_python.prompt",
                "dependencies": ["models_python.prompt"],
            },
        )

        graph, warnings = _build_scoped_global_dep_graph(
            [root_report, nested_models, nested_report],
            ["report", "examples/demo:models", "examples/demo:report"],
            tmp_path,
        )

        assert graph["report"] == []
        assert graph["examples/demo:report"] == ["examples/demo:models"]
        assert warnings == []

    def test_scoped_global_dep_graph_warns_on_unresolved_dependency(self, tmp_path):
        """Dangling dep edges (e.g., typo'd filenames in architecture.json)
        must emit a warning so operators don't get a silently-clean dry-run."""
        module = _global_module(
            "app",
            tmp_path,
            key="app",
            entry={
                "filename": "app_python.prompt",
                "dependencies": ["missing_python.prompt"],
            },
        )

        graph, warnings = _build_scoped_global_dep_graph(
            [module],
            ["app"],
            tmp_path,
        )

        assert graph == {"app": []}
        assert len(warnings) == 1
        assert "app" in warnings[0]
        assert "missing_python.prompt" in warnings[0]
        assert "unresolved dependency" in warnings[0]

    def test_scoped_global_dep_graph_ignores_self_dependency(self, tmp_path):
        """Self-deps must not leave a module blocked behind itself."""
        module = _global_module(
            "app",
            tmp_path,
            key="app",
            entry={
                "filename": "app_python.prompt",
                "dependencies": ["app_python.prompt"],
            },
        )

        graph, warnings = _build_scoped_global_dep_graph(
            [module],
            ["app"],
            tmp_path,
        )

        assert graph == {"app": []}
        assert warnings == []

    def test_scoped_global_dep_graph_resolves_unambiguous_cross_arch_dep(self, tmp_path):
        """When a dep doesn't match in the same arch but is unambiguous globally,
        the edge resolves (preserving the prior combined-architecture behaviour)."""
        root_arch = tmp_path / "architecture.json"
        nested_arch_dir = tmp_path / "examples" / "demo"
        nested_arch_dir.mkdir(parents=True)
        nested_arch = nested_arch_dir / "architecture.json"

        # Module 'app' lives in root arch and depends on 'helper'.
        app_module = GlobalSyncModule(
            key="app",
            basename="app",
            cwd=tmp_path,
            architecture_path=root_arch,
            entry={
                "filename": "app_python.prompt",
                "dependencies": ["helper_python.prompt"],
            },
        )
        # Module 'helper' lives in a different (nested) arch.
        helper_module = GlobalSyncModule(
            key="examples/demo:helper",
            basename="helper",
            cwd=nested_arch_dir,
            architecture_path=nested_arch,
            entry={
                "filename": "helper_python.prompt",
                "dependencies": [],
            },
        )

        graph, warnings = _build_scoped_global_dep_graph(
            [app_module, helper_module],
            ["app", "examples/demo:helper"],
            tmp_path,
        )

        assert graph["app"] == ["examples/demo:helper"]
        assert graph["examples/demo:helper"] == []
        assert warnings == []

    def test_scoped_global_dep_graph_warns_on_ambiguous_cross_arch_dep(self, tmp_path):
        """When a cross-arch basename is ambiguous (claimed by multiple modules),
        emit a warning and drop the edge rather than guess."""
        root_arch = tmp_path / "architecture.json"
        nested_arch1_dir = tmp_path / "examples" / "alpha"
        nested_arch2_dir = tmp_path / "examples" / "beta"
        nested_arch1_dir.mkdir(parents=True)
        nested_arch2_dir.mkdir(parents=True)
        nested_arch1 = nested_arch1_dir / "architecture.json"
        nested_arch2 = nested_arch2_dir / "architecture.json"

        # Module 'app' in root depends on 'helper'.
        app_module = GlobalSyncModule(
            key="app",
            basename="app",
            cwd=tmp_path,
            architecture_path=root_arch,
            entry={
                "filename": "app_python.prompt",
                "dependencies": ["helper_python.prompt"],
            },
        )
        # Two modules named 'helper' in two different nested archs.
        helper_alpha = GlobalSyncModule(
            key="examples/alpha:helper",
            basename="helper",
            cwd=nested_arch1_dir,
            architecture_path=nested_arch1,
            entry={
                "filename": "helper_python.prompt",
                "dependencies": [],
            },
        )
        helper_beta = GlobalSyncModule(
            key="examples/beta:helper",
            basename="helper",
            cwd=nested_arch2_dir,
            architecture_path=nested_arch2,
            entry={
                "filename": "helper_python.prompt",
                "dependencies": [],
            },
        )

        graph, warnings = _build_scoped_global_dep_graph(
            [app_module, helper_alpha, helper_beta],
            ["app", "examples/alpha:helper", "examples/beta:helper"],
            tmp_path,
        )

        # Ambiguous → edge dropped.
        assert graph["app"] == []
        assert any("ambiguous cross-arch dependency" in w for w in warnings)
        # The warning should name both candidates for operator visibility.
        assert any(
            "examples/alpha:helper" in w and "examples/beta:helper" in w
            for w in warnings
        )


class TestArchitectureSyncModules:
    """Tests for ``_architecture_sync_modules`` and its nested .pddrc handling."""

    @staticmethod
    def _write_pddrc(path: Path, contexts: Dict[str, Any]) -> None:
        import yaml

        path.write_text(yaml.dump({"contexts": contexts}), encoding="utf-8")

    def test_root_arch_module_picks_up_nested_pddrc_cwd(self, tmp_path):
        """A root architecture.json entry whose basename is owned by a nested
        .pddrc must resolve its cwd to the nested directory, not project_root.

        Regression test for the no-arg global sync path: previously
        _architecture_sync_modules set cwd=arch_path.parent unconditionally,
        which broke modules whose prompts live under a nested .pddrc.
        """
        # Root architecture declares one entry: src/services/orchestrator.
        root_arch = tmp_path / "architecture.json"
        root_arch.write_text(
            json.dumps(
                [
                    {
                        "filename": "src/services/orchestrator_python.prompt",
                        "filepath": "src/services/orchestrator.py",
                        "dependencies": [],
                    }
                ]
            ),
            encoding="utf-8",
        )
        # Nested .pddrc claims that prompt with a specific path pattern.
        nested_dir = tmp_path / "extensions" / "app"
        nested_dir.mkdir(parents=True)
        prompts_dir = nested_dir / "prompts" / "src" / "services"
        prompts_dir.mkdir(parents=True)
        (prompts_dir / "orchestrator_python.prompt").write_text(
            "% nested prompt", encoding="utf-8"
        )
        self._write_pddrc(
            nested_dir / ".pddrc",
            {
                "services": {
                    "paths": ["src/services/**", "prompts/src/services/**"],
                    "defaults": {"prompts_dir": "prompts/src/services"},
                }
            },
        )

        modules, _architecture, _arch_path = _architecture_sync_modules(tmp_path)

        # Exactly one module should be returned.
        assert len(modules) == 1
        module = modules[0]
        assert module.basename == "src/services/orchestrator"
        # The nested .pddrc must have claimed ownership: cwd should be the
        # nested directory, not project_root.
        assert module.cwd == nested_dir, (
            f"Expected nested dir {nested_dir}, got {module.cwd}. "
            "Root-arch module owned by nested .pddrc should resolve to "
            "nested cwd, not project_root."
        )

    def test_nested_arch_module_without_pddrc_defaults_to_arch_dir(self, tmp_path):
        """When no .pddrc claims a basename, cwd defaults to the arch file's
        own directory (preserves nested-arch isolation)."""
        # ``services/api`` is a real nested project; ``examples/`` is excluded as
        # a bundled-sample tree per issue #1060.
        nested_dir = tmp_path / "services" / "api"
        nested_dir.mkdir(parents=True)
        nested_arch = nested_dir / "architecture.json"
        nested_arch.write_text(
            json.dumps(
                [
                    {
                        "filename": "widget_python.prompt",
                        "filepath": "widget.py",
                        "dependencies": [],
                    }
                ]
            ),
            encoding="utf-8",
        )

        modules, _architecture, _arch_path = _architecture_sync_modules(tmp_path)

        assert len(modules) == 1
        assert modules[0].basename == "widget"
        assert modules[0].cwd == nested_dir

    def test_duplicate_basenames_use_arch_scope_even_when_cwd_matches(self, tmp_path):
        """Duplicate basename keys must stay distinct even if nested .pddrc
        resolution sends both modules to the same cwd."""
        shared_dir = tmp_path / "shared"
        shared_dir.mkdir()
        for arch_dir in (tmp_path, shared_dir):
            (arch_dir / "architecture.json").write_text(
                json.dumps(
                    [
                        {
                            "filename": "report_python.prompt",
                            "filepath": "report.py",
                            "dependencies": [],
                        }
                    ]
                ),
                encoding="utf-8",
            )

        (shared_dir / "prompts").mkdir()
        (shared_dir / "prompts" / "report_python.prompt").write_text(
            "% shared report prompt", encoding="utf-8"
        )
        self._write_pddrc(
            shared_dir / ".pddrc",
            {
                "shared": {
                    "paths": ["report"],
                    "defaults": {"prompts_dir": "prompts"},
                }
            },
        )

        modules, _architecture, _arch_path = _architecture_sync_modules(tmp_path)

        report_modules = [module for module in modules if module.basename == "report"]
        assert len(report_modules) == 2
        assert {module.key for module in report_modules} == {
            ".:report",
            "shared:report",
        }
        assert {module.cwd for module in report_modules} == {shared_dir}

    def test_duplicate_absolute_filepaths_are_scheduled_once_and_merge_dependencies(self, tmp_path):
        """Root and nested architecture entries for the same file should not
        produce duplicate global sync work or lose dependency edges."""
        (tmp_path / "architecture.json").write_text(
            json.dumps(
                [
                    {
                        "filename": "backend/report_python.prompt",
                        "filepath": "backend/functions/report.py",
                        "dependencies": ["backend/config_python.prompt"],
                    }
                ]
            ),
            encoding="utf-8",
        )
        nested_dir = tmp_path / "backend" / "functions"
        nested_dir.mkdir(parents=True)
        (nested_dir / "architecture.json").write_text(
            json.dumps(
                [
                    {
                        "filename": "backend/report_python.prompt",
                        "filepath": "report.py",
                        "dependencies": ["backend/models_python.prompt"],
                    }
                ]
            ),
            encoding="utf-8",
        )

        modules, architecture, _arch_path = _architecture_sync_modules(tmp_path)

        assert [module.basename for module in modules] == ["backend/report"]
        assert len(architecture) == 1
        assert architecture[0]["dependencies"] == [
            "backend/config_python.prompt",
            "backend/models_python.prompt",
        ]
        assert modules[0].entry["dependencies"] == architecture[0]["dependencies"]

    def test_duplicate_output_alias_resolves_dependency_to_skipped_filename(self, tmp_path):
        """Dependencies that name a skipped duplicate must resolve to the kept module."""
        (tmp_path / "architecture.json").write_text(
            json.dumps(
                [
                    {
                        "filename": "shared/report_python.prompt",
                        "filepath": "pkg/report.py",
                        "dependencies": [],
                    }
                ]
            ),
            encoding="utf-8",
        )
        nested_dir = tmp_path / "pkg"
        nested_dir.mkdir()
        (nested_dir / "architecture.json").write_text(
            json.dumps(
                [
                    {
                        "filename": "report_python.prompt",
                        "filepath": "report.py",
                        "dependencies": [],
                    },
                    {
                        "filename": "runner_python.prompt",
                        "filepath": "runner.py",
                        "dependencies": ["report_python.prompt"],
                    },
                ]
            ),
            encoding="utf-8",
        )

        modules, _architecture, _arch_path = _architecture_sync_modules(tmp_path)
        target_keys = [module.key for module in modules]
        graph, warnings = _build_scoped_global_dep_graph(
            modules,
            target_keys,
            tmp_path,
        )

        assert "shared/report" in target_keys
        assert "runner" in target_keys
        assert graph["runner"] == ["shared/report"]
        assert warnings == []

    def test_duplicate_output_dependencies_resolve_in_original_scope(self, tmp_path):
        """Merged duplicate dependencies must keep their original architecture scope."""
        (tmp_path / "architecture.json").write_text(
            json.dumps(
                [
                    {
                        "filename": "report_python.prompt",
                        "filepath": "pkg/report.py",
                        "dependencies": [],
                    },
                    {
                        "filename": "helper_python.prompt",
                        "filepath": "helper.py",
                        "dependencies": [],
                    },
                ]
            ),
            encoding="utf-8",
        )
        nested_dir = tmp_path / "pkg"
        nested_dir.mkdir()
        (nested_dir / "architecture.json").write_text(
            json.dumps(
                [
                    {
                        "filename": "report_python.prompt",
                        "filepath": "report.py",
                        "dependencies": ["helper_python.prompt"],
                    },
                    {
                        "filename": "helper_python.prompt",
                        "filepath": "helper.py",
                        "dependencies": [],
                    },
                ]
            ),
            encoding="utf-8",
        )

        modules, _architecture, _arch_path = _architecture_sync_modules(tmp_path)
        target_keys = [module.key for module in modules]
        graph, warnings = _build_scoped_global_dep_graph(
            modules,
            target_keys,
            tmp_path,
        )

        assert "report" in target_keys
        assert ".:helper" in target_keys
        assert "pkg:helper" in target_keys
        assert graph["report"] == ["pkg:helper"]
        assert warnings == []

    def test_duplicate_output_valid_dependencies_survive_malformed_kept_entry(self, tmp_path):
        """A malformed kept dependency field must not drop valid duplicate edges."""
        (tmp_path / "architecture.json").write_text(
            json.dumps(
                [
                    {
                        "filename": "report_python.prompt",
                        "filepath": "pkg/report.py",
                        "dependencies": "not-a-list",
                    }
                ]
            ),
            encoding="utf-8",
        )
        nested_dir = tmp_path / "pkg"
        nested_dir.mkdir()
        (nested_dir / "architecture.json").write_text(
            json.dumps(
                [
                    {
                        "filename": "report_python.prompt",
                        "filepath": "report.py",
                        "dependencies": ["helper_python.prompt"],
                    },
                    {
                        "filename": "helper_python.prompt",
                        "filepath": "helper.py",
                        "dependencies": [],
                    },
                ]
            ),
            encoding="utf-8",
        )

        modules, architecture, _arch_path = _architecture_sync_modules(tmp_path)
        target_keys = [module.key for module in modules]
        graph, warnings = _build_scoped_global_dep_graph(
            modules,
            target_keys,
            tmp_path,
        )

        assert architecture[0]["dependencies"] == ["helper_python.prompt"]
        assert graph["report"] == ["helper"]
        assert warnings == []

    @patch("pdd.agentic_sync._run_readonly_sync_determine_in_cwd")
    def test_duplicate_output_analysis_uses_syncable_duplicate_candidate(
        self, mock_determine, tmp_path
    ):
        """If the kept basename has no prompt, try the skipped duplicate basename."""
        decision = MagicMock()
        decision.operation = "generate"
        decision.reason = "stale"
        decision.estimated_cost = 1.25
        mock_determine.return_value = decision

        (tmp_path / "architecture.json").write_text(
            json.dumps(
                [
                    {
                        "filename": "backend/report_python.prompt",
                        "filepath": "backend/functions/report.py",
                        "dependencies": [],
                    }
                ]
            ),
            encoding="utf-8",
        )
        nested_dir = tmp_path / "backend" / "functions"
        nested_dir.mkdir(parents=True)
        (nested_dir / "architecture.json").write_text(
            json.dumps(
                [
                    {
                        "filename": "report_python.prompt",
                        "filepath": "report.py",
                        "dependencies": [],
                    }
                ]
            ),
            encoding="utf-8",
        )
        nested_prompts = nested_dir / "prompts"
        nested_prompts.mkdir()
        (nested_prompts / "report_python.prompt").write_text(
            "% nested report prompt",
            encoding="utf-8",
        )

        modules, _architecture, _arch_path = _architecture_sync_modules(tmp_path)
        analysis = _analyze_global_sync_modules(modules, tmp_path, quiet=True)

        assert [module.key for module in modules] == ["backend/report"]
        assert analysis.skipped_modules == []
        assert analysis.modules_to_sync == ["backend/report"]
        assert analysis.module_targets["backend/report"] == "report"
        assert analysis.module_cwds["backend/report"] == nested_dir
        mock_determine.assert_called_once()
        assert mock_determine.call_args.kwargs["basename"] == "report"

    @patch("pdd.agentic_sync._run_readonly_sync_determine_in_cwd")
    def test_duplicate_output_analysis_checks_later_stale_candidate(
        self, mock_determine, tmp_path
    ):
        """A clean first duplicate must not hide a stale later duplicate."""
        (tmp_path / "architecture.json").write_text(
            json.dumps(
                [
                    {
                        "filename": "backend/report_python.prompt",
                        "filepath": "backend/functions/report.py",
                        "dependencies": [],
                    }
                ]
            ),
            encoding="utf-8",
        )
        root_prompts = tmp_path / "prompts" / "backend"
        root_prompts.mkdir(parents=True)
        (root_prompts / "report_python.prompt").write_text(
            "% root report prompt",
            encoding="utf-8",
        )
        nested_dir = tmp_path / "backend" / "functions"
        nested_dir.mkdir(parents=True)
        (nested_dir / "architecture.json").write_text(
            json.dumps(
                [
                    {
                        "filename": "report_python.prompt",
                        "filepath": "report.py",
                        "dependencies": [],
                    }
                ]
            ),
            encoding="utf-8",
        )
        nested_prompts = nested_dir / "prompts"
        nested_prompts.mkdir()
        (nested_prompts / "report_python.prompt").write_text(
            "% nested report prompt",
            encoding="utf-8",
        )

        def fake_determine(_cwd, **kwargs):
            decision = MagicMock()
            decision.reason = kwargs["basename"]
            decision.estimated_cost = 2.5
            decision.operation = (
                "nothing" if kwargs["basename"] == "backend/report" else "generate"
            )
            return decision

        mock_determine.side_effect = fake_determine

        modules, _architecture, _arch_path = _architecture_sync_modules(tmp_path)
        analysis = _analyze_global_sync_modules(modules, tmp_path, quiet=True)

        assert [call.kwargs["basename"] for call in mock_determine.call_args_list] == [
            "backend/report",
            "report",
        ]
        assert analysis.skipped_modules == []
        assert analysis.modules_to_sync == ["backend/report"]
        assert analysis.module_targets["backend/report"] == "report"
        assert analysis.module_cwds["backend/report"] == nested_dir
        assert analysis.estimated_cost == 2.5


class TestRunGlobalSync:
    @patch("pdd.agentic_sync._find_project_root")
    @patch("pdd.agentic_sync._architecture_sync_modules", return_value=([], [], Path("/tmp/architecture.json")))
    def test_fails_when_architecture_missing(self, mock_arch_modules, mock_root, tmp_path):
        mock_root.return_value = tmp_path

        success, message, cost, model = run_global_sync(quiet=True)

        assert success is False
        assert "No architecture.json found" in message
        assert cost == 0.0
        assert model == "global-sync"

    @patch("pdd.agentic_sync._find_project_root")
    @patch("pdd.agentic_sync._architecture_sync_modules")
    @patch("pdd.agentic_sync._analyze_global_sync_modules")
    @patch("pdd.agentic_sync._build_scoped_global_dep_graph")
    def test_dry_run_reports_dependency_order_without_running_runner(
        self, mock_dep_graph, mock_analyze, mock_arch_modules, mock_root, tmp_path
    ):
        mock_root.return_value = tmp_path
        modules = [
            _global_module("app", tmp_path),
            _global_module("lib", tmp_path),
        ]
        mock_arch_modules.return_value = (
            modules,
            [module.entry for module in modules],
            tmp_path / "architecture.json",
        )
        mock_analyze.return_value = MagicMock(
            modules_to_sync=["app", "lib"],
            module_cwds={"app": tmp_path, "lib": tmp_path},
            module_targets={"app": "app", "lib": "lib"},
            estimated_cost=2.0,
            module_operations={"app": ["python: generate - stale"], "lib": ["python: generate - stale"]},
            skipped_modules=[],
            all_modules=["app", "lib"],
        )
        mock_dep_graph.return_value = ({"app": ["lib"], "lib": []}, [])

        success, message, cost, model = run_global_sync(quiet=True, dry_run=True)

        assert success is True
        assert "2 module(s) would sync" in message
        assert cost == 0.0
        assert model == "global-sync"

    @patch("pdd.agentic_sync._find_project_root")
    @patch("pdd.agentic_sync._architecture_sync_modules")
    @patch("pdd.agentic_sync._analyze_global_sync_modules")
    @patch("pdd.agentic_sync._build_scoped_global_dep_graph")
    @patch("pdd.agentic_sync.AsyncSyncRunner")
    def test_global_sync_runs_async_runner_in_dependency_order(
        self, mock_runner, mock_dep_graph, mock_analyze, mock_arch_modules, mock_root, tmp_path
    ):
        mock_root.return_value = tmp_path
        modules = [
            _global_module("app", tmp_path),
            _global_module("lib", tmp_path),
        ]
        mock_arch_modules.return_value = (
            modules,
            [module.entry for module in modules],
            tmp_path / "architecture.json",
        )
        mock_analyze.return_value = MagicMock(
            modules_to_sync=["app", "lib"],
            module_cwds={"app": tmp_path, "lib": tmp_path},
            module_targets={"app": "app", "lib": "lib"},
            estimated_cost=2.0,
            module_operations={"app": ["python: generate - stale"], "lib": ["python: generate - stale"]},
            skipped_modules=[],
            all_modules=["app", "lib"],
        )
        mock_dep_graph.return_value = ({"app": ["lib"], "lib": []}, [])
        mock_runner.return_value.run.return_value = (True, "done", 1.5)

        success, message, cost, model = run_global_sync(
            quiet=True,
            budget=3.0,
            skip_verify=True,
            one_session=True,
            local=True,
            target_coverage=95.0,
        )

        assert success is True
        assert message == "done"
        assert cost == 1.5
        assert model == "global-sync"
        runner_kwargs = mock_runner.call_args.kwargs
        assert runner_kwargs["basenames"] == ["lib", "app"]
        assert runner_kwargs["github_info"] is None
        assert runner_kwargs["module_targets"] == {"app": "app", "lib": "lib"}
        assert runner_kwargs["sync_options"]["total_budget"] == 3.0
        assert "budget" not in runner_kwargs["sync_options"]
        assert runner_kwargs["sync_options"]["skip_verify"] is True
        assert runner_kwargs["sync_options"]["one_session"] is True
        assert runner_kwargs["sync_options"]["local"] is True
        assert runner_kwargs["sync_options"]["target_coverage"] == pytest.approx(95.0)

    @patch("pdd.agentic_sync._find_project_root")
    @patch("pdd.agentic_sync._architecture_sync_modules")
    @patch("pdd.agentic_sync._analyze_global_sync_modules")
    @patch("pdd.agentic_sync._build_scoped_global_dep_graph")
    @patch("pdd.agentic_sync.AsyncSyncRunner")
    def test_global_sync_uses_combined_architecture_for_nested_deps(
        self, mock_runner, mock_dep_graph, mock_analyze, mock_arch_modules, mock_root, tmp_path
    ):
        mock_root.return_value = tmp_path
        modules = [
            _global_module("core", tmp_path),
            _global_module("nested/app", tmp_path),
            _global_module("nested/lib", tmp_path),
        ]
        mock_arch_modules.return_value = (
            modules,
            [module.entry for module in modules],
            tmp_path / "architecture.json",
        )
        mock_analyze.return_value = MagicMock(
            modules_to_sync=["nested/app", "nested/lib"],
            module_cwds={"nested/app": tmp_path / "nested", "nested/lib": tmp_path / "nested"},
            module_targets={"nested/app": "nested/app", "nested/lib": "nested/lib"},
            estimated_cost=2.0,
            module_operations={
                "nested/app": ["python: generate - stale"],
                "nested/lib": ["python: generate - stale"],
            },
            skipped_modules=[],
            all_modules=["core", "nested/app", "nested/lib"],
        )
        mock_dep_graph.return_value = (
            {"nested/app": ["nested/lib"], "nested/lib": []},
            [],
        )
        mock_runner.return_value.run.return_value = (True, "done", 1.0)

        success, _, _, _ = run_global_sync(quiet=True)

        assert success is True
        runner_kwargs = mock_runner.call_args.kwargs
        assert runner_kwargs["basenames"] == ["nested/lib", "nested/app"]
        assert runner_kwargs["dep_graph"]["nested/app"] == ["nested/lib"]

    @patch("pdd.agentic_sync._find_project_root")
    @patch("pdd.agentic_sync._architecture_sync_modules")
    @patch("pdd.agentic_sync._analyze_global_sync_modules")
    @patch("pdd.agentic_sync.AsyncSyncRunner")
    def test_global_sync_rejects_estimated_cost_over_total_budget(
        self, mock_runner, mock_analyze, mock_arch_modules, mock_root, tmp_path
    ):
        mock_root.return_value = tmp_path
        modules = [_global_module("app", tmp_path)]
        mock_arch_modules.return_value = (
            modules,
            [module.entry for module in modules],
            tmp_path / "architecture.json",
        )
        mock_analyze.return_value = MagicMock(
            modules_to_sync=["app"],
            module_cwds={"app": tmp_path},
            module_targets={"app": "app"},
            estimated_cost=5.5,
            module_operations={"app": ["python: generate - stale"]},
            skipped_modules=[],
            all_modules=["app"],
        )

        success, message, cost, model = run_global_sync(quiet=True, budget=5.0)

        assert success is False
        assert "exceeds budget" in message
        assert cost == 0.0
        assert model == "global-sync"
        mock_runner.assert_not_called()

    @patch("pdd.agentic_sync._find_project_root")
    @patch("pdd.agentic_sync._architecture_sync_modules")
    @patch("pdd.agentic_sync._analyze_global_sync_modules")
    @patch("pdd.agentic_sync._build_scoped_global_dep_graph")
    def test_dry_run_default_compacts_skipped_modules(
        self,
        mock_dep_graph,
        mock_analyze,
        mock_arch_modules,
        mock_root,
        tmp_path,
        monkeypatch,
    ):
        from rich.console import Console as _RichConsole
        import pdd.agentic_sync as agentic_sync_module

        recorder = _RichConsole(record=True, width=200, force_terminal=False)
        monkeypatch.setattr(agentic_sync_module, "console", recorder)

        mock_root.return_value = tmp_path
        modules = [_global_module("app", tmp_path)]
        mock_arch_modules.return_value = (
            modules,
            [module.entry for module in modules],
            tmp_path / "architecture.json",
        )
        mock_analyze.return_value = MagicMock(
            modules_to_sync=[],
            module_cwds={},
            module_targets={},
            estimated_cost=0.0,
            module_operations={},
            skipped_modules=[
                "mod_a: python requires example; outside Tier 1 prompt-staleness scope",
                "mod_b: python requires example; outside Tier 1 prompt-staleness scope",
                "mod_c: python requires test; outside Tier 1 prompt-staleness scope",
                "mod_d: python requires verify; outside Tier 1 prompt-staleness scope",
                "mod_e: python requires update; outside Tier 1 prompt-staleness scope",
                "mod_f: python requires fix; outside Tier 1 prompt-staleness scope",
                "mod_g: python requires crash; outside Tier 1 prompt-staleness scope",
                "mod_h: no syncable prompt file found",
                "mod_i: python requires something_weird; outside Tier 1 prompt-staleness scope",
            ],
            all_modules=["mod_a", "mod_b", "mod_c", "mod_d", "mod_e", "mod_f", "mod_g", "mod_h", "mod_i"],
        )
        mock_dep_graph.return_value = ({}, [])

        success, _, _, _ = run_global_sync(dry_run=True)

        assert success is True
        output = recorder.export_text(clear=False)
        # Bucket roll-up must use canonical order and skip zero-count buckets.
        expected_summary = (
            "Out of Tier 1 scope: 2 example, 1 test, 1 verify, 1 update, "
            "1 fix, 1 crash, 1 no-prompt fixture, 1 other"
        )
        assert expected_summary in output
        # Default (non-verbose) must not emit per-module yellow warnings.
        assert "Warning: mod_a" not in output
        assert "Warning: mod_b" not in output
        assert "Warning: mod_h" not in output

    @patch("pdd.agentic_sync._find_project_root")
    @patch("pdd.agentic_sync._architecture_sync_modules")
    @patch("pdd.agentic_sync._analyze_global_sync_modules")
    @patch("pdd.agentic_sync._build_scoped_global_dep_graph")
    def test_dry_run_verbose_lists_each_skipped_module(
        self,
        mock_dep_graph,
        mock_analyze,
        mock_arch_modules,
        mock_root,
        tmp_path,
        monkeypatch,
    ):
        from rich.console import Console as _RichConsole
        import pdd.agentic_sync as agentic_sync_module

        recorder = _RichConsole(record=True, width=200, force_terminal=False)
        monkeypatch.setattr(agentic_sync_module, "console", recorder)

        mock_root.return_value = tmp_path
        modules = [_global_module("app", tmp_path)]
        mock_arch_modules.return_value = (
            modules,
            [module.entry for module in modules],
            tmp_path / "architecture.json",
        )
        mock_analyze.return_value = MagicMock(
            modules_to_sync=[],
            module_cwds={},
            module_targets={},
            estimated_cost=0.0,
            module_operations={},
            skipped_modules=[
                "mod_a: python requires fix; outside Tier 1 prompt-staleness scope",
                "mod_b: python requires fix; outside Tier 1 prompt-staleness scope",
            ],
            all_modules=["mod_a", "mod_b"],
        )
        mock_dep_graph.return_value = ({}, [])

        success, _, _, _ = run_global_sync(dry_run=True, verbose=True)

        assert success is True
        output = recorder.export_text(clear=False)
        assert "Warning: mod_a" in output
        assert "Warning: mod_b" in output

    @patch("pdd.agentic_sync.sync_determine_operation")
    @patch("pdd.agentic_sync._detect_languages_with_context")
    def test_zero_stale_renders_green_success_signal(
        self, mock_detect_lang, mock_determine, tmp_path, monkeypatch
    ):
        from rich.console import Console as _RichConsole
        import pdd.agentic_sync as agentic_sync_module

        recorder = _RichConsole(record=True, width=200, force_terminal=True)
        monkeypatch.setattr(agentic_sync_module, "console", recorder)

        mock_detect_lang.return_value = {"python": tmp_path / "prompts/foo_python.prompt"}
        decision = MagicMock()
        decision.operation = "nothing"
        decision.reason = "clean"
        decision.estimated_cost = 0.0
        mock_determine.return_value = decision

        _analyze_global_sync_modules(
            [_global_module("clean_mod", tmp_path)],
            tmp_path,
            quiet=False,
        )

        plain_output = recorder.export_text(clear=False)
        assert "0 stale module(s)" in plain_output
        # ANSI green is escape code "\x1b[32m"; rich emits this when force_terminal=True
        ansi_output = recorder.export_text(clear=False, styles=True)
        assert "\x1b[32m" in ansi_output or "\x1b[1;32m" in ansi_output

    @patch("pdd.agentic_sync.sync_determine_operation")
    @patch("pdd.agentic_sync._detect_languages_with_context")
    def test_nonzero_stale_does_not_render_green(
        self, mock_detect_lang, mock_determine, tmp_path, monkeypatch
    ):
        from rich.console import Console as _RichConsole
        import pdd.agentic_sync as agentic_sync_module

        recorder = _RichConsole(record=True, width=200, force_terminal=True)
        monkeypatch.setattr(agentic_sync_module, "console", recorder)

        mock_detect_lang.return_value = {"python": tmp_path / "prompts/foo_python.prompt"}
        generate = MagicMock()
        generate.operation = "generate"
        generate.reason = "prompt changed"
        generate.estimated_cost = 1.0
        mock_determine.return_value = generate

        _analyze_global_sync_modules(
            [_global_module("stale_mod", tmp_path)],
            tmp_path,
            quiet=False,
        )

        plain_output = recorder.export_text(clear=False)
        assert "1 stale module(s)" in plain_output
        # The stale fragment itself should not be wrapped in green.
        ansi_output = recorder.export_text(clear=False, styles=True)
        assert "\x1b[32m" not in ansi_output
        assert "\x1b[1;32m" not in ansi_output

    def test_dry_run_plan_zero_stale_renders_green(self, monkeypatch):
        from rich.console import Console as _RichConsole
        import pdd.agentic_sync as agentic_sync_module

        recorder = _RichConsole(record=True, width=200, force_terminal=True)
        monkeypatch.setattr(agentic_sync_module, "console", recorder)

        analysis = GlobalSyncAnalysis(
            modules_to_sync=[],
            module_cwds={},
            module_targets={},
            estimated_cost=0.0,
            module_operations={},
            skipped_modules=[],
            all_modules=["mod_a"],
        )
        _print_global_sync_plan(analysis, [], [], budget=None, verbose=False)

        plain_output = recorder.export_text(clear=False)
        assert "Tier 1 (prompt staleness): 0 module(s) stale" in plain_output
        ansi_output = recorder.export_text(clear=False, styles=True)
        # Rich number-highlighting splits the styled run into multiple ANSI
        # segments, so the literal "module(s) stale" substring is not present
        # in the ANSI text. Locate the plan line by its "Tier" prefix and
        # confirm green markers appear on it.
        plan_line = next(
            line for line in ansi_output.splitlines() if "Tier" in line
        )
        assert "\x1b[32m" in plan_line or "\x1b[1;32m" in plan_line

    def test_dry_run_plan_nonzero_stale_not_green(self, monkeypatch):
        from rich.console import Console as _RichConsole
        import pdd.agentic_sync as agentic_sync_module

        recorder = _RichConsole(record=True, width=200, force_terminal=True)
        monkeypatch.setattr(agentic_sync_module, "console", recorder)

        analysis = GlobalSyncAnalysis(
            modules_to_sync=["mod_a"],
            module_cwds={},
            module_targets={},
            estimated_cost=0.0,
            module_operations={"mod_a": ["generate"]},
            skipped_modules=[],
            all_modules=["mod_a"],
        )
        _print_global_sync_plan(analysis, ["mod_a"], [], budget=None, verbose=False)

        plain_output = recorder.export_text(clear=False)
        assert "Tier 1 (prompt staleness): 1 module(s) stale" in plain_output
        ansi_output = recorder.export_text(clear=False, styles=True)
        # The nonzero stale plan line must NOT carry green success styling.
        plan_line = next(
            line for line in ansi_output.splitlines() if "Tier" in line
        )
        assert "\x1b[32m" not in plan_line
        assert "\x1b[1;32m" not in plan_line


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
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult({"foo": []}, []),
    )
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
        mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, {"foo": "foo"}, [], 0.0)

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
    @patch("pdd.agentic_sync.DurableSyncRunner")
    @patch("pdd.agentic_sync._filter_already_synced", return_value=["foo"])
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult({"foo": []}, []),
    )
    @patch("pdd.agentic_sync.load_prompt_template", return_value="template {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_issue_dry_run_does_not_start_write_mode_runner(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        mock_load_prompt,
        mock_build_graph,
        mock_dry_run,
        mock_branch_diff,
        mock_filter_synced,
        mock_durable_runner_cls,
        mock_runner_cls,
    ):
        """GitHub issue --dry-run must stop before child write-mode syncs."""
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
        mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, {"foo": "foo"}, [], 0.0)

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1",
            quiet=True,
            dry_run=True,
        )

        assert success is True
        assert "Dry run complete" in msg
        assert "foo" in msg
        assert cost == pytest.approx(0.05)
        assert model == "anthropic"
        mock_dry_run.assert_called_once()
        mock_filter_synced.assert_called_once()
        mock_runner_cls.assert_not_called()
        mock_durable_runner_cls.assert_not_called()

    @patch("pdd.agentic_sync._apply_architecture_corrections")
    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._filter_already_synced", return_value=["foo"])
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult({"foo": []}, []),
    )
    @patch("pdd.agentic_sync.load_prompt_template", return_value="template {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_issue_dry_run_does_not_write_dependency_corrections(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        mock_load_prompt,
        mock_build_graph,
        mock_dry_run,
        mock_branch_diff,
        mock_filter_synced,
        mock_runner_cls,
        mock_apply_corrections,
    ):
        """Dependency correction suggestions are read-only in issue dry-run mode."""
        issue_data = {"title": "Test", "body": "Fix foo", "comments_url": ""}
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (
            [{"filename": "foo_python.prompt", "dependencies": []}],
            Path("/tmp/architecture.json"),
        )
        mock_agentic_task.return_value = (
            True,
            (
                'MODULES_TO_SYNC: ["foo"]\n'
                "DEPS_VALID: false\n"
                'DEPS_CORRECTIONS: [{"filename": "foo_python.prompt", "dependencies": []}]'
            ),
            0.05,
            "anthropic",
        )
        mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, {"foo": "foo"}, [], 0.0)

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1",
            quiet=True,
            dry_run=True,
        )

        assert success is True
        assert "Dry run complete" in msg
        mock_apply_corrections.assert_not_called()
        mock_runner_cls.assert_not_called()

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch("pdd.agentic_sync.build_dep_graph_from_architecture_data")
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
        mock_build_graph.return_value = DepGraphFromArchitectureResult(
            {"crm_models": ["api_orders"], "api_orders": []}, []
        )
        mock_dry_run.return_value = (True, {"crm_models": Path("/tmp"), "api_orders": Path("/tmp")}, {"crm_models": "crm_models", "api_orders": "api_orders"}, [], 0.0)

        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 2 modules synced successfully", 0.20)
        mock_runner_cls.return_value = mock_runner

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        assert success
        # Verify stripped basenames were passed to build_dep_graph_from_architecture_data
        call_args = mock_build_graph.call_args
        assert sorted(call_args[0][1]) == ["api_orders", "crm_models"]
        # Verify stripped basenames were passed to AsyncSyncRunner
        runner_kwargs = mock_runner_cls.call_args[1]
        assert sorted(runner_kwargs["basenames"]) == ["api_orders", "crm_models"]

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult({"foo": []}, []),
    )
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
        mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, {"foo": "foo"}, [], 0.0)

        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 1 modules synced successfully", 0.10)
        mock_runner_cls.return_value = mock_runner

        run_agentic_sync("https://github.com/owner/repo/issues/1", quiet=True)

        # Verify initial_cost was passed to AsyncSyncRunner constructor
        runner_kwargs = mock_runner_cls.call_args[1]
        assert "initial_cost" in runner_kwargs
        assert runner_kwargs["initial_cost"] == pytest.approx(0.07)

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync.DurableSyncRunner")
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult({"foo": []}, []),
    )
    @patch("pdd.agentic_sync.load_prompt_template", return_value="template {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_durable_mode_uses_durable_runner(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        mock_load_prompt,
        mock_build_graph,
        mock_dry_run,
        mock_branch_diff,
        mock_durable_runner_cls,
        mock_async_runner_cls,
        tmp_path,
    ):
        issue_data = {"title": "Test", "body": "Fix foo", "comments_url": ""}
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (
            [{"filename": "foo_python.prompt", "dependencies": []}],
            tmp_path / "architecture.json",
        )
        mock_agentic_task.return_value = (
            True,
            'MODULES_TO_SYNC: ["foo"]\nDEPS_VALID: true',
            0.05,
            "anthropic",
        )
        mock_dry_run.return_value = (True, {"foo": tmp_path}, {"foo": "foo"}, [], 0.0)
        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "durable done", 0.15)
        mock_durable_runner_cls.return_value = mock_runner

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1328",
            quiet=True,
            durable=True,
            durable_branch="sync/custom",
            no_resume=True,
            durable_max_parallel=2,
        )

        assert success is True
        assert msg == "durable done"
        assert cost == pytest.approx(0.15)
        assert model == "anthropic"
        mock_async_runner_cls.assert_not_called()
        runner_kwargs = mock_durable_runner_cls.call_args.kwargs
        assert runner_kwargs["issue_number"] == 1328
        assert runner_kwargs["durable_branch"] == "sync/custom"
        assert runner_kwargs["no_resume"] is True
        assert runner_kwargs["durable_max_parallel"] == 2


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

    def test_hidden_worktree_pddrc_does_not_claim_root_module(self, tmp_path):
        """Local worktree copies must not steal module cwd resolution."""
        (tmp_path / "prompts" / "backend").mkdir(parents=True)
        (tmp_path / "prompts" / "backend" / "config_python.prompt").write_text("% root prompt")
        self._write_pddrc(tmp_path / ".pddrc", {
            "backend": {
                "paths": ["backend/**"],
                "defaults": {"prompts_dir": "prompts/backend"},
            },
        })

        worktree = tmp_path / ".worktrees" / "issue-123"
        (worktree / "prompts" / "backend").mkdir(parents=True)
        (worktree / "prompts" / "backend" / "config_python.prompt").write_text("% stale copy")
        self._write_pddrc(worktree / ".pddrc", {
            "backend": {
                "paths": ["backend/**"],
                "defaults": {"prompts_dir": "prompts/backend"},
            },
        })

        assert _resolve_module_cwd("backend/config", tmp_path) == tmp_path

    def test_nested_pddrc_match_requires_matching_prompt_file(self, tmp_path):
        """Broad nested contexts must not hijack similarly named root modules.

        The prompts-linter example has patterns like ``*llm*`` and a local
        ``llm_python.prompt``. That must not claim the root ``llm_model``
        module, whose prompt exists only at the project root.
        """
        (tmp_path / "prompts").mkdir()
        (tmp_path / "prompts" / "llm_model_python.prompt").write_text("% root prompt")
        self._write_pddrc(tmp_path / ".pddrc", {
            "default": {
                "defaults": {"prompts_dir": "prompts"},
            },
        })

        nested = tmp_path / "examples" / "prompts_linter"
        (nested / "prompts").mkdir(parents=True)
        (nested / "prompts" / "llm_python.prompt").write_text("% nested prompt")
        self._write_pddrc(nested / ".pddrc", {
            "utils": {
                "paths": ["*llm*"],
                "defaults": {"prompts_dir": "prompts"},
            },
        })

        assert _resolve_module_cwd("llm_model", tmp_path) == tmp_path
        assert _resolve_module_cwd("llm", tmp_path) == nested

    def test_root_prompt_wins_over_nested_broad_glob(self, tmp_path):
        """A root exact prompt should not be claimed by nested basename globs."""
        (tmp_path / "prompts").mkdir()
        (tmp_path / "prompts" / "cli_python.prompt").write_text("% root prompt")
        self._write_pddrc(tmp_path / ".pddrc", {
            "default": {
                "defaults": {"prompts_dir": "prompts"},
            },
        })

        nested = tmp_path / "examples" / "prompts_linter"
        (nested / "prompts").mkdir(parents=True)
        (nested / "prompts" / "cli_python.prompt").write_text("% nested prompt")
        self._write_pddrc(nested / ".pddrc", {
            "cli": {
                "paths": ["*cli*"],
                "defaults": {"prompts_dir": "prompts"},
            },
        })

        assert _resolve_module_cwd("cli", tmp_path) == tmp_path

    # --- Issue #1128: nested .pddrc shadowed by root .pddrc ---

    def test_nested_pddrc_takes_precedence_over_root(self, tmp_path):
        """When both root and nested .pddrc exist, nested wins for matching modules.

        This is the core bug from issue #1128: the root .pddrc previously shadowed
        nested .pddrc because _resolve_module_cwd short-circuited on root .pddrc
        existence and returned project_root, ignoring any nested configs.
        """
        # Root .pddrc with a catch-all-ish context for extensions
        self._write_pddrc(tmp_path / ".pddrc", {
            "extensions-github_pdd_app": {
                "paths": ["extensions/github_pdd_app/**"],
                "defaults": {"prompts_dir": "extensions/github_pdd_app/prompts"},
            },
        })
        # Nested .pddrc with specific service contexts
        nested_dir = tmp_path / "extensions" / "github_pdd_app"
        nested_dir.mkdir(parents=True)
        self._write_pddrc(nested_dir / ".pddrc", {
            "services": {
                "paths": ["src/services/**", "prompts/src/services/**"],
                "defaults": {"prompts_dir": "prompts/src/services"},
            },
            "pdd_executor_pkg": {
                "paths": ["src/workers/pdd_executor/**"],
                "defaults": {"prompts_dir": "prompts/src/workers/pdd_executor"},
            },
        })
        # Module that matches nested config's "services" context
        result = _resolve_module_cwd("src/services/solving_orchestrator", tmp_path)
        assert result == nested_dir, (
            f"Expected nested dir {nested_dir}, got {result}. "
            "Root .pddrc should not shadow nested .pddrc for modules matching nested contexts."
        )

    def test_module_matching_only_root_context_returns_project_root(self, tmp_path):
        """Module matching only root .pddrc context still returns project root (backward compat)."""
        # Root .pddrc with extension context
        self._write_pddrc(tmp_path / ".pddrc", {
            "extensions-github_pdd_app": {
                "paths": ["extensions/github_pdd_app/**"],
                "defaults": {"prompts_dir": "extensions/github_pdd_app/prompts"},
            },
        })
        # Nested .pddrc
        nested_dir = tmp_path / "extensions" / "github_pdd_app"
        nested_dir.mkdir(parents=True)
        self._write_pddrc(nested_dir / ".pddrc", {
            "services": {
                "paths": ["src/services/**"],
                "defaults": {"prompts_dir": "prompts/src/services"},
            },
        })
        # Module that matches root context but not nested
        result = _resolve_module_cwd("extensions/github_pdd_app/some_top_level_mod", tmp_path)
        assert result == tmp_path

    def test_module_matching_neither_root_nor_nested_falls_back(self, tmp_path):
        """Module matching no context in either config falls back to project root."""
        self._write_pddrc(tmp_path / ".pddrc", {
            "extensions-github_pdd_app": {
                "paths": ["extensions/github_pdd_app/**"],
                "defaults": {"prompts_dir": "extensions/github_pdd_app/prompts"},
            },
        })
        nested_dir = tmp_path / "extensions" / "github_pdd_app"
        nested_dir.mkdir(parents=True)
        self._write_pddrc(nested_dir / ".pddrc", {
            "services": {
                "paths": ["src/services/**"],
                "defaults": {"prompts_dir": "prompts/src/services"},
            },
        })
        result = _resolve_module_cwd("completely/unrelated_module", tmp_path)
        assert result == tmp_path

    def test_root_catchall_does_not_shadow_nested_specific_match(self, tmp_path):
        """Root .pddrc with catch-all pattern must NOT shadow nested .pddrc with specific match.

        This tests the exact scenario from the issue where root catch-all shadows nested
        specific configs.
        """
        # Root .pddrc with catch-all default context
        self._write_pddrc(tmp_path / ".pddrc", {
            "default": {
                "paths": ["**"],
                "defaults": {"prompts_dir": "prompts"},
            },
        })
        # Nested .pddrc with specific worker context
        nested_dir = tmp_path / "extensions" / "app"
        nested_dir.mkdir(parents=True)
        self._write_pddrc(nested_dir / ".pddrc", {
            "workers": {
                "paths": ["src/workers/pdd_executor/**"],
                "defaults": {"prompts_dir": "prompts/src/workers/pdd_executor"},
            },
        })
        result = _resolve_module_cwd("src/workers/pdd_executor/runner", tmp_path)
        assert result == nested_dir, (
            f"Expected nested dir {nested_dir}, got {result}. "
            "Root catch-all must not shadow nested specific match."
        )


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

        all_valid, cwds, _targets, errors, cost = _run_dry_run_validation(
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

        all_valid, cwds, _targets, errors, cost = _run_dry_run_validation(
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

        all_valid, cwds, _targets, errors, cost = _run_dry_run_validation(
            ["mod_y"], project_root, quiet=True
        )
        assert all_valid is False
        assert "mod_y" in errors[0]
        assert cost == pytest.approx(0.01)

    def test_dry_run_success_still_fails_prompt_contract_preflight(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ):
        """A syncable cwd is rejected when real sync would fail prompt-contract preflight."""
        prompts = tmp_path / "prompts"
        prompts.mkdir()
        source = tmp_path / "bad.py"
        source.write_text(
            "def keep_me():\n"
            "    return True\n\n"
            "def missing_from_context():\n"
            "    return False\n",
            encoding="utf-8",
        )
        (prompts / "bad_python.prompt").write_text(
            '<pdd-interface>{"type":"module","module":{"functions":['
            '{"name":"keep_me","signature":"()","returns":"bool"},'
            '{"name":"missing_from_context","signature":"()","returns":"bool"}'
            "]}}</pdd-interface>\n"
            "% Goal\n"
            "Preserve this module.\n"
            '<include select="def:keep_me">bad.py</include>\n',
            encoding="utf-8",
        )
        (tmp_path / "architecture.json").write_text(
            json.dumps(
                [
                    {
                        "filename": "bad_python.prompt",
                        "filepath": "bad.py",
                        "interface": {
                            "type": "module",
                            "module": {
                                "functions": [
                                    {"name": "keep_me"},
                                    {"name": "missing_from_context"},
                                ]
                            },
                        },
                    }
                ]
            ),
            encoding="utf-8",
        )

        mock_dry_run = MagicMock(return_value=(True, ""))
        mock_llm = MagicMock(return_value=(True, tmp_path, 0.02, ""))
        monkeypatch.setattr("pdd.agentic_sync._resolve_module_cwd", lambda *_, **__: tmp_path)
        monkeypatch.setattr("pdd.agentic_sync._run_single_dry_run", mock_dry_run)
        monkeypatch.setattr("pdd.agentic_sync._llm_fix_dry_run_failure", mock_llm)

        all_valid, cwds, _targets, errors, cost = _run_dry_run_validation(
            ["bad"], tmp_path, quiet=True
        )

        assert all_valid is False
        assert cwds == {}
        assert cost == 0.0
        assert len(errors) == 1
        assert "bad: prompt contract preflight failed" in errors[0]
        assert "missing_from_context" in errors[0]
        mock_dry_run.assert_called_once_with(
            "bad", tmp_path, quiet=True, local=False
        )
        mock_llm.assert_not_called()

    def test_dry_run_success_allows_legacy_no_self_include_prompt_contract(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ):
        """Legacy prompt-local interfaces without self-includes remain syncable."""
        prompts = tmp_path / "prompts"
        prompts.mkdir()
        (tmp_path / "legacy.py").write_text(
            "def keep_me():\n"
            "    return True\n",
            encoding="utf-8",
        )
        (prompts / "legacy_python.prompt").write_text(
            '<pdd-interface>{"type":"module","module":{"functions":['
            '{"name":"keep_me","signature":"()","returns":"bool"}'
            "]}}</pdd-interface>\n"
            "% Goal\n"
            "Preserve this legacy module.\n",
            encoding="utf-8",
        )
        (tmp_path / "architecture.json").write_text(
            json.dumps(
                [
                    {
                        "filename": "legacy_python.prompt",
                        "filepath": "legacy.py",
                        "interface": {
                            "type": "module",
                            "module": {"functions": [{"name": "keep_me"}]},
                        },
                    }
                ]
            ),
            encoding="utf-8",
        )

        monkeypatch.setattr("pdd.agentic_sync._resolve_module_cwd", lambda *_, **__: tmp_path)
        monkeypatch.setattr("pdd.agentic_sync._run_single_dry_run", lambda *a, **k: (True, ""))

        all_valid, cwds, _targets, errors, cost = _run_dry_run_validation(
            ["legacy"], tmp_path, quiet=True
        )

        assert all_valid is True
        assert cwds == {"legacy": tmp_path}
        assert errors == []
        assert cost == 0.0

    def test_dry_run_success_allows_changed_no_self_include_prompt_contract(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ):
        """Changed prompt-local contracts do not need output self-includes."""
        prompts = tmp_path / "prompts"
        prompts.mkdir()
        (tmp_path / "changed.py").write_text(
            "def keep_me():\n"
            "    return True\n",
            encoding="utf-8",
        )
        (prompts / "changed_python.prompt").write_text(
            '<pdd-interface>{"type":"module","module":{"functions":['
            '{"name":"keep_me","signature":"()","returns":"bool"}'
            "]}}</pdd-interface>\n"
            "% Goal\n"
            "Preserve this changed module.\n",
            encoding="utf-8",
        )
        (tmp_path / "architecture.json").write_text(
            json.dumps(
                [
                    {
                        "filename": "changed_python.prompt",
                        "filepath": "changed.py",
                        "interface": {
                            "type": "module",
                            "module": {"functions": [{"name": "keep_me"}]},
                        },
                    }
                ]
            ),
            encoding="utf-8",
        )

        monkeypatch.setattr("pdd.agentic_sync._resolve_module_cwd", lambda *_, **__: tmp_path)
        monkeypatch.setattr("pdd.agentic_sync._run_single_dry_run", lambda *a, **k: (True, ""))
        monkeypatch.setattr(
            "pdd.agentic_sync._prompt_contract_strict_self_context_required",
            lambda *a, **k: True,
        )

        all_valid, cwds, _targets, errors, cost = _run_dry_run_validation(
            ["changed"], tmp_path, quiet=True
        )

        assert all_valid is True
        assert cwds == {"changed": tmp_path}
        assert cost == 0.0
        assert errors == []


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
    def test_all_synced_operation_filtered_out(self, mock_pddrc_file, mock_config, mock_detect, mock_determine):
        """Module with operation='all_synced' is also a no-op."""
        cwd = Path("/project")
        mock_pddrc_file.return_value = cwd / ".pddrc"
        mock_config.return_value = {"contexts": {"default": {"defaults": {"prompts_dir": "prompts"}}}}
        mock_detect.return_value = {"python": Path("prompts/mod_a_python.prompt")}

        decision = MagicMock()
        decision.operation = "all_synced"
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

    # --- Issue #1128: nested .pddrc config propagation ---

    @patch("pdd.agentic_sync.sync_determine_operation")
    @patch("pdd.agentic_sync._detect_languages_with_context")
    def test_nested_cwd_uses_nested_pddrc_for_prompts_dir(
        self, mock_detect_lang, mock_determine, tmp_path
    ):
        """_resolve_module_cwd + _filter_already_synced integration: nested .pddrc must
        provide the correct prompts_dir and context_name to sync_determine_operation.

        Bug #1128: _resolve_module_cwd previously short-circuited when root .pddrc
        existed and returned project_root. _filter_already_synced then called
        _find_pddrc_file(project_root) which found the root .pddrc, context detection
        returned None, and the wrong prompts_dir was used. After the fix,
        _resolve_module_cwd returns nested_dir, so _find_pddrc_file finds the nested
        .pddrc with the correct context.
        """
        import yaml
        # Root .pddrc — does NOT have a "services" context
        (tmp_path / ".pddrc").write_text(yaml.dump({"contexts": {
            "extensions-github_pdd_app": {
                "paths": ["extensions/github_pdd_app/**"],
                "defaults": {"prompts_dir": "extensions/github_pdd_app/prompts"},
            },
        }}))
        # Nested .pddrc — has the "services" context
        nested_dir = tmp_path / "extensions" / "github_pdd_app"
        nested_dir.mkdir(parents=True)
        (nested_dir / ".pddrc").write_text(yaml.dump({"contexts": {
            "services": {
                "paths": ["src/services/**"],
                "defaults": {"prompts_dir": "prompts/src/services"},
            },
        }}))

        mock_detect_lang.return_value = {"python": Path("prompts/src/services/solving_orchestrator_python.prompt")}
        decision = MagicMock()
        decision.operation = "nothing"
        mock_determine.return_value = decision

        basename = "src/services/solving_orchestrator"
        # Use _resolve_module_cwd to get the cwd (exercises the buggy path)
        resolved_cwd = _resolve_module_cwd(basename, tmp_path)
        result = _filter_already_synced(
            [basename],
            {basename: resolved_cwd},
            quiet=True,
        )

        # Verify sync_determine_operation was called with the nested prompts_dir
        mock_determine.assert_called()
        call_kwargs = mock_determine.call_args.kwargs
        expected_prompts_dir = str(nested_dir / "prompts/src/services")
        assert call_kwargs["prompts_dir"] == expected_prompts_dir, (
            f"Expected prompts_dir={expected_prompts_dir}, got {call_kwargs['prompts_dir']}. "
            "Nested .pddrc prompts_dir must propagate to sync_determine_operation."
        )
        assert call_kwargs["context_override"] == "services", (
            f"Expected context_override='services', got {call_kwargs['context_override']}. "
            "Nested context name must propagate to sync_determine_operation."
        )

    @patch("pdd.agentic_sync.sync_determine_operation")
    @patch("pdd.agentic_sync._detect_languages_with_context")
    def test_nested_config_filters_correctly_via_full_pipeline(
        self, mock_detect_lang, mock_determine, tmp_path
    ):
        """End-to-end: _resolve_module_cwd → _filter_already_synced with nested config.

        Before fix: _resolve_module_cwd returns project_root → _find_pddrc_file finds root
        .pddrc → context detection returns None → prompts_dir defaults to root prompts/ →
        wrong prompts_dir passed to sync_determine_operation.
        After fix: _resolve_module_cwd returns nested_dir → _find_pddrc_file finds nested
        .pddrc → context detected → correct prompts_dir → correct fingerprint check.
        """
        import yaml
        # Root .pddrc — catch-all default context
        (tmp_path / ".pddrc").write_text(yaml.dump({"contexts": {
            "default": {
                "paths": ["**"],
                "defaults": {"prompts_dir": "prompts"},
            },
        }}))
        # Nested .pddrc with specific worker context
        nested_dir = tmp_path / "extensions" / "github_pdd_app"
        nested_dir.mkdir(parents=True)
        (nested_dir / ".pddrc").write_text(yaml.dump({"contexts": {
            "pdd_executor_pkg": {
                "paths": ["src/workers/pdd_executor/**"],
                "defaults": {"prompts_dir": "prompts/src/workers/pdd_executor"},
            },
        }}))

        mock_detect_lang.return_value = {"python": Path("prompts/src/workers/pdd_executor/runner_python.prompt")}
        decision = MagicMock()
        decision.operation = "nothing"
        mock_determine.return_value = decision

        basename = "src/workers/pdd_executor/runner"
        # Use _resolve_module_cwd to get the cwd (exercises the buggy path)
        resolved_cwd = _resolve_module_cwd(basename, tmp_path)
        result = _filter_already_synced(
            [basename],
            {basename: resolved_cwd},
            quiet=True,
        )

        # Verify the correct nested prompts_dir was used
        mock_determine.assert_called()
        call_kwargs = mock_determine.call_args.kwargs
        expected_prompts_dir = str(nested_dir / "prompts/src/workers/pdd_executor")
        assert call_kwargs["prompts_dir"] == expected_prompts_dir, (
            f"Expected prompts_dir={expected_prompts_dir}, got {call_kwargs['prompts_dir']}. "
            "Nested config must provide correct prompts_dir through the full pipeline."
        )


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
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
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
        """Prompts under a nested project's prompts/ keep the owning-project prefix.

        Extension prompts live at ``<project>/prompts/...`` rather than the repo
        root. The module key MUST be the full repo-root-relative path
        (``extensions/github_pdd_app/pdd_executor``), keeping the owning-project
        prefix — not the short ``pdd_executor`` that loses the project and makes
        the resolver run from the repo root with the wrong context (#1675).
        """
        diff_output = (
            "extensions/github_pdd_app/prompts/pdd_executor_Python.prompt\n"
            "extensions/github_pdd_app/prompts/src/worker_app_Python.prompt\n"
        )
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            result = _detect_modules_from_branch_diff(Path("/fake/project"))
        assert result == [
            "extensions/github_pdd_app/pdd_executor",
            "extensions/github_pdd_app/src/worker_app",
        ]


class TestBranchDiffIsRuntimeLlmOnly:
    """Issue #1396: helper that detects runtime-template-only branch diffs."""

    def test_true_when_all_prompt_changes_are_runtime_llm(self):
        """All ``.prompt`` changes are ``_LLM.prompt`` → True (no LLM call needed)."""
        diff_output = (
            "M\tpdd/prompts/agentic_sync_identify_modules_LLM.prompt\n"
            "A\tpdd/prompts/agentic_split_step4_propose_options_LLM.prompt\n"
        )
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            assert _branch_diff_is_runtime_llm_only(Path("/fake/project")) is True

    def test_false_when_real_prompt_change_present(self):
        """Mixed changes (one real prompt + one runtime template) → False."""
        diff_output = (
            "M\tprompts/ci_validation_python.prompt\n"
            "M\tpdd/prompts/agentic_sync_identify_modules_LLM.prompt\n"
        )
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            assert _branch_diff_is_runtime_llm_only(Path("/fake/project")) is False

    def test_false_when_no_prompt_changes(self):
        """Diff with only non-prompt files → False (defer to LLM fallback)."""
        diff_output = "M\tpdd/agentic_common.py\nM\ttests/test_agentic_common.py\n"
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            assert _branch_diff_is_runtime_llm_only(Path("/fake/project")) is False

    def test_false_when_runtime_prompt_and_non_prompt_change_present(self):
        """A runtime prompt plus source change is inconclusive, not a no-op."""
        diff_output = (
            "M\tpdd/prompts/agentic_sync_identify_modules_LLM.prompt\n"
            "M\tpdd/agentic_sync.py\n"
        )
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            assert _branch_diff_is_runtime_llm_only(Path("/fake/project")) is False

    def test_false_on_main_branch(self):
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(returncode=0, stdout="main\n", stderr="")
            assert _branch_diff_is_runtime_llm_only(Path("/fake/project")) is False

    def test_false_on_git_failure(self):
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = FileNotFoundError("git not found")
            assert _branch_diff_is_runtime_llm_only(Path("/fake/project")) is False

    def test_false_when_runtime_prompt_mixed_with_code_file(self):
        """Runtime ``_LLM.prompt`` change combined with a non-prompt source
        file (e.g. ``pdd/agentic_sync.py``) → False.

        Regression for issue #1396 review feedback: previously the helper
        ignored non-prompt files when deciding "runtime-only" and returned
        True, which caused ``run_agentic_sync`` to short-circuit to a no-op
        and silently skip the real code change.
        """
        diff_output = (
            "M\tpdd/prompts/foo_LLM.prompt\n"
            "M\tpdd/agentic_sync.py\n"
        )
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            assert _branch_diff_is_runtime_llm_only(Path("/fake/project")) is False

    def test_false_when_runtime_prompt_mixed_with_test_file(self):
        """Runtime ``_LLM.prompt`` change combined with a test file → False."""
        diff_output = (
            "M\tpdd/prompts/foo_LLM.prompt\n"
            "M\ttests/test_foo.py\n"
        )
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            assert _branch_diff_is_runtime_llm_only(Path("/fake/project")) is False

    def test_false_when_runtime_prompt_modified_and_real_file_deleted(self):
        """Runtime ``_LLM.prompt`` modification alongside the deletion of a real
        file (e.g. a non-LLM prompt or Python source file) → False.

        Regression for issue #1396 review round 4 feedback: previously the
        helper used ``--diff-filter=ACMR`` which excluded deletions, so a
        branch that modified only ``*_LLM.prompt`` among ACMR files but also
        deleted a real prompt/code/test/config file would incorrectly return
        True and ``run_agentic_sync`` would short-circuit to a no-op success,
        silently skipping the deletion.

        The fix uses ``--diff-filter=ACMRD`` (include deletions); the deleted
        non-runtime file fails the runtime-template predicate so the helper
        correctly returns False and defers to the LLM fallback.
        """
        # Deletion of a real (non-_LLM) prompt file: not runtime-only.
        diff_output = (
            "M\tpdd/prompts/foo_LLM.prompt\n"
            "D\tpdd/prompts/foo_python.prompt\n"
        )
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            assert _branch_diff_is_runtime_llm_only(Path("/fake/project")) is False

        # Deletion of a Python source file: not runtime-only.
        diff_output = (
            "M\tpdd/prompts/foo_LLM.prompt\n"
            "D\tpdd/some_module.py\n"
        )
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            assert _branch_diff_is_runtime_llm_only(Path("/fake/project")) is False

    def test_diff_filter_includes_deletions(self):
        """Verify the helper invokes ``git diff`` with ``--diff-filter=ACMRD``
        so deleted files are surfaced and evaluated against the
        runtime-template predicate (issue #1396 review round 4)."""
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout="", stderr=""),
            ]
            _branch_diff_is_runtime_llm_only(Path("/fake/project"))
            # Second subprocess.run call is the git diff invocation.
            assert mock_run.call_count == 2
            diff_call_args = mock_run.call_args_list[1].args[0]
            assert "--name-status" in diff_call_args
            assert "--diff-filter=ACMRD" in diff_call_args

    def test_false_when_real_prompt_renamed_to_runtime_prompt(self):
        """A real sync prompt renamed to ``*_LLM.prompt`` is not runtime-only.

        ``git diff --name-only`` reports only the destination path for renames,
        so it would make this look like a pure runtime-template change. The
        helper must use name-status data and reject the rename because the old
        path is a real sync prompt.
        """
        diff_output = "R100\tpdd/prompts/foo_python.prompt\tpdd/prompts/foo_LLM.prompt\n"
        with patch("pdd.agentic_sync.subprocess.run") as mock_run:
            mock_run.side_effect = [
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            assert _branch_diff_is_runtime_llm_only(Path("/fake/project")) is False


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
        mock_dry_run.return_value = (True, {}, {}, [], 0.0)

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
        mock_dry_run.return_value = (True, {}, {}, [], 0.0)

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


class TestRuntimeLlmTemplateNoop:
    """Issue #1396 / #1388 regression tests for ``run_agentic_sync``.

    These cover the actual issue shape end-to-end (not just the classifier and
    filter unit predicates):

    * An LLM identify response that lists only ``*_LLM`` modules must complete
      as a successful no-op without invoking dry-run validation or the runner.
    * A mixed identify response (one runtime template + one real module) must
      drop the runtime template and only the real module reaches dry-run /
      runner.
    * A branch diff that contains exclusively ``*_LLM.prompt`` changes must
      short-circuit to a deterministic no-op without calling the identify LLM.
    """

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch("pdd.agentic_sync._branch_diff_is_runtime_llm_only", return_value=False)
    @patch("pdd.agentic_sync.load_prompt_template", return_value="template {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_llm_returns_only_runtime_llm_modules_is_noop_success(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        mock_load_prompt,
        mock_branch_runtime_only,
        mock_branch_diff,
        mock_dry_run,
        mock_runner_cls,
    ):
        """LLM returns only ``*_LLM`` basenames → success no-op, runner not called."""
        issue_data = {"title": "Test", "body": "Touch runtime templates", "comments_url": ""}
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        # Architecture only contains the runtime LLM template entry.
        mock_load_arch.return_value = (
            [{"filename": "agentic_sync_identify_modules_LLM.prompt", "dependencies": []}],
            Path("/tmp/architecture.json"),
        )
        mock_agentic_task.return_value = (
            True,
            'MODULES_TO_SYNC: ["agentic_sync_identify_modules_LLM"]\nDEPS_VALID: true',
            0.04,
            "anthropic",
        )

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1396", quiet=True
        )

        assert success is True
        assert "All modules are already synced" in msg
        # The identify LLM was called (we got past branch diff), but no
        # downstream work happened: dry-run and the runner are untouched.
        mock_agentic_task.assert_called_once()
        mock_dry_run.assert_not_called()
        mock_runner_cls.assert_not_called()
        # Cost is just the LLM identify cost; runner cost is zero.
        assert cost == pytest.approx(0.04)
        assert model == "anthropic"

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult({"foo": []}, []),
    )
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch("pdd.agentic_sync._branch_diff_is_runtime_llm_only", return_value=False)
    @patch("pdd.agentic_sync.load_prompt_template", return_value="template {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_mixed_runtime_and_real_only_real_reaches_runner(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        mock_load_prompt,
        mock_branch_runtime_only,
        mock_branch_diff,
        mock_build_graph,
        mock_dry_run,
        mock_runner_cls,
    ):
        """Mixed runtime + real → only the real module reaches dry-run + runner."""
        issue_data = {"title": "Test", "body": "Mix", "comments_url": ""}
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (
            [
                {"filename": "agentic_sync_identify_modules_LLM.prompt", "dependencies": []},
                {"filename": "foo_python.prompt", "dependencies": []},
            ],
            Path("/tmp/architecture.json"),
        )
        # LLM returns one runtime template basename (must be dropped) and one
        # real module (must reach validation and the runner).
        mock_agentic_task.return_value = (
            True,
            'MODULES_TO_SYNC: ["agentic_sync_identify_modules_LLM", "foo"]\nDEPS_VALID: true',
            0.06,
            "anthropic",
        )
        mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, {"foo": "foo"}, [], 0.0)

        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 1 modules synced successfully", 0.10)
        mock_runner_cls.return_value = mock_runner

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1396", quiet=True
        )

        assert success is True
        # Dry-run validation was called with only the real module.
        mock_dry_run.assert_called_once()
        dry_run_kwargs = mock_dry_run.call_args.kwargs
        dry_run_args = mock_dry_run.call_args.args
        dry_run_modules = dry_run_kwargs.get("modules") if "modules" in dry_run_kwargs else (
            dry_run_args[0] if dry_run_args else None
        )
        assert dry_run_modules == ["foo"]
        # The runner was constructed with only the real module as a basename.
        runner_kwargs = mock_runner_cls.call_args[1]
        assert runner_kwargs["basenames"] == ["foo"]
        mock_runner.run.assert_called_once()

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch("pdd.agentic_sync._branch_diff_is_runtime_llm_only", return_value=True)
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_branch_diff_runtime_llm_only_short_circuits_without_llm(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_branch_runtime_only,
        mock_branch_diff,
        mock_agentic_task,
        mock_dry_run,
        mock_runner_cls,
    ):
        """Branch diff containing only ``*_LLM.prompt`` changes → deterministic
        no-op success; identify LLM, dry-run, and runner are never called."""
        issue_data = {"title": "Test", "body": "Only runtime templates", "comments_url": ""}
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (
            [{"filename": "agentic_sync_identify_modules_LLM.prompt", "dependencies": []}],
            Path("/tmp/architecture.json"),
        )

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1396", quiet=True
        )

        assert success is True
        assert "All modules are already synced" in msg
        # No LLM call, no dry-run validation, no runner.
        mock_agentic_task.assert_not_called()
        mock_dry_run.assert_not_called()
        mock_runner_cls.assert_not_called()
        # Zero cost since nothing was billed.
        assert cost == 0.0

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch("pdd.agentic_sync._branch_diff_is_runtime_llm_only", return_value=False)
    @patch("pdd.agentic_sync.load_prompt_template", return_value="template {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_empty_llm_modules_without_runtime_only_diff_is_failure(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        mock_load_prompt,
        mock_branch_runtime_only,
        mock_branch_diff,
        mock_dry_run,
        mock_runner_cls,
    ):
        """Empty ``MODULES_TO_SYNC`` from the LLM, when the diff is *not*
        runtime-template-only, must be treated as a failure rather than a
        silent no-op.

        Regression for issue #1396 review feedback: previously any empty LLM
        selection was a successful no-op, which could mask legitimate identify
        failures (e.g. parsing drops the result, or the model fails to infer
        modules for a normal issue).
        """
        issue_data = {"title": "Test", "body": "Real change", "comments_url": ""}
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (
            [{"filename": "foo_python.prompt", "dependencies": []}],
            Path("/tmp/architecture.json"),
        )
        # LLM returns empty MODULES_TO_SYNC, but the branch diff is *not*
        # runtime-template-only (mock_branch_runtime_only returns False).
        mock_agentic_task.return_value = (
            True,
            "MODULES_TO_SYNC: []\nDEPS_VALID: true",
            0.04,
            "anthropic",
        )

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1396", quiet=True
        )

        assert success is False
        assert "no modules to sync" in msg.lower()
        # No dry-run, no runner — we failed before reaching them.
        mock_dry_run.assert_not_called()
        mock_runner_cls.assert_not_called()


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

    def test_rejects_runtime_llm_template_basenames(self):
        """Runtime *_LLM.prompt templates are not syncable modules.

        Hard boundary for issue #1396: an architecture entry whose only file
        is a `_LLM.prompt` runtime template must not contribute either the
        bare `_LLM` basename or the stripped owner-style basename to the
        valid set. Both forms are guaranteed to fail in `pdd sync` because
        runtime LLM templates are consumed directly by their owning code
        module via `load_prompt_template(...)` and have no language-suffixed
        sync companion.
        """
        architecture = [
            {"filename": "agentic_bug_step10_verify_LLM.prompt"},
        ]

        # The bare `_LLM` basename must be rejected.
        valid, invalid = _filter_invalid_basenames(
            ["agentic_bug_step10_verify_LLM"], architecture
        )
        assert valid == []
        assert invalid == ["agentic_bug_step10_verify_LLM"]

        # The stripped owner-style basename must also be rejected when the
        # only architecture entry is a runtime `_LLM.prompt` template.
        valid, invalid = _filter_invalid_basenames(
            ["agentic_bug_step10_verify"], architecture
        )
        assert valid == []
        assert invalid == ["agentic_bug_step10_verify"]

    def test_returns_all_when_no_architecture(self):
        """If architecture is None, can't validate — keep all modules."""
        modules = ["mod_a", "hallucinated_mod"]

        valid, invalid = _filter_invalid_basenames(modules, None)

        assert valid == ["mod_a", "hallucinated_mod"]
        assert invalid == []

    def test_rejects_runtime_llm_even_without_architecture(self):
        """The runtime-template boundary applies even when architecture is absent."""
        modules = ["agentic_sync_identify_modules_LLM", "mod_a"]

        valid, invalid = _filter_invalid_basenames(modules, None)

        assert valid == ["mod_a"]
        assert invalid == ["agentic_sync_identify_modules_LLM"]

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

    def test_accepts_path_qualified_even_with_ambiguous_tail(self):
        """Path-qualified basenames are accepted even when the bare tail appears
        multiple times in architecture — the path itself disambiguates.

        Previously this rejected 'commands/auth' because 'auth' appeared twice,
        but the directory path already tells pdd sync which module is meant.
        Changed in #826 fix: path qualification IS disambiguation."""
        architecture = [
            {"filename": "auth_python.prompt"},   # could be commands/auth
            {"filename": "auth_python.prompt"},   # could be server/routes/auth
            {"filename": "cli_python.prompt"},    # unique basename
        ]
        modules = [
            "commands/auth",        # path-qualified — disambiguated by path
            "core/cli",             # path-qualified — also fine
        ]

        valid, invalid = _filter_invalid_basenames(modules, architecture)

        assert "commands/auth" in valid, (
            "Path-qualified basenames should be accepted — the path disambiguates"
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
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult({"foo": []}, []),
    )
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
        mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, {"foo": "foo"}, [], 0.0)

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

    def test_discovers_entries_from_nested_architecture_files(self, tmp_path):
        """New entries in nested architecture files (e.g. frontend/architecture.json)
        on the PR branch should be merged into the combined architecture.

        Regression test for promptdriven/pdd_cloud#826: pdd change created
        GitHubAppCTA in frontend/architecture.json but _augment_architecture only
        fetched root architecture.json, so the new module was rejected as invalid.
        """
        local_arch = [
            {"filename": "Sidebar_TypescriptReact.prompt", "filepath": "src/components/layout/Sidebar.tsx"},
        ]
        root_pr_arch = [
            {"filename": "Sidebar_TypescriptReact.prompt", "filepath": "src/components/layout/Sidebar.tsx"},
        ]
        frontend_pr_arch = [
            {"filename": "Sidebar_TypescriptReact.prompt", "filepath": "src/components/layout/Sidebar.tsx"},
            {"filename": "GitHubAppCTA_TypescriptReact.prompt", "filepath": "src/components/dashboard/GitHubAppCTA.tsx"},
        ]

        # Create a frontend/architecture.json on disk so find_architecture_for_project discovers it
        (tmp_path / "architecture.json").write_text(json.dumps(root_pr_arch))
        (tmp_path / "frontend").mkdir()
        (tmp_path / "frontend" / "architecture.json").write_text(json.dumps(frontend_pr_arch))

        def fake_git_show(args, **kwargs):
            """Return different architecture.json content based on the git show path."""
            ref_path = args[2]  # e.g. "origin/change/issue-836:architecture.json"
            if ref_path.endswith(":architecture.json"):
                mock = MagicMock(returncode=0, stdout=json.dumps(root_pr_arch), stderr="")
                return mock
            elif ref_path.endswith(":frontend/architecture.json"):
                mock = MagicMock(returncode=0, stdout=json.dumps(frontend_pr_arch), stderr="")
                return mock
            raise subprocess.CalledProcessError(128, "git show")

        with patch("pdd.agentic_sync.subprocess.run", side_effect=fake_git_show):
            result = _augment_architecture_from_pr_branch(local_arch, tmp_path, 836)

        filenames = [e["filename"] for e in result]
        assert "Sidebar_TypescriptReact.prompt" in filenames, "Existing entry should be preserved"
        assert "GitHubAppCTA_TypescriptReact.prompt" in filenames, (
            "New entry from frontend/architecture.json on PR branch must be discovered — "
            "currently only root architecture.json is fetched"
        )


    # --- Issue #1609: fallback branch (change/issue-N-job-*) support ---

    def test_adds_new_entries_from_fallback_branch_when_canonical_missing(self, tmp_path):
        """New entries should be picked up from a fallback change/issue-N-job-* branch
        when the canonical change/issue-N branch does not exist (clean-restart scenario).

        Regression test for Issue #1609: _augment_architecture_from_pr_branch hardcodes
        origin/change/issue-N and silently swallows CalledProcessError when that ref
        is missing, so new-module entries from the fallback branch are never merged.
        """
        local_arch = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py"},
        ]
        fallback_arch = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py"},
            {"filename": "new_module_python.prompt", "filepath": "pdd/new_module.py"},
        ]

        def fake_subprocess(args, **kwargs):
            subcmd = args[1]
            if subcmd == "for-each-ref":
                return MagicMock(returncode=0, stdout="origin/change/issue-1609-job-abc123\n", stderr="")
            # subcmd == "show"
            ref_path = args[2]
            if "issue-1609-job-abc123:" in ref_path:
                return MagicMock(returncode=0, stdout=json.dumps(fallback_arch), stderr="")
            # canonical branch does not exist
            raise subprocess.CalledProcessError(128, "git show")

        with patch("pdd.agentic_sync.subprocess.run", side_effect=fake_subprocess):
            result = _augment_architecture_from_pr_branch(local_arch, tmp_path, 1609)

        filenames = [e["filename"] for e in result]
        assert "foo_python.prompt" in filenames, "Existing entry should be preserved"
        assert "new_module_python.prompt" in filenames, (
            "New module on fallback branch change/issue-1609-job-abc123 must be discovered — "
            "currently _augment_architecture_from_pr_branch only checks the canonical branch "
            "and silently fails when it does not exist"
        )

    def test_merges_entries_from_both_canonical_and_fallback_branches(self, tmp_path):
        """When both canonical and fallback branches exist, unique new entries from
        each should be merged into the architecture.

        Regression test for Issue #1609.
        """
        local_arch: list = []
        canonical_arch = [{"filename": "module_a_python.prompt", "filepath": "pdd/module_a.py"}]
        fallback_arch = [{"filename": "module_b_python.prompt", "filepath": "pdd/module_b.py"}]

        def fake_subprocess(args, **kwargs):
            subcmd = args[1]
            if subcmd == "for-each-ref":
                return MagicMock(returncode=0, stdout="origin/change/issue-1609-job-xyz\n", stderr="")
            ref_path = args[2]
            if "issue-1609-job-xyz:" in ref_path:
                return MagicMock(returncode=0, stdout=json.dumps(fallback_arch), stderr="")
            # canonical branch (issue-1609:) succeeds
            return MagicMock(returncode=0, stdout=json.dumps(canonical_arch), stderr="")

        with patch("pdd.agentic_sync.subprocess.run", side_effect=fake_subprocess):
            result = _augment_architecture_from_pr_branch(local_arch, tmp_path, 1609)

        filenames = [e["filename"] for e in result]
        assert "module_a_python.prompt" in filenames, "Entry from canonical branch should be merged"
        assert "module_b_python.prompt" in filenames, (
            "Entry from fallback branch change/issue-1609-job-xyz must also be merged — "
            "currently _augment_architecture_from_pr_branch ignores fallback branches"
        )
        assert len(filenames) == 2, f"Expected exactly 2 entries, got {len(filenames)}: {filenames}"

    def test_no_fallback_branches_returns_original_architecture(self, tmp_path):
        """When git for-each-ref returns no fallback branches and the canonical branch
        also fails, the architecture is returned unchanged (non-regression).

        Regression test for Issue #1609.
        """
        local_arch = [{"filename": "foo_python.prompt"}]

        def fake_subprocess(args, **kwargs):
            subcmd = args[1]
            if subcmd == "for-each-ref":
                return MagicMock(returncode=0, stdout="", stderr="")
            # canonical branch does not exist either
            raise subprocess.CalledProcessError(128, "git show")

        with patch("pdd.agentic_sync.subprocess.run", side_effect=fake_subprocess):
            result = _augment_architecture_from_pr_branch(local_arch, tmp_path, 1609)

        assert result == local_arch, (
            "When no branches (canonical or fallback) exist, architecture should be returned unchanged"
        )

    def test_fallback_branch_does_not_duplicate_entries_already_in_canonical(self, tmp_path):
        """When the fallback branch repeats entries from the canonical branch, each
        filename should appear exactly once in the merged result.

        Regression test for Issue #1609.
        """
        local_arch: list = []
        canonical_arch = [
            {"filename": "shared_python.prompt", "filepath": "pdd/shared.py"},
            {"filename": "only_canonical_python.prompt", "filepath": "pdd/only_canonical.py"},
        ]
        fallback_arch = [
            {"filename": "shared_python.prompt", "filepath": "pdd/shared.py"},
            {"filename": "only_fallback_python.prompt", "filepath": "pdd/only_fallback.py"},
        ]

        def fake_subprocess(args, **kwargs):
            subcmd = args[1]
            if subcmd == "for-each-ref":
                return MagicMock(returncode=0, stdout="origin/change/issue-1609-job-abc123\n", stderr="")
            ref_path = args[2]
            if "issue-1609-job-abc123:" in ref_path:
                return MagicMock(returncode=0, stdout=json.dumps(fallback_arch), stderr="")
            # canonical branch succeeds
            return MagicMock(returncode=0, stdout=json.dumps(canonical_arch), stderr="")

        with patch("pdd.agentic_sync.subprocess.run", side_effect=fake_subprocess):
            result = _augment_architecture_from_pr_branch(local_arch, tmp_path, 1609)

        filenames = [e["filename"] for e in result]
        assert "shared_python.prompt" in filenames
        assert "only_canonical_python.prompt" in filenames
        assert "only_fallback_python.prompt" in filenames, (
            "Entry unique to fallback branch must be merged — "
            "currently only canonical branch is checked"
        )
        assert filenames.count("shared_python.prompt") == 1, (
            "shared_python.prompt must appear exactly once (no duplication across branches)"
        )

    def test_only_newest_fallback_branch_is_consulted_when_multiple_exist(self, tmp_path):
        """Only the newest clean-restart fallback branch should be consulted; entries
        from older/abandoned change/issue-N-job-* branches must NOT be merged.

        Regression test for the Issue #1609 follow-up: clean-restart creates a fresh
        change/issue-N-job-<slug> branch per attempt, so older job branches are
        abandoned. Merging architecture entries from every historical fallback ref can
        revive stale module names that then wrongly pass _filter_invalid_basenames, and
        makes the work scale with the number of historical remote refs. The lookup is
        bounded to the most recently committed fallback ref (git for-each-ref is sorted
        by -committerdate, so the first listed ref is newest).
        """
        local_arch = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py"},
        ]
        newest_arch = [
            {"filename": "active_module_python.prompt", "filepath": "pdd/active_module.py"},
        ]
        stale_arch = [
            {"filename": "stale_module_python.prompt", "filepath": "pdd/stale_module.py"},
        ]

        def fake_subprocess(args, **kwargs):
            subcmd = args[1]
            if subcmd == "for-each-ref":
                # --sort=-committerdate => newest first
                return MagicMock(
                    returncode=0,
                    stdout=(
                        "origin/change/issue-1609-job-newest\n"
                        "origin/change/issue-1609-job-stale\n"
                    ),
                    stderr="",
                )
            ref_path = args[2]
            if "issue-1609-job-newest:" in ref_path:
                return MagicMock(returncode=0, stdout=json.dumps(newest_arch), stderr="")
            if "issue-1609-job-stale:" in ref_path:
                return MagicMock(returncode=0, stdout=json.dumps(stale_arch), stderr="")
            # canonical branch does not exist (clean-restart scenario)
            raise subprocess.CalledProcessError(128, "git show")

        with patch("pdd.agentic_sync.subprocess.run", side_effect=fake_subprocess):
            result = _augment_architecture_from_pr_branch(local_arch, tmp_path, 1609)

        filenames = [e["filename"] for e in result]
        assert "foo_python.prompt" in filenames, "Existing entry should be preserved"
        assert "active_module_python.prompt" in filenames, (
            "Module on the newest fallback branch must be discovered"
        )
        assert "stale_module_python.prompt" not in filenames, (
            "Module that only exists on an older/abandoned fallback branch must NOT be "
            "merged — only the newest clean-restart fallback ref should be consulted"
        )

    def test_active_fallback_metadata_wins_over_stale_canonical_on_shared_filename(self, tmp_path):
        """When canonical and the active (newest) fallback branch both define the same
        filename with divergent metadata, the fallback's version must win the dedup, while
        canonical's UNIQUE entries are still merged.

        Clean-restart branches the job fallback from main and abandons the canonical
        branch, so canonical's metadata is stale. The merged architecture feeds
        build_dep_graph_from_architecture_data, so a stale canonical filepath/dependencies
        winning would corrupt the dependency graph. Listing the fallback before canonical
        makes the active branch win on shared filenames; keeping canonical in the list
        means a canonical-only new module is never dropped (no #1609 regression).
        """
        local_arch: list = []
        canonical_arch = [
            {"filename": "shared_python.prompt", "filepath": "pdd/STALE.py", "dependencies": ["stale_dep"]},
            {"filename": "only_canonical_python.prompt", "filepath": "pdd/only_canonical.py"},
        ]
        fallback_arch = [
            {"filename": "shared_python.prompt", "filepath": "pdd/ACTIVE.py", "dependencies": ["active_dep"]},
        ]

        def fake_subprocess(args, **kwargs):
            subcmd = args[1]
            if subcmd == "for-each-ref":
                return MagicMock(returncode=0, stdout="origin/change/issue-1609-job-active\n", stderr="")
            ref_path = args[2]
            if "issue-1609-job-active:" in ref_path:
                return MagicMock(returncode=0, stdout=json.dumps(fallback_arch), stderr="")
            # canonical branch exists but is stale (clean-restart abandoned it)
            return MagicMock(returncode=0, stdout=json.dumps(canonical_arch), stderr="")

        with patch("pdd.agentic_sync.subprocess.run", side_effect=fake_subprocess):
            result = _augment_architecture_from_pr_branch(local_arch, tmp_path, 1609)

        by_name = {e["filename"]: e for e in result}
        assert by_name["shared_python.prompt"]["filepath"] == "pdd/ACTIVE.py", (
            "Active fallback branch's metadata must win the filename-dedup over stale canonical"
        )
        assert by_name["shared_python.prompt"]["dependencies"] == ["active_dep"]
        assert "only_canonical_python.prompt" in by_name, (
            "Entry unique to canonical must still be merged — fallback-first ordering must "
            "not drop canonical-only modules (that would re-open #1609 under-inclusion)"
        )


class TestFilterInvalidBasenamesCodeExtensions:
    """_filter_invalid_basenames must strip code file extensions (.tsx, .ts, .py, etc.)
    from architecture.json filename entries before matching against sync basenames.

    Regression test for promptdriven/pdd_cloud#826: frontend/architecture.json uses
    filename: "GitHubAppCTA.tsx" but sync expects basename "GitHubAppCTA".
    """

    def test_strips_tsx_extension_for_tail_match(self):
        """Architecture entries with .tsx filenames should match bare basenames."""
        architecture = [
            {"filename": "GitHubAppCTA.tsx", "filepath": "src/components/dashboard/GitHubAppCTA.tsx"},
        ]
        modules = ["frontend/components/dashboard/GitHubAppCTA"]
        valid, invalid = _filter_invalid_basenames(modules, architecture)
        assert "frontend/components/dashboard/GitHubAppCTA" in valid, (
            f"Expected GitHubAppCTA to be valid but got invalid={invalid} — "
            ".tsx extension not stripped from architecture filename"
        )

    def test_strips_ts_extension_for_tail_match(self):
        """Architecture entries with .ts filenames should match bare basenames."""
        architecture = [
            {"filename": "github-app-api.ts", "filepath": "src/lib/github-app-api.ts"},
        ]
        modules = ["lib/github-app-api"]
        valid, invalid = _filter_invalid_basenames(modules, architecture)
        assert "lib/github-app-api" in valid

    def test_prompt_filenames_still_use_extract_module(self):
        """Standard .prompt filenames should still use extract_module_from_include."""
        architecture = [
            {"filename": "Sidebar_TypescriptReact.prompt"},
        ]
        modules = ["frontend/components/layout/Sidebar"]
        valid, invalid = _filter_invalid_basenames(modules, architecture)
        assert "frontend/components/layout/Sidebar" in valid

    def test_matches_filepath_when_filename_differs(self):
        """Architecture entries where filename differs from filepath basename.

        Regression test for pdd_cloud#826: dashboard page has
        filename='dashboardPage.tsx' but filepath='src/app/dashboard/page.tsx'.
        The sync basename 'page' should match via the filepath.
        """
        architecture = [
            {"filename": "dashboardPage.tsx", "filepath": "src/app/dashboard/page.tsx"},
            {"filename": "dashboardConnectPage.tsx", "filepath": "src/app/dashboard/connect/page.tsx"},
        ]
        modules = ["frontend/app/dashboard/page"]
        valid, invalid = _filter_invalid_basenames(modules, architecture)
        assert "frontend/app/dashboard/page" in valid, (
            f"Expected page to match via filepath 'src/app/dashboard/page.tsx', got invalid={invalid}"
        )

    def test_path_qualified_basename_accepted_despite_ambiguous_tail(self):
        """Path-qualified basenames are inherently unambiguous — the path disambiguates."""
        architecture = [
            {"filename": "utils.py"},
            {"filename": "utils.ts"},
        ]
        # Path-qualified basename should be accepted even if tail is ambiguous
        # because the directory path already tells us which module is meant
        modules = ["lib/utils"]
        valid, invalid = _filter_invalid_basenames(modules, architecture)
        assert "lib/utils" in valid, (
            "Path-qualified basenames should be accepted — the path disambiguates"
        )

    def test_bare_basename_still_needs_known_match(self):
        """Bare basenames (no path) must exist in known_basenames."""
        architecture = [
            {"filename": "Auth_python.prompt"},
        ]
        modules = ["NonExistent"]
        valid, invalid = _filter_invalid_basenames(modules, architecture)
        assert "NonExistent" in invalid

    def test_extension_stripping_does_not_create_false_positives(self):
        """Stripping .tsx should not match unrelated modules with same stem."""
        architecture = [
            {"filename": "Auth.tsx"},  # a React component
        ]
        # A Python module named "Auth" should still match via tail
        # (this is correct — Auth is unambiguous with count=1)
        modules = ["backend/services/Auth"]
        valid, invalid = _filter_invalid_basenames(modules, architecture)
        assert "backend/services/Auth" in valid


class TestAugmentAndFilterIntegration:
    """Integration test: _augment_architecture_from_pr_branch + _filter_invalid_basenames
    working together for multi-context repos with nested architecture files.

    Reproduces the exact scenario from pdd_cloud#826 where pdd-change created
    GitHubAppCTA in frontend/architecture.json but sync rejected it.
    """

    def test_new_module_in_nested_arch_passes_filter(self, tmp_path):
        """Full pipeline: augment from nested arch on PR branch, then filter basenames."""
        # Simulate main-branch architecture (no GitHubAppCTA)
        # Root arch uses prompt filenames; frontend arch uses code filenames
        root_arch_main = [
            {"filename": "components/layout/Sidebar_TypescriptReact.prompt"},
        ]
        frontend_arch_main = [
            {"filename": "Sidebar.tsx", "filepath": "src/components/layout/Sidebar.tsx"},
        ]

        # Simulate PR branch architecture (GitHubAppCTA added in frontend/)
        root_arch_pr = root_arch_main[:]
        frontend_arch_pr = frontend_arch_main + [
            {"filename": "GitHubAppCTA.tsx", "filepath": "src/components/dashboard/GitHubAppCTA.tsx"},
        ]

        # Set up disk structure for find_architecture_for_project
        (tmp_path / "architecture.json").write_text(json.dumps(root_arch_main))
        (tmp_path / "frontend").mkdir()
        (tmp_path / "frontend" / "architecture.json").write_text(json.dumps(frontend_arch_main))

        # Combined architecture from _load_architecture_json (main branch)
        combined_arch = root_arch_main + frontend_arch_main

        # Step 1: Augment from PR branch
        def fake_git_show(args, **kwargs):
            ref_path = args[2]
            if ref_path.endswith(":architecture.json"):
                return MagicMock(returncode=0, stdout=json.dumps(root_arch_pr), stderr="")
            elif ref_path.endswith(":frontend/architecture.json"):
                return MagicMock(returncode=0, stdout=json.dumps(frontend_arch_pr), stderr="")
            raise subprocess.CalledProcessError(128, "git show")

        with patch("pdd.agentic_sync.subprocess.run", side_effect=fake_git_show):
            augmented = _augment_architecture_from_pr_branch(combined_arch, tmp_path, 836)

        # Step 2: Filter basenames (as branch diff would produce them)
        modules = ["frontend/components/layout/Sidebar", "frontend/components/dashboard/GitHubAppCTA"]
        valid, invalid = _filter_invalid_basenames(modules, augmented)

        assert "frontend/components/layout/Sidebar" in valid, (
            f"Existing module should pass filter, got invalid={invalid}"
        )
        assert "frontend/components/dashboard/GitHubAppCTA" in valid, (
            f"New module from PR branch should pass filter after augmentation, got invalid={invalid}"
        )

    def test_new_module_on_fallback_branch_passes_basename_filter(self, tmp_path):
        """Integration regression test for Issue #1609.

        When a new module is created on a clean-restart fallback branch
        (change/issue-N-job-*), _augment_architecture_from_pr_branch must discover
        and merge the new entry so that _filter_invalid_basenames accepts the basename
        rather than rejecting it as a hallucination.
        """
        local_arch = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py"},
        ]
        fallback_arch = [
            {"filename": "foo_python.prompt", "filepath": "pdd/foo.py"},
            {"filename": "new_module_python.prompt", "filepath": "pdd/new_module.py"},
        ]

        # Set up disk structure so find_architecture_for_project discovers architecture.json
        (tmp_path / "architecture.json").write_text(json.dumps(local_arch))

        def fake_subprocess(args, **kwargs):
            subcmd = args[1]
            if subcmd == "for-each-ref":
                return MagicMock(returncode=0, stdout="origin/change/issue-1609-job-abc123\n", stderr="")
            ref_path = args[2]
            if "issue-1609-job-abc123:" in ref_path:
                return MagicMock(returncode=0, stdout=json.dumps(fallback_arch), stderr="")
            # canonical branch does not exist
            raise subprocess.CalledProcessError(128, "git show")

        with patch("pdd.agentic_sync.subprocess.run", side_effect=fake_subprocess):
            augmented = _augment_architecture_from_pr_branch(list(local_arch), tmp_path, 1609)

        # Simulate the sync pipeline: basename filter runs immediately after augmentation
        modules_to_sync = ["foo", "new_module"]
        valid, invalid = _filter_invalid_basenames(modules_to_sync, augmented)

        assert "foo" in valid, f"Existing module should pass filter, got invalid={invalid}"
        assert "new_module" in valid, (
            f"New module on fallback branch should pass filter after augmentation — "
            f"currently augmentation misses the fallback branch so new_module appears in invalid={invalid}"
        )
        assert invalid == [], (
            f"No basenames should be rejected as hallucinations, got invalid={invalid}"
        )


# --- Issue #1256: Dict-format PR architecture tolerance test ---


def test_augment_architecture_from_pr_branch_dict_format_merges_modules(tmp_path):
    """Dict-format PR architecture should have its modules extracted and merged (Test 9).

    When a PR branch has architecture.json in object format {prd_files, modules},
    _augment_architecture_from_pr_branch should extract the modules and merge new
    entries into the architecture list. Currently, isinstance(pr_arch, list) at
    line 167 silently drops dict-format data — root cause of #1244 sync failure.
    """
    # Local architecture (bare array) with one existing module
    local_arch = [{"filename": "existing_Python.prompt", "priority": 1, "dependencies": []}]
    (tmp_path / "architecture.json").write_text(json.dumps(local_arch), encoding="utf-8")

    # PR branch returns dict-format architecture with an additional module
    pr_arch_dict = {
        "prd_files": ["docs/prd.md"],
        "modules": [
            {"filename": "existing_Python.prompt", "priority": 1, "dependencies": []},
            {"filename": "new_module_Python.prompt", "priority": 2, "dependencies": []},
        ],
    }

    def fake_git_show(args, **kwargs):
        return MagicMock(returncode=0, stdout=json.dumps(pr_arch_dict), stderr="")

    with patch("pdd.agentic_sync.subprocess.run", side_effect=fake_git_show):
        augmented = _augment_architecture_from_pr_branch(
            list(local_arch), tmp_path, 123
        )

    assert augmented is not None
    filenames = {m["filename"] for m in augmented}
    assert "new_module_Python.prompt" in filenames, (
        "Dict-format PR architecture modules should be merged, "
        "but isinstance(pr_arch, list) check at agentic_sync.py:167 silently drops them"
    )


# ---------------------------------------------------------------------------
# Per-module context resolution plumbing (issue #1675)
# ---------------------------------------------------------------------------


def test_resolve_sync_units_map_each_module_to_its_cwd_context(tmp_path):
    """Each targeted module resolves a unit with the context its cwd .pddrc assigns."""
    from pdd.resolved_sync_unit import resolve_sync_unit

    cwd_a = tmp_path / "a"
    cwd_b = tmp_path / "b"
    cwd_a.mkdir()
    cwd_b.mkdir()
    (cwd_a / ".pddrc").write_text(
        'version: "1.0"\ncontexts:\n  ctx_a:\n    paths: ["alpha*"]\n'
        '    defaults:\n      prompts_dir: "prompts"\n',
        encoding="utf-8",
    )
    (cwd_b / ".pddrc").write_text(
        'version: "1.0"\ncontexts:\n  ctx_b:\n    paths: ["beta*"]\n'
        '    defaults:\n      prompts_dir: "prompts"\n',
        encoding="utf-8",
    )

    units = {
        bn: resolve_sync_unit(bn, bn, cwd)
        for bn, cwd in {"alpha": cwd_a, "beta": cwd_b}.items()
    }
    assert {bn: u.context for bn, u in units.items()} == {
        "alpha": "ctx_a",
        "beta": "ctx_b",
    }


def test_resolve_module_sync_context_passes_pddrc_path(tmp_path, monkeypatch):
    """Context detection must use the found .pddrc, not one from the process cwd.

    Regression guard for the #1675 fix: the filesystem fallback in
    _detect_context_from_basename resolves nested prompts_dir contexts relative
    to the supplied pddrc_path.
    """
    import pdd.agentic_sync as asm

    (tmp_path / ".pddrc").write_text(
        'version: "1.0"\ncontexts:\n  default:\n    paths: ["**"]\n',
        encoding="utf-8",
    )
    captured = {}

    def _fake_detect(basename, config, pddrc_path=None):
        captured["pddrc_path"] = pddrc_path
        return None

    monkeypatch.setattr(asm, "_detect_context_from_basename", _fake_detect)
    asm._resolve_module_sync_context("foo", tmp_path)
    assert captured["pddrc_path"] == tmp_path / ".pddrc"


# ---------------------------------------------------------------------------
# Full ResolvedSyncUnit: deep discovery, ambiguity, global units (#1675)
# ---------------------------------------------------------------------------

def _pddrc_with_context(name, pattern):
    return (
        'version: "1.0"\n'
        "contexts:\n"
        f"  {name}:\n"
        f'    paths: ["{pattern}"]\n'
        "    defaults:\n"
        '      prompts_dir: "prompts"\n'
    )


def test_resolve_module_cwd_discovers_depth_three(tmp_path):
    # Req 1: a nested .pddrc deeper than depth 2 (apps/foo/service) is found.
    from pdd.agentic_sync import _resolve_module_cwd

    deep = tmp_path / "apps" / "foo" / "service"
    deep.mkdir(parents=True)
    (deep / ".pddrc").write_text(_pddrc_with_context("svc", "widget"), encoding="utf-8")
    assert _resolve_module_cwd("widget", tmp_path) == deep


def test_resolve_module_cwd_ambiguous_bare_basename_raises(tmp_path):
    # Req 2: a bare basename claimed by two distinct projects cannot be owned by
    # basename alone -> raise under strict ownership rather than silently picking.
    from pdd.agentic_sync import _resolve_module_cwd, AmbiguousModuleOwnerError

    for proj in ("a", "b"):
        d = tmp_path / proj
        d.mkdir()
        (d / ".pddrc").write_text(_pddrc_with_context("ctx", "widget"), encoding="utf-8")

    with pytest.raises(AmbiguousModuleOwnerError):
        _resolve_module_cwd("widget", tmp_path, strict_ownership=True)

    # Non-strict callers keep legacy first-match behavior (one of the owners).
    assert _resolve_module_cwd("widget", tmp_path) in (tmp_path / "a", tmp_path / "b")

    # A path-qualified basename is unambiguous by construction (the path names
    # the project); it never trips the ambiguity guard. Its execution cwd is
    # validated by dry-run, so resolution falls back to project_root and the
    # child runs the full path from there.
    assert (
        _resolve_module_cwd("a/widget", tmp_path, strict_ownership=True) == tmp_path
    )


def test_resolve_module_cwd_single_owner_resolves(tmp_path):
    # Req 2: with exactly one owning project, a bare basename resolves to it
    # (no ambiguity), proving ownership is by project, not by enumeration order.
    from pdd.agentic_sync import _resolve_module_cwd

    owner = tmp_path / "only"
    owner.mkdir()
    (owner / ".pddrc").write_text(_pddrc_with_context("ctx", "widget"), encoding="utf-8")
    assert _resolve_module_cwd("widget", tmp_path, strict_ownership=True) == owner


_DEFAULT_ONLY_PDDRC = (
    'version: "1.0"\n'
    "contexts:\n"
    "  default:\n"
    '    paths: ["**"]\n'
    "    defaults:\n"
    '      prompts_dir: "prompts"\n'
)


def test_resolve_module_cwd_strict_resolves_nested_only_prompt_owner(tmp_path):
    # Req 1: a bare basename whose prompt lives only in a nested project (under
    # its default context, with no specific pattern) resolves to that nested
    # project under strict ownership — not root with the parent context.
    from pdd.agentic_sync import _resolve_module_cwd

    svc = tmp_path / "svc"
    (svc / "prompts").mkdir(parents=True)
    (svc / ".pddrc").write_text(_DEFAULT_ONLY_PDDRC, encoding="utf-8")
    (svc / "prompts" / "widget_python.prompt").write_text("x", encoding="utf-8")
    assert _resolve_module_cwd("widget", tmp_path, strict_ownership=True) == svc


def test_resolve_module_cwd_strict_root_plus_nested_is_ambiguous(tmp_path):
    # Req 1/2: a bare basename owned by BOTH the repo root and a nested project
    # is ambiguous (the old "run from root, reuse parent context" class of bug).
    from pdd.agentic_sync import _resolve_module_cwd, AmbiguousModuleOwnerError

    (tmp_path / "prompts").mkdir()
    (tmp_path / "prompts" / "widget_python.prompt").write_text("x", encoding="utf-8")
    svc = tmp_path / "svc"
    svc.mkdir()
    (svc / ".pddrc").write_text(_pddrc_with_context("ctx", "widget"), encoding="utf-8")
    with pytest.raises(AmbiguousModuleOwnerError):
        _resolve_module_cwd("widget", tmp_path, strict_ownership=True)


def test_resolve_module_cwd_strict_different_depth_is_ambiguous(tmp_path):
    # Req 2: two projects at different nesting depths both claiming a bare
    # basename are ambiguous — the deeper one must not silently win.
    from pdd.agentic_sync import _resolve_module_cwd, AmbiguousModuleOwnerError

    foo = tmp_path / "apps" / "foo"
    svc = foo / "service"
    svc.mkdir(parents=True)
    (foo / ".pddrc").write_text(_pddrc_with_context("ctx_foo", "widget"), encoding="utf-8")
    (svc / ".pddrc").write_text(_pddrc_with_context("ctx_svc", "widget"), encoding="utf-8")
    with pytest.raises(AmbiguousModuleOwnerError):
        _resolve_module_cwd("widget", tmp_path, strict_ownership=True)


@patch("pdd.agentic_sync.sync_determine_operation")
@patch("pdd.agentic_sync._detect_languages_with_context")
def test_analyze_global_sync_builds_units_with_resolved_context(
    mock_lang, mock_determine, tmp_path
):
    # Req 4: global analysis produces a ResolvedSyncUnit per chosen module with
    # the context resolved against that module's own nested cwd .pddrc.
    nested = tmp_path / "extensions" / "app"
    nested.mkdir(parents=True)
    (nested / ".pddrc").write_text(
        _pddrc_with_context("app_ctx", "pdd_codex"), encoding="utf-8"
    )
    mock_lang.return_value = {"python": nested / "prompts/pdd_codex_python.prompt"}
    decision = MagicMock()
    decision.operation = "generate"
    decision.reason = "prompt changed"
    decision.estimated_cost = 1.0
    mock_determine.return_value = decision

    module = GlobalSyncModule(
        key="pdd_codex",
        basename="pdd_codex",
        cwd=nested,
        architecture_path=nested / "architecture.json",
        entry={"filename": "pdd_codex_python.prompt", "dependencies": []},
    )
    analysis = _analyze_global_sync_modules(
        [module], tmp_path, quiet=True, context_override="root_ctx"
    )
    units = analysis.module_units or {}
    assert "pdd_codex" in units
    # root_ctx is invalid in the nested cwd -> substitute the nested context.
    assert units["pdd_codex"].context == "app_ctx"
    assert units["pdd_codex"].cwd == nested
    assert units["pdd_codex"].architecture_path == nested / "architecture.json"


# ---------------------------------------------------------------------------
# Path-qualified targeted modules -> one resolved unit (issue #1675 final)
# ---------------------------------------------------------------------------

def test_relativize_target_strips_cwd_prefix(tmp_path):
    from pdd.agentic_sync import _relativize_target

    assert _relativize_target("a/b/c", tmp_path / "a", tmp_path) == "b/c"
    assert _relativize_target("a/b/c", tmp_path, tmp_path) == "a/b/c"
    assert _relativize_target("bare", tmp_path / "a", tmp_path) == "bare"


def test_resolve_module_cwd_and_target_path_qualified_nested(tmp_path, monkeypatch):
    # Trigger from the maintainer's report: issue-sync emits
    # extensions/github_pdd_app/src/worker_app -> cwd=extensions/github_pdd_app,
    # target=src/worker_app (so dry-run can find the prompt).
    import pdd.agentic_sync as asm

    nested = tmp_path / "extensions" / "github_pdd_app"
    nested.mkdir(parents=True)
    (nested / ".pddrc").write_text(_pddrc_with_context("src", "src/**"), encoding="utf-8")

    def fake_ctx(basename, cwd):
        if Path(cwd) == nested and basename == "src/worker_app":
            return ("src", nested / "prompts", {"python": nested / "prompts/src/worker_app_python.prompt"})
        return (None, Path(cwd) / "prompts", {})

    monkeypatch.setattr(asm, "_resolve_module_sync_context", fake_ctx)
    cwd, target = asm._resolve_module_cwd_and_target(
        "extensions/github_pdd_app/src/worker_app", tmp_path
    )
    assert cwd == nested
    assert target == "src/worker_app"


def test_resolve_module_cwd_and_target_root_layout_falls_back(tmp_path):
    # A path-qualified module no nested project owns runs the full path from root.
    from pdd.agentic_sync import _resolve_module_cwd_and_target

    (tmp_path / "src").mkdir()
    cwd, target = _resolve_module_cwd_and_target("src/config", tmp_path)
    assert cwd == tmp_path
    assert target == "src/config"


def test_branch_diff_to_resolver_chain_for_nested_module(tmp_path):
    # End-to-end regression for the maintainer's trigger (#1675): a branch diff
    # touching extensions/github_pdd_app/prompts/src/worker_app_Python.prompt
    # must yield the FULL key, which the resolver maps to the owning project +
    # relative target — not the short key that loses the project prefix.
    from pdd.agentic_sync import (
        _detect_modules_from_branch_diff,
        _resolve_module_cwd_and_target,
    )

    nested = tmp_path / "extensions" / "github_pdd_app"
    (nested / "prompts" / "src").mkdir(parents=True)
    (nested / ".pddrc").write_text(_pddrc_with_context("src", "src/**"), encoding="utf-8")
    (nested / "prompts" / "src" / "worker_app_python.prompt").write_text("x", encoding="utf-8")

    diff = "extensions/github_pdd_app/prompts/src/worker_app_Python.prompt\n"
    with patch("pdd.agentic_sync.subprocess.run") as mock_run:
        mock_run.side_effect = [
            MagicMock(returncode=0, stdout="feature\n", stderr=""),
            MagicMock(returncode=0, stdout=diff, stderr=""),
        ]
        keys = _detect_modules_from_branch_diff(tmp_path)

    assert keys == ["extensions/github_pdd_app/src/worker_app"]
    cwd, target = _resolve_module_cwd_and_target(keys[0], tmp_path)
    assert cwd == nested
    assert target == "src/worker_app"


def test_build_targeted_dep_graph_preserves_nested_edges(tmp_path):
    # #1675: full keys don't match nested arch entries directly (edges dropped);
    # _build_targeted_dep_graph matches via the relative target and remaps edges
    # back to full keys so nested dependency ordering is preserved.
    from pdd.agentic_sync import _build_targeted_dep_graph
    from pdd.agentic_sync_runner import build_dep_graph_from_architecture_data

    nested = tmp_path / "extensions" / "github_pdd_app"
    (nested / "prompts" / "src").mkdir(parents=True)
    (nested / ".pddrc").write_text(_pddrc_with_context("src", "src/**"), encoding="utf-8")
    (nested / "prompts" / "src" / "worker_app_python.prompt").write_text("x", encoding="utf-8")
    (nested / "prompts" / "src" / "config_python.prompt").write_text("x", encoding="utf-8")

    architecture = [
        {
            "filename": "src/worker_app_python.prompt",
            "filepath": "src/worker_app.py",
            "dependencies": ["src/config_python.prompt"],
        },
        {"filename": "src/config_python.prompt", "filepath": "src/config.py", "dependencies": []},
    ]
    modules = [
        "extensions/github_pdd_app/src/worker_app",
        "extensions/github_pdd_app/src/config",
    ]

    # Without remapping, full keys do not match the nested entries -> no edges.
    naive = build_dep_graph_from_architecture_data(architecture, modules)
    assert naive.graph["extensions/github_pdd_app/src/worker_app"] == []

    # With the targeted builder, the edge is preserved and remapped to full keys.
    graph, _warnings = _build_targeted_dep_graph(
        architecture, modules, tmp_path, "architecture.json"
    )
    assert graph["extensions/github_pdd_app/src/worker_app"] == [
        "extensions/github_pdd_app/src/config"
    ]
    assert graph["extensions/github_pdd_app/src/config"] == []


def test_build_targeted_dep_graph_distinct_projects_same_target(tmp_path):
    # #1675: two distinct projects each own `src/worker_app` -> `src/config`.
    # The dep graph must wire each worker_app to ITS OWN config, not collapse
    # them onto a shared relative-target node.
    import json
    from pdd.agentic_sync import _build_targeted_dep_graph

    arch_entries = [
        {
            "filename": "src/worker_app_python.prompt",
            "filepath": "src/worker_app.py",
            "dependencies": ["src/config_python.prompt"],
        },
        {"filename": "src/config_python.prompt", "filepath": "src/config.py", "dependencies": []},
    ]
    for proj in ("a", "b"):
        d = tmp_path / "apps" / proj
        (d / "prompts" / "src").mkdir(parents=True)
        (d / ".pddrc").write_text(_pddrc_with_context("src", "src/**"), encoding="utf-8")
        (d / "prompts" / "src" / "worker_app_python.prompt").write_text("x", encoding="utf-8")
        (d / "prompts" / "src" / "config_python.prompt").write_text("x", encoding="utf-8")
        (d / "architecture.json").write_text(json.dumps(arch_entries), encoding="utf-8")

    modules = [
        "apps/a/src/worker_app",
        "apps/a/src/config",
        "apps/b/src/worker_app",
        "apps/b/src/config",
    ]
    combined = arch_entries + arch_entries  # flattened combined arch (collides)
    graph, _warnings = _build_targeted_dep_graph(combined, modules, tmp_path, "arch.json")

    assert graph["apps/a/src/worker_app"] == ["apps/a/src/config"]
    assert graph["apps/b/src/worker_app"] == ["apps/b/src/config"]


def test_build_targeted_dep_graph_intra_project_edge_with_colliding_target(tmp_path):
    # #1675 (round 11): a same-project edge service -> worker_app must resolve
    # even when worker_app's relative target also exists in another project.
    import json
    from pdd.agentic_sync import _build_targeted_dep_graph

    a_entries = [
        {
            "filename": "src/service_python.prompt",
            "filepath": "src/service.py",
            "dependencies": ["src/worker_app_python.prompt"],
        },
        {"filename": "src/worker_app_python.prompt", "filepath": "src/worker_app.py", "dependencies": []},
    ]
    b_entries = [
        {"filename": "src/worker_app_python.prompt", "filepath": "src/worker_app.py", "dependencies": []},
    ]
    for proj, entries in (("a", a_entries), ("b", b_entries)):
        d = tmp_path / "apps" / proj
        (d / "prompts" / "src").mkdir(parents=True)
        (d / ".pddrc").write_text(_pddrc_with_context("src", "src/**"), encoding="utf-8")
        for name in ("service", "worker_app"):
            if any(name in e["filename"] for e in entries):
                (d / "prompts" / "src" / f"{name}_python.prompt").write_text("x", encoding="utf-8")
        (d / "architecture.json").write_text(json.dumps(entries), encoding="utf-8")

    modules = [
        "apps/a/src/service",       # unique relative target
        "apps/a/src/worker_app",    # collides with apps/b
        "apps/b/src/worker_app",    # collides with apps/a
    ]
    graph, _warnings = _build_targeted_dep_graph(
        a_entries + b_entries, modules, tmp_path, "arch.json"
    )
    # Same-project edge preserved despite the colliding target.
    assert graph["apps/a/src/service"] == ["apps/a/src/worker_app"]
    assert graph["apps/b/src/worker_app"] == []


def test_resolve_module_cwd_and_target_canonicalizes_nested_relative_key(tmp_path):
    # #1675: a short nested-relative key (e.g. from LLM/manual identification)
    # whose prompt lives in exactly one nested project canonicalizes to that
    # project, not the repo root.
    from pdd.agentic_sync import _resolve_module_cwd_and_target

    nested = tmp_path / "extensions" / "github_pdd_app"
    (nested / "prompts" / "src").mkdir(parents=True)
    (nested / ".pddrc").write_text(_pddrc_with_context("src", "src/**"), encoding="utf-8")
    (nested / "prompts" / "src" / "worker_app_python.prompt").write_text("x", encoding="utf-8")

    cwd, target = _resolve_module_cwd_and_target("src/worker_app", tmp_path)
    assert cwd == nested
    assert target == "src/worker_app"


def test_resolve_module_cwd_and_target_nested_relative_key_ambiguous(tmp_path):
    # A nested-relative key owned by two projects is ambiguous -> fail loudly.
    from pdd.agentic_sync import (
        _resolve_module_cwd_and_target,
        AmbiguousModuleOwnerError,
    )

    for proj in ("a", "b"):
        d = tmp_path / "apps" / proj
        (d / "prompts" / "src").mkdir(parents=True)
        (d / ".pddrc").write_text(_pddrc_with_context("src", "src/**"), encoding="utf-8")
        (d / "prompts" / "src" / "worker_app_python.prompt").write_text("x", encoding="utf-8")

    with pytest.raises(AmbiguousModuleOwnerError):
        _resolve_module_cwd_and_target("src/worker_app", tmp_path)


def test_resolve_module_cwd_and_target_root_layout_path_qualified(tmp_path):
    # A path-qualified key owned by the repo root (no nested owner) stays at root.
    from pdd.agentic_sync import _resolve_module_cwd_and_target

    (tmp_path / "prompts" / "src").mkdir(parents=True)
    (tmp_path / "prompts" / "src" / "config_python.prompt").write_text("x", encoding="utf-8")
    # An unrelated nested project that does NOT own src/config.
    other = tmp_path / "extensions" / "other"
    (other / "prompts").mkdir(parents=True)
    (other / ".pddrc").write_text(_pddrc_with_context("other", "other/**"), encoding="utf-8")

    cwd, target = _resolve_module_cwd_and_target("src/config", tmp_path)
    assert cwd == tmp_path
    assert target == "src/config"


def test_resolve_module_cwd_and_target_root_ownership_wins_over_nested(tmp_path):
    # #1675: when the repo root owns a path-qualified key AND a nested project
    # also has a same-named module, the repo-root-relative key resolves to root.
    from pdd.agentic_sync import _resolve_module_cwd_and_target

    (tmp_path / "prompts" / "src").mkdir(parents=True)
    (tmp_path / "prompts" / "src" / "config_python.prompt").write_text("x", encoding="utf-8")
    nested = tmp_path / "extensions" / "github_pdd_app"
    (nested / "prompts" / "src").mkdir(parents=True)
    (nested / ".pddrc").write_text(_pddrc_with_context("src", "src/**"), encoding="utf-8")
    (nested / "prompts" / "src" / "config_python.prompt").write_text("x", encoding="utf-8")

    cwd, target = _resolve_module_cwd_and_target("src/config", tmp_path)
    assert cwd == tmp_path
    assert target == "src/config"


def test_resolve_module_cwd_and_target_root_context_points_into_nested(tmp_path):
    # pdd_cloud case (#1675): the ROOT .pddrc has a context whose prompts_dir
    # points INTO the nested extension's prompt tree, so root can *resolve* the
    # prompt path but does not OWN the module. A short nested-relative key must
    # canonicalize to the nested project + its own context, not root.
    from pdd.agentic_sync import _resolve_module_cwd_and_target
    from pdd.resolved_sync_unit import resolve_sync_unit

    nested = tmp_path / "extensions" / "github_pdd_app"
    (nested / "prompts" / "src").mkdir(parents=True)
    (tmp_path / ".pddrc").write_text(
        'version: "1.0"\n'
        "contexts:\n"
        "  extensions-github_pdd_app:\n"
        '    paths: ["extensions/github_pdd_app/**"]\n'
        "    defaults:\n"
        '      prompts_dir: "extensions/github_pdd_app/prompts"\n'
        "  default:\n"
        '    paths: ["**"]\n'
        "    defaults:\n"
        '      prompts_dir: "prompts"\n',
        encoding="utf-8",
    )
    (nested / ".pddrc").write_text(_pddrc_with_context("src", "src/**"), encoding="utf-8")
    (nested / "prompts" / "src" / "worker_app_python.prompt").write_text("x", encoding="utf-8")

    cwd, target = _resolve_module_cwd_and_target("src/worker_app", tmp_path)
    assert cwd == nested
    assert target == "src/worker_app"
    unit = resolve_sync_unit(
        "src/worker_app", target, cwd, requested_context="extensions-github_pdd_app"
    )
    assert unit.context == "src"  # nested context, NOT the root one



def _big_interface_entry(filename: str, *, dep: str = "") -> Dict[str, Any]:
    """An architecture entry whose `interface`/`description`/`reason` dominate."""
    return {
        "filename": filename,
        "filepath": f"pdd/{filename}",
        "origin": "code",
        "dependencies": [dep] if dep else [],
        # The fields that must NOT survive compaction. ~5KB of interface text
        # is exactly what blows the identify-modules prompt past the limit.
        "interface": "INTERFACE_TEXT " * 400,
        "description": "DESCRIPTION_TEXT " * 100,
        "reason": "REASON_TEXT " * 50,
    }

class TestNormalizeModulesForSync:
    """Tests for module basename normalization before validation."""

    def test_preserves_exact_architecture_basename_that_ends_with_language_word(self, monkeypatch):
        """`operation_log` must not become `operation` when Log is in language_format.csv."""
        monkeypatch.setenv("PDD_PATH", str(Path(__file__).resolve().parents[1]))
        architecture = [{"filename": "operation_log_python.prompt", "dependencies": []}]

        result = _normalize_modules_for_sync(["operation_log"], architecture)

        assert result == ["operation_log"]

    def test_strips_llm_language_suffix_when_needed(self):
        """Architecture-style LLM names still normalize to sync basenames."""
        architecture = [{"filename": "crm_models_Python.prompt", "dependencies": []}]

        result = _normalize_modules_for_sync(["crm_models_Python"], architecture)

        assert result == ["crm_models"]

    def test_strips_final_component_suffix_without_losing_path(self):
        """Path-qualified names keep their directory prefix after stripping."""
        architecture = [{"filename": "commands/contracts_python.prompt", "dependencies": []}]

        result = _normalize_modules_for_sync(["commands/contracts_python"], architecture)

        assert result == ["commands/contracts"]


class TestParseChangedModulesEnv:
    """Tests for the cloud-provided changed-module env parser."""

    def test_empty_values_return_empty_list(self):
        assert _parse_changed_modules_env("") == []
        assert _parse_changed_modules_env("   ") == []
        assert _parse_changed_modules_env(",, ,") == []

    def test_splits_trims_dedupes_and_preserves_paths(self):
        value = (
            " src/services/foo, frontend/app/dashboard/page, "
            "src/services/foo,,frontend/app/dashboard/page, agentic_sync "
        )

        assert _parse_changed_modules_env(value) == [
            "src/services/foo",
            "frontend/app/dashboard/page",
            "agentic_sync",
        ]


# ---------------------------------------------------------------------------
# _detect_modules_from_branch_diff
# ---------------------------------------------------------------------------


class TestCompactArchitectureForIdentification:
    def test_drops_heavy_fields_keeps_signal_fields(self):
        arch = [_big_interface_entry("foo_Python.prompt", dep="bar_Python.prompt")]
        compact = _compact_architecture_for_identification(arch)

        assert compact == [
            {
                "filename": "foo_Python.prompt",
                "filepath": "pdd/foo_Python.prompt",
                "origin": "code",
                "dependencies": ["bar_Python.prompt"],
            }
        ]
        # Heavy fields are gone.
        assert "interface" not in compact[0]
        assert "description" not in compact[0]
        assert "reason" not in compact[0]

    def test_preserves_entry_order(self):
        arch = [
            _big_interface_entry("a_Python.prompt"),
            _big_interface_entry("b_Python.prompt"),
            _big_interface_entry("c_Python.prompt"),
        ]
        compact = _compact_architecture_for_identification(arch)
        assert [e["filename"] for e in compact] == [
            "a_Python.prompt",
            "b_Python.prompt",
            "c_Python.prompt",
        ]

    def test_does_not_mutate_input(self):
        arch = [_big_interface_entry("foo_Python.prompt")]
        _compact_architecture_for_identification(arch)
        # Original still carries its heavy fields.
        assert "interface" in arch[0]

    def test_none_and_empty_returned_as_is(self):
        assert _compact_architecture_for_identification(None) is None
        empty: List[Dict[str, Any]] = []
        assert _compact_architecture_for_identification(empty) == []

    def test_skips_non_dict_entries(self):
        arch = [_big_interface_entry("foo_Python.prompt"), "not-a-dict", 42]
        compact = _compact_architecture_for_identification(arch)
        assert len(compact) == 1
        assert compact[0]["filename"] == "foo_Python.prompt"


class TestFilterLowSignalComments:
    def test_drops_job_queued_comment(self):
        comments = [{"body": "🚀 **Job Queued!**\n\nYour sync is queued."}]
        assert _filter_low_signal_comments(comments) == []

    def test_drops_progress_and_error_and_state_comments(self):
        comments = [
            {"body": "## PDD Agentic Sync Progress\n\n- step 1"},
            {"body": "## PDD Agentic Sync - Error\n\n```\nboom\n```"},
            {"body": "<!-- PDD_WORKFLOW_STATE: {\"x\": 1} -->\nstuff"},
        ]
        assert _filter_low_signal_comments(comments) == []

    def test_keeps_human_comment_with_files_modified_signal(self):
        keep = {"body": "Here is the result:\nFILES_MODIFIED: prompts/foo_Python.prompt"}
        comments = [
            {"body": "🚀 **Job Queued!**"},
            keep,
        ]
        result = _filter_low_signal_comments(comments)
        assert result == [keep]

    def test_drops_empty_and_whitespace_body(self):
        comments = [{"body": ""}, {"body": "   \n  "}, {"body": "real signal"}]
        result = _filter_low_signal_comments(comments)
        assert result == [{"body": "real signal"}]

    def test_none_returned_as_is(self):
        assert _filter_low_signal_comments(None) is None

    def test_is_low_signal_comment_predicate(self):
        assert _is_low_signal_comment("") is True
        assert _is_low_signal_comment("   ") is True
        assert _is_low_signal_comment("🚀 **Job Queued!** now") is True
        assert _is_low_signal_comment("## PDD Agentic Sync Progress\nx") is True
        assert _is_low_signal_comment("normal human comment") is False
        # A leading blank line must not hide the anchor.
        assert _is_low_signal_comment("\n\n## PDD Agentic Sync - Error") is True


class TestBuildIdentifyIssueContent:
    def test_includes_title_body_and_comment_block(self):
        out = _build_identify_issue_content(
            "My Title",
            "Body text",
            [{"user": {"login": "alice"}, "body": "a comment"}],
        )
        assert "Title: My Title" in out
        assert "Body text" in out
        assert "Comments:" in out
        assert "Comment by alice" in out
        assert "a comment" in out

    def test_no_comments_omits_comment_section(self):
        out = _build_identify_issue_content("T", "B", None)
        assert "Title: T" in out
        assert "Comments:" not in out


class TestTruncateHeadTail:
    def test_short_text_unchanged(self):
        assert _truncate_head_tail("hello", 100) == "hello"

    def test_long_text_truncated_within_budget(self):
        text = "x" * 5000
        out = _truncate_head_tail(text, 1000)
        assert len(out) <= 1000
        assert "truncated" in out
        # Head and tail of the original survive.
        assert out.startswith("x")
        assert out.endswith("x")


def _identify_fallback_patches(method):
    """Stack the mocks needed to force + observe the LLM identify-modules call.

    The patches are applied so the wrapped test receives them as positional
    args in THIS order (after ``self`` and after any extra ``@patch`` decorators
    stacked above ``@_identify_fallback_patches``):
    mock_gh_cli, mock_gh_cmd, mock_load_arch, mock_find_root, mock_branch_diff,
    mock_runtime_only, mock_load_prompt, mock_agentic_task.
    """
    # Applied programmatically, the FIRST patch() call binds innermost and so
    # becomes the FIRST positional arg. Apply in documented arg order.
    method = patch("pdd.agentic_sync._check_gh_cli", return_value=True)(method)
    method = patch("pdd.agentic_sync._run_gh_command")(method)
    method = patch("pdd.agentic_sync._load_architecture_json")(method)
    method = patch(
        "pdd.agentic_sync._find_project_root", return_value=Path("/tmp/proj")
    )(method)
    method = patch(
        "pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[]
    )(method)
    method = patch(
        "pdd.agentic_sync._branch_diff_is_runtime_llm_only", return_value=False
    )(method)
    method = patch(
        "pdd.agentic_sync.load_prompt_template",
        return_value=(
            "ISSUE:\n{issue_content}\nARCH:\n{architecture_json}\nNUM:{issue_number}"
        ),
    )(method)
    method = patch("pdd.agentic_sync.run_agentic_task")(method)
    return method


class TestIdentifyModulesPromptSize:
    """Integration: force the LLM fallback and inspect the rendered prompt."""

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._filter_already_synced", return_value=[])
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult({"foo": []}, []),
    )
    @_identify_fallback_patches
    def test_normal_arch_prompt_excludes_interface_and_is_under_budget(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_find_root,
        mock_branch_diff,
        mock_runtime_only,
        mock_load_prompt,
        mock_agentic_task,
        mock_build_graph,
        mock_dry_run,
        mock_filter_synced,
        mock_runner_cls,
    ):
        issue_data = {"title": "Fix foo", "body": "do it", "comments_url": ""}
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (
            [
                _big_interface_entry("foo_Python.prompt"),
                _big_interface_entry("bar_Python.prompt"),
            ],
            Path("/tmp/architecture.json"),
        )
        mock_agentic_task.return_value = (
            True,
            'MODULES_TO_SYNC: ["foo"]\nDEPS_VALID: true',
            0.0,
            "anthropic",
        )
        mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, {"foo": "foo"}, [], 0.0)
        mock_runner_cls.return_value.run.return_value = (True, "synced", 0.0)

        run_agentic_sync("https://github.com/owner/repo/issues/1", quiet=True)

        mock_agentic_task.assert_called_once()
        prompt = mock_agentic_task.call_args.kwargs["instruction"]
        assert "INTERFACE_TEXT" not in prompt
        assert "DESCRIPTION_TEXT" not in prompt
        assert "REASON_TEXT" not in prompt
        # origin/dependency fields the LLM actually needs are still present.
        assert "foo_Python.prompt" in prompt
        assert len(prompt) < _IDENTIFY_MODULES_MAX_CHARS

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._filter_already_synced", return_value=[])
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult({"foo": []}, []),
    )
    @_identify_fallback_patches
    def test_size_guard_accounts_for_run_agentic_task_wrapper(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_find_root,
        mock_branch_diff,
        mock_runtime_only,
        mock_load_prompt,
        mock_agentic_task,
        mock_build_graph,
        mock_dry_run,
        mock_filter_synced,
        mock_runner_cls,
        monkeypatch,
    ):
        """PDD_USER_FEEDBACK and the fixed provider suffix count toward budget."""
        monkeypatch.setenv("PDD_USER_FEEDBACK", "abc")
        template = "ISSUE:\n{issue_content}\nARCH:\n{architecture_json}\nNUM:{issue_number}"
        mock_load_prompt.return_value = template
        architecture = [
            {"filename": "foo_Python.prompt", "filepath": "pdd/foo", "origin": "code", "dependencies": []}
        ]
        compact = _compact_architecture_for_identification(architecture)
        safe_arch_json = json.dumps(compact, indent=2).replace("{", "{{").replace("}", "}}")

        def render(body: str) -> str:
            issue_content = _build_identify_issue_content("WRAPPER_TITLE_TOKEN", body, None)
            return template.format(
                issue_content=issue_content,
                architecture_json=safe_arch_json,
                issue_number=1,
            )

        base_len = len(render(""))
        body = "B" * (_IDENTIFY_MODULES_MAX_CHARS - base_len - 10)
        # The raw instruction fits, but run_agentic_task's wrapper would push
        # the actual provider prompt over the limit without the new guard.
        assert len(render(body)) < _IDENTIFY_MODULES_MAX_CHARS
        assert len(build_agentic_task_instruction(render(body))) > _IDENTIFY_MODULES_MAX_CHARS

        issue_data = {"title": "WRAPPER_TITLE_TOKEN", "body": body, "comments_url": ""}
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (architecture, Path("/tmp/architecture.json"))
        mock_agentic_task.return_value = (
            True,
            'MODULES_TO_SYNC: ["foo"]\nDEPS_VALID: true',
            0.0,
            "anthropic",
        )
        mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, {"foo": "foo"}, [], 0.0)
        mock_runner_cls.return_value.run.return_value = (True, "synced", 0.0)

        run_agentic_sync("https://github.com/owner/repo/issues/1", quiet=True)

        mock_agentic_task.assert_called_once()
        prompt = mock_agentic_task.call_args.kwargs["instruction"]
        assert len(build_agentic_task_instruction(prompt)) <= _IDENTIFY_MODULES_MAX_CHARS
        assert "WRAPPER_TITLE_TOKEN" in prompt

    @_identify_fallback_patches
    def test_pathological_arch_hard_fails_with_input_too_large(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_find_root,
        mock_branch_diff,
        mock_runtime_only,
        mock_load_prompt,
        mock_agentic_task,
    ):
        issue_data = {"title": "Fix foo", "body": "do it", "comments_url": ""}
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        # Even compacted, the architecture alone blows the budget: each entry's
        # filename/filepath is itself enormous so dropping interface won't help.
        huge = "Z" * 50_000
        pathological = [
            {
                "filename": f"{huge}_{i}_Python.prompt",
                "filepath": f"pdd/{huge}_{i}",
                "origin": "code",
                "dependencies": [],
            }
            for i in range(40)
        ]
        mock_load_arch.return_value = (
            pathological,
            Path("/tmp/architecture.json"),
        )

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True, use_github_state=False
        )

        assert success is False
        assert "input_too_large" in msg
        assert "no modules to sync" not in msg.lower()
        assert cost == pytest.approx(0.0)
        mock_agentic_task.assert_not_called()

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._filter_already_synced", return_value=[])
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult({"foo": []}, []),
    )
    @_identify_fallback_patches
    def test_huge_comments_are_trimmed_to_fit_budget(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_find_root,
        mock_branch_diff,
        mock_runtime_only,
        mock_load_prompt,
        mock_agentic_task,
        mock_build_graph,
        mock_dry_run,
        mock_filter_synced,
        mock_runner_cls,
    ):
        # Small architecture, but comments alone exceed the budget so the size
        # guard must drop/trim them while still calling the LLM.
        huge_comment_body = "C" * (_IDENTIFY_MODULES_MAX_CHARS + 50_000)
        issue_data = {
            "title": "UNIQUE_TITLE_TOKEN",
            "body": "small body",
            "comments_url": "https://api.github.com/repos/owner/repo/issues/1/comments",
        }
        comments_json = json.dumps(
            [{"user": {"login": "bot"}, "body": huge_comment_body}]
        )
        mock_gh_cmd.side_effect = [
            (True, json.dumps(issue_data)),
            (True, comments_json),
        ]
        mock_load_arch.return_value = (
            [{"filename": "foo_Python.prompt", "filepath": "pdd/foo", "origin": "code", "dependencies": []}],
            Path("/tmp/architecture.json"),
        )
        mock_agentic_task.return_value = (
            True,
            'MODULES_TO_SYNC: ["foo"]\nDEPS_VALID: true',
            0.0,
            "anthropic",
        )
        mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, {"foo": "foo"}, [], 0.0)
        mock_runner_cls.return_value.run.return_value = (True, "synced", 0.0)

        run_agentic_sync("https://github.com/owner/repo/issues/1", quiet=True)

        mock_agentic_task.assert_called_once()
        prompt = mock_agentic_task.call_args.kwargs["instruction"]
        assert len(prompt) < _IDENTIFY_MODULES_MAX_CHARS
        # The title (signal) survives even though comments were trimmed.
        assert "UNIQUE_TITLE_TOKEN" in prompt
        # The giant comment body did not make it through verbatim.
        assert huge_comment_body not in prompt

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._filter_already_synced", return_value=[])
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult({"foo": []}, []),
    )
    @_identify_fallback_patches
    def test_brace_heavy_body_is_truncated_but_still_calls_llm(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_find_root,
        mock_branch_diff,
        mock_runtime_only,
        mock_load_prompt,
        mock_agentic_task,
        mock_build_graph,
        mock_dry_run,
        mock_filter_synced,
        mock_runner_cls,
    ):
        # Small architecture, NO comments, but a LARGE brace-heavy body. Each
        # `{`/`}` doubles under _escape_format_braces, so the escaped body is
        # ~2x raw — the rendered prompt blows the budget and the body-truncation
        # lever (raw body trimmed to budget // 2) must keep it under the limit
        # while still calling the LLM. Regression for the brace-escaping bound.
        brace_heavy_body = "{}" * _IDENTIFY_MODULES_MAX_CHARS  # ~2.1M raw chars
        issue_data = {
            "title": "TRUNCATE_TITLE_TOKEN",
            "body": brace_heavy_body,
            "comments_url": "",
        }
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (
            [{"filename": "foo_Python.prompt", "filepath": "pdd/foo", "origin": "code", "dependencies": []}],
            Path("/tmp/architecture.json"),
        )
        mock_agentic_task.return_value = (
            True,
            'MODULES_TO_SYNC: ["foo"]\nDEPS_VALID: true',
            0.0,
            "anthropic",
        )
        mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, {"foo": "foo"}, [], 0.0)
        mock_runner_cls.return_value.run.return_value = (True, "synced", 0.0)

        run_agentic_sync("https://github.com/owner/repo/issues/1", quiet=True)

        mock_agentic_task.assert_called_once()
        prompt = mock_agentic_task.call_args.kwargs["instruction"]
        # Body was truncated enough that the brace-escaped prompt still fits.
        assert len(prompt) < _IDENTIFY_MODULES_MAX_CHARS
        # The title (signal) survives the body truncation.
        assert "TRUNCATE_TITLE_TOKEN" in prompt


class TestPddChangedModulesFastPath:
    """Integration tests for PDD_CHANGED_MODULES issue-sync selection."""

    def _run_with_env(
        self,
        monkeypatch,
        tmp_path,
        *,
        env_value: str | None,
        issue_body: str = "sync the current module",
        user_feedback: str | None = None,
        architecture: List[Dict[str, Any]] | None = None,
        filter_synced: List[str] | None = None,
        quiet: bool = True,
    ):
        if env_value is None:
            monkeypatch.delenv("PDD_CHANGED_MODULES", raising=False)
        else:
            monkeypatch.setenv("PDD_CHANGED_MODULES", env_value)
        if user_feedback is None:
            monkeypatch.delenv("PDD_USER_FEEDBACK", raising=False)
        else:
            monkeypatch.setenv("PDD_USER_FEEDBACK", user_feedback)

        modules_after_filter = filter_synced or ["foo"]
        dry_run_cwds = {module: tmp_path for module in modules_after_filter}
        dry_run_targets = {module: module.rsplit("/", 1)[-1] for module in modules_after_filter}
        issue_data = {"title": "Issue", "body": issue_body, "comments_url": ""}
        arch = architecture or [{"filename": "foo_python.prompt", "dependencies": []}]

        patches = [
            patch("pdd.agentic_sync._check_gh_cli", return_value=True),
            patch("pdd.agentic_sync._run_gh_command", return_value=(True, json.dumps(issue_data))),
            patch("pdd.agentic_sync._find_project_root", return_value=tmp_path),
            patch("pdd.agentic_sync._load_architecture_json", return_value=(arch, tmp_path / "architecture.json")),
            patch("pdd.agentic_sync._augment_architecture_from_pr_branch", side_effect=lambda a, _r, _i: a),
            patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[]),
            patch("pdd.agentic_sync._branch_diff_is_runtime_llm_only", return_value=False),
            patch("pdd.agentic_sync.load_prompt_template", return_value="ISSUE {issue_content} ARCH {architecture_json}"),
            patch("pdd.agentic_sync.run_agentic_task"),
            patch("pdd.agentic_sync._build_targeted_dep_graph", return_value=({m: [] for m in modules_after_filter}, [])),
            patch("pdd.agentic_sync._run_dry_run_validation", return_value=(True, dry_run_cwds, dry_run_targets, [], 0.0)),
            patch("pdd.agentic_sync._filter_already_synced", return_value=modules_after_filter),
        ]
        with patches[0] as mock_gh_cli, patches[1] as mock_gh_cmd, patches[2], patches[3], \
            patches[4], patches[5], patches[6], patches[7] as mock_load_prompt, \
            patches[8] as mock_agentic_task, patches[9], patches[10] as mock_dry_run, \
            patches[11] as mock_filter_synced:
            mock_agentic_task.return_value = (
                True,
                'MODULES_TO_SYNC: ["foo"]\nDEPS_VALID: true',
                0.5,
                "anthropic",
            )
            result = run_agentic_sync(
                "https://github.com/owner/repo/issues/1",
                quiet=quiet,
                dry_run=True,
                use_github_state=False,
            )

        return {
            "result": result,
            "mock_gh_cli": mock_gh_cli,
            "mock_gh_cmd": mock_gh_cmd,
            "mock_load_prompt": mock_load_prompt,
            "mock_agentic_task": mock_agentic_task,
            "mock_dry_run": mock_dry_run,
            "mock_filter_synced": mock_filter_synced,
        }

    def test_env_fast_path_bypasses_identify_modules_llm(self, monkeypatch, tmp_path):
        observed_modules = ["src/services/foo", "frontend/app/dashboard/page"]
        result = self._run_with_env(
            monkeypatch,
            tmp_path,
            env_value=(
                " src/services/foo, frontend/app/dashboard/page, "
                "src/services/foo,, "
            ),
            architecture=[
                {"filename": "foo_python.prompt", "dependencies": []},
                {"filename": "page_python.prompt", "dependencies": []},
            ],
            filter_synced=observed_modules,
        )

        success, msg, cost, model = result["result"]
        assert success is True
        assert msg == (
            "Dry run complete: 2 module(s) would sync: "
            "src/services/foo, frontend/app/dashboard/page"
        )
        assert cost == pytest.approx(0.0)
        assert model == ""
        result["mock_load_prompt"].assert_not_called()
        result["mock_agentic_task"].assert_not_called()
        result["mock_dry_run"].assert_called_once()
        assert result["mock_dry_run"].call_args.kwargs["modules"] == observed_modules

    def test_stale_user_feedback_does_not_override_env_selection(self, monkeypatch, tmp_path):
        result = self._run_with_env(
            monkeypatch,
            tmp_path,
            env_value="current_module",
            user_feedback=(
                "IMPORTANT: The following modules were changed and MUST be synced: "
                "stale/abandoned/module"
            ),
            architecture=[{"filename": "current_module_python.prompt", "dependencies": []}],
            filter_synced=["current_module"],
        )

        success, msg, _cost, _model = result["result"]
        assert success is True
        assert "current_module" in msg
        assert "stale/abandoned/module" not in msg
        result["mock_agentic_task"].assert_not_called()
        assert result["mock_dry_run"].call_args.kwargs["modules"] == ["current_module"]

    def test_any_unresolvable_env_entry_fails_even_with_valid_entries(
        self, monkeypatch, tmp_path
    ):
        result = self._run_with_env(
            monkeypatch,
            tmp_path,
            env_value="foo,missing_module",
            architecture=[{"filename": "foo_python.prompt", "dependencies": []}],
            filter_synced=["foo"],
        )

        success, msg, cost, model = result["result"]
        assert success is False
        assert msg == "PDD_CHANGED_MODULES contained unresolved module targets: ['missing_module']"
        assert "LLM identified no modules to sync" not in msg
        assert cost == pytest.approx(0.0)
        assert model == ""
        result["mock_agentic_task"].assert_not_called()
        result["mock_dry_run"].assert_not_called()

    def test_runtime_template_env_entry_has_specific_diagnostic(
        self, monkeypatch, tmp_path
    ):
        result = self._run_with_env(
            monkeypatch,
            tmp_path,
            env_value="foo_LLM",
            architecture=[{"filename": "foo_LLM.prompt", "dependencies": []}],
            filter_synced=["foo_LLM"],
        )

        success, msg, cost, model = result["result"]
        assert success is False
        assert msg == "PDD_CHANGED_MODULES contained unresolved module targets: ['foo_LLM']"
        assert "already synced" not in msg
        assert cost == pytest.approx(0.0)
        assert model == ""
        result["mock_agentic_task"].assert_not_called()
        result["mock_dry_run"].assert_not_called()

    def test_oversized_identify_context_is_not_constructed_when_env_is_valid(
        self, monkeypatch, tmp_path
    ):
        huge_body = "{}" * (_IDENTIFY_MODULES_MAX_CHARS + 10_000)
        result = self._run_with_env(
            monkeypatch,
            tmp_path,
            env_value="foo",
            issue_body=huge_body,
            architecture=[_big_interface_entry("foo_python.prompt")],
            filter_synced=["foo"],
        )

        success, msg, _cost, _model = result["result"]
        assert success is True
        assert "foo" in msg
        result["mock_load_prompt"].assert_not_called()
        result["mock_agentic_task"].assert_not_called()

    def test_unset_or_empty_env_preserves_llm_fallback(self, monkeypatch, tmp_path):
        for env_value in (None, " , , "):
            result = self._run_with_env(
                monkeypatch,
                tmp_path,
                env_value=env_value,
                architecture=[{"filename": "foo_python.prompt", "dependencies": []}],
                filter_synced=["foo"],
            )

            success, msg, cost, model = result["result"]
            assert success is True
            assert "foo" in msg
            assert cost == pytest.approx(0.5)
            assert model == "anthropic"
            result["mock_load_prompt"].assert_called_once()
            result["mock_agentic_task"].assert_called_once()

    def test_unresolvable_env_entries_have_specific_diagnostic(self, monkeypatch, tmp_path):
        result = self._run_with_env(
            monkeypatch,
            tmp_path,
            env_value="missing_module",
            architecture=[{"filename": "foo_python.prompt", "dependencies": []}],
            filter_synced=["missing_module"],
        )

        success, msg, cost, model = result["result"]
        assert success is False
        assert msg == "PDD_CHANGED_MODULES contained unresolved module targets: ['missing_module']"
        assert "LLM identified no modules to sync" not in msg
        assert cost == pytest.approx(0.0)
        assert model == ""
        result["mock_agentic_task"].assert_not_called()
        result["mock_dry_run"].assert_not_called()

    def test_env_fast_path_prints_selected_modules(self, monkeypatch, tmp_path, capsys):
        result = self._run_with_env(
            monkeypatch,
            tmp_path,
            env_value="foo",
            architecture=[{"filename": "foo_python.prompt", "dependencies": []}],
            filter_synced=["foo"],
            quiet=False,
        )

        assert result["result"][0] is True
        output = capsys.readouterr().out
        assert "Using PDD_CHANGED_MODULES for module identification: ['foo']" in output
        assert "Resolved PDD_CHANGED_MODULES module selection: ['foo']" in output


    @patch("pdd.agentic_sync._post_error_comment")
    @_identify_fallback_patches
    def test_hard_fail_posts_error_comment_when_github_state(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_find_root,
        mock_branch_diff,
        mock_runtime_only,
        mock_load_prompt,
        mock_agentic_task,
        mock_post_error,
    ):
        issue_data = {"title": "Fix foo", "body": "do it", "comments_url": ""}
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        # Compacted architecture alone exceeds the budget (see pathological test).
        huge = "Z" * 50_000
        pathological = [
            {
                "filename": f"{huge}_{i}_Python.prompt",
                "filepath": f"pdd/{huge}_{i}",
                "origin": "code",
                "dependencies": [],
            }
            for i in range(40)
        ]
        mock_load_arch.return_value = (pathological, Path("/tmp/architecture.json"))

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True, use_github_state=True
        )

        assert success is False
        assert "input_too_large" in msg
        mock_agentic_task.assert_not_called()
        mock_post_error.assert_called_once()
        # The posted comment carries the real oversize reason.
        posted_msg = mock_post_error.call_args.args[3]
        assert "input_too_large" in posted_msg


class TestBranchDiffIssueScopeReconciliation:
    """Issue #1980: the branch-diff fast path must reconcile its scope with the
    modules the issue explicitly names.

    Repro (epic PR #1868 E2E validation): the issue explicitly asks to sync
    ``greeter`` and ``textutil``; the work-branch diff only touches ``greeter``.
    The fast path synced only ``greeter``, dropped the greeter -> textutil
    dependency edge with a yellow warning, and reported Success. The chosen
    semantics: deterministically extract explicitly-named known modules from the
    issue title/body and UNION any that are missing into the diff-detected
    scope — still zero LLM calls.
    """

    _ARCH = [
        {"filename": "textutil_python.prompt", "dependencies": []},
        {"filename": "greeter_python.prompt", "dependencies": ["textutil_python.prompt"]},
    ]

    @staticmethod
    def _issue(body: str) -> Dict[str, Any]:
        return {"title": "Sync the greeter feature", "body": body, "comments_url": ""}

    # ------------------------------------------------------------------
    # Helper-level unit tests (deterministic extraction)
    # ------------------------------------------------------------------

    def test_extracts_backticked_known_modules(self):
        from pdd.agentic_sync import _extract_issue_named_modules

        named = _extract_issue_named_modules(
            "Sync the greeter feature",
            "Please sync `greeter` and `textutil` together.",
            self._ARCH,
        )
        assert named == ["greeter", "textutil"]

    def test_extracts_prompt_file_paths(self):
        """FILES_MODIFIED-style prompt paths resolve to known basenames."""
        from pdd.agentic_sync import _extract_issue_named_modules

        named = _extract_issue_named_modules(
            "Sync the greeter feature",
            "FILES_MODIFIED:\n"
            "- prompts/greeter_python.prompt\n"
            "- prompts/textutil_python.prompt\n",
            self._ARCH,
        )
        assert named == ["greeter", "textutil"]

    def test_prose_word_matching_single_word_module_is_not_extracted(self):
        """A module named like an ordinary prose word (e.g. ``python``) must not
        be pulled into scope just because the word appears in the issue text."""
        from pdd.agentic_sync import _extract_issue_named_modules

        arch = self._ARCH + [{"filename": "python_python.prompt", "dependencies": []}]
        named = _extract_issue_named_modules(
            "Fix the greeting",
            "The `greeter` module is written in python and should say hi.",
            arch,
        )
        assert named == ["greeter"]

    def test_underscored_module_name_in_prose_is_extracted(self):
        """Multi-word (underscored) basenames cannot be ordinary prose words, so a
        bare word-boundary mention counts as an explicit reference."""
        from pdd.agentic_sync import _extract_issue_named_modules

        arch = [{"filename": "ci_validation_python.prompt", "dependencies": []}]
        named = _extract_issue_named_modules(
            "CI fails", "Update ci_validation to handle the new matrix.", arch
        )
        assert named == ["ci_validation"]

    def test_underscored_name_inside_longer_token_is_not_extracted(self):
        from pdd.agentic_sync import _extract_issue_named_modules

        arch = [{"filename": "ci_validation_python.prompt", "dependencies": []}]
        named = _extract_issue_named_modules(
            "CI fails", "See ci_validation_extra and prompts/ci_validation_python_old.py.", arch
        )
        assert named == []

    def test_runtime_llm_templates_never_extracted(self):
        """#1396 boundary: runtime ``*_LLM.prompt`` mentions add nothing."""
        from pdd.agentic_sync import _extract_issue_named_modules

        arch = self._ARCH + [
            {"filename": "agentic_sync_identify_modules_LLM.prompt", "dependencies": []}
        ]
        named = _extract_issue_named_modules(
            "Tweak templates",
            "Edit `agentic_sync_identify_modules_LLM` and "
            "prompts/agentic_sync_identify_modules_LLM.prompt.",
            arch,
        )
        assert named == []

    def test_no_architecture_extracts_nothing(self):
        from pdd.agentic_sync import _extract_issue_named_modules

        assert _extract_issue_named_modules("t", "sync `greeter`", None) == []
        assert _extract_issue_named_modules("t", "sync `greeter`", []) == []

    # ------------------------------------------------------------------
    # run_agentic_sync integration tests (the actual issue shape)
    # ------------------------------------------------------------------

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult(
            {"greeter": ["textutil"], "textutil": []}, []
        ),
    )
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=["greeter"])
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_union_issue_named_modules_missing_from_diff(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        mock_branch_diff,
        mock_build_graph,
        mock_dry_run,
        mock_runner_cls,
    ):
        """Issue names ``greeter`` and ``textutil``; diff touches only greeter →
        the final scope must include BOTH, with zero LLM calls."""
        mock_gh_cmd.return_value = (
            True,
            json.dumps(self._issue("Please sync `greeter` and `textutil` together.")),
        )
        mock_load_arch.return_value = (list(self._ARCH), Path("/tmp/architecture.json"))
        mock_dry_run.return_value = (
            True,
            {"greeter": Path("/tmp"), "textutil": Path("/tmp")},
            {"greeter": "greeter", "textutil": "textutil"},
            [],
            0.0,
        )
        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 2 modules synced successfully", 0.10)
        mock_runner_cls.return_value = mock_runner

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1980", quiet=True
        )

        assert success is True
        # The fast path stays free: no identify LLM call.
        mock_agentic_task.assert_not_called()
        # Both the diff-detected and the issue-named module reach dry-run.
        mock_dry_run.assert_called_once()
        dry_run_modules = mock_dry_run.call_args.kwargs.get(
            "modules",
            mock_dry_run.call_args.args[0] if mock_dry_run.call_args.args else None,
        )
        assert sorted(dry_run_modules) == ["greeter", "textutil"]
        # ...and the runner.
        runner_kwargs = mock_runner_cls.call_args[1]
        assert sorted(runner_kwargs["basenames"]) == ["greeter", "textutil"]

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult(
            {"greeter": ["textutil"], "textutil": []}, []
        ),
    )
    @patch(
        "pdd.agentic_sync._detect_modules_from_branch_diff",
        return_value=["greeter", "textutil"],
    )
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_diff_superset_of_issue_names_is_unchanged(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        mock_branch_diff,
        mock_build_graph,
        mock_dry_run,
        mock_runner_cls,
    ):
        """Diff scope already covers the issue-named module → behavior unchanged
        (same scope, no LLM call)."""
        mock_gh_cmd.return_value = (
            True,
            json.dumps(self._issue("Only `greeter` needs an update.")),
        )
        mock_load_arch.return_value = (list(self._ARCH), Path("/tmp/architecture.json"))
        mock_dry_run.return_value = (
            True,
            {"greeter": Path("/tmp"), "textutil": Path("/tmp")},
            {"greeter": "greeter", "textutil": "textutil"},
            [],
            0.0,
        )
        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 2 modules synced successfully", 0.10)
        mock_runner_cls.return_value = mock_runner

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1980", quiet=True
        )

        assert success is True
        mock_agentic_task.assert_not_called()
        dry_run_modules = mock_dry_run.call_args.kwargs.get(
            "modules",
            mock_dry_run.call_args.args[0] if mock_dry_run.call_args.args else None,
        )
        assert dry_run_modules == ["greeter", "textutil"]

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult(
            {"greeter": ["textutil"], "textutil": [], "python": []}, []
        ),
    )
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=["greeter"])
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_prose_non_module_words_do_not_inflate_scope(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        mock_branch_diff,
        mock_build_graph,
        mock_dry_run,
        mock_runner_cls,
    ):
        """Prose mentioning a word that happens to be a module name (``python``)
        must not inflate the diff-detected scope."""
        mock_gh_cmd.return_value = (
            True,
            json.dumps(
                self._issue("The greeting is wrong; it is written in python and says bye.")
            ),
        )
        arch = list(self._ARCH) + [{"filename": "python_python.prompt", "dependencies": []}]
        mock_load_arch.return_value = (arch, Path("/tmp/architecture.json"))
        mock_dry_run.return_value = (
            True, {"greeter": Path("/tmp")}, {"greeter": "greeter"}, [], 0.0
        )
        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 1 modules synced successfully", 0.10)
        mock_runner_cls.return_value = mock_runner

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1980", quiet=True
        )

        assert success is True
        mock_agentic_task.assert_not_called()
        dry_run_modules = mock_dry_run.call_args.kwargs.get(
            "modules",
            mock_dry_run.call_args.args[0] if mock_dry_run.call_args.args else None,
        )
        assert dry_run_modules == ["greeter"]

    # ------------------------------------------------------------------
    # Round-2 review regressions (PR #1983 Codex findings)
    # ------------------------------------------------------------------

    _DUP_TAIL_ARCH = [
        {"filename": "extensions/a/src/page_python.prompt", "dependencies": []},
        {"filename": "extensions/b/src/page_python.prompt", "dependencies": []},
    ]

    def test_extracts_modules_from_filtered_comments(self):
        """P1a: FILES_MODIFIED markers arrive as issue comments; extraction must
        cover the same filtered comment content the identify path uses."""
        from pdd.agentic_sync import _extract_issue_named_modules

        comments = [
            {"user": {"login": "app-bot"}, "body": (
                "FILES_MODIFIED:\n- prompts/textutil_python.prompt\n"
            )},
        ]
        named = _extract_issue_named_modules(
            "Sync the greeter feature",
            "The greeting is wrong.",
            self._ARCH,
            comments=comments,
        )
        assert named == ["textutil"]

    def test_low_signal_style_comment_content_not_required(self):
        """Comments param is optional: omitting it keeps title/body behavior."""
        from pdd.agentic_sync import _extract_issue_named_modules

        named = _extract_issue_named_modules(
            "Sync", "Fix `greeter`.", self._ARCH
        )
        assert named == ["greeter"]

    def test_prompt_path_tokens_preserve_path_qualification(self):
        """P1b(i): a nested prompt path must resolve to its path-qualified module
        key, not collapse to an (ambiguous) bare filename basename."""
        from pdd.agentic_sync import _extract_issue_named_modules

        named = _extract_issue_named_modules(
            "Fix page",
            "FILES_MODIFIED:\n- extensions/b/prompts/src/page_python.prompt\n",
            self._DUP_TAIL_ARCH,
        )
        assert named == ["extensions/b/src/page"]

    def test_backticked_path_qualified_key_resolves_exactly(self):
        from pdd.agentic_sync import _extract_issue_named_modules

        named = _extract_issue_named_modules(
            "Fix page",
            "Please fix `extensions/b/src/page` only.",
            self._DUP_TAIL_ARCH,
        )
        assert named == ["extensions/b/src/page"]

    def test_duplicate_tail_does_not_mask_missing_issue_module(self):
        """P1b(ii): a diff touching extensions/a's ``page`` must not mask an
        explicit request for extensions/b's ``page``."""
        from pdd.agentic_sync import _issue_modules_missing_from_scope

        missing = _issue_modules_missing_from_scope(
            ["extensions/a/src/page"],
            ["extensions/b/src/page"],
            self._DUP_TAIL_ARCH,
        )
        assert missing == ["extensions/b/src/page"]

    def test_unambiguous_tail_still_covers_bare_issue_module(self):
        """Tail-based coverage stays for globally-unambiguous tails so diff keys
        that are more qualified than architecture basenames do not re-add."""
        from pdd.agentic_sync import _issue_modules_missing_from_scope

        missing = _issue_modules_missing_from_scope(
            ["extensions/proj/src/greeter"],
            ["greeter"],
            self._ARCH,
        )
        assert missing == []

    def test_exact_scope_key_always_covers(self):
        from pdd.agentic_sync import _issue_modules_missing_from_scope

        missing = _issue_modules_missing_from_scope(
            ["extensions/b/src/page"],
            ["extensions/b/src/page"],
            self._DUP_TAIL_ARCH,
        )
        assert missing == []

    def test_hyphenated_module_name_in_prose_is_extracted(self):
        """P2: hyphenated identifier-like basenames (e.g. ``check-run``) cannot
        be ordinary prose words either; a bare word-boundary mention counts."""
        from pdd.agentic_sync import _extract_issue_named_modules

        arch = [{"filename": "check-run_python.prompt", "dependencies": []}]
        named = _extract_issue_named_modules(
            "CI checks", "Update check-run so the checks pass.", arch
        )
        assert named == ["check-run"]

    def test_hyphenated_name_inside_longer_token_is_not_extracted(self):
        from pdd.agentic_sync import _extract_issue_named_modules

        arch = [{"filename": "check-run_python.prompt", "dependencies": []}]
        named = _extract_issue_named_modules(
            "CI checks", "See double-check-run and check-run-extra.", arch
        )
        assert named == []

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult(
            {"greeter": ["textutil"], "textutil": []}, []
        ),
    )
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=["greeter"])
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_union_from_comment_only_files_modified(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        mock_branch_diff,
        mock_build_graph,
        mock_dry_run,
        mock_runner_cls,
    ):
        """P1a integration: only an issue COMMENT names the second module via a
        FILES_MODIFIED marker → the fast path must still union it."""
        issue = {
            "title": "Sync the greeter feature",
            "body": "The greeting is wrong.",
            "comments_url": "https://api.github.com/repos/o/r/issues/1980/comments",
        }
        comments = [
            {"user": {"login": "app-bot"}, "body": (
                "FILES_MODIFIED:\n- prompts/textutil_python.prompt\n"
            )},
        ]
        mock_gh_cmd.side_effect = [
            (True, json.dumps(issue)),
            (True, json.dumps(comments)),
        ]
        mock_load_arch.return_value = (list(self._ARCH), Path("/tmp/architecture.json"))
        mock_dry_run.return_value = (
            True,
            {"greeter": Path("/tmp"), "textutil": Path("/tmp")},
            {"greeter": "greeter", "textutil": "textutil"},
            [],
            0.0,
        )
        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 2 modules synced successfully", 0.10)
        mock_runner_cls.return_value = mock_runner

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1980", quiet=True
        )

        assert success is True
        mock_agentic_task.assert_not_called()
        dry_run_modules = mock_dry_run.call_args.kwargs.get(
            "modules",
            mock_dry_run.call_args.args[0] if mock_dry_run.call_args.args else None,
        )
        assert sorted(dry_run_modules) == ["greeter", "textutil"]

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult(
            {"extensions/a/src/page": [], "extensions/b/src/page": []}, []
        ),
    )
    @patch(
        "pdd.agentic_sync._detect_modules_from_branch_diff",
        return_value=["extensions/a/src/page"],
    )
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_union_path_qualified_duplicate_tail_not_masked(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        mock_branch_diff,
        mock_build_graph,
        mock_dry_run,
        mock_runner_cls,
    ):
        """P1b integration: diff touches extensions/a's ``page``; issue names
        extensions/b's ``page`` path-qualified → both must be in scope."""
        mock_gh_cmd.return_value = (
            True,
            json.dumps({
                "title": "Fix page",
                "body": "Please fix `extensions/b/src/page` as requested.",
                "comments_url": "",
            }),
        )
        mock_load_arch.return_value = (
            list(self._DUP_TAIL_ARCH), Path("/tmp/architecture.json")
        )
        mock_dry_run.return_value = (
            True,
            {"extensions/a/src/page": Path("/tmp"), "extensions/b/src/page": Path("/tmp")},
            {"extensions/a/src/page": "page", "extensions/b/src/page": "page"},
            [],
            0.0,
        )
        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 2 modules synced successfully", 0.10)
        mock_runner_cls.return_value = mock_runner

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1980", quiet=True
        )

        assert success is True
        mock_agentic_task.assert_not_called()
        dry_run_modules = mock_dry_run.call_args.kwargs.get(
            "modules",
            mock_dry_run.call_args.args[0] if mock_dry_run.call_args.args else None,
        )
        assert sorted(dry_run_modules) == [
            "extensions/a/src/page", "extensions/b/src/page",
        ]
