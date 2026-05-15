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
    _arch_path_in_scope,
    _architecture_module_basenames,
    _architecture_sync_modules,
    _augment_architecture_from_pr_branch,
    _build_scoped_global_dep_graph,
    _branch_diff_is_runtime_llm_only,
    _detect_modules_from_branch_diff,
    _enforce_orchestrator_scope,
    _filter_already_synced,
    _find_project_root,
    _is_catchall_match,
    _is_github_issue_url,
    _is_runtime_llm_template,
    _llm_fix_dry_run_failure,
    _load_architecture_json,
    _extract_allowed_write_paths,
    _parse_llm_response,
    _print_global_sync_plan,
    _resolve_module_cwd,
    _run_dry_run_validation,
    _run_single_dry_run,
    GlobalSyncAnalysis,
    GlobalSyncModule,
    run_agentic_sync,
    run_global_sync,
)
from pdd.agentic_common import IssueContract
from pdd.agentic_sync_runner import (
    DepGraphFromArchitectureResult,
    _hash_baseline_paths,
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


class TestExtractAllowedWritePaths:
    """
    Issue #1013 (F1, F3, F16): the deprecated ``_extract_allowed_write_paths``
    wrapper now delegates to :func:`pdd.agentic_common.parse_issue_contract`,
    which only recognizes two structured contract formats: HTML-comment
    blocks and heading+fenced-block. The legacy loose-markdown parsing tested
    here previously is intentionally NOT supported by the new contract API —
    deeper coverage lives in ``tests/test_agentic_common.py``.
    """

    def test_extracts_split_contract_allowed_paths_from_fenced_block(self):
        issue = """
## Allowed Write Set
```text
pdd/update_main.py
pdd/prompts/update_main_python.prompt
tests/test_update_main.py
```

But sync wrote other files.
"""
        assert _extract_allowed_write_paths(issue) == [
            "pdd/update_main.py",
            "pdd/prompts/update_main_python.prompt",
            "tests/test_update_main.py",
        ]

    def test_extracts_split_contract_allowed_paths_from_html_comment(self):
        issue = """
Some discussion.

<!-- PDD_ISSUE_CONTRACT
{"allowed_paths": ["pdd/update_main.py", "tests/test_update_main.py"]}
-->

More discussion.
"""
        assert _extract_allowed_write_paths(issue) == [
            "pdd/update_main.py",
            "tests/test_update_main.py",
        ]

    def test_returns_empty_without_contract_marker(self):
        assert _extract_allowed_write_paths("Touch `pdd/foo.py` if needed.") == []

    def test_ignores_loose_markdown_bullets_without_structured_block(self):
        # The legacy markdown-bullet format is no longer supported; the new
        # contract API requires either an HTML-comment or a fenced block.
        issue = """
## Split Contract
Allowed write set:

  * `pdd/update_main.py`
  * `tests/test_update_main.py`
"""
        assert _extract_allowed_write_paths(issue) == []


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
        nested_dir = tmp_path / "examples" / "demo"
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
        mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, [], 0.0)

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
        mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, [], 0.0)

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
        mock_dry_run.return_value = (True, {"crm_models": Path("/tmp"), "api_orders": Path("/tmp")}, [], 0.0)

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
        mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, [], 0.0)

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
        mock_dry_run.return_value = (True, {"foo": tmp_path}, [], 0.0)
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
# Iter-26: orchestrator-level scope guard for the LLM dependency-correction
# step. The per-module scope guard runs INSIDE the runner; the dependency-
# correction step writes architecture.json BEFORE any runner exists. If the
# split-contract allowed write set does not include ``architecture.json``,
# the orchestrator must skip the correction so the contract is not silently
# violated. These tests cover the gate decision plus the already-synced
# early-return path which dispatches no runner at all.
# ---------------------------------------------------------------------------


# A bullet-list contract that the parser in pdd.agentic_common recognizes.
# The ``**Allowed write set:**`` inline label is the discriminator; ``## Split
# Contract`` is just the surrounding heading. NOTE: architecture.json is NOT
# in this allow set, so the orchestrator must skip the deps-correction step.
_CONTRACT_BODY_ARCH_OUT_OF_SCOPE = (
    "Fix foo.\n"
    "\n"
    "## Split Contract\n"
    "\n"
    "**Allowed write set:**\n"
    "\n"
    "- `pdd/foo.py`\n"
)

# Same shape but architecture.json IS in the allow set — the correction should
# be applied.
_CONTRACT_BODY_ARCH_IN_SCOPE = (
    "Fix foo.\n"
    "\n"
    "## Split Contract\n"
    "\n"
    "**Allowed write set:**\n"
    "\n"
    "- `pdd/foo.py`\n"
    "- `architecture.json`\n"
)

# Iter-28 B-2: contract allows a NESTED architecture path. Used by the
# nested-arch B-2 tests to assert the gate compares the real ``arch_path``
# (resolved repo-relative) rather than the literal string ``architecture.json``.
_CONTRACT_BODY_NESTED_ARCH_IN_SCOPE = (
    "Fix foo.\n"
    "\n"
    "## Split Contract\n"
    "\n"
    "**Allowed write set:**\n"
    "\n"
    "- `pdd/foo.py`\n"
    "- `frontend/architecture.json`\n"
)


class TestDependencyCorrectionsScopeGuard:
    """Verify the orchestrator-level scope gate on
    ``_apply_architecture_corrections``. The gate runs BEFORE any runner is
    dispatched, so per-module scope enforcement cannot catch this write."""

    @patch("pdd.agentic_sync._find_project_root")
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
    def test_dependency_corrections_skipped_when_arch_outside_contract(
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
        mock_find_root,
        tmp_path,
        capsys,
    ):
        """Contract excludes architecture.json → corrections must NOT run."""
        # Iter-32 B-1: pin project root to tmp_path so the dispatch-boundary
        # orchestrator scope guard sweeps a clean tmp tree (the real repo
        # has dirty worktrees that would trip the guard).
        _init_git_repo(tmp_path)
        mock_find_root.return_value = tmp_path
        issue_data = {
            "title": "Fix foo",
            "body": _CONTRACT_BODY_ARCH_OUT_OF_SCOPE,
            "comments_url": "",
        }
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (
            [{"filename": "foo_python.prompt", "dependencies": []}],
            tmp_path / "architecture.json",
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
        mock_dry_run.return_value = (True, {"foo": tmp_path}, [], 0.0)

        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 1 modules synced successfully", 0.10)
        mock_runner_cls.return_value = mock_runner

        success, msg, cost, model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1",
            quiet=False,  # capture the skip-warning text
        )

        assert success is True
        mock_apply_corrections.assert_not_called()
        captured = capsys.readouterr()
        # Warning text from the orchestrator skip branch. Rich console may
        # line-wrap the message at any width, so we collapse whitespace
        # before substring-matching for the discriminating phrase.
        flat = " ".join(captured.out.split())
        assert "Sync scope guard: skipping LLM dependency corrections" in flat
        assert "architecture.json is outside" in flat

    @patch("pdd.agentic_sync._find_project_root")
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
    def test_dependency_corrections_applied_when_arch_in_contract(
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
        mock_find_root,
        tmp_path,
    ):
        """Contract includes architecture.json → corrections must run."""
        # Iter-32 B-1: init git in tmp_path so the dispatch-boundary
        # orchestrator scope guard's working-tree probes succeed.
        _init_git_repo(tmp_path)
        mock_find_root.return_value = tmp_path
        arch_data = [{"filename": "foo_python.prompt", "dependencies": []}]
        mock_apply_corrections.return_value = arch_data

        issue_data = {
            "title": "Fix foo",
            "body": _CONTRACT_BODY_ARCH_IN_SCOPE,
            "comments_url": "",
        }
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (
            arch_data,
            tmp_path / "architecture.json",
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
        mock_dry_run.return_value = (True, {"foo": tmp_path}, [], 0.0)

        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 1 modules synced successfully", 0.10)
        mock_runner_cls.return_value = mock_runner

        success, _msg, _cost, _model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        assert success is True
        mock_apply_corrections.assert_called_once()

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
    def test_dependency_corrections_applied_when_no_contract(
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
        tmp_path,
    ):
        """No contract markers → permissive mode preserves pre-iter-26 behavior."""
        arch_data = [{"filename": "foo_python.prompt", "dependencies": []}]
        mock_apply_corrections.return_value = arch_data

        # No HTML comment, no fenced block, no ``**Allowed write set:**`` label.
        issue_data = {
            "title": "Fix foo",
            "body": "Just fix foo, no contract here.",
            "comments_url": "",
        }
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (
            arch_data,
            tmp_path / "architecture.json",
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
        mock_dry_run.return_value = (True, {"foo": tmp_path}, [], 0.0)

        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 1 modules synced successfully", 0.10)
        mock_runner_cls.return_value = mock_runner

        success, _msg, _cost, _model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        assert success is True
        mock_apply_corrections.assert_called_once()

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
    def test_dependency_corrections_applied_when_scope_guard_disabled(
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
        tmp_path,
    ):
        """``--no-scope-guard`` bypasses the gate even when arch is out of scope."""
        arch_data = [{"filename": "foo_python.prompt", "dependencies": []}]
        mock_apply_corrections.return_value = arch_data

        issue_data = {
            "title": "Fix foo",
            "body": _CONTRACT_BODY_ARCH_OUT_OF_SCOPE,
            "comments_url": "",
        }
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (
            arch_data,
            tmp_path / "architecture.json",
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
        mock_dry_run.return_value = (True, {"foo": tmp_path}, [], 0.0)

        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 1 modules synced successfully", 0.10)
        mock_runner_cls.return_value = mock_runner

        success, _msg, _cost, _model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1",
            quiet=True,
            scope_guard=False,
        )

        assert success is True
        mock_apply_corrections.assert_called_once()

    @patch("pdd.agentic_sync._apply_architecture_corrections")
    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync.DurableSyncRunner")
    @patch("pdd.agentic_sync._filter_already_synced", return_value=[])
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
    def test_already_synced_early_return_does_not_leak_arch_changes(
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
        mock_async_runner_cls,
        mock_apply_corrections,
        tmp_path,
    ):
        """Defensive: even if every module is already synced and the runner is
        never dispatched, the orchestrator must NOT write architecture.json
        out-of-scope. Verifies both the mock-level assertion AND that no
        ``M architecture.json`` shows up in a real git repo's ``git status``
        after the orchestrator returns its early "already synced" success.
        """
        # Build a tiny git repo with a committed architecture.json so any
        # subsequent write would show as a tracked modification.
        repo = tmp_path / "repo"
        repo.mkdir()
        subprocess.run(["git", "init", "--quiet"], cwd=repo, check=True)
        subprocess.run(
            ["git", "config", "user.email", "test@example.com"],
            cwd=repo,
            check=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Test"],
            cwd=repo,
            check=True,
        )
        arch_file = repo / "architecture.json"
        arch_data = [{"filename": "foo_python.prompt", "dependencies": []}]
        arch_file.write_text(json.dumps(arch_data, indent=2))
        subprocess.run(
            ["git", "add", "architecture.json"], cwd=repo, check=True
        )
        subprocess.run(
            ["git", "commit", "--quiet", "-m", "init arch"],
            cwd=repo,
            check=True,
        )

        issue_data = {
            "title": "Fix foo",
            "body": _CONTRACT_BODY_ARCH_OUT_OF_SCOPE,
            "comments_url": "",
        }
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (arch_data, arch_file)
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
        mock_dry_run.return_value = (True, {"foo": repo}, [], 0.0)

        old_cwd = Path.cwd()
        try:
            os.chdir(repo)
            success, msg, _cost, _model = run_agentic_sync(
                "https://github.com/owner/repo/issues/1", quiet=True
            )
        finally:
            os.chdir(old_cwd)

        # Orchestrator returns the "already synced" early-success path.
        assert success is True
        assert "already synced" in msg.lower()

        # The gate must have refused the only out-of-contract write the
        # orchestrator can perform.
        mock_apply_corrections.assert_not_called()
        # No runner is dispatched on the already-synced path.
        mock_async_runner_cls.assert_not_called()
        mock_durable_runner_cls.assert_not_called()

        # Defense-in-depth: a real git status check confirms the on-disk
        # architecture.json is untouched.
        status = subprocess.run(
            ["git", "status", "--porcelain"],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        )
        assert "architecture.json" not in status.stdout

    # ------------------------------------------------------------------
    # Iter-28 B-2: nested arch_path bypass
    # ------------------------------------------------------------------

    @patch("pdd.agentic_sync._find_project_root")
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
    def test_dependency_corrections_skipped_for_nested_arch_outside_contract(
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
        mock_find_root,
        tmp_path,
    ):
        """Contract allows the literal string ``architecture.json`` but the
        REAL arch path is ``frontend/architecture.json``. Iter-28 B-2: the
        gate must compare the resolved arch path, not the bare string, so
        the nested arch write is rejected."""
        # Iter-32 B-1: init git + pin root so the dispatch-boundary scope
        # guard sweeps a clean tmp tree.
        _init_git_repo(tmp_path)
        mock_find_root.return_value = tmp_path
        arch_data = [{"filename": "foo_python.prompt", "dependencies": []}]
        # Contract allows root architecture.json only — NOT the nested path.
        issue_data = {
            "title": "Fix foo",
            "body": _CONTRACT_BODY_ARCH_IN_SCOPE,
            "comments_url": "",
        }
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        # arch_path resolves nested: frontend/architecture.json under
        # tmp_path. The literal-string gate would have matched the contract's
        # ``architecture.json`` entry and let the write through; the
        # resolved-path gate must NOT.
        nested_arch = tmp_path / "frontend" / "architecture.json"
        (tmp_path / "frontend").mkdir()
        mock_load_arch.return_value = (arch_data, nested_arch)
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
        mock_dry_run.return_value = (True, {"foo": tmp_path}, [], 0.0)

        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 1 modules synced successfully", 0.10)
        mock_runner_cls.return_value = mock_runner

        success, _msg, _cost, _model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        assert success is True
        mock_apply_corrections.assert_not_called()

    @patch("pdd.agentic_sync._find_project_root")
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
    def test_dependency_corrections_applied_for_nested_arch_in_contract(
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
        mock_find_root,
        tmp_path,
    ):
        """Contract explicitly allows ``frontend/architecture.json`` and the
        arch path matches → gate must permit the write."""
        # Iter-32 B-1: init git so the dispatch-boundary scope guard's
        # working-tree probes succeed.
        _init_git_repo(tmp_path)
        mock_find_root.return_value = tmp_path
        arch_data = [{"filename": "foo_python.prompt", "dependencies": []}]
        mock_apply_corrections.return_value = arch_data

        issue_data = {
            "title": "Fix foo",
            "body": _CONTRACT_BODY_NESTED_ARCH_IN_SCOPE,
            "comments_url": "",
        }
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        nested_arch = tmp_path / "frontend" / "architecture.json"
        (tmp_path / "frontend").mkdir()
        mock_load_arch.return_value = (arch_data, nested_arch)
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
        mock_dry_run.return_value = (True, {"foo": tmp_path}, [], 0.0)

        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 1 modules synced successfully", 0.10)
        mock_runner_cls.return_value = mock_runner

        success, _msg, _cost, _model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        assert success is True
        mock_apply_corrections.assert_called_once()

    @patch("pdd.agentic_sync._find_project_root")
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
    def test_dependency_corrections_skipped_for_arch_outside_project_root(
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
        mock_find_root,
        tmp_path,
    ):
        """``arch_path`` resolves outside ``project_root`` → never in scope.

        Defense-in-depth: even if some upstream bug threads an arch path
        outside the repo root into the orchestrator, ``_arch_path_in_scope``
        catches the ``ValueError`` from ``relative_to`` and returns False so
        the write is refused.
        """
        # Iter-32 B-1: init git + pin root so the dispatch-boundary scope
        # guard sweeps a clean tmp tree.
        _init_git_repo(tmp_path)
        mock_find_root.return_value = tmp_path
        arch_data = [{"filename": "foo_python.prompt", "dependencies": []}]
        issue_data = {
            "title": "Fix foo",
            "body": _CONTRACT_BODY_ARCH_IN_SCOPE,
            "comments_url": "",
        }
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        # Force an arch path that resolves OUTSIDE project_root.
        outside_arch = (tmp_path.parent / "outside_root" / "architecture.json").resolve()
        outside_arch.parent.mkdir(parents=True, exist_ok=True)
        mock_load_arch.return_value = (arch_data, outside_arch)
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
        mock_dry_run.return_value = (True, {"foo": tmp_path}, [], 0.0)

        mock_runner = MagicMock()
        mock_runner.run.return_value = (True, "All 1 modules synced successfully", 0.10)
        mock_runner_cls.return_value = mock_runner

        success, _msg, _cost, _model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        assert success is True
        mock_apply_corrections.assert_not_called()


# ---------------------------------------------------------------------------
# _arch_path_in_scope (iter-28 B-2 helper, unit-level)
# ---------------------------------------------------------------------------


class TestArchPathInScope:
    """Unit-level coverage of the resolved-path scope check used by the
    iter-26 orchestrator gate, post-iter-28 B-2."""

    @staticmethod
    def _contract(*allowed: str) -> IssueContract:
        return IssueContract(
            allowed_paths=tuple(allowed),
            companion_allowlist=(),
            source="test",
        )

    def test_no_contract_permissive(self, tmp_path):
        """No contract → always in scope (pre-iter-26 behavior preserved)."""
        assert _arch_path_in_scope(
            tmp_path / "architecture.json",
            tmp_path,
            issue_contract=None,
            scope_guard=True,
        )

    def test_scope_guard_disabled_bypasses_check(self, tmp_path):
        """``--no-scope-guard`` → always in scope, contract ignored."""
        contract = self._contract("pdd/foo.py")  # arch NOT in contract
        assert _arch_path_in_scope(
            tmp_path / "architecture.json",
            tmp_path,
            issue_contract=contract,
            scope_guard=False,
        )

    def test_literal_arch_in_contract_match(self, tmp_path):
        """Root arch + contract allows ``architecture.json`` → in scope."""
        contract = self._contract("pdd/foo.py", "architecture.json")
        assert _arch_path_in_scope(
            tmp_path / "architecture.json",
            tmp_path,
            issue_contract=contract,
            scope_guard=True,
        )

    def test_nested_arch_with_literal_contract_rejected(self, tmp_path):
        """Nested arch + contract only allows literal ``architecture.json``
        → out of scope (the iter-28 B-2 fix)."""
        contract = self._contract("pdd/foo.py", "architecture.json")
        assert not _arch_path_in_scope(
            tmp_path / "frontend" / "architecture.json",
            tmp_path,
            issue_contract=contract,
            scope_guard=True,
        )

    def test_nested_arch_with_nested_contract_match(self, tmp_path):
        """Nested arch + contract names the same nested path → in scope."""
        contract = self._contract("pdd/foo.py", "frontend/architecture.json")
        assert _arch_path_in_scope(
            tmp_path / "frontend" / "architecture.json",
            tmp_path,
            issue_contract=contract,
            scope_guard=True,
        )

    def test_arch_outside_project_root_rejected(self, tmp_path):
        """``arch_path`` outside the repo → out of scope (ValueError → False)."""
        contract = self._contract("architecture.json")
        outside = (tmp_path.parent / "outside_root" / "architecture.json").resolve()
        outside.parent.mkdir(parents=True, exist_ok=True)
        assert not _arch_path_in_scope(
            outside,
            tmp_path,
            issue_contract=contract,
            scope_guard=True,
        )

    def test_empty_contract_allowed_paths_rejected(self, tmp_path):
        """Empty ``allowed_paths`` tuple → no path is in scope."""
        contract = self._contract()  # ``allowed_paths=()``
        assert not _arch_path_in_scope(
            tmp_path / "architecture.json",
            tmp_path,
            issue_contract=contract,
            scope_guard=True,
        )


# ---------------------------------------------------------------------------
# _enforce_orchestrator_scope (iter-30 unified orchestrator scope guard)
# ---------------------------------------------------------------------------


def _init_git_repo(tmp_path: Path) -> None:
    """Create a minimal git repo at *tmp_path* for orchestrator scope tests."""
    subprocess.run(
        ["git", "init", "--quiet", "--initial-branch=main", str(tmp_path)],
        check=True,
    )
    subprocess.run(
        ["git", "-C", str(tmp_path), "config", "user.email", "test@example.com"],
        check=True,
    )
    subprocess.run(
        ["git", "-C", str(tmp_path), "config", "user.name", "Test"],
        check=True,
    )
    # Seed with a committed file so HEAD exists.
    seed = tmp_path / ".pddrc"
    seed.write_text("# pddrc\n", encoding="utf-8")
    subprocess.run(
        ["git", "-C", str(tmp_path), "add", "-A"],
        check=True,
    )
    subprocess.run(
        ["git", "-C", str(tmp_path), "commit", "--quiet", "-m", "init"],
        check=True,
    )


def _hash_baseline_single(project_root: Path, rel: str) -> str:
    """Tiny helper: SHA-1 of the file at *project_root / rel* (for baseline maps)."""
    import hashlib
    return hashlib.sha1((project_root / rel).read_bytes()).hexdigest()


class TestEnforceOrchestratorScope:
    """Iter-30: unit-level coverage of the orchestrator scope guard helper.

    These tests exercise :func:`_enforce_orchestrator_scope` directly. Higher-
    level integration tests that drive :func:`run_agentic_sync` end-to-end are
    in :class:`TestOrchestratorScopeGuardIntegration`.
    """

    @staticmethod
    def _contract(*allowed: str) -> IssueContract:
        return IssueContract(
            allowed_paths=tuple(allowed),
            companion_allowlist=(),
            source="test",
        )

    def test_no_op_when_no_contract(self, tmp_path):
        """``issue_contract is None`` → permissive, returns None unconditionally."""
        _init_git_repo(tmp_path)
        out_of_scope = tmp_path / "wild.py"
        out_of_scope.write_text("unsanctioned\n", encoding="utf-8")

        result = _enforce_orchestrator_scope(
            tmp_path,
            issue_contract=None,
            scope_guard=True,
            baseline_changed={},
            baseline_ignored={},
            quiet=True,
        )
        assert result is None
        # Permissive mode preserves the file on disk.
        assert out_of_scope.exists()

    def test_no_op_when_scope_guard_disabled(self, tmp_path):
        """``scope_guard=False`` → no-op even with a contract."""
        _init_git_repo(tmp_path)
        out_of_scope = tmp_path / "wild.py"
        out_of_scope.write_text("unsanctioned\n", encoding="utf-8")

        contract = self._contract("pdd/foo.py")
        result = _enforce_orchestrator_scope(
            tmp_path,
            issue_contract=contract,
            scope_guard=False,
            baseline_changed={},
            baseline_ignored={},
            quiet=True,
        )
        assert result is None
        assert out_of_scope.exists()

    def test_reverts_untracked_out_of_contract_writes(self, tmp_path):
        """Untracked out-of-contract file → reverted, diagnostic returned."""
        _init_git_repo(tmp_path)
        contract = self._contract("pdd/foo.py")
        out_of_scope = tmp_path / "outside.py"
        out_of_scope.write_text("oops\n", encoding="utf-8")

        result = _enforce_orchestrator_scope(
            tmp_path,
            issue_contract=contract,
            scope_guard=True,
            baseline_changed={},
            baseline_ignored={},
            quiet=True,
        )
        assert result is not None
        assert "outside.py" in result
        assert "Orchestrator scope guard" in result
        assert not out_of_scope.exists()

    def test_preserves_pre_existing_baseline_path(self, tmp_path):
        """Pre-existing untracked file in baseline (unchanged SHA) → preserved."""
        _init_git_repo(tmp_path)
        contract = self._contract("pdd/foo.py")
        user_wip = tmp_path / "userwip.py"
        user_wip.write_text("user code\n", encoding="utf-8")

        # Snapshot the baseline (matches what run_agentic_sync does).
        baseline = {"userwip.py": _hash_baseline_single(tmp_path, "userwip.py")}

        result = _enforce_orchestrator_scope(
            tmp_path,
            issue_contract=contract,
            scope_guard=True,
            baseline_changed=baseline,
            baseline_ignored={},
            quiet=True,
        )
        # Unchanged baseline → no revert needed.
        assert result is None
        assert user_wip.exists()

    def test_detects_baseline_clobber(self, tmp_path):
        """Baseline path overwritten with different content → flagged & reverted."""
        _init_git_repo(tmp_path)
        contract = self._contract("pdd/foo.py")
        user_wip = tmp_path / "userwip.py"
        user_wip.write_text("original\n", encoding="utf-8")
        baseline = {"userwip.py": _hash_baseline_single(tmp_path, "userwip.py")}

        # Now clobber the baseline.
        user_wip.write_text("CLOBBERED by LLM\n", encoding="utf-8")

        result = _enforce_orchestrator_scope(
            tmp_path,
            issue_contract=contract,
            scope_guard=True,
            baseline_changed=baseline,
            baseline_ignored={},
            quiet=True,
        )
        assert result is not None
        assert "userwip.py" in result
        # The file is gone after the revert helper sweeps it (untracked +
        # not allowed → removed).
        assert not user_wip.exists()

    def test_companion_allowlist_default_auto_allows_pdd_meta(self, tmp_path):
        """``.pdd/meta/*.json`` is auto-allowed by DEFAULT_SYNC_COMPANION_ALLOWLIST."""
        _init_git_repo(tmp_path)
        contract = self._contract("pdd/foo.py")
        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)
        meta_file = meta_dir / "foo_python.json"
        meta_file.write_text('{"fingerprint": "x"}', encoding="utf-8")

        result = _enforce_orchestrator_scope(
            tmp_path,
            issue_contract=contract,
            scope_guard=True,
            baseline_changed={},
            baseline_ignored={},
            quiet=True,
        )
        # Companion-allowlisted → no revert, no diagnostic.
        assert result is None
        assert meta_file.exists()


# ---------------------------------------------------------------------------
# Orchestrator scope guard integration (iter-30)
# ---------------------------------------------------------------------------


class TestOrchestratorScopeGuardIntegration:
    """Iter-30: integration tests that drive :func:`run_agentic_sync` and
    verify the orchestrator scope guard reverts/preserves correctly at the
    early-return boundary."""

    _ISSUE_BODY_WITH_BULLET_CONTRACT = (
        "Title: feat: foo\n\n"
        "## Allowed Write Set\n\n"
        "**Allowed write set:**\n"
        "- pdd/foo.py\n"
    )
    _ISSUE_BODY_NO_CONTRACT = "Title: feat: foo\n\nNo structured contract here."

    def _issue_payload(self, body: str) -> str:
        return json.dumps({"title": "Test", "body": body, "comments_url": ""})

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync.load_prompt_template", return_value="t {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_reverts_out_of_contract_llm_writes(
        self,
        _mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        _mock_load_prompt,
        mock_runner_cls,
        tmp_path,
        monkeypatch,
    ):
        """LLM writes an out-of-contract file during identify-modules →
        orchestrator scope guard reverts before the orchestrator returns.

        The mock for ``run_agentic_task`` writes ``outside.py`` to disk and
        returns an empty module list, so the orchestrator hits the
        "LLM identified no modules to sync" early return (line ~1925). The
        scope guard wrap on that return must observe and revert the write.
        """
        _init_git_repo(tmp_path)
        monkeypatch.setattr("pdd.agentic_sync._find_project_root", lambda *_: tmp_path)
        monkeypatch.setattr(
            "pdd.agentic_sync._detect_modules_from_branch_diff", lambda *_: []
        )
        mock_gh_cmd.return_value = (
            True, self._issue_payload(self._ISSUE_BODY_WITH_BULLET_CONTRACT)
        )
        mock_load_arch.return_value = (None, tmp_path / "architecture.json")

        def llm_side_effect(*_args, **_kwargs):
            # Simulate LLM writing an out-of-contract file mid-call.
            (tmp_path / "outside.py").write_text("LLM wrote me\n", encoding="utf-8")
            # Return a parse-failing response so we land on the
            # "no modules to sync" early return inside the scope guard.
            return True, "MODULES_TO_SYNC: []\nDEPS_VALID: true", 0.01, "anthropic"

        mock_agentic_task.side_effect = llm_side_effect

        success, msg, _cost, _model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        assert success is False
        assert "Orchestrator scope guard" in msg
        assert "outside.py" in msg
        assert not (tmp_path / "outside.py").exists(), (
            "scope guard must revert the out-of-contract write"
        )
        mock_runner_cls.assert_not_called()

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync.load_prompt_template", return_value="t {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_preserves_pre_existing_baseline(
        self,
        _mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        _mock_load_prompt,
        mock_runner_cls,
        tmp_path,
        monkeypatch,
    ):
        """User WIP that pre-exists at orchestrator entry → preserved."""
        _init_git_repo(tmp_path)
        # Pre-existing dirty user WIP.
        (tmp_path / "userwip.py").write_text("user work in progress\n", encoding="utf-8")

        monkeypatch.setattr("pdd.agentic_sync._find_project_root", lambda *_: tmp_path)
        monkeypatch.setattr(
            "pdd.agentic_sync._detect_modules_from_branch_diff", lambda *_: []
        )
        mock_gh_cmd.return_value = (
            True, self._issue_payload(self._ISSUE_BODY_WITH_BULLET_CONTRACT)
        )
        mock_load_arch.return_value = (None, tmp_path / "architecture.json")

        # LLM does NOT touch userwip.py; just returns no modules.
        mock_agentic_task.return_value = (
            True, "MODULES_TO_SYNC: []\nDEPS_VALID: true", 0.01, "anthropic"
        )

        success, msg, _cost, _model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        # Pre-existing untracked file MUST be preserved by the baseline rule.
        assert (tmp_path / "userwip.py").exists()
        assert (tmp_path / "userwip.py").read_text(encoding="utf-8") == (
            "user work in progress\n"
        )
        # Scope guard MUST NOT mention userwip.py in the diagnostic.
        assert "userwip.py" not in msg
        mock_runner_cls.assert_not_called()

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync.load_prompt_template", return_value="t {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_detects_baseline_clobber(
        self,
        _mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        _mock_load_prompt,
        mock_runner_cls,
        tmp_path,
        monkeypatch,
    ):
        """LLM overwrites a baseline path with new content → flagged."""
        _init_git_repo(tmp_path)
        (tmp_path / "userwip.py").write_text("original\n", encoding="utf-8")

        monkeypatch.setattr("pdd.agentic_sync._find_project_root", lambda *_: tmp_path)
        monkeypatch.setattr(
            "pdd.agentic_sync._detect_modules_from_branch_diff", lambda *_: []
        )
        mock_gh_cmd.return_value = (
            True, self._issue_payload(self._ISSUE_BODY_WITH_BULLET_CONTRACT)
        )
        mock_load_arch.return_value = (None, tmp_path / "architecture.json")

        def llm_side_effect(*_args, **_kwargs):
            # Clobber pre-existing baseline path.
            (tmp_path / "userwip.py").write_text(
                "CLOBBERED by malicious LLM\n", encoding="utf-8"
            )
            return True, "MODULES_TO_SYNC: []\nDEPS_VALID: true", 0.01, "anthropic"

        mock_agentic_task.side_effect = llm_side_effect

        success, msg, _cost, _model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        assert success is False
        assert "Orchestrator scope guard" in msg
        assert "userwip.py" in msg
        mock_runner_cls.assert_not_called()

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync.load_prompt_template", return_value="t {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_no_op_when_no_contract(
        self,
        _mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        _mock_load_prompt,
        mock_runner_cls,
        tmp_path,
        monkeypatch,
    ):
        """Permissive mode: no contract on issue → no revert, existing
        behavior preserved."""
        _init_git_repo(tmp_path)
        monkeypatch.setattr("pdd.agentic_sync._find_project_root", lambda *_: tmp_path)
        monkeypatch.setattr(
            "pdd.agentic_sync._detect_modules_from_branch_diff", lambda *_: []
        )
        mock_gh_cmd.return_value = (
            True, self._issue_payload(self._ISSUE_BODY_NO_CONTRACT)
        )
        mock_load_arch.return_value = (None, tmp_path / "architecture.json")

        def llm_side_effect(*_args, **_kwargs):
            (tmp_path / "outside.py").write_text("LLM wrote me\n", encoding="utf-8")
            return True, "MODULES_TO_SYNC: []\nDEPS_VALID: true", 0.01, "anthropic"

        mock_agentic_task.side_effect = llm_side_effect

        success, msg, _cost, _model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        # No contract → permissive mode → no revert, no diagnostic.
        assert "Orchestrator scope guard" not in msg
        assert (tmp_path / "outside.py").exists()

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync.load_prompt_template", return_value="t {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_no_op_with_no_scope_guard_flag(
        self,
        _mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        _mock_load_prompt,
        mock_runner_cls,
        tmp_path,
        monkeypatch,
    ):
        """``scope_guard=False`` → explicit opt-out, no revert, existing
        behavior preserved (matches iter-26 / iter-28 gate semantics)."""
        _init_git_repo(tmp_path)
        monkeypatch.setattr("pdd.agentic_sync._find_project_root", lambda *_: tmp_path)
        monkeypatch.setattr(
            "pdd.agentic_sync._detect_modules_from_branch_diff", lambda *_: []
        )
        mock_gh_cmd.return_value = (
            True, self._issue_payload(self._ISSUE_BODY_WITH_BULLET_CONTRACT)
        )
        mock_load_arch.return_value = (None, tmp_path / "architecture.json")

        def llm_side_effect(*_args, **_kwargs):
            (tmp_path / "outside.py").write_text("LLM wrote me\n", encoding="utf-8")
            return True, "MODULES_TO_SYNC: []\nDEPS_VALID: true", 0.01, "anthropic"

        mock_agentic_task.side_effect = llm_side_effect

        success, msg, _cost, _model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1",
            quiet=True,
            scope_guard=False,
        )

        # Explicit opt-out → no revert, no diagnostic.
        assert "Orchestrator scope guard" not in msg
        assert (tmp_path / "outside.py").exists()

    # ---------------------------------------------------------------------
    # Iter-32 B-1: dispatch-boundary scope guard
    # ---------------------------------------------------------------------
    # iter-30 wrapped every EARLY-RETURN site with
    # ``_orch_scope_check_return``. The natural completion (iter-32) is to
    # also gate the SUCCESSFUL DISPATCH path so pre-dispatch out-of-contract
    # writes are not snapshotted as ``_baseline_changed_paths`` by the
    # runner and silently preserved for the entire sync session.

    @patch("pdd.agentic_sync._filter_already_synced")
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync.load_prompt_template", return_value="t {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_orchestrator_scope_guard_blocks_dispatch_when_predispatch_writes_out_of_contract(
        self,
        _mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        _mock_load_prompt,
        mock_runner_cls,
        mock_dry_run,
        mock_filter_synced,
        tmp_path,
        monkeypatch,
    ):
        """Pre-dispatch out-of-contract write that survives past all
        early-return sites → orchestrator scope guard blocks dispatch and
        reverts the write before the runner is constructed."""
        _init_git_repo(tmp_path)
        monkeypatch.setattr("pdd.agentic_sync._find_project_root", lambda *_: tmp_path)
        monkeypatch.setattr(
            "pdd.agentic_sync._detect_modules_from_branch_diff", lambda *_: []
        )
        mock_gh_cmd.return_value = (
            True, self._issue_payload(self._ISSUE_BODY_WITH_BULLET_CONTRACT)
        )
        mock_load_arch.return_value = (None, tmp_path / "architecture.json")

        def llm_side_effect(*_args, **_kwargs):
            # Simulate the LLM identify-modules call writing an
            # out-of-contract file mid-call AND returning a valid module
            # list so the flow proceeds toward dispatch (skipping the
            # iter-30 early-return wrap).
            (tmp_path / "outside.py").write_text("LLM wrote me\n", encoding="utf-8")
            return True, 'MODULES_TO_SYNC: ["foo"]\nDEPS_VALID: true', 0.01, "anthropic"

        mock_agentic_task.side_effect = llm_side_effect
        # Skip dry-run early-return: report success with a cwd for "foo".
        mock_dry_run.return_value = (True, {"foo": tmp_path}, [], 0.0)
        # Skip "all already synced" early-return: keep "foo" in the list.
        mock_filter_synced.return_value = ["foo"]

        success, msg, _cost, _model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        assert success is False
        assert "before dispatch" in msg
        assert "outside.py" in msg
        assert not (tmp_path / "outside.py").exists(), (
            "dispatch-boundary scope guard must revert the out-of-contract write"
        )
        # Runner was NEVER constructed because dispatch was aborted.
        mock_runner_cls.assert_not_called()

    @patch("pdd.agentic_sync._filter_already_synced")
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync.load_prompt_template", return_value="t {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_orchestrator_scope_guard_allows_dispatch_when_clean(
        self,
        _mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        _mock_load_prompt,
        mock_runner_cls,
        mock_dry_run,
        mock_filter_synced,
        tmp_path,
        monkeypatch,
    ):
        """Clean working tree at dispatch boundary → runner constructed
        and dispatched normally."""
        _init_git_repo(tmp_path)
        monkeypatch.setattr("pdd.agentic_sync._find_project_root", lambda *_: tmp_path)
        monkeypatch.setattr(
            "pdd.agentic_sync._detect_modules_from_branch_diff", lambda *_: []
        )
        mock_gh_cmd.return_value = (
            True, self._issue_payload(self._ISSUE_BODY_WITH_BULLET_CONTRACT)
        )
        mock_load_arch.return_value = (None, tmp_path / "architecture.json")

        # LLM does NOT write anything out-of-contract; returns a valid
        # module list.
        mock_agentic_task.return_value = (
            True, 'MODULES_TO_SYNC: ["foo"]\nDEPS_VALID: true', 0.01, "anthropic"
        )
        mock_dry_run.return_value = (True, {"foo": tmp_path}, [], 0.0)
        mock_filter_synced.return_value = ["foo"]
        # Provide a runnable runner mock so the dispatch can complete.
        mock_runner_cls.return_value.run.return_value = (True, "ok", 0.0)

        success, msg, _cost, _model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        assert success is True
        assert msg == "ok"
        assert "before dispatch" not in msg
        # Runner WAS constructed and .run() WAS called.
        mock_runner_cls.assert_called_once()
        mock_runner_cls.return_value.run.assert_called_once()

    @patch("pdd.agentic_sync._filter_already_synced")
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync.load_prompt_template", return_value="t {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_orchestrator_scope_guard_dispatch_check_is_no_op_with_no_contract(
        self,
        _mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        _mock_load_prompt,
        mock_runner_cls,
        mock_dry_run,
        mock_filter_synced,
        tmp_path,
        monkeypatch,
    ):
        """Permissive mode (no contract markers) → dispatch-boundary check
        is a no-op even when the LLM wrote out-of-contract files."""
        _init_git_repo(tmp_path)
        monkeypatch.setattr("pdd.agentic_sync._find_project_root", lambda *_: tmp_path)
        monkeypatch.setattr(
            "pdd.agentic_sync._detect_modules_from_branch_diff", lambda *_: []
        )
        mock_gh_cmd.return_value = (
            True, self._issue_payload(self._ISSUE_BODY_NO_CONTRACT)
        )
        mock_load_arch.return_value = (None, tmp_path / "architecture.json")

        def llm_side_effect(*_args, **_kwargs):
            (tmp_path / "outside.py").write_text("LLM wrote me\n", encoding="utf-8")
            return True, 'MODULES_TO_SYNC: ["foo"]\nDEPS_VALID: true', 0.01, "anthropic"

        mock_agentic_task.side_effect = llm_side_effect
        mock_dry_run.return_value = (True, {"foo": tmp_path}, [], 0.0)
        mock_filter_synced.return_value = ["foo"]
        mock_runner_cls.return_value.run.return_value = (True, "ok", 0.0)

        success, msg, _cost, _model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1", quiet=True
        )

        # Permissive mode → dispatch proceeds, no revert, file preserved.
        assert success is True
        assert "before dispatch" not in msg
        assert (tmp_path / "outside.py").exists()
        mock_runner_cls.assert_called_once()
        mock_runner_cls.return_value.run.assert_called_once()

    @patch("pdd.agentic_sync._filter_already_synced")
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync.load_prompt_template", return_value="t {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_orchestrator_scope_guard_dispatch_check_is_no_op_with_scope_guard_disabled(
        self,
        _mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        _mock_load_prompt,
        mock_runner_cls,
        mock_dry_run,
        mock_filter_synced,
        tmp_path,
        monkeypatch,
    ):
        """``scope_guard=False`` (opt-out) with a contract present →
        dispatch-boundary check is a no-op."""
        _init_git_repo(tmp_path)
        monkeypatch.setattr("pdd.agentic_sync._find_project_root", lambda *_: tmp_path)
        monkeypatch.setattr(
            "pdd.agentic_sync._detect_modules_from_branch_diff", lambda *_: []
        )
        mock_gh_cmd.return_value = (
            True, self._issue_payload(self._ISSUE_BODY_WITH_BULLET_CONTRACT)
        )
        mock_load_arch.return_value = (None, tmp_path / "architecture.json")

        def llm_side_effect(*_args, **_kwargs):
            (tmp_path / "outside.py").write_text("LLM wrote me\n", encoding="utf-8")
            return True, 'MODULES_TO_SYNC: ["foo"]\nDEPS_VALID: true', 0.01, "anthropic"

        mock_agentic_task.side_effect = llm_side_effect
        mock_dry_run.return_value = (True, {"foo": tmp_path}, [], 0.0)
        mock_filter_synced.return_value = ["foo"]
        mock_runner_cls.return_value.run.return_value = (True, "ok", 0.0)

        success, msg, _cost, _model = run_agentic_sync(
            "https://github.com/owner/repo/issues/1",
            quiet=True,
            scope_guard=False,
        )

        # Opt-out → dispatch proceeds, no revert, file preserved.
        assert success is True
        assert "before dispatch" not in msg
        assert (tmp_path / "outside.py").exists()
        mock_runner_cls.assert_called_once()
        mock_runner_cls.return_value.run.assert_called_once()


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
        monkeypatch.setattr("pdd.agentic_sync._resolve_module_cwd", lambda *_: tmp_path)
        monkeypatch.setattr("pdd.agentic_sync._run_single_dry_run", mock_dry_run)
        monkeypatch.setattr("pdd.agentic_sync._llm_fix_dry_run_failure", mock_llm)

        all_valid, cwds, errors, cost = _run_dry_run_validation(
            ["bad"], tmp_path, quiet=True
        )

        assert all_valid is False
        assert cwds == {}
        assert cost == 0.0
        assert len(errors) == 1
        assert "bad: prompt contract preflight failed" in errors[0]
        assert "missing_from_context" in errors[0]
        mock_dry_run.assert_called_once_with("bad", tmp_path, quiet=True)
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

        monkeypatch.setattr("pdd.agentic_sync._resolve_module_cwd", lambda *_: tmp_path)
        monkeypatch.setattr("pdd.agentic_sync._run_single_dry_run", lambda *a, **k: (True, ""))

        all_valid, cwds, errors, cost = _run_dry_run_validation(
            ["legacy"], tmp_path, quiet=True
        )

        assert all_valid is True
        assert cwds == {"legacy": tmp_path}
        assert errors == []
        assert cost == 0.0

    def test_dry_run_success_rejects_changed_no_self_include_prompt_contract(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ):
        """Changed prompt-local self-contracts must include existing source context."""
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

        monkeypatch.setattr("pdd.agentic_sync._resolve_module_cwd", lambda *_: tmp_path)
        monkeypatch.setattr("pdd.agentic_sync._run_single_dry_run", lambda *a, **k: (True, ""))
        monkeypatch.setattr(
            "pdd.agentic_sync._prompt_contract_strict_self_context_required",
            lambda *a, **k: True,
        )

        all_valid, cwds, errors, cost = _run_dry_run_validation(
            ["changed"], tmp_path, quiet=True
        )

        assert all_valid is False
        assert cwds == {}
        assert cost == 0.0
        assert len(errors) == 1
        assert "changed: prompt contract preflight failed" in errors[0]
        assert "includes no existing module source context" in errors[0]


# ---------------------------------------------------------------------------
# _llm_fix_dry_run_failure safe-argv (iter-30 B-2 replacement)
# ---------------------------------------------------------------------------


class TestLlmFixDryRunSafeArgv:
    """Iter-30: the orchestrator no longer executes an LLM-supplied shell
    string. The LLM only returns ``SYNC_CWD: <path>``; the orchestrator
    builds the argv itself and runs with ``shell=False``. Closes iter-29 B-2
    (shell injection at the orchestrator level)."""

    @staticmethod
    def _llm_response(cwd_value: str) -> str:
        return f"SYNC_CWD: {cwd_value}\n"

    @patch("pdd.agentic_sync.subprocess.run")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync.load_prompt_template")
    def test_llm_fix_dry_run_uses_safe_argv_not_shell(
        self,
        mock_load_prompt,
        mock_agentic_task,
        mock_subprocess,
        tmp_path,
    ):
        """LLM returns ``SYNC_CWD: subdir`` → argv is a list, shell=False."""
        subdir = tmp_path / "subdir"
        subdir.mkdir()
        mock_load_prompt.return_value = (
            "{basename} {dry_run_error} {project_tree} {pddrc_locations} {attempted_cwd}"
        )
        mock_agentic_task.return_value = (
            True,
            self._llm_response("subdir"),
            0.01,
            "anthropic",
        )
        mock_subprocess.return_value = MagicMock(
            returncode=0,
            stdout="",
            stderr="",
        )

        ok, cwd, cost, err = _llm_fix_dry_run_failure(
            basename="foo",
            project_root=tmp_path,
            dry_run_error="prompt not found",
            quiet=True,
        )

        assert ok is True
        assert cwd == subdir.resolve()
        assert err == ""

        # argv must be a list (not a string), shell must be False.
        call_args, call_kwargs = mock_subprocess.call_args
        argv = call_args[0]
        assert isinstance(argv, list), "argv must be a list — shell=False shape"
        assert call_kwargs.get("shell", False) is False
        assert "--dry-run" in argv
        assert "sync" in argv
        assert "foo" in argv
        # cwd is the resolved SYNC_CWD path, not the project root.
        assert call_kwargs.get("cwd") == str(subdir.resolve())

    @patch("pdd.agentic_sync.subprocess.run")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync.load_prompt_template")
    def test_llm_fix_dry_run_rejects_path_outside_project_root(
        self,
        mock_load_prompt,
        mock_agentic_task,
        mock_subprocess,
        tmp_path,
    ):
        """LLM returns ``SYNC_CWD: /etc`` (outside project root) → reject."""
        mock_load_prompt.return_value = (
            "{basename} {dry_run_error} {project_tree} {pddrc_locations} {attempted_cwd}"
        )
        mock_agentic_task.return_value = (
            True,
            self._llm_response("/etc"),
            0.01,
            "anthropic",
        )

        ok, cwd, cost, err = _llm_fix_dry_run_failure(
            basename="foo",
            project_root=tmp_path,
            dry_run_error="prompt not found",
            quiet=True,
        )

        assert ok is False
        assert cwd is None
        assert "outside project root" in err
        mock_subprocess.assert_not_called()

    @patch("pdd.agentic_sync.subprocess.run")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync.load_prompt_template")
    def test_llm_fix_dry_run_rejects_legacy_sync_cmd_format(
        self,
        mock_load_prompt,
        mock_agentic_task,
        mock_subprocess,
        tmp_path,
    ):
        """Stale-cache ``SYNC_CMD: pdd sync foo`` → reject with migration error."""
        mock_load_prompt.return_value = (
            "{basename} {dry_run_error} {project_tree} {pddrc_locations} {attempted_cwd}"
        )
        mock_agentic_task.return_value = (
            True,
            "SYNC_CMD: pdd --force sync foo --dry-run --agentic --no-steer\n",
            0.01,
            "anthropic",
        )

        ok, cwd, cost, err = _llm_fix_dry_run_failure(
            basename="foo",
            project_root=tmp_path,
            dry_run_error="prompt not found",
            quiet=True,
        )

        assert ok is False
        assert cwd is None
        assert "SYNC_CWD" in err
        assert "legacy" in err.lower()
        mock_subprocess.assert_not_called()

    @patch("pdd.agentic_sync.subprocess.run")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync.load_prompt_template")
    def test_llm_fix_dry_run_rejects_shell_metachars_in_cwd(
        self,
        mock_load_prompt,
        mock_agentic_task,
        mock_subprocess,
        tmp_path,
    ):
        """SYNC_CWD containing shell metacharacters is rejected defensively."""
        mock_load_prompt.return_value = (
            "{basename} {dry_run_error} {project_tree} {pddrc_locations} {attempted_cwd}"
        )
        mock_agentic_task.return_value = (
            True,
            self._llm_response("subdir; rm -rf /"),
            0.01,
            "anthropic",
        )

        ok, cwd, cost, err = _llm_fix_dry_run_failure(
            basename="foo",
            project_root=tmp_path,
            dry_run_error="prompt not found",
            quiet=True,
        )

        assert ok is False
        assert cwd is None
        assert "forbidden character" in err
        mock_subprocess.assert_not_called()


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
                MagicMock(returncode=0, stdout="feature-branch\n", stderr=""),
                MagicMock(returncode=0, stdout=diff_output, stderr=""),
            ]
            result = _detect_modules_from_branch_diff(Path("/fake/project"))
        assert result == ["pdd_executor", "solving_orchestrator"]


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
        mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, [], 0.0)

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
