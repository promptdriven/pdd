"""Tests for pdd.ci_drift_heal module."""
from __future__ import annotations

import os
import subprocess
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.ci_drift_heal import (
    DriftInfo,
    HealResult,
    PromptRevertError,
    _AUTO_HEAL_SUCCESS_TRAILER,
    _capture_rollback_state,
    _git_relative_path_candidates,
    _run_pdd_command,
    _get_git_changed_files,
    detect_drift,
    heal_module,
    commit_and_push,
    main,
)


# ---------------------------------------------------------------------------
# DriftInfo / HealResult dataclass tests
# ---------------------------------------------------------------------------

class TestDriftInfo:
    def test_create_prompt_drift(self):
        """DriftInfo stores basename, language, operation, reason."""
        d = DriftInfo(basename="auth", language="python", operation="update", reason="Prompt changed")
        assert d.basename == "auth"
        assert d.language == "python"
        assert d.operation == "update"
        assert d.reason == "Prompt changed"

    def test_create_example_drift(self):
        d = DriftInfo(basename="api", language="python", operation="example", reason="Example stale")
        assert d.operation == "example"


class TestHealResult:
    def test_default_values(self):
        r = HealResult(basename="mod", success=True)
        assert r.cost == 0.0
        assert r.error == ""

    def test_custom_values(self):
        r = HealResult(basename="mod", success=False, cost=1.5, error="timeout")
        assert r.cost == 1.5
        assert r.error == "timeout"


# ---------------------------------------------------------------------------
# detect_drift tests
# ---------------------------------------------------------------------------

class TestDetectDrift:
    def _setup_mocks(self, decisions_map):
        """Helper to build mocks for detect_drift."""
        mock_prompt_files = [
            Path(f"prompts/{bn}_python.prompt") for bn in decisions_map
        ]

        def fake_infer(path):
            stem = Path(path).stem
            parts = stem.rsplit("_", 1)
            return parts[0], parts[1]

        def fake_sync(basename, language, target_coverage, log_mode):
            return decisions_map[basename]

        return mock_prompt_files, fake_infer, fake_sync

    def test_detects_prompt_drift(self):
        """Modules with operation=='update' appear in prompt_drifts."""
        decision = MagicMock(operation="update", reason="Prompt changed")
        files, infer, sync = self._setup_mocks({"auth": decision})

        with patch("pdd.user_story_tests.discover_prompt_files", return_value=files), \
             patch("pdd.operation_log.infer_module_identity", side_effect=infer), \
             patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=sync):
            prompt_drifts, example_drifts = detect_drift()

        assert len(prompt_drifts) == 1
        assert prompt_drifts[0].basename == "auth"
        assert prompt_drifts[0].operation == "update"
        assert len(example_drifts) == 0

    def test_detects_example_drift(self):
        """Modules with operation=='example' appear in example_drifts."""
        decision = MagicMock(operation="example", reason="Example stale")
        files, infer, sync = self._setup_mocks({"api": decision})

        with patch("pdd.user_story_tests.discover_prompt_files", return_value=files), \
             patch("pdd.operation_log.infer_module_identity", side_effect=infer), \
             patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=sync):
            prompt_drifts, example_drifts = detect_drift()

        assert len(prompt_drifts) == 0
        assert len(example_drifts) == 1
        assert example_drifts[0].basename == "api"

    def test_example_drift_populates_prompt_and_code_paths(self):
        """`operation='example'` drift carries prompt_path and code_path so
        heal_module can run `pdd example <prompt> <code>` directly."""
        decision = MagicMock(operation="example", reason="Example stale")
        files, infer, sync = self._setup_mocks({"api": decision})

        fake_paths = {
            "prompt": Path("/repo/prompts/api_python.prompt"),
            "code": Path("/repo/api.py"),
        }

        with patch("pdd.user_story_tests.discover_prompt_files", return_value=files), \
             patch("pdd.operation_log.infer_module_identity", side_effect=infer), \
             patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=sync), \
             patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=fake_paths):
            _, example_drifts = detect_drift()

        assert len(example_drifts) == 1
        d = example_drifts[0]
        assert d.operation == "example"
        assert d.prompt_path == "/repo/prompts/api_python.prompt"
        assert d.code_path == "/repo/api.py"

    def test_non_example_ops_preserve_original_operation(self):
        """verify/generate/auto-deps/test/crash decisions keep their operation name.

        The prior implementation collapsed every non-update decision to
        `operation='example'`, losing the intent. Auto-heal must preserve
        the original operation so heal_module can dispatch correctly (pdd
        example for example, pdd sync for the others).
        """
        for op in ("verify", "generate", "auto-deps", "test", "crash"):
            decision = MagicMock(operation=op, reason=f"{op} needed")
            files, infer, sync = self._setup_mocks({"mod": decision})

            with patch("pdd.user_story_tests.discover_prompt_files", return_value=files), \
                 patch("pdd.operation_log.infer_module_identity", side_effect=infer), \
                 patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=sync):
                _, drifts = detect_drift()

            assert len(drifts) == 1, f"expected 1 drift for op={op}"
            assert drifts[0].operation == op, f"op collapsed to {drifts[0].operation} for {op}"

    def test_no_drift(self):
        """Modules with operation=='nothing' are not collected."""
        decision = MagicMock(operation="nothing")
        files, infer, sync = self._setup_mocks({"utils": decision})

        with patch("pdd.user_story_tests.discover_prompt_files", return_value=files), \
             patch("pdd.operation_log.infer_module_identity", side_effect=infer), \
             patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=sync):
            prompt_drifts, example_drifts = detect_drift()

        assert len(prompt_drifts) == 0
        assert len(example_drifts) == 0

    def test_module_filter(self):
        """Only modules in the filter list are checked."""
        d_update = MagicMock(operation="update", reason="changed")
        d_example = MagicMock(operation="example", reason="stale")
        files, infer, sync = self._setup_mocks({"auth": d_update, "api": d_example})

        with patch("pdd.user_story_tests.discover_prompt_files", return_value=files), \
             patch("pdd.operation_log.infer_module_identity", side_effect=infer), \
             patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=sync):
            prompt_drifts, example_drifts = detect_drift(modules=["auth"])

        assert len(prompt_drifts) == 1
        assert len(example_drifts) == 0

    def test_infer_identity_error_skips_module(self):
        """Modules that fail identity inference are skipped gracefully."""
        mock_files = [Path("prompts/bad_python.prompt")]

        with patch("pdd.user_story_tests.discover_prompt_files", return_value=mock_files), \
             patch("pdd.operation_log.infer_module_identity", side_effect=ValueError("bad")), \
             patch("pdd.sync_determine_operation.sync_determine_operation") as mock_sync:
            prompt_drifts, example_drifts = detect_drift()

        assert len(prompt_drifts) == 0
        assert len(example_drifts) == 0
        mock_sync.assert_not_called()

    def test_sync_determine_error_skips_module(self):
        """Modules that fail sync_determine_operation are skipped."""
        mock_files = [Path("prompts/mod_python.prompt")]

        def fake_infer(path):
            return "mod", "python"

        with patch("pdd.user_story_tests.discover_prompt_files", return_value=mock_files), \
             patch("pdd.operation_log.infer_module_identity", side_effect=fake_infer), \
             patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=RuntimeError("fail")):
            prompt_drifts, example_drifts = detect_drift()

        assert len(prompt_drifts) == 0
        assert len(example_drifts) == 0


# ---------------------------------------------------------------------------
# _get_git_changed_files tests
# ---------------------------------------------------------------------------


class TestGetGitChangedFiles:
    def test_returns_set_of_changed_files(self):
        mock_result = MagicMock(returncode=0, stdout="pdd/auth.py\npdd/api.py\n")
        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result):
            result = _get_git_changed_files("origin/main...HEAD")
        assert result == {"pdd/auth.py", "pdd/api.py"}

    def test_returns_empty_on_failure(self):
        mock_result = MagicMock(returncode=1, stdout="", stderr="error")
        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result):
            result = _get_git_changed_files("origin/main...HEAD")
        assert result == set()

    def test_returns_empty_on_exception(self):
        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=FileNotFoundError):
            result = _get_git_changed_files("origin/main...HEAD")
        assert result == set()

    def test_strips_whitespace(self):
        mock_result = MagicMock(returncode=0, stdout="  pdd/auth.py  \n\n  pdd/api.py\n")
        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result):
            result = _get_git_changed_files("origin/main...HEAD")
        assert result == {"pdd/auth.py", "pdd/api.py"}

    def test_relative_path_candidates_include_symlink_target(self, tmp_path):
        """Prompt paths may come through the prompts/ symlink while Git reports pdd/prompts/."""
        prompt_dir = tmp_path / "pdd" / "prompts"
        prompt_dir.mkdir(parents=True)
        (tmp_path / "prompts").symlink_to("pdd/prompts")
        prompt_path = tmp_path / "prompts" / "auth_python.prompt"
        prompt_path.write_text("prompt", encoding="utf-8")

        candidates = _git_relative_path_candidates(prompt_path, tmp_path)

        assert "prompts/auth_python.prompt" in candidates
        assert "pdd/prompts/auth_python.prompt" in candidates


# ---------------------------------------------------------------------------
# detect_drift with diff_base (git-based reclassification) tests
# ---------------------------------------------------------------------------


class TestDetectDriftWithDiffBase:
    def _setup_mocks(self, decisions_map):
        mock_prompt_files = [
            Path(f"prompts/{bn}_python.prompt") for bn in decisions_map
        ]
        def fake_infer(path):
            stem = Path(path).stem
            parts = stem.rsplit("_", 1)
            return parts[0], parts[1]
        def fake_sync(basename, language, target_coverage, log_mode):
            return decisions_map[basename]
        return mock_prompt_files, fake_infer, fake_sync

    def test_code_changed_prompt_unchanged_reclassified_as_update(self):
        """When code changed but prompt didn't, auto-deps drift becomes update drift."""
        decision = MagicMock(operation="auto-deps", reason="New prompt with dependencies detected")
        files, infer, sync = self._setup_mocks({"auth": decision})
        changed_files = {"pdd/auth.py", "tests/test_auth.py"}
        mock_paths = {"code": Path("pdd/auth.py"), "prompt": Path("prompts/auth_python.prompt")}

        with patch("pdd.user_story_tests.discover_prompt_files", return_value=files), \
             patch("pdd.operation_log.infer_module_identity", side_effect=infer), \
             patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=sync), \
             patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=mock_paths), \
             patch("pdd.ci_drift_heal._get_git_changed_files", return_value=changed_files):
            prompt_drifts, example_drifts = detect_drift(modules=["auth"], diff_base="origin/main...HEAD")

        assert len(prompt_drifts) == 1
        assert prompt_drifts[0].basename == "auth"
        assert prompt_drifts[0].operation == "update"
        assert prompt_drifts[0].code_path == "pdd/auth.py"
        assert len(example_drifts) == 0

    def test_prompt_also_changed_stays_as_example(self):
        """When both code and prompt changed, stays as example drift."""
        decision = MagicMock(operation="auto-deps", reason="New prompt with dependencies detected")
        files, infer, sync = self._setup_mocks({"auth": decision})
        # Git reports prompt files via their canonical path (`pdd/prompts/...`)
        # even though the repo exposes them through a `prompts -> pdd/prompts`
        # symlink and `get_pdd_file_paths` returns the symlinked form.
        changed_files = {"pdd/auth.py", "pdd/prompts/auth_python.prompt"}
        mock_paths = {"code": Path("pdd/auth.py"), "prompt": Path("prompts/auth_python.prompt")}

        with patch("pdd.user_story_tests.discover_prompt_files", return_value=files), \
             patch("pdd.operation_log.infer_module_identity", side_effect=infer), \
             patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=sync), \
             patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=mock_paths), \
             patch("pdd.ci_drift_heal._get_git_changed_files", return_value=changed_files):
            prompt_drifts, example_drifts = detect_drift(modules=["auth"], diff_base="origin/main...HEAD")

        assert len(prompt_drifts) == 0
        assert len(example_drifts) == 1

    def test_no_diff_base_skips_reclassification(self):
        """Without diff_base, no git-based reclassification occurs."""
        decision = MagicMock(operation="auto-deps", reason="New prompt with dependencies detected")
        files, infer, sync = self._setup_mocks({"auth": decision})

        with patch("pdd.user_story_tests.discover_prompt_files", return_value=files), \
             patch("pdd.operation_log.infer_module_identity", side_effect=infer), \
             patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=sync), \
             patch("pdd.ci_drift_heal._get_git_changed_files") as mock_git:
            prompt_drifts, example_drifts = detect_drift(modules=["auth"])

        mock_git.assert_not_called()
        assert len(example_drifts) == 1
        assert len(prompt_drifts) == 0

    def test_generate_operation_also_reclassified(self):
        """'generate' operation is also reclassified when code changed but prompt didn't."""
        decision = MagicMock(operation="generate", reason="New prompt ready for code generation")
        files, infer, sync = self._setup_mocks({"api": decision})
        changed_files = {"pdd/api.py"}
        mock_paths = {"code": Path("pdd/api.py"), "prompt": Path("prompts/api_python.prompt")}

        with patch("pdd.user_story_tests.discover_prompt_files", return_value=files), \
             patch("pdd.operation_log.infer_module_identity", side_effect=infer), \
             patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=sync), \
             patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=mock_paths), \
             patch("pdd.ci_drift_heal._get_git_changed_files", return_value=changed_files):
            prompt_drifts, example_drifts = detect_drift(modules=["api"], diff_base="origin/main...HEAD")

        assert len(prompt_drifts) == 1
        assert prompt_drifts[0].operation == "update"
        assert len(example_drifts) == 0

    def test_only_prompt_changed_stays_as_example(self):
        """When only prompt changed (not code), stays as example drift."""
        decision = MagicMock(operation="auto-deps", reason="New prompt with dependencies detected")
        files, infer, sync = self._setup_mocks({"auth": decision})
        changed_files = {"pdd/prompts/auth_python.prompt"}
        mock_paths = {"code": Path("pdd/auth.py"), "prompt": Path("prompts/auth_python.prompt")}

        with patch("pdd.user_story_tests.discover_prompt_files", return_value=files), \
             patch("pdd.operation_log.infer_module_identity", side_effect=infer), \
             patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=sync), \
             patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=mock_paths), \
             patch("pdd.ci_drift_heal._get_git_changed_files", return_value=changed_files):
            prompt_drifts, example_drifts = detect_drift(modules=["auth"], diff_base="origin/main...HEAD")

        assert len(prompt_drifts) == 0
        assert len(example_drifts) == 1

    def test_git_changed_files_called_once(self):
        """_get_git_changed_files is called once, not per-module."""
        d1 = MagicMock(operation="auto-deps", reason="deps")
        d2 = MagicMock(operation="generate", reason="gen")
        files, infer, sync = self._setup_mocks({"auth": d1, "api": d2})
        changed_files = {"pdd/auth.py", "pdd/api.py"}

        def fake_get_paths(basename, language):
            if basename == "auth":
                return {"code": Path("pdd/auth.py"), "prompt": Path("prompts/auth_python.prompt")}
            return {"code": Path("pdd/api.py"), "prompt": Path("prompts/api_python.prompt")}

        with patch("pdd.user_story_tests.discover_prompt_files", return_value=files), \
             patch("pdd.operation_log.infer_module_identity", side_effect=infer), \
             patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=sync), \
             patch("pdd.sync_determine_operation.get_pdd_file_paths", side_effect=fake_get_paths), \
             patch("pdd.ci_drift_heal._get_git_changed_files", return_value=changed_files) as mock_git:
            detect_drift(modules=["auth", "api"], diff_base="origin/main...HEAD")

        mock_git.assert_called_once_with("origin/main...HEAD")

    def test_symlinked_prompt_path_resolves_to_canonical_form(self, tmp_path, monkeypatch):
        """Prompt paths from `prompts/` symlink resolve to git's `pdd/prompts/` form.

        Regression for PR #1292 auto-heal failure: `get_pdd_file_paths` returns
        prompt paths under the `prompts -> pdd/prompts` symlink, but `git diff`
        reports the canonical `pdd/prompts/...` path. Without symlink resolution
        the membership check would miss, falsely flagging the prompt as
        unchanged and reclassifying real prompt-edit PRs as code-only drift.
        """
        (tmp_path / "pdd" / "prompts").mkdir(parents=True)
        (tmp_path / "prompts").symlink_to(tmp_path / "pdd" / "prompts")
        prompt_file = tmp_path / "pdd" / "prompts" / "auth_python.prompt"
        prompt_file.write_text("% prompt\n")
        code_file = tmp_path / "pdd" / "auth.py"
        code_file.parent.mkdir(parents=True, exist_ok=True)
        code_file.write_text("def foo(): pass\n")
        monkeypatch.chdir(tmp_path)

        decision = MagicMock(operation="auto-deps", reason="deps")
        files, infer, sync = self._setup_mocks({"auth": decision})
        # Both paths absolute; prompt accessed via the symlink, mirroring what
        # `get_pdd_file_paths` returns in CI.
        mock_paths = {
            "code": code_file,
            "prompt": tmp_path / "prompts" / "auth_python.prompt",
        }
        # Git-canonical paths (what `git diff --name-only` actually emits).
        changed_files = {"pdd/auth.py", "pdd/prompts/auth_python.prompt"}

        with patch("pdd.user_story_tests.discover_prompt_files", return_value=files), \
             patch("pdd.operation_log.infer_module_identity", side_effect=infer), \
             patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=sync), \
             patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=mock_paths), \
             patch("pdd.ci_drift_heal._get_git_changed_files", return_value=changed_files):
            prompt_drifts, example_drifts = detect_drift(modules=["auth"], diff_base="origin/main...HEAD")

        # Both code AND prompt changed → must NOT reclassify as prompt drift.
        assert len(prompt_drifts) == 0
        assert len(example_drifts) == 1

    def test_get_pdd_file_paths_failure_falls_back_to_example(self):
        """If get_pdd_file_paths raises, drift stays as example."""
        decision = MagicMock(operation="auto-deps", reason="deps")
        files, infer, sync = self._setup_mocks({"auth": decision})
        changed_files = {"pdd/auth.py"}

        with patch("pdd.user_story_tests.discover_prompt_files", return_value=files), \
             patch("pdd.operation_log.infer_module_identity", side_effect=infer), \
             patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=sync), \
             patch("pdd.sync_determine_operation.get_pdd_file_paths", side_effect=RuntimeError("fail")), \
             patch("pdd.ci_drift_heal._get_git_changed_files", return_value=changed_files):
            prompt_drifts, example_drifts = detect_drift(modules=["auth"], diff_base="origin/main...HEAD")

        assert len(prompt_drifts) == 0
        assert len(example_drifts) == 1


# ---------------------------------------------------------------------------
# heal_module tests
# ---------------------------------------------------------------------------

class TestHealModule:
    def _make_env(self):
        return {"PDD_FORCE": "1", "CI": "1", "NO_COLOR": "1", "PDD_OUTPUT_COST_PATH": "/tmp/c.csv"}

    def test_update_runs_update_then_example_with_strength_override(self):
        """Update drift runs forced pdd update/example commands.

        Passes `--strength 0.5` explicitly so the command overrides any
        `.pddrc` context strength (e.g. 0.818) that would otherwise push
        model selection to Sonnet/Opus-class models and defeat the env-var
        pin to Gemini Pro.
        """
        drift = DriftInfo(
            "auth",
            "python",
            "update",
            "changed",
            code_path="/repo/auth.py",
            prompt_path="/repo/prompts/auth_python.prompt",
        )
        mock_result = MagicMock(returncode=0, stderr="")

        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run:
            result = heal_module(drift, self._make_env())

        assert result is True
        pdd_cmds = [c[0][0] for c in mock_run.call_args_list if c[0][0][:1] == ["pdd"]]
        assert pdd_cmds == [
            ["pdd", "--force", "--strength", "0.5", "update", "/repo/auth.py"],
            [
                "pdd",
                "--force",
                "--strength",
                "0.5",
                "example",
                "/repo/prompts/auth_python.prompt",
                "/repo/auth.py",
            ],
        ]

    def test_update_no_code_path_fails_closed(self):
        """prompt drift (update) refuses repo-wide fallback when code_path is None."""
        drift = DriftInfo(
            "auth",
            "python",
            "update",
            "changed",
            code_path=None,
            prompt_path="/repo/prompts/auth_python.prompt",
        )

        with patch("pdd.ci_drift_heal.subprocess.run") as mock_run:
            result = heal_module(drift, self._make_env())

        assert result is False
        mock_run.assert_not_called()

    def test_update_failure_skips_example(self):
        """If pdd update fails, pdd example is not attempted."""
        drift = DriftInfo(
            "auth",
            "python",
            "update",
            "changed",
            code_path="/repo/auth.py",
            prompt_path="/repo/prompts/auth_python.prompt",
        )
        mock_result = MagicMock(returncode=1, stderr="error")

        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run:
            result = heal_module(drift, self._make_env())

        assert result is False
        # Only update was called, not example
        assert len(mock_run.call_args_list) == 1

    def test_update_ok_example_fails_and_reverts_prompt(self):
        """If update succeeds but example fails, treat the heal as failed and revert prompt edits."""
        drift = DriftInfo(
            "auth",
            "python",
            "update",
            "changed",
            code_path="/repo/auth.py",
            prompt_path="/repo/prompts/auth_python.prompt",
        )
        call_count = [0]

        def mock_run(cmd, **kwargs):
            call_count[0] += 1
            r = MagicMock()
            if cmd[:3] == ["git", "rev-parse", "--show-toplevel"]:
                r.returncode = 0
                r.stdout = "/repo\n"
                r.stderr = ""
                return r
            if cmd[:4] == ["git", "checkout", "HEAD", "--"]:
                r.returncode = 0
                r.stderr = ""
                return r
            if cmd[:4] == ["git", "status", "--porcelain", "--"]:
                r.returncode = 0
                r.stdout = ""
                r.stderr = ""
                return r
            r.returncode = 0 if call_count[0] == 1 else 1  # update ok, example fails
            r.stderr = "" if call_count[0] == 1 else "example error"
            return r

        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=mock_run) as mock_subprocess:
            result = heal_module(drift, self._make_env())

        assert result is False
        checkout_calls = [
            c for c in mock_subprocess.call_args_list
            if c[0][0][:4] == ["git", "checkout", "HEAD", "--"]
        ]
        assert len(checkout_calls) == 1
        assert checkout_calls[0][0][0][-1] == "prompts/auth_python.prompt"

    def test_update_ok_example_fails_and_revert_failure_raises(self):
        """If prompt revert fails after example failure, surface a fatal revert error."""
        drift = DriftInfo(
            "auth",
            "python",
            "update",
            "changed",
            code_path="/repo/auth.py",
            prompt_path="/repo/prompts/auth_python.prompt",
        )
        call_count = [0]

        def mock_run(cmd, **kwargs):
            call_count[0] += 1
            r = MagicMock()
            if cmd[:3] == ["git", "rev-parse", "--show-toplevel"]:
                r.returncode = 0
                r.stdout = "/repo\n"
                r.stderr = ""
                return r
            if cmd[:4] == ["git", "checkout", "HEAD", "--"]:
                r.returncode = 1
                r.stderr = "cannot checkout"
                return r
            r.returncode = 0 if call_count[0] == 1 else 1
            r.stderr = "" if call_count[0] == 1 else "sync error"
            return r

        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=mock_run):
            with pytest.raises(PromptRevertError):
                heal_module(drift, self._make_env())

    def test_revert_prompt_file_uses_repo_relative_path_for_absolute_prompt(self):
        """Absolute prompt paths must be normalized before git checkout/status."""
        from pdd.ci_drift_heal import _revert_prompt_file

        drift = DriftInfo(
            "auth",
            "python",
            "update",
            "changed",
            prompt_path="/repo/prompts/auth_python.prompt",
        )
        calls = []

        def mock_run(cmd, **kwargs):
            calls.append(cmd)
            if cmd[:3] == ["git", "rev-parse", "--show-toplevel"]:
                return subprocess.CompletedProcess(cmd, 0, "/repo\n", "")
            if cmd[:4] == ["git", "checkout", "HEAD", "--"]:
                return subprocess.CompletedProcess(cmd, 0, "", "")
            if cmd[:4] == ["git", "status", "--porcelain", "--"]:
                return subprocess.CompletedProcess(cmd, 0, "", "")
            raise AssertionError(f"Unexpected command: {cmd}")

        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=mock_run):
            _revert_prompt_file(drift)

        assert ["git", "checkout", "HEAD", "--", "prompts/auth_python.prompt"] in calls
        assert ["git", "status", "--porcelain", "--", "prompts/auth_python.prompt"] in calls

    def test_update_does_not_skip_follow_up_example_by_default(self):
        """agentic_change_orchestrator example step runs normally once the default skip is removed."""
        drift = DriftInfo(
            "agentic_change_orchestrator",
            "python",
            "update",
            "changed",
            code_path="/repo/agentic_change_orchestrator.py",
            prompt_path="/repo/prompts/agentic_change_orchestrator_python.prompt",
        )
        mock_result = MagicMock(returncode=0, stderr="")

        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run:
            result = heal_module(drift, self._make_env())

        assert result is True
        pdd_cmds = [c[0][0] for c in mock_run.call_args_list if c[0][0][:1] == ["pdd"]]
        assert pdd_cmds == [
            ["pdd", "--force", "--strength", "0.5", "update", "/repo/agentic_change_orchestrator.py"],
            [
                "pdd",
                "--force",
                "--strength",
                "0.5",
                "example",
                "/repo/prompts/agentic_change_orchestrator_python.prompt",
                "/repo/agentic_change_orchestrator.py",
            ],
        ]

    def test_update_skip_env_runs_update_but_skips_follow_up_example(self):
        """Explicit skip env still bypasses the follow-up example step for operational recovery."""
        drift = DriftInfo(
            "agentic_change_orchestrator",
            "python",
            "update",
            "changed",
            code_path="/repo/agentic_change_orchestrator.py",
            prompt_path="/repo/prompts/agentic_change_orchestrator_python.prompt",
        )
        mock_result = MagicMock(returncode=0, stderr="")

        with patch.dict(
            os.environ,
            {"PDD_HEAL_SYNC_SKIP_MODULES": "agentic_change_orchestrator"},
            clear=False,
        ), patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run:
            result = heal_module(drift, self._make_env())

        assert result is True
        pdd_cmds = [c[0][0] for c in mock_run.call_args_list if c[0][0][:1] == ["pdd"]]
        assert pdd_cmds == [
            ["pdd", "--force", "--strength", "0.5", "update", "/repo/agentic_change_orchestrator.py"],
        ]

    def test_example_drift_runs_pdd_example(self):
        """example drift runs `pdd --force --strength 0.5 example <prompt> <code>`."""
        drift = DriftInfo(
            "api",
            "python",
            "example",
            "stale",
            code_path="/repo/api.py",
            prompt_path="/repo/prompts/api_python.prompt",
        )
        mock_result = MagicMock(returncode=0, stderr="")

        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run:
            result = heal_module(drift, self._make_env())

        assert result is True
        assert len(mock_run.call_args_list) == 1
        assert mock_run.call_args[0][0] == [
            "pdd",
            "--force",
            "--strength",
            "0.5",
            "example",
            "/repo/prompts/api_python.prompt",
            "/repo/api.py",
        ]

    def test_verify_drift_runs_pdd_sync_to_preserve_semantics(self):
        """operation=='verify' (user-edited example needs validation) must NOT run pdd example.

        pdd example regenerates the example from scratch, which would
        overwrite user edits. verify drift keeps pdd sync so
        sync_determine_operation dispatches through verify/fix loops.
        """
        drift = DriftInfo(
            "api",
            "python",
            "verify",
            "example edited",
            code_path="/repo/api.py",
            prompt_path="/repo/prompts/api_python.prompt",
        )
        mock_result = MagicMock(returncode=0, stderr="")

        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run:
            result = heal_module(drift, self._make_env())

        assert result is True
        pdd_cmds = [c[0][0] for c in mock_run.call_args_list if c[0][0][:1] == ["pdd"]]
        assert pdd_cmds == [["pdd", "--force", "--strength", "0.5", "sync", "api"]]

    def test_generate_drift_runs_pdd_sync_to_preserve_semantics(self):
        """operation=='generate' (prompt changed, code needs regen) must run pdd sync.

        pdd example only regenerates the example from existing code —
        it won't regenerate code from the updated prompt. pdd sync dispatches
        to the full generate flow.
        """
        drift = DriftInfo(
            "api", "python", "generate", "prompt changed",
            code_path="/repo/api.py",
            prompt_path="/repo/prompts/api_python.prompt",
        )
        mock_result = MagicMock(returncode=0, stderr="")

        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run:
            result = heal_module(drift, self._make_env())

        assert result is True
        pdd_cmds = [c[0][0] for c in mock_run.call_args_list if c[0][0][:1] == ["pdd"]]
        assert pdd_cmds == [["pdd", "--force", "--strength", "0.5", "sync", "api"]]

    def test_auto_deps_drift_runs_bounded_auto_deps_command(self):
        """operation=='auto-deps' should not fall through to full sync/generate/crash."""
        drift = DriftInfo(
            "api", "python", "auto-deps", "prompt dependencies changed",
            prompt_path="/repo/prompts/api_python.prompt",
        )
        mock_result = MagicMock(returncode=0, stderr="")

        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run, \
             patch("pdd.ci_drift_heal._auto_deps_directory", return_value="context"):
            result = heal_module(drift, self._make_env())

        assert result is True
        pdd_cmds = [c[0][0] for c in mock_run.call_args_list if c[0][0][:1] == ["pdd"]]
        assert pdd_cmds == [[
            "pdd",
            "--force",
            "--strength",
            "0.5",
            "auto-deps",
            "/repo/prompts/api_python.prompt",
            "context",
            "--output",
            "/repo/prompts/api_python.prompt",
            "--csv",
            "project_dependencies.csv",
        ]]

    def test_sync_fallback_ops_do_not_require_paths(self):
        """verify/generate/test/crash work without paths because pdd sync resolves them."""
        for op in ("verify", "generate", "test", "crash"):
            drift = DriftInfo("mod", "python", op, f"{op} needed")
            mock_result = MagicMock(returncode=0, stderr="")
            with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run:
                result = heal_module(drift, self._make_env())
            assert result is True, f"failed for op={op}"
            pdd_cmds = [c[0][0] for c in mock_run.call_args_list if c[0][0][:1] == ["pdd"]]
            assert pdd_cmds == [["pdd", "--force", "--strength", "0.5", "sync", "mod"]], f"unexpected cmds for op={op}: {pdd_cmds}"

    def test_update_without_prompt_path_resolves_after_update(self):
        """Code-without-prompt flow: pdd update creates the prompt, then we
        resolve prompt_path lazily before the follow-up pdd example.

        This is the `reason='Code exists without prompt — needs pdd update'`
        drift created by detect_drift when scanning modules without a prompt.
        """
        drift = DriftInfo(
            "newmod",
            "python",
            "update",
            "Code exists without prompt — needs pdd update",
            code_path="/repo/newmod.py",
            prompt_path=None,  # doesn't exist pre-update; pdd update creates it
        )
        mock_result = MagicMock(returncode=0, stderr="")

        # After pdd update runs, prompt_path should resolve via get_pdd_file_paths
        created_prompt = MagicMock()
        created_prompt.exists.return_value = True
        created_prompt.__str__ = lambda self: "/repo/prompts/newmod_python.prompt"
        fake_paths = {
            "prompt": created_prompt,
            "code": MagicMock(__str__=lambda self: "/repo/newmod.py"),
        }

        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run, \
             patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=fake_paths):
            result = heal_module(drift, self._make_env())

        assert result is True
        pdd_cmds = [c[0][0] for c in mock_run.call_args_list if c[0][0][:1] == ["pdd"]]
        # pdd update runs first; pdd example runs with the freshly-resolved prompt path
        assert pdd_cmds[0] == ["pdd", "--force", "--strength", "0.5", "update", "/repo/newmod.py"]
        assert pdd_cmds[1] == [
            "pdd",
            "--force",
            "--strength",
            "0.5",
            "example",
            "/repo/prompts/newmod_python.prompt",
            "/repo/newmod.py",
        ]

    def test_example_drift_missing_prompt_path_fails_closed(self):
        """example drift without a resolved prompt path fails without running pdd."""
        drift = DriftInfo("api", "python", "example", "stale", code_path="/repo/api.py")
        # prompt_path is None — heal_module must refuse rather than guess

        with patch("pdd.ci_drift_heal.subprocess.run") as mock_run:
            result = heal_module(drift, self._make_env())

        assert result is False
        mock_run.assert_not_called()

    def test_example_drift_missing_code_path_fails_closed(self):
        """example drift without a resolved code path fails without running pdd."""
        drift = DriftInfo(
            "api", "python", "example", "stale",
            prompt_path="/repo/prompts/api_python.prompt",
        )
        # code_path is None

        with patch("pdd.ci_drift_heal.subprocess.run") as mock_run:
            result = heal_module(drift, self._make_env())

        assert result is False
        mock_run.assert_not_called()

    def test_update_with_unresolvable_prompt_fails_closed(self):
        """Update drift where prompt_path can't be resolved even after pdd update.

        If `pdd update` claimed success but `get_pdd_file_paths` still can't
        find the prompt, the module's path resolution is inconsistent — maybe
        `pdd update` wrote to a different location than the path-resolver
        expects, maybe language was misdetected, maybe update returned 0 by
        accident. Whatever the cause, we refuse to treat this as a successful
        heal: returning True would push the module into `healed_modules` and
        let `commit_and_push`'s `git add -A` publish whatever state is on
        disk, including possibly a prompt at the wrong location.
        """
        drift = DriftInfo(
            "auth", "python", "update", "changed",
            code_path="/repo/auth.py",
            prompt_path=None,
        )
        mock_result = MagicMock(returncode=0, stderr="")
        # Simulate get_pdd_file_paths returning a prompt path that doesn't exist on disk
        no_prompt = MagicMock()
        no_prompt.exists.return_value = False
        fake_paths = {"prompt": no_prompt, "code": MagicMock()}

        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run, \
             patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=fake_paths):
            result = heal_module(drift, self._make_env())

        # pdd update itself ran; but we fail closed because the post-update
        # state is inconsistent — don't let the failed module piggy-back on
        # other modules' commits.
        assert result is False
        pdd_cmds = [c[0][0] for c in mock_run.call_args_list if c[0][0][:1] == ["pdd"]]
        assert pdd_cmds == [["pdd", "--force", "--strength", "0.5", "update", "/repo/auth.py"]]

    def test_example_skip_env_returns_none_without_running(self):
        """Explicit skip env bypasses a module's heal step without failing CI."""
        drift = DriftInfo(
            "agentic_change_orchestrator",
            "python",
            "example",
            "stale",
            code_path="/repo/agentic_change_orchestrator.py",
            prompt_path="/repo/prompts/agentic_change_orchestrator_python.prompt",
        )

        with patch.dict(
            os.environ,
            {"PDD_HEAL_SYNC_SKIP_MODULES": "agentic_change_orchestrator"},
            clear=False,
        ), patch("pdd.ci_drift_heal.subprocess.run") as mock_run:
            result = heal_module(drift, self._make_env())

        assert result is None
        mock_run.assert_not_called()

    def test_subprocess_timeout(self):
        """TimeoutExpired returns False."""
        drift = DriftInfo("auth", "python", "update", "changed")

        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=subprocess.TimeoutExpired("pdd", 300)):
            result = heal_module(drift, self._make_env())

        assert result is False

    def test_pdd_not_found(self):
        """FileNotFoundError returns False."""
        drift = DriftInfo("auth", "python", "update", "changed")

        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=FileNotFoundError):
            result = heal_module(drift, self._make_env())

        assert result is False

    def test_unknown_operation(self):
        """Unknown operation type returns False."""
        drift = DriftInfo("auth", "python", "unknown", "reason")
        result = heal_module(drift, {"PDD_FORCE": "1"})
        assert result is False

    def test_env_passed_to_subprocess(self):
        """Environment dict is passed to subprocess.run for every pdd invocation."""
        drift = DriftInfo(
            "auth",
            "python",
            "update",
            "changed",
            code_path="/repo/auth.py",
            prompt_path="/repo/prompts/auth_python.prompt",
        )
        env = self._make_env()
        mock_result = MagicMock(returncode=0, stderr="")

        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run:
            heal_module(drift, env)

        # Every pdd command must use the heal env (git helper calls are
        # allowed to omit it — they need the ambient repo env to run).
        pdd_calls = [c for c in mock_run.call_args_list if c[0][0][:1] == ["pdd"]]
        assert pdd_calls, "heal_module should have invoked at least one pdd command"
        for call in pdd_calls:
            assert call[1].get("env") is env


# ---------------------------------------------------------------------------
# commit_and_push tests
# ---------------------------------------------------------------------------

class TestCaptureRollbackState:
    """_capture_rollback_state must recognize pdd sync/update even when
    top-level flags like `--strength 0.5` precede the subcommand."""

    _ENV = {"PDD_RESTORE_PROTECTED_PATHS_ON_FAILURE": "1"}

    def test_recognizes_update_with_strength_flag(self):
        clean = MagicMock(returncode=0, stdout="", stderr="")
        with patch("pdd.ci_drift_heal.subprocess.run", return_value=clean):
            result = _capture_rollback_state(
                ["pdd", "--force", "--strength", "0.5", "update", "/repo/foo.py"],
                self._ENV,
            )
        assert result is True  # clean state, rollback-eligible

    def test_recognizes_sync_with_strength_flag(self):
        clean = MagicMock(returncode=0, stdout="", stderr="")
        with patch("pdd.ci_drift_heal.subprocess.run", return_value=clean):
            result = _capture_rollback_state(
                ["pdd", "--force", "--strength", "0.5", "sync", "mod"],
                self._ENV,
            )
        assert result is True

    def test_ignores_pdd_example(self):
        """pdd example isn't tracked by the rollback mechanism."""
        result = _capture_rollback_state(
            ["pdd", "--force", "--strength", "0.5", "example", "p.prompt", "c.py"],
            self._ENV,
        )
        assert result is None

    def test_ignores_non_pdd_commands(self):
        result = _capture_rollback_state(["git", "status"], self._ENV)
        assert result is None


class TestCommitAndPush:
    def _mock_run_success(self, cmd, **kwargs):
        """Default subprocess mock: diff --cached returns 1 (changes exist), rest return 0."""
        r = MagicMock()
        r.returncode = 1 if cmd == ["git", "diff", "--cached", "--quiet"] else 0
        r.stdout = ""
        r.stderr = ""
        return r

    def test_empty_module_list(self):
        """Empty list returns True without running git."""
        assert commit_and_push([]) is True

    def test_commit_message_format(self):
        """Commit message includes module names."""
        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=self._mock_run_success) as mock_run, \
             patch("pdd.ci_drift_heal.Path.exists", return_value=True):
            commit_and_push(["auth", "api"], skip_ci=False)

        # Find the commit call
        commit_calls = [c for c in mock_run.call_args_list if c[0][0][0:2] == ["git", "commit"]]
        assert len(commit_calls) == 1
        msg = commit_calls[0][0][0][3]  # -m argument
        assert "auth" in msg
        assert "api" in msg
        assert "chore: auto-heal" in msg

    def test_checkpoint_adds_success_trailer(self):
        """Successful PR checkpoints get an explicit commit body marker."""
        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=self._mock_run_success) as mock_run, \
             patch("pdd.ci_drift_heal.Path.exists", return_value=True):
            commit_and_push(["auth"], checkpoint=True)

        commit_calls = [c for c in mock_run.call_args_list if c[0][0][0:2] == ["git", "commit"]]
        assert len(commit_calls) == 1
        commit_cmd = commit_calls[0][0][0]
        assert commit_cmd[-2:] == ["-m", _AUTO_HEAL_SUCCESS_TRAILER]

    def test_skip_ci_flag(self):
        """skip_ci=True prepends [skip ci] to commit message."""
        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=self._mock_run_success) as mock_run, \
             patch("pdd.ci_drift_heal.Path.exists", return_value=True):
            commit_and_push(["auth"], skip_ci=True)

        commit_calls = [c for c in mock_run.call_args_list if c[0][0][0:2] == ["git", "commit"]]
        msg = commit_calls[0][0][0][3]
        assert msg.startswith("[skip ci]")

    def test_no_staged_changes(self):
        """Returns True if no staged changes exist."""
        def mock_run(cmd, **kwargs):
            r = MagicMock()
            r.returncode = 0  # diff --cached --quiet returns 0 = no changes
            r.stdout = ""
            r.stderr = ""
            return r

        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=mock_run), \
             patch("pdd.ci_drift_heal.Path.exists", return_value=True):
            result = commit_and_push(["auth"])

        assert result is True

    def test_commit_failure(self):
        """Returns False when git commit fails."""
        call_count = [0]

        def mock_run(cmd, **kwargs):
            r = MagicMock()
            if cmd == ["git", "diff", "--cached", "--quiet"]:
                r.returncode = 1  # changes exist
            elif cmd[0:2] == ["git", "commit"]:
                r.returncode = 1
                r.stderr = "commit failed"
            else:
                r.returncode = 0
            r.stdout = ""
            if not hasattr(r, 'stderr') or r.stderr is None:
                r.stderr = ""
            return r

        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=mock_run), \
             patch("pdd.ci_drift_heal.Path.exists", return_value=True):
            result = commit_and_push(["auth"])

        assert result is False

    def test_push_failure(self):
        """Returns False when git push fails."""
        def mock_run(cmd, **kwargs):
            r = MagicMock()
            if cmd == ["git", "diff", "--cached", "--quiet"]:
                r.returncode = 1
            elif cmd == ["git", "push"]:
                r.returncode = 1
                r.stderr = "push failed"
            else:
                r.returncode = 0
            r.stdout = ""
            if not hasattr(r, 'stderr') or r.stderr is None:
                r.stderr = ""
            return r

        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=mock_run), \
             patch("pdd.ci_drift_heal.Path.exists", return_value=True):
            result = commit_and_push(["auth"])

        assert result is False

    def test_stages_all_changes(self):
        """Uses git add -A to stage all changes (healing may create new files)."""
        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=self._mock_run_success) as mock_run:
            commit_and_push(["auth"])

        add_calls = [c for c in mock_run.call_args_list if len(c[0][0]) >= 3 and c[0][0][0:2] == ["git", "add"]]
        assert len(add_calls) == 1
        assert add_calls[0][0][0] == ["git", "add", "-A"]


# ---------------------------------------------------------------------------
# main() tests
# ---------------------------------------------------------------------------

class TestMain:
    @staticmethod
    def _init_git_repo(repo: Path) -> None:
        subprocess.run(["git", "init"], cwd=repo, check=True, capture_output=True, text=True)
        subprocess.run(
            ["git", "config", "user.email", "ci-drift-heal-test@example.com"],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "CI Drift Heal Test"],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        )

    def test_no_drift_returns_zero(self):
        """When no drift detected, returns 0."""
        with patch("pdd.ci_drift_heal.detect_drift", return_value=([], [])):
            result = main()
        assert result == 0

    def test_no_drift_with_module_filter(self):
        """Module filter is passed to detect_drift."""
        with patch("pdd.ci_drift_heal.detect_drift", return_value=([], [])) as mock_detect:
            main(modules=["auth"])
        mock_detect.assert_called_once_with(["auth"], diff_base=None)

    def test_detection_failure_returns_one(self):
        """If detect_drift raises, returns 1."""
        with patch("pdd.ci_drift_heal.detect_drift", side_effect=RuntimeError("fail")):
            result = main()
        assert result == 1

    def test_successful_heal_and_commit(self):
        """Successful heal + commit returns 0."""
        drifts = ([DriftInfo("auth", "python", "update", "changed")], [])

        with patch("pdd.ci_drift_heal.detect_drift", return_value=drifts), \
             patch("pdd.ci_drift_heal.heal_module", return_value=True), \
             patch("pdd.ci_drift_heal.commit_and_push", return_value=True) as mock_commit, \
             patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake.csv")), \
             patch("pdd.ci_drift_heal.os.close"), \
             patch("pdd.ci_drift_heal.os.unlink"), \
             patch("pdd.ci_drift_heal.Path.write_text"):
            result = main()

        assert result == 0
        mock_commit.assert_called_once_with(["auth"], False, checkpoint=True)

    def test_heal_failure_returns_one(self):
        """Failed heal returns 1."""
        drifts = ([DriftInfo("auth", "python", "update", "changed")], [])

        with patch("pdd.ci_drift_heal.detect_drift", return_value=drifts), \
             patch("pdd.ci_drift_heal.heal_module", return_value=False), \
             patch("pdd.ci_drift_heal.commit_and_push", return_value=True), \
             patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake.csv")), \
             patch("pdd.ci_drift_heal.os.close"), \
             patch("pdd.ci_drift_heal.os.unlink"), \
             patch("pdd.ci_drift_heal.Path.write_text"):
            result = main()

        assert result == 1

    def test_commit_failure_returns_one(self):
        """Failed commit returns 1."""
        drifts = ([DriftInfo("auth", "python", "update", "changed")], [])

        with patch("pdd.ci_drift_heal.detect_drift", return_value=drifts), \
             patch("pdd.ci_drift_heal.heal_module", return_value=True), \
             patch("pdd.ci_drift_heal.commit_and_push", return_value=False), \
             patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake.csv")), \
             patch("pdd.ci_drift_heal.os.close"), \
             patch("pdd.ci_drift_heal.os.unlink"), \
             patch("pdd.ci_drift_heal.Path.write_text"):
            result = main()

        assert result == 1

    def test_budget_cap_stops_healing(self):
        """Budget cap prevents healing remaining modules."""
        drifts = (
            [
                DriftInfo("mod1", "python", "update", "changed"),
                DriftInfo("mod2", "python", "update", "changed"),
            ],
            [],
        )
        heal_calls = []

        def track_heal(drift, env):
            heal_calls.append(drift.basename)
            return True

        def high_cost(csv_path):
            return 10.0  # exceeds budget

        with patch("pdd.ci_drift_heal.detect_drift", return_value=drifts), \
             patch("pdd.ci_drift_heal.heal_module", side_effect=track_heal), \
             patch("pdd.ci_drift_heal._parse_cost_from_csv", side_effect=high_cost), \
             patch("pdd.ci_drift_heal.commit_and_push", return_value=True) as mock_commit, \
             patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake.csv")), \
             patch("pdd.ci_drift_heal.os.close"), \
             patch("pdd.ci_drift_heal.os.unlink"), \
             patch("pdd.ci_drift_heal.Path.write_text"):
            result = main(budget_cap=5.0)

        # mod1 healed, mod2 skipped due to budget
        assert heal_calls == ["mod1"]
        mock_commit.assert_not_called()
        assert result == 0

    def test_skip_ci_passed_to_commit(self):
        """skip_ci flag is forwarded to commit_and_push."""
        drifts = ([DriftInfo("auth", "python", "update", "changed")], [])

        with patch("pdd.ci_drift_heal.detect_drift", return_value=drifts), \
             patch("pdd.ci_drift_heal.heal_module", return_value=True), \
             patch("pdd.ci_drift_heal.commit_and_push", return_value=True) as mock_commit, \
             patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake.csv")), \
             patch("pdd.ci_drift_heal.os.close"), \
             patch("pdd.ci_drift_heal.os.unlink"), \
             patch("pdd.ci_drift_heal.Path.write_text"):
            main(skip_ci=True)

        mock_commit.assert_called_once_with(["auth"], True, checkpoint=False)

    def test_no_healed_modules_skips_commit(self):
        """If all modules fail healing, commit phase is skipped."""
        drifts = ([DriftInfo("auth", "python", "update", "changed")], [])

        with patch("pdd.ci_drift_heal.detect_drift", return_value=drifts), \
             patch("pdd.ci_drift_heal.heal_module", return_value=False), \
             patch("pdd.ci_drift_heal.commit_and_push") as mock_commit, \
             patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake.csv")), \
             patch("pdd.ci_drift_heal.os.close"), \
             patch("pdd.ci_drift_heal.os.unlink"), \
             patch("pdd.ci_drift_heal.Path.write_text"):
            result = main()

        mock_commit.assert_not_called()
        assert result == 1

    def test_pr_partial_failure_skips_commit_even_after_success(self):
        """PR mode must not checkpoint a run with any failed module."""
        drifts = (
            [
                DriftInfo("auth", "python", "update", "changed"),
                DriftInfo("api", "python", "update", "changed"),
            ],
            [],
        )

        with patch("pdd.ci_drift_heal.detect_drift", return_value=drifts), \
             patch("pdd.ci_drift_heal.heal_module", side_effect=[True, False]), \
             patch("pdd.ci_drift_heal.commit_and_push") as mock_commit, \
             patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake.csv")), \
             patch("pdd.ci_drift_heal.os.close"), \
             patch("pdd.ci_drift_heal.os.unlink"), \
             patch("pdd.ci_drift_heal.Path.write_text"):
            result = main(skip_ci=False)

        mock_commit.assert_not_called()
        assert result == 1

    def test_push_partial_failure_can_commit_without_checkpoint(self):
        """Push-to-main mode remains advisory but never creates a PR checkpoint."""
        drifts = (
            [
                DriftInfo("auth", "python", "update", "changed"),
                DriftInfo("api", "python", "update", "changed"),
            ],
            [],
        )

        with patch("pdd.ci_drift_heal.detect_drift", return_value=drifts), \
             patch("pdd.ci_drift_heal.heal_module", side_effect=[True, False]), \
             patch("pdd.ci_drift_heal.commit_and_push", return_value=True) as mock_commit, \
             patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake.csv")), \
             patch("pdd.ci_drift_heal.os.close"), \
             patch("pdd.ci_drift_heal.os.unlink"), \
             patch("pdd.ci_drift_heal.Path.write_text"):
            result = main(skip_ci=True)

        mock_commit.assert_called_once_with(["auth"], True, checkpoint=False)
        assert result == 0

    def test_pr_skipped_module_after_success_skips_commit_checkpoint(self):
        """PR mode must not checkpoint when any requested module was skipped."""
        drifts = (
            [
                DriftInfo("auth", "python", "update", "changed"),
                DriftInfo("api", "python", "update", "changed"),
            ],
            [],
        )

        with patch("pdd.ci_drift_heal.detect_drift", return_value=drifts), \
             patch("pdd.ci_drift_heal.heal_module", side_effect=[True, None]), \
             patch("pdd.ci_drift_heal.commit_and_push") as mock_commit, \
             patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake.csv")), \
             patch("pdd.ci_drift_heal.os.close"), \
             patch("pdd.ci_drift_heal.os.unlink"), \
             patch("pdd.ci_drift_heal.Path.write_text"):
            result = main(skip_ci=False)

        mock_commit.assert_not_called()
        assert result == 0

    def test_pr_update_followup_skip_after_success_skips_commit_checkpoint(self):
        """An update with skipped follow-up example is not checkpointable in PR mode."""
        drifts = (
            [
                DriftInfo("auth", "python", "update", "changed"),
            ],
            [],
        )

        with patch.dict(os.environ, {"PDD_HEAL_SYNC_SKIP_MODULES": "auth"}, clear=False), \
             patch("pdd.ci_drift_heal.detect_drift", return_value=drifts), \
             patch("pdd.ci_drift_heal.heal_module", return_value=True), \
             patch("pdd.ci_drift_heal.commit_and_push") as mock_commit, \
             patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake.csv")), \
             patch("pdd.ci_drift_heal.os.close"), \
             patch("pdd.ci_drift_heal.os.unlink"), \
             patch("pdd.ci_drift_heal.Path.write_text"):
            result = main(skip_ci=False)

        mock_commit.assert_not_called()
        assert result == 0

    def test_push_skipped_module_after_success_can_commit_without_checkpoint(self):
        """Push-to-main mode may commit healed work but never creates a PR checkpoint."""
        drifts = (
            [
                DriftInfo("auth", "python", "update", "changed"),
                DriftInfo("api", "python", "update", "changed"),
            ],
            [],
        )

        with patch("pdd.ci_drift_heal.detect_drift", return_value=drifts), \
             patch("pdd.ci_drift_heal.heal_module", side_effect=[True, None]), \
             patch("pdd.ci_drift_heal.commit_and_push", return_value=True) as mock_commit, \
             patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake.csv")), \
             patch("pdd.ci_drift_heal.os.close"), \
             patch("pdd.ci_drift_heal.os.unlink"), \
             patch("pdd.ci_drift_heal.Path.write_text"):
            result = main(skip_ci=True)

        mock_commit.assert_called_once_with(["auth"], True, checkpoint=False)
        assert result == 0

    def test_push_update_followup_skip_after_success_commits_without_checkpoint(self):
        """Push-to-main mode may publish an update whose follow-up example was skipped."""
        drifts = (
            [
                DriftInfo("auth", "python", "update", "changed"),
            ],
            [],
        )

        with patch.dict(os.environ, {"PDD_HEAL_SYNC_SKIP_MODULES": "auth"}, clear=False), \
             patch("pdd.ci_drift_heal.detect_drift", return_value=drifts), \
             patch("pdd.ci_drift_heal.heal_module", return_value=True), \
             patch("pdd.ci_drift_heal.commit_and_push", return_value=True) as mock_commit, \
             patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake.csv")), \
             patch("pdd.ci_drift_heal.os.close"), \
             patch("pdd.ci_drift_heal.os.unlink"), \
             patch("pdd.ci_drift_heal.Path.write_text"):
            result = main(skip_ci=True)

        mock_commit.assert_called_once_with(["auth"], True, checkpoint=False)
        assert result == 0

    def test_prompt_revert_failure_blocks_commit_even_after_other_success(self):
        """A failed revert makes the whole run unsafe to commit."""
        drifts = (
            [
                DriftInfo("auth", "python", "update", "changed"),
                DriftInfo("api", "python", "update", "changed"),
            ],
            [],
        )

        with patch("pdd.ci_drift_heal.detect_drift", return_value=drifts), \
             patch(
                 "pdd.ci_drift_heal.heal_module",
                 side_effect=[True, PromptRevertError("revert failed")],
             ), \
             patch("pdd.ci_drift_heal.commit_and_push") as mock_commit, \
             patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake.csv")), \
             patch("pdd.ci_drift_heal.os.close"), \
             patch("pdd.ci_drift_heal.os.unlink"), \
             patch("pdd.ci_drift_heal.Path.write_text"):
            result = main()

        mock_commit.assert_not_called()
        assert result == 1

    def test_explicit_sync_skip_env_skips_example_without_failing_build(self):
        """Operator override can skip a module's example regeneration without blocking auto-heal."""
        drifts = (
            [],
            [
                DriftInfo(
                    "agentic_change_orchestrator",
                    "python",
                    "example",
                    "stale",
                    code_path="/repo/agentic_change_orchestrator.py",
                    prompt_path="/repo/prompts/agentic_change_orchestrator_python.prompt",
                )
            ],
        )

        with patch.dict(
             os.environ,
             {"PDD_HEAL_SYNC_SKIP_MODULES": "agentic_change_orchestrator"},
             clear=False,
        ), patch("pdd.ci_drift_heal.detect_drift", return_value=drifts), \
             patch("pdd.ci_drift_heal._run_pdd_command") as mock_run_pdd, \
             patch("pdd.ci_drift_heal.commit_and_push") as mock_commit, \
             patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake.csv")), \
             patch("pdd.ci_drift_heal.os.close"), \
             patch("pdd.ci_drift_heal.os.unlink"), \
             patch("pdd.ci_drift_heal.Path.write_text"):
            result = main()

        assert result == 0
        mock_run_pdd.assert_not_called()
        mock_commit.assert_not_called()

    def test_end_to_end_example_failure_reverts_prompt_and_skips_commit(self, tmp_path, monkeypatch):
        """main() leaves a temp repo clean when update succeeds but follow-up example fails."""
        repo = tmp_path / "repo"
        repo.mkdir()
        self._init_git_repo(repo)

        prompt_path = repo / "pdd" / "prompts" / "auth_python.prompt"
        code_path = repo / "pdd" / "auth.py"
        prompt_path.parent.mkdir(parents=True)
        code_path.parent.mkdir(parents=True, exist_ok=True)

        initial_prompt = "% Goal\ninitial prompt\n"
        updated_prompt = "% Goal\nupdated prompt\n"
        prompt_path.write_text(initial_prompt, encoding="utf-8")
        code_path.write_text("def auth():\n    return True\n", encoding="utf-8")

        subprocess.run(["git", "add", "-A"], cwd=repo, check=True, capture_output=True, text=True)
        subprocess.run(
            ["git", "commit", "-m", "initial"],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        )

        monkeypatch.chdir(repo)
        drift = DriftInfo(
            "auth",
            "python",
            "update",
            "changed",
            code_path=str(code_path),
            prompt_path=str(prompt_path),
        )

        def run_pdd_side_effect(cmd, env, label):
            if cmd == ["pdd", "--force", "--strength", "0.5", "update", str(code_path)]:
                prompt_path.write_text(updated_prompt, encoding="utf-8")
                return True
            if cmd == ["pdd", "--force", "--strength", "0.5", "example", str(prompt_path), str(code_path)]:
                return False
            raise AssertionError(f"Unexpected command: {cmd}")

        with patch("pdd.ci_drift_heal.detect_drift", return_value=([drift], [])), \
             patch("pdd.ci_drift_heal._run_pdd_command", side_effect=run_pdd_side_effect):
            result = main()

        assert result == 1
        assert prompt_path.read_text(encoding="utf-8") == initial_prompt

        status = subprocess.run(
            ["git", "status", "--short"],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        )
        assert status.stdout.strip() == ""

        head_message = subprocess.run(
            ["git", "log", "-1", "--pretty=%s"],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        )
        assert head_message.stdout.strip() == "initial"

    def test_end_to_end_missing_code_path_skips_update_and_leaves_repo_clean(self, tmp_path, monkeypatch):
        """main() fails closed without invoking pdd update when code_path is unresolved."""
        repo = tmp_path / "repo"
        repo.mkdir()
        self._init_git_repo(repo)

        prompt_path = repo / "pdd" / "prompts" / "auth_python.prompt"
        prompt_path.parent.mkdir(parents=True)
        initial_prompt = "% Goal\ninitial prompt\n"
        prompt_path.write_text(initial_prompt, encoding="utf-8")

        subprocess.run(["git", "add", "-A"], cwd=repo, check=True, capture_output=True, text=True)
        subprocess.run(
            ["git", "commit", "-m", "initial"],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        )

        monkeypatch.chdir(repo)
        drift = DriftInfo(
            "auth",
            "python",
            "update",
            "changed",
            code_path=None,
            prompt_path="pdd/prompts/auth_python.prompt",
        )

        with patch("pdd.ci_drift_heal.detect_drift", return_value=([drift], [])), \
             patch("pdd.ci_drift_heal._run_pdd_command") as mock_run_pdd:
            result = main()

        assert result == 1
        mock_run_pdd.assert_not_called()
        assert prompt_path.read_text(encoding="utf-8") == initial_prompt

        status = subprocess.run(
            ["git", "status", "--short"],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        )
        assert status.stdout.strip() == ""


# ---------------------------------------------------------------------------
# _parse_cost_from_csv tests (via parse behavior in main)
# ---------------------------------------------------------------------------

class TestParseCostFromCsv:
    def test_valid_csv(self, tmp_path):
        """Parses cost column from CSV."""
        from pdd.ci_drift_heal import _parse_cost_from_csv

        csv_file = tmp_path / "cost.csv"
        csv_file.write_text("operation,cost\nupdate,0.15\nsync,0.25\n")
        assert _parse_cost_from_csv(str(csv_file)) == pytest.approx(0.40)

    def test_total_cost_column(self, tmp_path):
        """Falls back to total_cost column."""
        from pdd.ci_drift_heal import _parse_cost_from_csv

        csv_file = tmp_path / "cost.csv"
        csv_file.write_text("operation,total_cost\nupdate,0.50\n")
        assert _parse_cost_from_csv(str(csv_file)) == pytest.approx(0.50)

    def test_missing_file(self):
        """Returns 0.0 for non-existent file."""
        from pdd.ci_drift_heal import _parse_cost_from_csv

        assert _parse_cost_from_csv("/nonexistent/path.csv") == 0.0

    def test_empty_file(self, tmp_path):
        """Returns 0.0 for empty file."""
        from pdd.ci_drift_heal import _parse_cost_from_csv

        csv_file = tmp_path / "cost.csv"
        csv_file.write_text("")
        assert _parse_cost_from_csv(str(csv_file)) == 0.0

    def test_invalid_cost_values(self, tmp_path):
        """Skips non-numeric cost values."""
        from pdd.ci_drift_heal import _parse_cost_from_csv

        csv_file = tmp_path / "cost.csv"
        csv_file.write_text("operation,cost\nupdate,abc\nsync,0.10\n")
        assert _parse_cost_from_csv(str(csv_file)) == pytest.approx(0.10)


# ---------------------------------------------------------------------------
# _build_ci_env tests
# ---------------------------------------------------------------------------

class TestBuildCiEnv:
    def test_sets_required_env_vars(self):
        """Sets PDD_FORCE, CI, NO_COLOR, PDD_OUTPUT_COST_PATH."""
        from pdd.ci_drift_heal import _build_ci_env

        env = _build_ci_env("/tmp/cost.csv")
        assert env["PDD_FORCE"] == "1"
        assert env["CI"] == "1"
        assert env["NO_COLOR"] == "1"
        assert env["PDD_OUTPUT_COST_PATH"] == "/tmp/cost.csv"
        assert env["PDD_RESTORE_PROTECTED_PATHS_ON_FAILURE"] == "1"

    def test_inherits_current_env(self):
        """Inherits existing environment variables."""
        from pdd.ci_drift_heal import _build_ci_env

        with patch.dict(os.environ, {"MY_VAR": "hello"}):
            env = _build_ci_env("/tmp/cost.csv")
        assert env.get("MY_VAR") == "hello"


# ---------------------------------------------------------------------------
# _run_pdd_command rollback tests
# ---------------------------------------------------------------------------


class TestRunPddCommandRollback:
    def _env(self):
        env = {"PDD_RESTORE_PROTECTED_PATHS_ON_FAILURE": "1"}
        return env

    def test_timeout_restores_protected_paths_when_clean(self):
        """Timed-out sync restores tracked metadata/cache files if they started clean."""
        clean_status = MagicMock(returncode=0, stdout="", stderr="")
        restore_ok = MagicMock(returncode=0, stdout="", stderr="")

        def mock_run(cmd, **kwargs):
            if cmd[:3] == ["git", "status", "--porcelain"]:
                return clean_status
            if cmd[:3] == ["git", "restore", "--source=HEAD"]:
                return restore_ok
            if cmd == ["pdd", "sync", "auth"]:
                raise subprocess.TimeoutExpired(cmd, 600)
            raise AssertionError(f"Unexpected command: {cmd}")

        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=mock_run) as mock_run:
            result = _run_pdd_command(["pdd", "sync", "auth"], self._env(), "Heal auth")

        assert result is False
        calls = [c[0][0] for c in mock_run.call_args_list]
        assert ["git", "status", "--porcelain", "--", ".pdd/meta", "project_dependencies.csv"] in calls
        assert ["git", "restore", "--source=HEAD", "--", ".pdd/meta", "project_dependencies.csv"] in calls

    def test_failure_does_not_restore_when_protected_paths_already_dirty(self):
        """Pre-existing metadata/cache edits are left alone on heal failure."""
        dirty_status = MagicMock(
            returncode=0,
            stdout=" D .pdd/meta/auth_python.json\n",
            stderr="",
        )
        failed = MagicMock(returncode=1, stdout="", stderr="boom")

        def mock_run(cmd, **kwargs):
            if cmd[:3] == ["git", "status", "--porcelain"]:
                return dirty_status
            if cmd == ["pdd", "sync", "auth"]:
                return failed
            if cmd[:2] == ["git", "restore"]:
                raise AssertionError("restore should not run for already-dirty protected paths")
            raise AssertionError(f"Unexpected command: {cmd}")

        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=mock_run) as mock_run:
            result = _run_pdd_command(["pdd", "sync", "auth"], self._env(), "Heal auth")

        assert result is False
        calls = [c[0][0] for c in mock_run.call_args_list]
        assert ["git", "status", "--porcelain", "--", ".pdd/meta", "project_dependencies.csv"] in calls
        assert not any(cmd[:2] == ["git", "restore"] for cmd in calls)


# ---------------------------------------------------------------------------
# _parse_args tests
# ---------------------------------------------------------------------------

class TestParseArgs:
    def test_no_args(self):
        """Default values when no arguments given."""
        from pdd.ci_drift_heal import _parse_args

        args = _parse_args([])
        assert args.modules is None
        assert args.budget_cap is None
        assert args.skip_ci is False

    def test_modules(self):
        """--modules parses space-separated basenames."""
        from pdd.ci_drift_heal import _parse_args

        args = _parse_args(["--modules", "auth", "api"])
        assert args.modules == ["auth", "api"]

    def test_budget_cap(self):
        """--budget-cap parses float value."""
        from pdd.ci_drift_heal import _parse_args

        args = _parse_args(["--budget-cap", "5.50"])
        assert args.budget_cap == pytest.approx(5.50)

    def test_skip_ci(self):
        """--skip-ci sets flag to True."""
        from pdd.ci_drift_heal import _parse_args

        args = _parse_args(["--skip-ci"])
        assert args.skip_ci is True

    def test_modules_comma_separated(self):
        """Comma-separated modules string is expanded."""
        from pdd.ci_drift_heal import _parse_args

        args = _parse_args(["--modules", "auth,api"])
        assert args.modules == ["auth", "api"]

    def test_modules_space_separated(self):
        """Space-separated modules are kept as-is."""
        from pdd.ci_drift_heal import _parse_args

        args = _parse_args(["--modules", "auth", "api"])
        assert args.modules == ["auth", "api"]

    def test_modules_mixed(self):
        """Mixed comma and space-separated modules are fully expanded."""
        from pdd.ci_drift_heal import _parse_args

        args = _parse_args(["--modules", "auth,api", "utils"])
        assert args.modules == ["auth", "api", "utils"]

    def test_diff_base(self):
        """--diff-base parses string value."""
        from pdd.ci_drift_heal import _parse_args
        args = _parse_args(["--diff-base", "origin/main...HEAD"])
        assert args.diff_base == "origin/main...HEAD"

    def test_diff_base_default_none(self):
        """--diff-base defaults to None."""
        from pdd.ci_drift_heal import _parse_args
        args = _parse_args([])
        assert args.diff_base is None

    def test_all_options(self):
        """All options combined."""
        from pdd.ci_drift_heal import _parse_args
        args = _parse_args(["--modules", "auth", "--budget-cap", "3.0", "--skip-ci", "--diff-base", "HEAD~1"])
        assert args.modules == ["auth"]
        assert args.budget_cap == pytest.approx(3.0)
        assert args.skip_ci is True
        assert args.diff_base == "HEAD~1"


# ---------------------------------------------------------------------------
# Change-magnitude gate tests (PR gltanaka/pdd#1187 regression)
# ---------------------------------------------------------------------------

class TestPromptChurnGate:
    """Verify that _enforce_prompt_churn_gate reverts rewrites whose
    prompt churn is wildly out of proportion to the code change."""

    def _make_drift(self):
        return DriftInfo(
            basename="mod",
            language="python",
            operation="update",
            reason="code changed",
            code_path="pdd/mod.py",
            prompt_path="prompts/mod_python.prompt",
            diff_base="HEAD~1",
        )

    def test_gate_passes_when_ratio_under_cap(self, monkeypatch):
        from pdd.ci_drift_heal import _enforce_prompt_churn_gate

        def fake_numstat(args):
            if "prompts/mod_python.prompt" in args:
                return (2, 1)  # prompt churn 3
            return (1, 0)  # code churn 1; ratio = 3

        monkeypatch.setattr("pdd.ci_drift_heal._numstat_line_counts", fake_numstat)
        assert _enforce_prompt_churn_gate(self._make_drift()) is True

    def test_gate_trips_and_reverts_when_ratio_exceeds_cap(self, monkeypatch):
        from pdd.ci_drift_heal import _enforce_prompt_churn_gate

        def fake_numstat(args):
            if "prompts/mod_python.prompt" in args:
                return (41, 176)  # exact PR #1187 shape: 217 lines
            return (12, 1)  # code churn 13; ratio ~16.7

        monkeypatch.setattr("pdd.ci_drift_heal._numstat_line_counts", fake_numstat)

        captured_cmds = []

        def fake_run(cmd, **kwargs):
            captured_cmds.append(cmd)
            return subprocess.CompletedProcess(cmd, 0, stdout="", stderr="")

        monkeypatch.setattr("pdd.ci_drift_heal.subprocess.run", fake_run)

        result = _enforce_prompt_churn_gate(self._make_drift())
        assert result is False
        assert any(
            "checkout" in cmd and "prompts/mod_python.prompt" in cmd
            for cmd in captured_cmds
        )

    def test_gate_passes_when_inputs_missing(self, monkeypatch):
        from pdd.ci_drift_heal import _enforce_prompt_churn_gate

        drift = DriftInfo(
            basename="mod",
            language="python",
            operation="update",
            reason="x",
            code_path="pdd/mod.py",
            prompt_path=None,  # no prompt path → cannot measure
            diff_base="HEAD~1",
        )
        # Should not even call numstat when prompt_path is None
        called = {"count": 0}

        def fake_numstat(args):
            called["count"] += 1
            return (100, 100)

        monkeypatch.setattr("pdd.ci_drift_heal._numstat_line_counts", fake_numstat)
        assert _enforce_prompt_churn_gate(drift) is True
        assert called["count"] == 0

    def test_gate_passes_when_numstat_fails(self, monkeypatch):
        """If numstat returns None (git error), the gate is permissive so
        the structural-invariant validator can still run as primary guard."""
        from pdd.ci_drift_heal import _enforce_prompt_churn_gate

        monkeypatch.setattr(
            "pdd.ci_drift_heal._numstat_line_counts", lambda args: None
        )
        assert _enforce_prompt_churn_gate(self._make_drift()) is True

    def test_gate_cap_overridable_via_env(self, monkeypatch):
        from pdd.ci_drift_heal import _enforce_prompt_churn_gate

        def fake_numstat(args):
            if "prompts/mod_python.prompt" in args:
                return (3, 3)  # prompt churn 6
            return (1, 0)  # code churn 1; ratio 6

        monkeypatch.setattr("pdd.ci_drift_heal._numstat_line_counts", fake_numstat)
        monkeypatch.setenv("PDD_HEAL_PROMPT_CHURN_MAX_RATIO", "10.0")
        # cap is 10, ratio is 6 → passes
        assert _enforce_prompt_churn_gate(self._make_drift()) is True

        monkeypatch.setenv("PDD_HEAL_PROMPT_CHURN_MAX_RATIO", "3.0")
        # cap 3, ratio 6 → revert path triggers subprocess
        with patch("pdd.ci_drift_heal.subprocess.run") as mock_run:
            mock_run.return_value = subprocess.CompletedProcess([], 0, "", "")
            assert _enforce_prompt_churn_gate(self._make_drift()) is False


# ---------------------------------------------------------------------------
# Structural-invariants gate tests (PR gltanaka/pdd#1187 regression)
# ---------------------------------------------------------------------------

_FIXTURE_DIR = Path(__file__).parent / "fixtures"


class TestStructuralInvariants:
    """Verify that _enforce_structural_invariants rejects rewrites that
    strip <include> tags, <pdd.*> prefixed tags, % section markers, or
    fenced code blocks from the pre-heal prompt content. Gate is path-
    agnostic so it applies regardless of whether the legacy or agentic
    path produced the rewrite."""

    def _make_drift(self, prompt_path="prompts/mod_python.prompt"):
        return DriftInfo(
            basename="mod",
            language="python",
            operation="update",
            reason="code changed",
            code_path="/repo/pdd/mod.py",
            prompt_path=prompt_path,
            diff_base="HEAD~1",
        )

    def _patch_git_show(self, pre_content):
        """Patch _git_show_prompt_at_head to return pre_content."""
        return patch(
            "pdd.ci_drift_heal._git_show_prompt_at_head",
            return_value=pre_content,
        )

    def _patch_read(self, post_content):
        """Patch Path.read_text on the prompt path to return post_content."""
        return patch(
            "pdd.ci_drift_heal.Path.read_text",
            return_value=post_content,
        )

    def test_invariants_pass_on_identical_content(self):
        from pdd.ci_drift_heal import _enforce_structural_invariants

        content = (
            "<include>context/preamble.prompt</include>\n"
            "% Goal\n"
            "do the thing\n"
            "<pdd.foo_bar>\n"
            "stuff\n"
            "</pdd.foo_bar>\n"
            "```python\nprint('x')\n```\n"
        )
        with self._patch_git_show(content), self._patch_read(content):
            assert _enforce_structural_invariants(self._make_drift()) is True

    def test_invariants_pass_on_trivial_edit_preserving_structure(self):
        from pdd.ci_drift_heal import _enforce_structural_invariants

        pre = (
            "<include>ctx.prompt</include>\n"
            "% Goal\ndo x\n"
            "<pdd.helper>\n"
            "```python\nprint('x')\n```\n"
        )
        post = pre + "\n% Notes\nnew note added\n"
        with self._patch_git_show(pre), self._patch_read(post):
            assert _enforce_structural_invariants(self._make_drift()) is True

    def test_invariants_reject_stripped_pdd_prefix(self):
        from pdd.ci_drift_heal import _enforce_structural_invariants

        pre = "% Deps\n<pdd.agentic_common>\n<pdd.load_prompt_template>\n"
        post = "% Deps\n<agentic_common>\n<load_prompt_template>\n"
        with self._patch_git_show(pre), self._patch_read(post), \
             patch("pdd.ci_drift_heal.subprocess.run") as mock_run:
            mock_run.return_value = subprocess.CompletedProcess([], 0, "", "")
            assert _enforce_structural_invariants(self._make_drift()) is False

    def test_invariants_reject_dropped_include(self):
        from pdd.ci_drift_heal import _enforce_structural_invariants

        pre = (
            "<include>context/preamble.prompt</include>\n"
            "<include-many>tests/*</include-many>\n"
            "% Goal\n"
        )
        post = "% Goal\n"
        with self._patch_git_show(pre), self._patch_read(post), \
             patch("pdd.ci_drift_heal.subprocess.run") as mock_run:
            mock_run.return_value = subprocess.CompletedProcess([], 0, "", "")
            assert _enforce_structural_invariants(self._make_drift()) is False

    def test_invariants_reject_stripped_percent_markers(self):
        from pdd.ci_drift_heal import _enforce_structural_invariants

        pre = (
            "% Goal\ng\n% Inputs\ni\n% Steps\ns\n"
            "% Outputs\no\n% Notes\nn\n% Deps\nd\n"
        )
        # Six markers → threshold is ceil(6/2) = 3. Drop to 2 to violate.
        post = "% Goal\ng\n% Inputs\ni\n"
        with self._patch_git_show(pre), self._patch_read(post), \
             patch("pdd.ci_drift_heal.subprocess.run") as mock_run:
            mock_run.return_value = subprocess.CompletedProcess([], 0, "", "")
            assert _enforce_structural_invariants(self._make_drift()) is False

    def test_invariants_reject_dropped_fenced_code_block(self):
        from pdd.ci_drift_heal import _enforce_structural_invariants

        pre = (
            "% Goal\ng\n"
            "```python\n"
            "SPEC_LITERAL = {'x': 1, 'y': 2}\n"
            "```\n"
        )
        post = "% Goal\ng\nno more fenced block — prose only.\n"
        with self._patch_git_show(pre), self._patch_read(post), \
             patch("pdd.ci_drift_heal.subprocess.run") as mock_run:
            mock_run.return_value = subprocess.CompletedProcess([], 0, "", "")
            assert _enforce_structural_invariants(self._make_drift()) is False

    def test_invariants_reverts_prompt_file_on_violation(self):
        from pdd.ci_drift_heal import _enforce_structural_invariants

        pre = "<pdd.needed>\n% Goal\n"
        post = "<needed>\n% Goal\n"
        def mock_run(cmd, **kwargs):
            if cmd[:3] == ["git", "rev-parse", "--show-toplevel"]:
                return subprocess.CompletedProcess(cmd, 0, "/repo\n", "")
            return subprocess.CompletedProcess(cmd, 0, "", "")

        with self._patch_git_show(pre), self._patch_read(post), \
             patch("pdd.ci_drift_heal.subprocess.run", side_effect=mock_run) as mock_run:
            assert _enforce_structural_invariants(self._make_drift()) is False

        # Exactly one git checkout issued to revert the prompt file.
        checkout_calls = [
            c for c in mock_run.call_args_list
            if c[0][0][:3] == ["git", "checkout", "HEAD"]
        ]
        assert len(checkout_calls) == 1
        assert checkout_calls[0][0][0][-1] == "prompts/mod_python.prompt"

    def test_invariants_pass_when_inputs_missing(self):
        """Mirrors churn gate permissive-on-missing behavior."""
        from pdd.ci_drift_heal import _enforce_structural_invariants

        # No prompt_path → skip.
        drift = DriftInfo(
            basename="mod", language="python", operation="update",
            reason="x", code_path="/repo/pdd/mod.py",
            prompt_path=None, diff_base="HEAD~1",
        )
        assert _enforce_structural_invariants(drift) is True

        # git show fails → skip.
        with patch(
            "pdd.ci_drift_heal._git_show_prompt_at_head",
            return_value=None,
        ):
            assert _enforce_structural_invariants(self._make_drift()) is True

    def test_invariants_reject_actual_1187_regression(self):
        """End-to-end: real pre/post #1187 fixture content must be rejected."""
        from pdd.ci_drift_heal import _enforce_structural_invariants

        pre_path = _FIXTURE_DIR / "autoheal_1187_pre.prompt"
        post_path = _FIXTURE_DIR / "autoheal_1187_post.prompt"
        assert pre_path.exists(), f"fixture missing: {pre_path}"
        assert post_path.exists(), f"fixture missing: {post_path}"

        pre_content = pre_path.read_text()
        post_content = post_path.read_text()

        with patch(
            "pdd.ci_drift_heal._git_show_prompt_at_head",
            return_value=pre_content,
        ), patch(
            "pdd.ci_drift_heal.Path.read_text",
            return_value=post_content,
        ), patch("pdd.ci_drift_heal.subprocess.run") as mock_run:
            mock_run.return_value = subprocess.CompletedProcess([], 0, "", "")
            result = _enforce_structural_invariants(self._make_drift())

        assert result is False, (
            "Structural invariants must reject the real pre→post #1187 "
            "rewrite (41 lines replacing 176): <pdd.*> tags stripped, "
            "<include> preamble dropped, % markers eliminated."
        )

    def test_invariants_skip_fenced_blocks_via_env(self, monkeypatch):
        """PDD_HEAL_INVARIANTS_SKIP=fenced_blocks bypasses invariant #4.

        Motivation (per PR #1221 review): invariant #4 is the strictest —
        fenced blocks must be byte-identical — which would lock legitimate
        example-code refactors out of prompts. The env var provides an
        escape hatch so operators can unblock without a code change."""
        from pdd.ci_drift_heal import _enforce_structural_invariants

        pre = (
            "<include>ctx.prompt</include>\n"
            "% Goal\n"
            "<pdd.helper>\n"
            "```python\ndef old_signature(x): ...\n```\n"
        )
        post = (
            "<include>ctx.prompt</include>\n"
            "% Goal\n"
            "<pdd.helper>\n"
            "```python\ndef new_signature(x, y): ...\n```\n"
        )
        monkeypatch.setenv("PDD_HEAL_INVARIANTS_SKIP", "fenced_blocks")
        with self._patch_git_show(pre), self._patch_read(post):
            assert _enforce_structural_invariants(self._make_drift()) is True, (
                "With fenced_blocks skipped, a legitimate signature change "
                "inside a fenced block must pass the validator."
            )

    def test_invariants_skip_multiple_via_comma_separated_env(self, monkeypatch):
        """Comma-separated env list skips multiple invariants at once."""
        from pdd.ci_drift_heal import _enforce_structural_invariants

        pre = (
            "<include>ctx.prompt</include>\n"
            "% Goal\ndo\n"
            "<pdd.helper>\n"
            "```python\nprint('x')\n```\n"
        )
        # Strip both <pdd.*> and fenced block
        post = "<include>ctx.prompt</include>\n% Goal\ndo\n<helper>\n"
        monkeypatch.setenv(
            "PDD_HEAL_INVARIANTS_SKIP", "pdd_tags,fenced_blocks"
        )
        with self._patch_git_show(pre), self._patch_read(post):
            assert _enforce_structural_invariants(self._make_drift()) is True

    def test_invariants_skip_unknown_names_logged_but_ignored(self, monkeypatch):
        """Typo in env var name should not break the heal — log warning,
        drop unknown names, enforce the rest normally."""
        from pdd.ci_drift_heal import _enforce_structural_invariants

        pre = "<pdd.helper>\n% Goal\ndo\n"
        post = "<helper>\n% Goal\ndo\n"  # pdd prefix stripped
        # "fenced_block" (singular) is a common typo
        monkeypatch.setenv("PDD_HEAL_INVARIANTS_SKIP", "fenced_block,foo_bar")
        with self._patch_git_show(pre), self._patch_read(post), \
             patch("pdd.ci_drift_heal.subprocess.run") as mock_run:
            mock_run.return_value = subprocess.CompletedProcess([], 0, "", "")
            # Unknown names dropped → pdd_tags invariant still runs → rejects
            assert _enforce_structural_invariants(self._make_drift()) is False

    def test_invariants_skip_empty_env_enforces_all(self, monkeypatch):
        """Empty / whitespace-only env var enforces all invariants
        (equivalent to unset)."""
        from pdd.ci_drift_heal import _enforce_structural_invariants

        pre = "<pdd.helper>\ntext\n"
        post = "<helper>\ntext\n"
        monkeypatch.setenv("PDD_HEAL_INVARIANTS_SKIP", "   ")
        with self._patch_git_show(pre), self._patch_read(post), \
             patch("pdd.ci_drift_heal.subprocess.run") as mock_run:
            mock_run.return_value = subprocess.CompletedProcess([], 0, "", "")
            assert _enforce_structural_invariants(self._make_drift()) is False
