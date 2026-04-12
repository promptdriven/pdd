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
        changed_files = {"pdd/auth.py", "prompts/auth_python.prompt"}
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
        changed_files = {"prompts/auth_python.prompt"}
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

    def test_update_runs_update_then_sync(self):
        """prompt drift (update) runs 'pdd update' then 'pdd sync' in one pass."""
        drift = DriftInfo("auth", "python", "update", "changed", code_path="/repo/auth.py")
        mock_result = MagicMock(returncode=0, stderr="")

        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run:
            result = heal_module(drift, self._make_env())

        assert result is True
        cmds = [c[0][0] for c in mock_run.call_args_list]
        assert cmds[0] == ["pdd", "update", "/repo/auth.py"]
        assert cmds[1] == ["pdd", "sync", "auth"]

    def test_update_no_code_path_falls_back(self):
        """prompt drift (update) runs 'pdd update' (no args) when code_path is None."""
        drift = DriftInfo("auth", "python", "update", "changed", code_path=None)
        mock_result = MagicMock(returncode=0, stderr="")

        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run:
            result = heal_module(drift, self._make_env())

        assert result is True
        cmds = [c[0][0] for c in mock_run.call_args_list]
        assert cmds[0] == ["pdd", "update"]
        assert cmds[1] == ["pdd", "sync", "auth"]

    def test_update_failure_skips_sync(self):
        """If pdd update fails, pdd sync is not attempted."""
        drift = DriftInfo("auth", "python", "update", "changed", code_path="/repo/auth.py")
        mock_result = MagicMock(returncode=1, stderr="error")

        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run:
            result = heal_module(drift, self._make_env())

        assert result is False
        # Only update was called, not sync
        assert len(mock_run.call_args_list) == 1

    def test_update_ok_sync_fails_still_returns_true(self):
        """If update succeeds but sync fails, returns True (prompt update is committed)."""
        drift = DriftInfo("auth", "python", "update", "changed", code_path="/repo/auth.py")
        call_count = [0]

        def mock_run(cmd, **kwargs):
            call_count[0] += 1
            r = MagicMock()
            r.returncode = 0 if call_count[0] == 1 else 1  # update ok, sync fails
            r.stderr = "" if call_count[0] == 1 else "sync error"
            return r

        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=mock_run):
            result = heal_module(drift, self._make_env())

        assert result is True  # partial success — prompt was updated

    def test_example_runs_pdd_sync(self):
        """example drift runs 'pdd sync <basename>'."""
        drift = DriftInfo("api", "python", "example", "stale")
        mock_result = MagicMock(returncode=0, stderr="")

        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run:
            result = heal_module(drift, self._make_env())

        assert result is True
        assert len(mock_run.call_args_list) == 1
        assert mock_run.call_args[0][0] == ["pdd", "sync", "api"]

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
        """Environment dict is passed to subprocess.run."""
        drift = DriftInfo("auth", "python", "update", "changed")
        env = self._make_env()
        mock_result = MagicMock(returncode=0, stderr="")

        with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run:
            heal_module(drift, env)

        # Both update and sync calls should use the same env
        for call in mock_run.call_args_list:
            assert call[1]["env"] is env


# ---------------------------------------------------------------------------
# commit_and_push tests
# ---------------------------------------------------------------------------

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
             patch("pdd.ci_drift_heal.commit_and_push", return_value=True), \
             patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake.csv")), \
             patch("pdd.ci_drift_heal.os.close"), \
             patch("pdd.ci_drift_heal.os.unlink"), \
             patch("pdd.ci_drift_heal.Path.write_text"):
            result = main()

        assert result == 0

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
             patch("pdd.ci_drift_heal.commit_and_push", return_value=True), \
             patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake.csv")), \
             patch("pdd.ci_drift_heal.os.close"), \
             patch("pdd.ci_drift_heal.os.unlink"), \
             patch("pdd.ci_drift_heal.Path.write_text"):
            result = main(budget_cap=5.0)

        # mod1 healed, mod2 skipped due to budget
        assert heal_calls == ["mod1"]
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

        mock_commit.assert_called_once_with(["auth"], True)

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
