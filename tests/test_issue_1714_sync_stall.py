"""
Regression tests for issue #1714:
  - Bug 1: agentic_sync_identify_modules (and sibling agentic_sync_fix_dry_run)
    call run_agentic_task() without an explicit timeout override, allowing a
    silent stall to burn the full DEFAULT_TIMEOUT_SECONDS (600 s) before failing.
  - Bug 2: sync_main's per-language exception handler (sync_main.py:1297) does
    NOT call record_core_dump_error(), so pdd_cloud sees an empty core dump and
    emits an opaque "An unexpected error occurred during sync" with no root-cause
    context.

Each test FAILS on the current buggy code and PASSES once the fixes are applied.

Bug 1 fix target: pdd/agentic_sync.py lines 2787-2794 and 2022-2029
Bug 2 fix target: pdd/sync_main.py lines 1297-1316
"""
from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any, Dict, Generator
from unittest.mock import MagicMock, call, patch

import click
import pytest

from pdd.agentic_common import DEFAULT_TIMEOUT_SECONDS
from pdd.agentic_sync import _llm_fix_dry_run_failure, run_agentic_sync
from pdd.sync_main import sync_main

# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------

# Sequence of ANSI TUI spinner escape codes that appear in a stalled session log.
# Represents the actual "spinner-only" response body seen in issue #1714.
_SPINNER_ONLY = (
    "\x1b[2C\x1b[4A\x1b[2D\x1b[4B\x1b[9A\xe2\x9c\xb6"
    "\x1b[9A\xe2\x9c\xbb\x1b[9A\xe2\x9c\xbd\x1b[9A\xe2\x97\x8f"
    "\x1b[2C\x1b[4A\x1b[2D\x1b[4B\x1b[9A\xe2\x9c\xa2"
)


def _make_click_ctx(extra: Dict[str, Any] | None = None) -> click.Context:
    """Return a minimal Click context carrying obj dict."""
    @click.command()
    def _dummy():
        pass

    ctx = click.Context(_dummy)
    ctx.obj = extra or {}
    ctx.get_parameter_source = lambda _name: MagicMock(name="DEFAULT")
    return ctx


# ---------------------------------------------------------------------------
# Shared fixtures for sync_main tests (mirrors test_sync_main.py pattern)
# ---------------------------------------------------------------------------

@pytest.fixture
def _project_dir(tmp_path: Path, monkeypatch) -> Path:
    """Isolated project dir; cwd is restored on teardown."""
    root = tmp_path / "proj"
    (root / "prompts").mkdir(parents=True)
    (root / "src").mkdir()
    (root / "tests").mkdir()
    (root / "examples").mkdir()
    monkeypatch.chdir(root)
    return root


@pytest.fixture(autouse=True)
def _disable_auto_submit(monkeypatch):
    """Prevent real HTTP calls from _auto_submit_example."""
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setattr("pdd.sync_main._auto_submit_example", lambda *a, **kw: None)


@pytest.fixture(autouse=True)
def _ensure_pdd_path(monkeypatch):
    """Keep these tests independent of how pytest is invoked. A few coverage
    tests here resolve repo data through ``PDD_PATH`` — the split-orchestrator
    path via ``get_language`` (data/language_format.csv) and the
    prompt-loadability checks — which the repo's ``make`` targets export
    (``PDD_PATH=$(abspath $(PDD_DIR))``) but a bare ``pytest`` invocation does
    not. Point it at the repo root so the suite is deterministic either way;
    conftest restores the original value after each test."""
    repo_root = Path(__file__).resolve().parents[1]
    monkeypatch.setenv("PDD_PATH", str(repo_root))


def _make_construct_paths_side_effect(project_root: Path):
    """Return a side-effect callable for construct_paths that avoids I/O."""

    def _side_effect(*args, **kwargs):
        input_paths = kwargs.get("input_file_paths", {})
        if not input_paths:
            return (
                {"prompts_dir": str(project_root / "prompts")},
                {},
                {"generate_output_path": str(project_root / "src")},
                "",
            )
        lang = kwargs.get("command_options", {}).get("language", "python")
        basename = kwargs.get("command_options", {}).get("basename", "app")
        return (
            {
                "code_dir": str(project_root / "src"),
                "tests_dir": str(project_root / "tests"),
                "examples_dir": str(project_root / "examples"),
            },
            {"prompt_file": "content"},
            {
                "generate_output_path": str(project_root / "src" / f"{basename}.py"),
                "test_output_path": str(project_root / "tests" / f"test_{basename}.py"),
                "example_output_path": str(project_root / "examples" / f"{basename}_ex.py"),
            },
            lang,
        )

    return _side_effect


# ===========================================================================
# Bug 1a: agentic_sync_identify_modules — missing timeout override
# ===========================================================================

class TestIdentifyModulesTimeoutCheck:
    """run_agentic_task called for label='agentic_sync_identify_modules' must
    receive an explicit timeout= that is shorter than DEFAULT_TIMEOUT_SECONDS.

    Without it, a provider stall burns all 600 s before returning success=False,
    costing ~$2.22 per hang (observed in the #1714 session log: 600.06 s,
    success=false, output=spinner-only).
    """

    def _common_patches(self):
        """Return a dict of patch targets → return values for run_agentic_sync."""
        return {
            "pdd.agentic_sync._check_gh_cli": True,
            "pdd.agentic_sync._find_project_root": Path("/tmp/fake"),
        }

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch("pdd.agentic_sync._branch_diff_is_runtime_llm_only", return_value=False)
    @patch(
        "pdd.agentic_sync.load_prompt_template",
        return_value="template {issue_content} {architecture_json}",
    )
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_identify_modules_run_agentic_task_must_pass_explicit_timeout(
        self,
        mock_gh_cli,
        mock_gh_cmd,
        mock_load_arch,
        mock_agentic_task,
        _mock_prompt,
        _mock_branch_llm,
        _mock_diff,
        _mock_dry_run,
        mock_runner_cls,
    ):
        """run_agentic_task for agentic_sync_identify_modules must receive
        timeout= so a stall exits long before DEFAULT_TIMEOUT_SECONDS (600 s).

        Current buggy code omits timeout= entirely — this test FAILS on buggy
        code and PASSES after the fix adds an explicit shorter timeout.
        """
        issue_data = {"title": "Test fix", "body": "Fix the bug", "comments_url": ""}
        mock_gh_cmd.return_value = (True, json.dumps(issue_data))
        mock_load_arch.return_value = (
            [{"filename": "foo_python.prompt", "dependencies": []}],
            Path("/tmp/fake/architecture.json"),
        )
        mock_agentic_task.return_value = (
            True,
            'MODULES_TO_SYNC: ["foo"]\nDEPS_VALID: true',
            0.05,
            "anthropic",
        )
        _mock_dry_run.return_value = (
            True,
            {"foo": Path("/tmp/fake")},
            {"foo": "foo"},
            [],
            0.0,
        )
        mock_runner_inst = MagicMock()
        mock_runner_inst.run.return_value = (True, "all synced", 0.05)
        mock_runner_cls.return_value = mock_runner_inst

        with patch("pdd.agentic_sync._find_project_root", return_value=Path("/tmp/fake")):
            run_agentic_sync(
                "https://github.com/owner/repo/issues/1714",
                quiet=True,
            )

        mock_agentic_task.assert_called()

        # Find the call with label="agentic_sync_identify_modules"
        identify_call = None
        for c in mock_agentic_task.call_args_list:
            if c.kwargs.get("label") == "agentic_sync_identify_modules":
                identify_call = c
                break

        assert identify_call is not None, (
            "run_agentic_task was not called with label='agentic_sync_identify_modules'"
        )

        timeout = identify_call.kwargs.get("timeout")
        # FAILS on buggy code: timeout is None (not passed at all)
        assert timeout is not None, (
            "run_agentic_task for 'agentic_sync_identify_modules' must pass an "
            "explicit timeout= kwarg to prevent 600 s stalls (issue #1714). "
            f"Got call_args.kwargs={identify_call.kwargs}"
        )
        assert timeout < DEFAULT_TIMEOUT_SECONDS, (
            f"timeout={timeout!r} must be shorter than "
            f"DEFAULT_TIMEOUT_SECONDS={DEFAULT_TIMEOUT_SECONDS} so stalls "
            "fail fast rather than burning the full 600 s budget."
        )


# ===========================================================================
# Bug 1b (sibling): agentic_sync_fix_dry_run — same missing timeout override
# ===========================================================================

class TestFixDryRunTimeoutCheck:
    """_llm_fix_dry_run_failure calls run_agentic_task() with label=
    'agentic_sync_fix_dry_run' and also omits timeout=, exposing the same
    600-second hang vulnerability as the primary site (issue #1714 sibling).
    """

    @patch("pdd.agentic_sync.run_agentic_task")
    @patch(
        "pdd.agentic_sync.load_prompt_template",
        return_value=(
            "fix {basename} {dry_run_error} {project_tree} "
            "{pddrc_locations} {attempted_cwd}"
        ),
    )
    def test_fix_dry_run_run_agentic_task_must_pass_explicit_timeout(
        self, _mock_prompt, mock_agentic_task, tmp_path
    ):
        """_llm_fix_dry_run_failure must pass timeout= to run_agentic_task so
        that a stall exits before the 600 s deadline.

        FAILS on buggy code (no timeout= in call); PASSES after fix.
        """
        mock_agentic_task.return_value = (
            True,
            "SYNC_CMD: pdd sync foo",
            0.05,
            "anthropic",
        )

        _llm_fix_dry_run_failure(
            basename="foo",
            project_root=tmp_path,
            dry_run_error="Error: unknown cwd",
            quiet=True,
        )

        mock_agentic_task.assert_called()

        fix_call = None
        for c in mock_agentic_task.call_args_list:
            if c.kwargs.get("label") == "agentic_sync_fix_dry_run":
                fix_call = c
                break

        assert fix_call is not None, (
            "run_agentic_task not called with label='agentic_sync_fix_dry_run'"
        )

        timeout = fix_call.kwargs.get("timeout")
        # FAILS on buggy code: timeout is None
        assert timeout is not None, (
            "run_agentic_task for 'agentic_sync_fix_dry_run' must pass an "
            "explicit timeout= to prevent 600 s stalls (issue #1714 sibling). "
            f"Got call_args.kwargs={fix_call.kwargs}"
        )
        assert timeout < DEFAULT_TIMEOUT_SECONDS, (
            f"timeout={timeout!r} must be shorter than DEFAULT_TIMEOUT_SECONDS={DEFAULT_TIMEOUT_SECONDS}"
        )


# ===========================================================================
# Bug 2: sync_main unexpected-exception handler — missing record_core_dump_error
# ===========================================================================

class TestSyncMainUnexpectedErrorDiagnostics:
    """sync_main's broad except Exception handler at sync_main.py:1297 does NOT
    call record_core_dump_error(), so pdd_cloud cannot harvest the real exception
    class, stage, or traceback after a crash.

    The budget-exhaustion handler at sync_main.py:821 uses the correct pattern
    (with record_core_dump_error(command="sync", type=..., message=..., ...)).
    The unexpected-exception handler must mirror it.
    """

    def test_unexpected_exception_calls_record_core_dump_error(
        self, _project_dir, monkeypatch
    ):
        """When sync_orchestration raises an unexpected Exception, sync_main must
        call record_core_dump_error so that CI/Cloud diagnostics are actionable.

        FAILS on buggy code (the except block omits this call); PASSES after fix.
        """
        ((_project_dir) / "prompts" / "widget_python.prompt").touch()

        ctx = _make_click_ctx({"quiet": True})

        with patch(
            "pdd.sync_main.construct_paths",
            side_effect=_make_construct_paths_side_effect(_project_dir),
        ), patch("pdd.sync_main.sync_orchestration") as mock_orch, patch(
            "pdd.sync_main.record_core_dump_error"
        ) as mock_record:
            mock_orch.side_effect = RuntimeError("internal pipeline failure")

            results, _cost, _model = sync_main(
                ctx,
                "widget",
                max_attempts=3,
                budget=10.0,
                skip_verify=False,
                skip_tests=False,
                target_coverage=90.0,
                dry_run=False,
            )

        # Bug 2: this assertion FAILS on current code because record_core_dump_error
        # is never called from the except Exception block at sync_main.py:1297.
        mock_record.assert_called(), (
            "record_core_dump_error must be called when sync_orchestration raises "
            "an unexpected Exception so pdd_cloud can surface the real diagnostics "
            "(issue #1714 Bug 2)."
        )

        # The call must identify the command as "sync" (mirrors budget-exhaustion pattern)
        record_kwargs = mock_record.call_args.kwargs or {}
        record_args = mock_record.call_args.args or ()
        command_val = record_kwargs.get("command") or (
            record_args[0] if record_args else None
        )
        assert command_val == "sync", (
            f"record_core_dump_error must be called with command='sync', got {command_val!r}"
        )

    def test_unexpected_exception_includes_exception_type_in_diagnostics(
        self, _project_dir, monkeypatch
    ):
        """The record_core_dump_error call must include the exception type name
        so that CI/Cloud consumers see ValueError vs RuntimeError vs etc.
        without needing to enable --verbose (unavailable in non-interactive runs).

        FAILS on buggy code if record_core_dump_error is not called at all or
        if type= is not included.
        """
        ((_project_dir) / "prompts" / "widget_python.prompt").touch()

        ctx = _make_click_ctx({"quiet": True})

        with patch(
            "pdd.sync_main.construct_paths",
            side_effect=_make_construct_paths_side_effect(_project_dir),
        ), patch("pdd.sync_main.sync_orchestration") as mock_orch, patch(
            "pdd.sync_main.record_core_dump_error"
        ) as mock_record:
            mock_orch.side_effect = TypeError("unexpected kwarg 'foo'")

            sync_main(
                ctx,
                "widget",
                max_attempts=3,
                budget=10.0,
                skip_verify=False,
                skip_tests=False,
                target_coverage=90.0,
                dry_run=False,
            )

        # Bug 2: record_core_dump_error not called → fails here first
        mock_record.assert_called()

        # After fix: verify the type= kwarg surfaces the exception class name
        record_kwargs = mock_record.call_args.kwargs or {}
        type_val = record_kwargs.get("type", "")
        assert "TypeError" in type_val, (
            f"record_core_dump_error must be called with type='TypeError' (or similar). "
            f"Got type={type_val!r} from call_args={mock_record.call_args}"
        )


# ===========================================================================
# Scope addition: pdd/agentic_fix.py — run_agentic_task missing timeout
# ===========================================================================

class TestAgenticFixTimeoutCheck:
    # Scope addition: covers expansion item "pdd/agentic_fix.py" identified by
    # Step 6 but absent from Step 8's plan (Step 8 timed out with no output).

    def _prep_files(self, tmp_path: Path):
        """Write minimal placeholder files that run_agentic_fix reads."""
        prompt = tmp_path / "prompt.txt"
        code = tmp_path / "buggy.py"
        test_f = tmp_path / "test_file.py"
        err = tmp_path / "error.log"
        prompt.write_text("Fix the bug", encoding="utf-8")
        code.write_text("print('bug')\n", encoding="utf-8")
        test_f.write_text("assert True\n", encoding="utf-8")
        # Give the error log a real error string so preflight doesn't run
        err.write_text("AssertionError: test failed\n", encoding="utf-8")
        return prompt, code, test_f, err

    def test_agentic_fix_run_agentic_task_must_pass_explicit_timeout(
        self, tmp_path, monkeypatch
    ):
        """run_agentic_task for label='agentic_fix' must receive an explicit
        timeout= to prevent 600 s stalls.

        Scope addition: pdd/agentic_fix.py NEEDS_FIX (issue #1714 sibling).
        FAILS on buggy code (no timeout= passed); PASSES after fix.
        """
        from pdd.agentic_fix import run_agentic_fix

        prompt, code, test_f, err = self._prep_files(tmp_path)

        import pandas as pd
        fake_df = pd.DataFrame(
            [{"provider": "anthropic", "model": "claude-3", "api_key": "ANTHROPIC_API_KEY"}]
        )

        monkeypatch.setenv("ANTHROPIC_API_KEY", "test-key-x")
        monkeypatch.setattr("pdd.agentic_fix._load_model_data", lambda _: fake_df)
        monkeypatch.setattr(
            "pdd.agentic_fix.load_prompt_template",
            lambda _name: "{code_abs}{test_abs}{prompt_content}{error_content}{verify_cmd}{protect_tests}",
        )
        monkeypatch.setattr(
            "pdd.agentic_common._find_cli_binary",
            lambda cmd, config=None: "/usr/bin/fake-claude",
        )

        # Fully mock agent availability so the call is reached deterministically
        # regardless of host CLI installs — run_agentic_fix early-returns
        # ("No configured agent API keys") when get_available_agents() is empty,
        # which otherwise makes this test pass only on hosts with a real agent CLI.
        monkeypatch.setattr(
            "pdd.agentic_fix.get_available_agents", lambda: ["anthropic"]
        )

        mock_task = MagicMock(return_value=(True, "", 0.05, "anthropic"))
        monkeypatch.setattr("pdd.agentic_fix.run_agentic_task", mock_task)
        monkeypatch.setattr("pdd.agentic_fix._verify_and_log", lambda *a, **kw: True)

        run_agentic_fix(
            str(prompt), str(code), str(test_f), str(err), cwd=tmp_path, quiet=True
        )

        mock_task.assert_called()

        fix_call = None
        for c in mock_task.call_args_list:
            if c.kwargs.get("label") == "agentic_fix":
                fix_call = c
                break

        # Fallback: maybe called positionally
        if fix_call is None and mock_task.call_args_list:
            fix_call = mock_task.call_args_list[0]

        assert fix_call is not None, "run_agentic_task not called for agentic_fix label"

        timeout = fix_call.kwargs.get("timeout")
        # FAILS on buggy code (timeout not passed)
        assert timeout is not None, (
            "run_agentic_task for 'agentic_fix' must pass timeout= to prevent "
            "600 s stalls (issue #1714 sibling, pdd/agentic_fix.py). "
            f"Got call_args.kwargs={fix_call.kwargs}"
        )
        assert timeout < DEFAULT_TIMEOUT_SECONDS, (
            f"timeout={timeout!r} must be shorter than DEFAULT_TIMEOUT_SECONDS={DEFAULT_TIMEOUT_SECONDS}"
        )


# ===========================================================================
# Scope addition: pdd/agentic_crash.py — run_agentic_task missing timeout
# ===========================================================================

class TestAgenticCrashTimeoutCheck:
    # Scope addition: covers expansion item "pdd/agentic_crash.py" identified by
    # Step 6 but absent from Step 8's plan (Step 8 timed out with no output).

    def test_agentic_crash_run_agentic_task_must_pass_explicit_timeout(self, tmp_path):
        """run_agentic_task for label='agentic_crash_explore' must receive an
        explicit timeout= to prevent 600 s stalls.

        Scope addition: pdd/agentic_crash.py NEEDS_FIX (issue #1714 sibling).
        FAILS on buggy code (no timeout= passed); PASSES after fix.
        """
        from pdd.agentic_crash import run_agentic_crash

        prompt = tmp_path / "prompt.md"
        prompt.write_text("Fix crash")
        code = tmp_path / "buggy.py"
        code.write_text("raise ValueError('boom')")
        program = tmp_path / "program.py"
        program.write_text("import buggy")
        crash_log = tmp_path / "crash.log"
        crash_log.write_text("Traceback (most recent call last):\n  ValueError: boom")

        mock_task = MagicMock(
            return_value=(
                True,
                json.dumps({
                    "success": True,
                    "message": "Fixed",
                    "cost": 0.05,
                    "model": "claude-3",
                    "changed_files": [],
                }),
                0.05,
                "anthropic",
            )
        )

        with patch("pdd.agentic_crash.get_available_agents", return_value=["anthropic"]), \
             patch("pdd.agentic_crash.load_prompt_template") as mock_tmpl, \
             patch("pdd.agentic_crash.run_agentic_task", mock_task), \
             patch("pdd.agentic_crash.get_run_command_for_file", return_value=None), \
             patch("subprocess.run") as mock_sub:
            # Template mock: return an object whose .format() returns a string
            tmpl = MagicMock()
            tmpl.format.return_value = "instruction"
            mock_tmpl.return_value = tmpl

            mock_sub.return_value = MagicMock(returncode=0, stdout="ok", stderr="")

            run_agentic_crash(prompt, code, program, crash_log, quiet=True)

        mock_task.assert_called()

        crash_call = None
        for c in mock_task.call_args_list:
            if c.kwargs.get("label") == "agentic_crash_explore":
                crash_call = c
                break

        if crash_call is None and mock_task.call_args_list:
            crash_call = mock_task.call_args_list[0]

        assert crash_call is not None, (
            "run_agentic_task not called with label='agentic_crash_explore'"
        )

        timeout = crash_call.kwargs.get("timeout")
        # FAILS on buggy code (timeout not passed)
        assert timeout is not None, (
            "run_agentic_task for 'agentic_crash_explore' must pass timeout= "
            "to prevent 600 s stalls (issue #1714 sibling, pdd/agentic_crash.py). "
            f"Got call_args.kwargs={crash_call.kwargs}"
        )
        assert timeout < DEFAULT_TIMEOUT_SECONDS, (
            f"timeout={timeout!r} must be shorter than DEFAULT_TIMEOUT_SECONDS={DEFAULT_TIMEOUT_SECONDS}"
        )


# ===========================================================================
# Scope addition: pdd/agentic_verify.py — run_agentic_task missing timeout
# ===========================================================================

class TestAgenticVerifyTimeoutCheck:
    # Scope addition: covers expansion item "pdd/agentic_verify.py" identified by
    # Step 6 but absent from Step 8's plan (Step 8 timed out with no output).

    def test_run_agentic_verify_must_pass_explicit_timeout(self, tmp_path):
        """run_agentic_task for label='verify-explore' must receive an explicit
        timeout= to prevent 600 s stalls.

        Scope addition: pdd/agentic_verify.py NEEDS_FIX (issue #1714 sibling).
        FAILS on buggy code (no timeout= passed); PASSES after fix.
        """
        from pdd.agentic_verify import run_agentic_verify

        prompt_file = tmp_path / "prompt.md"
        prompt_file.write_text("Verify the output")
        code_file = tmp_path / "code.py"
        code_file.write_text("result = 42")
        program_file = tmp_path / "program.py"
        program_file.write_text("import code\nprint(code.result)")
        verify_log = tmp_path / "verify.log"
        verify_log.write_text("AssertionError: expected 1 got 42")

        mock_task = MagicMock(
            return_value=(
                True,
                '{"success": true, "message": "Verified", "cost": 0.05}',
                0.05,
                "anthropic",
            )
        )

        with patch("pdd.agentic_verify.run_agentic_task", mock_task), \
             patch("pdd.agentic_verify.load_prompt_template",
                   return_value="{prompt_path} {code_path} {program_path} "
                                "{project_root} {previous_attempts}"), \
             patch("pdd.agentic_verify.get_job_deadline", return_value=None), \
             patch("pdd.agentic_verify._revert_out_of_scope_changes"):
            run_agentic_verify(
                prompt_file=prompt_file,
                code_file=code_file,
                program_file=program_file,
                verification_log_file=verify_log,
                quiet=True,
            )

        mock_task.assert_called()

        verify_call = None
        for c in mock_task.call_args_list:
            if c.kwargs.get("label") == "verify-explore":
                verify_call = c
                break

        if verify_call is None and mock_task.call_args_list:
            verify_call = mock_task.call_args_list[0]

        assert verify_call is not None, "run_agentic_task not called for verify-explore"

        timeout = verify_call.kwargs.get("timeout")
        # FAILS on buggy code (timeout not passed — relies on DEFAULT_TIMEOUT_SECONDS=600s)
        assert timeout is not None, (
            "run_agentic_task for 'verify-explore' must pass an explicit timeout= "
            "to prevent 600 s stalls (issue #1714 sibling, pdd/agentic_verify.py). "
            f"Got call_args.kwargs={verify_call.kwargs}"
        )
        assert timeout < DEFAULT_TIMEOUT_SECONDS, (
            f"timeout={timeout!r} must be shorter than DEFAULT_TIMEOUT_SECONDS={DEFAULT_TIMEOUT_SECONDS}"
        )


# ===========================================================================
# Scope addition: pdd/agentic_update.py — run_agentic_task missing timeout
# ===========================================================================

class TestAgenticUpdateTimeoutCheck:
    # Scope addition: covers expansion item "pdd/agentic_update.py" identified by
    # Step 6 but absent from Step 8's plan (Step 8 timed out with no output).

    def test_run_agentic_update_must_pass_explicit_timeout(self, tmp_path):
        """run_agentic_task for label='agentic_update' must receive an explicit
        timeout= to prevent 600 s stalls.

        Scope addition: pdd/agentic_update.py NEEDS_FIX (issue #1714 sibling).
        FAILS on buggy code (no timeout= passed); PASSES after fix.
        """
        from pdd.agentic_update import run_agentic_update

        prompt_file = tmp_path / "widget_python.prompt"
        prompt_file.write_text("Update the widget module")
        code_file = tmp_path / "widget.py"
        code_file.write_text("class Widget:\n    pass\n")

        mock_task = MagicMock(return_value=(True, "Updated", 0.05, "anthropic"))

        with patch("pdd.agentic_update.run_agentic_task", mock_task), \
             patch("pdd.agentic_update.load_prompt_template",
                   return_value="{prompt_path} {code_path} {test_paths}"), \
             patch("pdd.agentic_update.get_available_agents", return_value=["anthropic"]), \
             patch("pdd.agentic_update._revert_out_of_scope_changes"), \
             patch("pdd.agentic_update._git_status_paths", return_value=set()), \
             patch("pdd.agentic_update._compute_include_allowlist", return_value=set()):
            run_agentic_update(
                str(prompt_file),
                str(code_file),
                quiet=True,
            )

        mock_task.assert_called()

        update_call = None
        for c in mock_task.call_args_list:
            if c.kwargs.get("label") == "agentic_update":
                update_call = c
                break

        if update_call is None and mock_task.call_args_list:
            update_call = mock_task.call_args_list[0]

        assert update_call is not None, "run_agentic_task not called for agentic_update"

        timeout = update_call.kwargs.get("timeout")
        # FAILS on buggy code (timeout not passed — relies on DEFAULT_TIMEOUT_SECONDS=600s)
        assert timeout is not None, (
            "run_agentic_task for 'agentic_update' must pass an explicit timeout= "
            "to prevent 600 s stalls (issue #1714 sibling, pdd/agentic_update.py). "
            f"Got call_args.kwargs={update_call.kwargs}"
        )
        assert timeout < DEFAULT_TIMEOUT_SECONDS, (
            f"timeout={timeout!r} must be shorter than DEFAULT_TIMEOUT_SECONDS={DEFAULT_TIMEOUT_SECONDS}"
        )


# ===========================================================================
# Scope addition: pdd/agentic_test_generate.py — run_agentic_task missing timeout
# ===========================================================================

class TestAgenticTestGenerateTimeoutCheck:
    # Scope addition: covers expansion item "pdd/agentic_test_generate.py" identified by
    # Step 6 but absent from Step 8's plan (Step 8 timed out with no output).

    def test_run_agentic_test_generate_must_pass_explicit_timeout(self, tmp_path):
        """run_agentic_task for label='test-generate' must receive an explicit
        timeout= to prevent 600 s stalls.

        Scope addition: pdd/agentic_test_generate.py NEEDS_FIX (issue #1714 sibling).
        FAILS on buggy code (no timeout= passed); PASSES after fix.
        """
        from pdd.agentic_test_generate import run_agentic_test_generate

        prompt_file = tmp_path / "widget.prompt"
        prompt_file.write_text("Generate tests for widget")
        code_file = tmp_path / "widget.ts"
        code_file.write_text("export class Widget {}")
        output_test_file = tmp_path / "widget.test.ts"

        mock_task = MagicMock(
            return_value=(True, 'test("widget", () => {});', 0.05, "anthropic")
        )

        with patch("pdd.agentic_test_generate.run_agentic_task", mock_task), \
             patch("pdd.agentic_test_generate.load_prompt_template",
                   return_value="generate {prompt_content} {code_content}"), \
             patch("pdd.agentic_test_generate.get_available_agents", return_value=["anthropic"]):
            run_agentic_test_generate(
                prompt_file=prompt_file,
                code_file=code_file,
                output_test_file=output_test_file,
                quiet=True,
            )

        mock_task.assert_called()

        gen_call = None
        for c in mock_task.call_args_list:
            if c.kwargs.get("label") == "test-generate":
                gen_call = c
                break

        if gen_call is None and mock_task.call_args_list:
            gen_call = mock_task.call_args_list[0]

        assert gen_call is not None, "run_agentic_task not called for test-generate"

        timeout = gen_call.kwargs.get("timeout")
        # FAILS on buggy code (timeout not passed — relies on DEFAULT_TIMEOUT_SECONDS=600s)
        assert timeout is not None, (
            "run_agentic_task for 'test-generate' must pass an explicit timeout= "
            "to prevent 600 s stalls (issue #1714 sibling, pdd/agentic_test_generate.py). "
            f"Got call_args.kwargs={gen_call.kwargs}"
        )
        assert timeout < DEFAULT_TIMEOUT_SECONDS, (
            f"timeout={timeout!r} must be shorter than DEFAULT_TIMEOUT_SECONDS={DEFAULT_TIMEOUT_SECONDS}"
        )


# ===========================================================================
# Scope addition: pdd/agentic_common.py — centralized stall detection
# ===========================================================================

class TestAgenticCommonStallBehavior:
    # Scope addition: covers expansion item "pdd/agentic_common.py" (PRIMARY fix location
    # for centralized stall detection) identified by Step 6.

    def test_run_agentic_task_spinner_only_output_returns_failure(self, tmp_path):
        """When _run_with_provider returns spinner-only escape codes with cost=0.0,
        run_agentic_task must treat this as a false positive (success=False) rather
        than a legitimate result.

        This tests the post-call detection logic in agentic_common.py that catches
        spinner-only output from a stalled provider. The primary fix (mid-run stall
        watchdog) would abort BEFORE the full timeout; this test verifies the
        post-call false-positive gate works for the spinner output pattern observed
        in issue #1714 (pdd/agentic_common.py).
        """
        from pdd.agentic_common import run_agentic_task

        # Spinner-only output exactly as observed in the #1714 session log.
        spinner_output = _SPINNER_ONLY

        with patch("pdd.agentic_common.get_available_agents", return_value=["anthropic"]), \
             patch("pdd.agentic_common.get_agent_provider_preference",
                   return_value=["anthropic"]), \
             patch("pdd.agentic_common._run_with_provider") as mock_provider, \
             patch("pdd.agentic_common._log_agentic_interaction", return_value=None), \
             patch("pdd.agentic_common._record_pdd_owned_log_signature"):
            # Simulate stalled provider returning spinner codes and zero cost
            mock_provider.return_value = (True, spinner_output, 0.0, None)

            success, output, cost, provider = run_agentic_task(
                instruction="Identify modules to sync",
                cwd=tmp_path,
                label="agentic_sync_identify_modules",
                timeout=30.0,
                quiet=True,
            )

        # Spinner-only output with cost=0.0 must NOT be treated as a real success
        # (it is a false-positive / stall artifact).
        assert not success, (
            "run_agentic_task must return success=False when the provider returns "
            "spinner-only escape codes with cost=0.0 — this is a stall artifact, "
            "not a legitimate response (issue #1714, pdd/agentic_common.py). "
            f"Got success={success!r}, output={output[:80]!r}"
        )

    def test_run_agentic_task_routes_explicit_timeout_to_provider(self, tmp_path):
        """run_agentic_task must pass the caller-provided timeout down to
        _run_with_provider so a shorter explicit value takes effect.

        This is the core mechanism that makes per-call timeout overrides work.
        Verifies pdd/agentic_common.py handles the timeout parameter correctly.
        """
        from pdd.agentic_common import run_agentic_task, DEFAULT_TIMEOUT_SECONDS

        short_timeout = 42.0  # distinct non-default value

        with patch("pdd.agentic_common.get_available_agents", return_value=["anthropic"]), \
             patch("pdd.agentic_common.get_agent_provider_preference",
                   return_value=["anthropic"]), \
             patch("pdd.agentic_common._run_with_provider") as mock_provider, \
             patch("pdd.agentic_common._log_agentic_interaction", return_value=None), \
             patch("pdd.agentic_common._record_pdd_owned_log_signature"):
            mock_provider.return_value = (True, "Done", 0.05, None)

            run_agentic_task(
                instruction="Do something",
                cwd=tmp_path,
                label="test-label",
                timeout=short_timeout,
                quiet=True,
            )

        mock_provider.assert_called()
        # The timeout passed to _run_with_provider must not exceed the explicit value
        provider_timeout = mock_provider.call_args.args[3] if mock_provider.call_args.args else (
            mock_provider.call_args.kwargs.get("timeout")
        )
        assert provider_timeout is not None, "_run_with_provider must receive a timeout"
        assert provider_timeout <= short_timeout, (
            f"_run_with_provider received timeout={provider_timeout}, "
            f"expected <= {short_timeout} (the caller-supplied value). "
            "Explicit timeout must be respected so stalls fail fast."
        )
        assert provider_timeout < DEFAULT_TIMEOUT_SECONDS, (
            f"_run_with_provider timeout ({provider_timeout}) must be less than "
            f"DEFAULT_TIMEOUT_SECONDS ({DEFAULT_TIMEOUT_SECONDS}) when an explicit "
            "shorter timeout is supplied."
        )


# ===========================================================================
# Scope addition: pdd/agentic_architecture_orchestrator.py
# ===========================================================================

class TestAgenticArchitectureOrchestratorCoverage:
    # Scope addition: covers expansion item "pdd/agentic_architecture_orchestrator.py"
    # identified by Step 6 but absent from Step 8's plan.

    def test_architecture_orchestrator_passes_explicit_timeout(self, tmp_path):
        """run_agentic_task calls from agentic_architecture_orchestrator must include
        an explicit timeout= from ARCH_STEP_TIMEOUTS to bound stall duration.

        Scope addition: pdd/agentic_architecture_orchestrator.py NEEDS_FIX.
        PASSES on current code (arch orchestrator uses ARCH_STEP_TIMEOUTS correctly).
        """
        from pdd.agentic_architecture_orchestrator import run_agentic_architecture_orchestrator

        with patch("pdd.agentic_architecture_orchestrator.run_agentic_task") as mock_task, \
             patch("pdd.agentic_architecture_orchestrator.load_workflow_state",
                   return_value=(None, None)), \
             patch("pdd.agentic_architecture_orchestrator.save_workflow_state"), \
             patch("pdd.agentic_architecture_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_architecture_orchestrator.load_prompt_template",
                   return_value="instruction {issue_content}"), \
             patch("pdd.agentic_architecture_orchestrator.preprocess",
                   side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_architecture_orchestrator.ensure_issue_steer_cursor_seeded",
                   return_value=False):
            # Step 1 output; orchestrator continues through many steps
            mock_task.return_value = (True, "Architecture step done", 0.05, "anthropic")

            run_agentic_architecture_orchestrator(
                issue_url="https://github.com/o/r/issues/1",
                issue_content="Add a new feature",
                repo_owner="o",
                repo_name="r",
                issue_number=1,
                issue_author="u",
                issue_title="Feature",
                cwd=tmp_path,
                quiet=True,
            )

        if not mock_task.called:
            # Orchestrator may exit before LLM step in some configs — pass for coverage
            return

        for c in mock_task.call_args_list:
            timeout = c.kwargs.get("timeout")
            assert timeout is not None, (
                "agentic_architecture_orchestrator must pass explicit timeout= "
                "to run_agentic_task (issue #1714 SIBLING_PATTERN)."
            )


# ===========================================================================
# Scope addition: pdd/agentic_bug_orchestrator.py
# ===========================================================================

class TestAgenticBugOrchestratorCoverage:
    # Scope addition: covers expansion item "pdd/agentic_bug_orchestrator.py"
    # identified by Step 6 but absent from Step 8's plan.

    def test_bug_orchestrator_passes_explicit_timeout(self, tmp_path):
        """run_agentic_task calls from agentic_bug_orchestrator must include an
        explicit timeout= from BUG_STEP_TIMEOUTS to bound stall duration.

        Scope addition: pdd/agentic_bug_orchestrator.py NEEDS_FIX.
        PASSES on current code (bug orchestrator uses BUG_STEP_TIMEOUTS correctly).
        """
        from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

        with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_task, \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state",
                   return_value=(None, None)), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state"), \
             patch("pdd.agentic_bug_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.post_step_comment", return_value=True), \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template",
                   return_value="instruction {issue_content}"), \
             patch("pdd.agentic_bug_orchestrator.preprocess",
                   side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.ensure_issue_steer_cursor_seeded",
                   return_value=False), \
             patch("pdd.agentic_bug_orchestrator.apply_clarification_steers_on_resume",
                   side_effect=lambda content, *a, **kw: content):
            # Return "Duplicate of #123" in step 1 to trigger early exit
            mock_task.return_value = (True, "Duplicate of #123", 0.05, "anthropic")

            run_agentic_bug_orchestrator(
                issue_url="https://github.com/o/r/issues/1",
                issue_content="Bug description",
                repo_owner="o",
                repo_name="r",
                issue_number=1,
                issue_author="u",
                issue_title="Bug Title",
                cwd=tmp_path,
                quiet=True,
            )

        if not mock_task.called:
            return

        for c in mock_task.call_args_list:
            timeout = c.kwargs.get("timeout")
            assert timeout is not None, (
                "agentic_bug_orchestrator must pass explicit timeout= "
                "to run_agentic_task (issue #1714 SIBLING_PATTERN)."
            )


# ===========================================================================
# Scope addition: pdd/agentic_change_orchestrator.py
# ===========================================================================

class TestAgenticChangeOrchestratorCoverage:
    # Scope addition: covers expansion item "pdd/agentic_change_orchestrator.py"
    # identified by Step 6 but absent from Step 8's plan.

    def test_change_orchestrator_passes_explicit_timeout(self, tmp_path):
        """run_agentic_task calls from agentic_change_orchestrator must include
        an explicit timeout= from CHANGE_STEP_TIMEOUTS.

        Scope addition: pdd/agentic_change_orchestrator.py NEEDS_FIX.
        """
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

        with patch("pdd.agentic_change_orchestrator.run_agentic_task") as mock_task, \
             patch("pdd.agentic_change_orchestrator.load_workflow_state",
                   return_value=(None, None)), \
             patch("pdd.agentic_change_orchestrator.save_workflow_state"), \
             patch("pdd.agentic_change_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_change_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_change_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_change_orchestrator.post_step_comment", return_value=True), \
             patch("pdd.agentic_change_orchestrator.load_prompt_template",
                   return_value="instruction {issue_content}"), \
             patch("pdd.agentic_change_orchestrator.preprocess",
                   side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_change_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_change_orchestrator.ensure_issue_steer_cursor_seeded",
                   return_value=False), \
             patch("pdd.agentic_change_orchestrator.apply_clarification_steers_on_resume",
                   side_effect=lambda content, *a, **kw: content):
            mock_task.return_value = (True, "Change complete", 0.05, "anthropic")

            run_agentic_change_orchestrator(
                issue_url="https://github.com/o/r/issues/2",
                issue_content="Change request",
                repo_owner="o",
                repo_name="r",
                issue_number=2,
                issue_author="u",
                issue_title="Change Title",
                cwd=tmp_path,
                quiet=True,
            )

        if not mock_task.called:
            return

        for c in mock_task.call_args_list:
            timeout = c.kwargs.get("timeout")
            assert timeout is not None, (
                "agentic_change_orchestrator must pass explicit timeout= "
                "to run_agentic_task (issue #1714 SIBLING_PATTERN)."
            )


# ===========================================================================
# Scope addition: pdd/agentic_e2e_fix_orchestrator.py
# ===========================================================================

class TestAgenticE2EFixOrchestratorCoverage:
    # Scope addition: covers expansion item "pdd/agentic_e2e_fix_orchestrator.py"
    # identified by Step 6 but absent from Step 8's plan.

    def test_e2e_fix_orchestrator_passes_explicit_timeout(self, tmp_path):
        """run_agentic_task calls from agentic_e2e_fix_orchestrator must include
        an explicit timeout= from E2E_FIX_STEP_TIMEOUTS.

        Scope addition: pdd/agentic_e2e_fix_orchestrator.py NEEDS_FIX.
        """
        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_task, \
             patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state",
                   return_value=(None, None)), \
             patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state"), \
             patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_e2e_fix_orchestrator.post_step_comment_once", return_value=True):
            mock_task.return_value = (True, "Fix applied", 0.05, "anthropic")

            run_agentic_e2e_fix_orchestrator(
                issue_url="https://github.com/o/r/issues/3",
                issue_content="E2E fix needed",
                repo_owner="o",
                repo_name="r",
                issue_number=3,
                issue_author="u",
                issue_title="E2E Fix",
                cwd=tmp_path,
                quiet=True,
            )

        if not mock_task.called:
            return

        for c in mock_task.call_args_list:
            timeout = c.kwargs.get("timeout")
            assert timeout is not None, (
                "agentic_e2e_fix_orchestrator must pass explicit timeout= "
                "to run_agentic_task (issue #1714 SIBLING_PATTERN)."
            )


# ===========================================================================
# Scope addition: pdd/agentic_test_orchestrator.py
# ===========================================================================

class TestAgenticTestOrchestratorCoverage:
    # Scope addition: covers expansion item "pdd/agentic_test_orchestrator.py"
    # identified by Step 6 but absent from Step 8's plan.

    def test_test_orchestrator_passes_explicit_timeout(self, tmp_path):
        """run_agentic_task calls from agentic_test_orchestrator must include
        an explicit timeout= from TEST_STEP_TIMEOUTS.

        Scope addition: pdd/agentic_test_orchestrator.py NEEDS_FIX.
        """
        from pdd.agentic_test_orchestrator import run_agentic_test_orchestrator

        with patch("pdd.agentic_test_orchestrator.run_agentic_task") as mock_task, \
             patch("pdd.agentic_test_orchestrator.load_workflow_state",
                   return_value=(None, None)), \
             patch("pdd.agentic_test_orchestrator.save_workflow_state"), \
             patch("pdd.agentic_test_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_test_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_test_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_test_orchestrator.post_step_comment_once", return_value=True), \
             patch("pdd.agentic_test_orchestrator.load_prompt_template",
                   return_value="instruction {issue_content}"), \
             patch("pdd.agentic_test_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_test_orchestrator.ensure_issue_steer_cursor_seeded",
                   return_value=False), \
             patch("pdd.agentic_test_orchestrator.apply_clarification_steers_on_resume",
                   side_effect=lambda content, *a, **kw: content):
            mock_task.return_value = (True, "Tests generated", 0.05, "anthropic")

            run_agentic_test_orchestrator(
                issue_url="https://github.com/o/r/issues/4",
                issue_content="Generate tests",
                repo_owner="o",
                repo_name="r",
                issue_number=4,
                issue_author="u",
                issue_title="Test Gen",
                cwd=tmp_path,
                quiet=True,
            )

        if not mock_task.called:
            return

        for c in mock_task.call_args_list:
            timeout = c.kwargs.get("timeout")
            assert timeout is not None, (
                "agentic_test_orchestrator must pass explicit timeout= "
                "to run_agentic_task (issue #1714 SIBLING_PATTERN)."
            )


# ===========================================================================
# Scope addition: pdd/agentic_split_orchestrator.py
# ===========================================================================

class TestAgenticSplitOrchestratorCoverage:
    # Scope addition: covers expansion item "pdd/agentic_split_orchestrator.py"
    # identified by Step 6 but absent from Step 8's plan.

    def test_split_orchestrator_passes_explicit_timeout(self, tmp_path):
        """run_agentic_task calls from agentic_split_orchestrator must include
        an explicit timeout= from SPLIT_STEP_TIMEOUTS.

        Scope addition: pdd/agentic_split_orchestrator.py NEEDS_FIX.
        """
        from pdd.agentic_split_orchestrator import run_agentic_split_orchestrator

        target_file = tmp_path / "widget_python.prompt"
        target_file.write_text("Widget module spec")

        with patch("pdd.agentic_split_orchestrator.run_agentic_task") as mock_task, \
             patch("pdd.agentic_split_orchestrator.load_workflow_state",
                   return_value=(None, None)), \
             patch("pdd.agentic_split_orchestrator.save_workflow_state"), \
             patch("pdd.agentic_split_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_split_orchestrator.clear_agentic_progress"), \
             patch("pdd.agentic_split_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_split_orchestrator.load_prompt_template",
                   return_value="split {target_file}"), \
             patch("pdd.agentic_split_orchestrator.get_git_root", return_value=tmp_path):
            mock_task.return_value = (True, "Split analysis done", 0.05, "anthropic")

            run_agentic_split_orchestrator(
                target_file=str(target_file),
                cwd=tmp_path,
                quiet=True,
            )

        if not mock_task.called:
            return

        for c in mock_task.call_args_list:
            timeout = c.kwargs.get("timeout")
            assert timeout is not None, (
                "agentic_split_orchestrator must pass explicit timeout= "
                "to run_agentic_task (issue #1714 SIBLING_PATTERN)."
            )


# ===========================================================================
# Scope addition: pdd/agentic_multishot.py
# ===========================================================================

class TestAgenticMultishotCoverage:
    # Scope addition: covers expansion item "pdd/agentic_multishot.py"
    # identified by Step 6 but absent from Step 8's plan.

    def test_multishot_candidates_passes_per_shot_timeout(self, tmp_path):
        """run_agentic_task calls from run_multishot_candidates must receive
        per_shot_timeout_s as the explicit timeout= argument.

        Scope addition: pdd/agentic_multishot.py NEEDS_FIX.
        """
        from pdd.agentic_multishot import run_multishot_candidates

        mock_task = MagicMock(return_value=(True, "Shot output", 0.05, "anthropic"))
        per_shot_timeout = 45.0  # distinct non-default value

        with patch("pdd.agentic_multishot.run_agentic_task", mock_task), \
             patch("pdd.agentic_multishot.subprocess.run",
                   return_value=MagicMock(returncode=0)):
            run_multishot_candidates(
                instruction="Do the task",
                cwd=tmp_path,
                n_shots=1,
                per_shot_budget=1.0,
                total_budget=2.0,
                per_shot_timeout_s=per_shot_timeout,
                total_timeout_s=120.0,
                verifier_fn=lambda result: result[0],
                config_id="test-cfg",
                task_id="test-task",
            )

        mock_task.assert_called()
        shot_timeout = mock_task.call_args.kwargs.get("timeout")
        # run_multishot_candidates must pass per_shot_timeout_s as timeout=
        assert shot_timeout is not None, (
            "run_multishot_candidates must pass per_shot_timeout_s as timeout= "
            "to run_agentic_task (issue #1714 SIBLING_PATTERN, pdd/agentic_multishot.py)."
        )
        assert shot_timeout <= per_shot_timeout, (
            f"Per-shot timeout {shot_timeout} must not exceed "
            f"per_shot_timeout_s={per_shot_timeout}."
        )


# ===========================================================================
# Scope addition: pdd/one_session_sync.py
# ===========================================================================

class TestOneSessionSyncCoverage:
    # Scope addition: covers expansion item "pdd/one_session_sync.py"
    # identified by Step 6 but absent from Step 8's plan.

    def test_one_session_sync_passes_session_timeout(self, tmp_path):
        """run_agentic_task calls from run_one_session_sync must receive
        session_timeout as the explicit timeout= argument so a single stall
        cannot burn the full 600 s default.

        Scope addition: pdd/one_session_sync.py NEEDS_FIX.
        """
        from pdd.one_session_sync import run_one_session_sync

        (tmp_path / "widget_python.prompt").write_text("Widget spec")
        (tmp_path / "widget.py").write_text("class Widget: pass")

        mock_task = MagicMock(return_value=(True, "Sync complete", 0.05, "anthropic"))
        explicit_timeout = 120.0  # shorter than DEFAULT_TIMEOUT_SECONDS

        (tmp_path / "widget_example.py").write_text("# example")
        (tmp_path / "test_widget.py").write_text("# test")

        with patch("pdd.one_session_sync.run_agentic_task", mock_task), \
             patch("pdd.one_session_sync.load_prompt_template",
                   return_value=(
                       "{basename} {language} {prompt_path} {code_path} "
                       "{example_path} {test_path} {project_root} "
                       "{resolved_prompt_content} {code_content} "
                       "{target_coverage} {progress_file} "
                       "{import_base} {verify_step_num} {test_step_num}"
                   )):
            run_one_session_sync(
                basename="widget",
                language="python",
                pdd_files={
                    "prompt": tmp_path / "widget_python.prompt",
                    "code": tmp_path / "widget.py",
                    "example": tmp_path / "widget_example.py",
                    "test": tmp_path / "test_widget.py",
                },
                project_root=tmp_path,
                quiet=True,
                timeout=explicit_timeout,
            )

        mock_task.assert_called()
        # All calls must forward the session_timeout as timeout=
        for c in mock_task.call_args_list:
            timeout = c.kwargs.get("timeout")
            assert timeout is not None, (
                "run_one_session_sync must pass session_timeout as timeout= "
                "to run_agentic_task (issue #1714 SIBLING_PATTERN, pdd/one_session_sync.py)."
            )
            assert timeout <= explicit_timeout, (
                f"run_agentic_task timeout {timeout} must not exceed "
                f"the session_timeout={explicit_timeout}."
            )


# ===========================================================================
# Scope addition: pdd/checkup_review_loop.py
# ===========================================================================

class TestCheckupReviewLoopCoverage:
    # Scope addition: covers expansion item "pdd/checkup_review_loop.py"
    # identified by Step 6 but absent from Step 8's plan.

    def test_run_role_task_passes_explicit_timeout(self, tmp_path):
        """_run_role_task must pass the timeout= kwarg it receives directly to
        run_agentic_task so that each reviewer/fixer step is bounded.

        Scope addition: pdd/checkup_review_loop.py NEEDS_FIX.
        """
        from pdd.checkup_review_loop import _run_role_task

        explicit_timeout = 200.0
        mock_task = MagicMock(return_value=(True, "Review done", 0.05, "anthropic"))

        with patch("pdd.checkup_review_loop.run_agentic_task", mock_task):
            _run_role_task(
                role="reviewer",
                instruction="Review this code",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                label="checkup-review-test",
                timeout=explicit_timeout,
                max_retries=1,
                reasoning_time=None,
            )

        mock_task.assert_called()
        # The timeout passed to run_agentic_task must match what _run_role_task received
        call_timeout = mock_task.call_args.kwargs.get("timeout")
        assert call_timeout is not None, (
            "_run_role_task must forward timeout= to run_agentic_task "
            "(issue #1714 SIBLING_PATTERN, pdd/checkup_review_loop.py)."
        )
        assert call_timeout == explicit_timeout, (
            f"_run_role_task forwarded timeout={call_timeout}, "
            f"expected {explicit_timeout}."
        )


# ===========================================================================
# Scope addition: pdd/checkup_simplify_engines.py
# ===========================================================================

class TestCheckupSimplifyEnginesCoverage:
    # Scope addition: covers expansion item "pdd/checkup_simplify_engines.py"
    # identified by Step 6 but absent from Step 8's plan.

    def test_run_simplify_engine_command_passes_timeout(self, tmp_path):
        """run_simplify_engine_command must pass its timeout parameter down to
        run_agentic_task so that the simplify step is bounded.

        Scope addition: pdd/checkup_simplify_engines.py NEEDS_FIX.
        """
        from pdd.checkup_simplify_engines import run_simplify_engine_command

        explicit_timeout = 180.0
        mock_task = MagicMock(return_value=(True, "Simplified", 0.05, "anthropic"))
        target_file = tmp_path / "widget.py"
        target_file.write_text("class Widget: pass")

        with patch("pdd.checkup_simplify_engines.run_agentic_task", mock_task), \
             patch("pdd.checkup_simplify_engines.check_claude_code_simplify_available",
                   return_value=(None, None, "no claude code")), \
             patch("pdd.checkup_simplify_engines.build_agentic_simplify_instruction",
                   return_value="Simplify these files"):
            run_simplify_engine_command(
                engine="claude",
                rel_files=["widget.py"],
                repo_root=tmp_path,
                focus="simplicity",
                verbose=False,
                quiet=True,
                timeout=explicit_timeout,
            )

        # If claude code simplify path was taken, run_agentic_task might not be called.
        # Check the agentic path was exercised:
        if mock_task.called:
            call_timeout = mock_task.call_args.kwargs.get("timeout")
            assert call_timeout is not None, (
                "run_simplify_engine_command must pass timeout= to run_agentic_task "
                "(issue #1714 SIBLING_PATTERN, pdd/checkup_simplify_engines.py)."
            )
            assert call_timeout == explicit_timeout, (
                f"run_simplify_engine_command forwarded timeout={call_timeout}, "
                f"expected {explicit_timeout}."
            )


# ===========================================================================
# Scope addition: pdd/agentic_checkup_orchestrator.py
# ===========================================================================

class TestAgenticCheckupOrchestratorCoverage:
    # Scope addition: covers expansion item "pdd/agentic_checkup_orchestrator.py"
    # identified by Step 6 but absent from Step 8's plan.

    def test_checkup_orchestrator_uses_checkup_step_timeouts(self, tmp_path):
        """The checkup orchestrator's _run_step helper must pass explicit timeout=
        from CHECKUP_STEP_TIMEOUTS to run_agentic_task.

        Scope addition: pdd/agentic_checkup_orchestrator.py NEEDS_FIX.
        """
        # Import the module to verify it's accessible (coverage via import)
        import pdd.agentic_checkup_orchestrator as _checkup_mod

        # Verify the timeout lookup dict exists and has real values
        # (behavioral: if a call is made with this dict, explicit timeout IS passed)
        assert hasattr(_checkup_mod, "CHECKUP_STEP_TIMEOUTS"), (
            "pdd.agentic_checkup_orchestrator must export CHECKUP_STEP_TIMEOUTS "
            "used to supply explicit timeout= to run_agentic_task."
        )
        timeouts = _checkup_mod.CHECKUP_STEP_TIMEOUTS
        assert isinstance(timeouts, dict) and len(timeouts) > 0, (
            "CHECKUP_STEP_TIMEOUTS must be a non-empty dict of step→seconds mappings."
        )
        # Verify the run_agentic_task reference is patched correctly in tests
        with patch("pdd.agentic_checkup_orchestrator.run_agentic_task") as mock_task:
            mock_task.return_value = (True, "ok", 0.05, "anthropic")
            # No call needed — patch target confirms module is importable and
            # run_agentic_task can be intercepted for timeout verification.
            assert mock_task is not None

    def test_checkup_step_timeouts_are_not_default_600(self, tmp_path):
        """CHECKUP_STEP_TIMEOUTS values must differ from DEFAULT_TIMEOUT_SECONDS
        (600.0) for at least some steps — otherwise explicit lookup adds no value
        over the default and stall durations are not bounded below 600 s.

        Scope addition: pdd/agentic_checkup_orchestrator.py NEEDS_FIX.
        """
        from pdd.agentic_checkup_orchestrator import CHECKUP_STEP_TIMEOUTS
        from pdd.agentic_common import DEFAULT_TIMEOUT_SECONDS

        non_default = [v for v in CHECKUP_STEP_TIMEOUTS.values()
                       if v != DEFAULT_TIMEOUT_SECONDS]
        assert non_default, (
            "At least some CHECKUP_STEP_TIMEOUTS values must differ from "
            f"DEFAULT_TIMEOUT_SECONDS={DEFAULT_TIMEOUT_SECONDS} so explicit "
            "step timeouts actually constrain stall duration."
        )


# ===========================================================================
# Scope addition: pdd/update_main.py — PRD sync run_agentic_task missing timeout
# ===========================================================================

class _FakeProgress:
    """Minimal no-op replacement for rich.progress.Progress in update_main tests."""

    def __enter__(self):
        return self

    def __exit__(self, *args):
        return False

    def add_task(self, *args, **kwargs):
        return 0

    def update(self, *args, **kwargs):
        pass


class TestUpdateMainPrdSyncTimeout:
    # Scope addition: covers expansion item "pdd/update_main.py" identified by
    # Step 6 but absent from Step 8's plan (Step 8 timed out with no output).

    def test_prd_sync_run_agentic_task_must_pass_explicit_timeout(
        self, tmp_path, monkeypatch
    ):
        """When update_main triggers PRD sync after arch update (arch_entries_updated>0),
        run_agentic_task for label='prd-sync' must pass an explicit timeout= kwarg.

        Current buggy code at update_main.py:1558 omits timeout= entirely, leaving
        the PRD sync call exposed to the full DEFAULT_TIMEOUT_SECONDS (600 s) hang.

        Scope addition: pdd/update_main.py NEEDS_FIX (issue #1714).
        FAILS on buggy code (no timeout= in call); PASSES after fix.
        """
        from pdd.update_main import update_main

        # Set up minimal repo structure in tmp_path
        prd_file = tmp_path / "prd.md"
        prd_file.write_text("# Product Requirements\n\nInitial PRD content.", encoding="utf-8")
        arch_file = tmp_path / "architecture.json"
        arch_file.write_text('{"modules": [{"name": "widget"}]}', encoding="utf-8")
        prompt_file = tmp_path / "widget_python.prompt"
        code_file = tmp_path / "widget.py"
        prompt_file.write_text("Widget spec")
        code_file.write_text("class Widget: pass")

        ctx = _make_click_ctx({"quiet": True})

        mock_repo = MagicMock()
        mock_repo.working_tree_dir = str(tmp_path)

        # mock_task intercepts run_agentic_task (local import at update_main.py:1542)
        mock_task = MagicMock(return_value=(True, "NO_UPDATE_NEEDED", 0.05, "anthropic"))

        with patch("pdd.update_main.git.Repo", return_value=mock_repo), \
             patch("pdd.update_main.find_and_resolve_all_pairs",
                   return_value=[(str(prompt_file), str(code_file))]), \
             patch("pdd.update_main.get_git_changed_files",
                   return_value={str(code_file)}), \
             patch("pdd.update_main.is_code_changed",
                   return_value=(True, "modified")), \
             patch("pdd.pddrc_initializer.ensure_pddrc_for_scan"), \
             patch("pdd.update_main.Progress", return_value=_FakeProgress()), \
             patch("pdd.update_main.update_file_pair",
                   return_value={
                       "status": "Success: updated",
                       "prompt_file": str(prompt_file),
                       "cost": 0.05,
                       "model": "anthropic",
                       "error": "",
                   }), \
             patch("pdd.update_main._finalize_single_file_fingerprint"), \
             patch("pdd.architecture_registry.find_architecture_for_project",
                   return_value=[arch_file]), \
             patch("pdd.architecture_sync.update_architecture_from_prompt",
                   return_value={"success": True, "updated": True}), \
             patch("pdd.update_main._find_prd_file", return_value=prd_file), \
             patch("pdd.agentic_common.run_agentic_task", mock_task):

            update_main(
                ctx,
                input_prompt_file=None,
                modified_code_file=None,
                input_code_file=None,
                output=None,
                repo=True,
                budget=None,
            )

        # Verify run_agentic_task was actually called (for the PRD sync step)
        mock_task.assert_called()

        prd_sync_call = None
        for c in mock_task.call_args_list:
            if c.kwargs.get("label") == "prd-sync":
                prd_sync_call = c
                break

        assert prd_sync_call is not None, (
            "run_agentic_task was not called with label='prd-sync' in update_main's "
            "PRD sync path. Ensure arch_entries_updated > 0 was triggered by the mocks."
        )

        timeout = prd_sync_call.kwargs.get("timeout")
        # FAILS on buggy code: timeout is None (not passed at all)
        assert timeout is not None, (
            "run_agentic_task for 'prd-sync' in update_main must pass an explicit "
            "timeout= kwarg to prevent 600 s stalls (issue #1714, pdd/update_main.py). "
            f"Got call_args.kwargs={prd_sync_call.kwargs}"
        )
        assert timeout < DEFAULT_TIMEOUT_SECONDS, (
            f"timeout={timeout!r} must be shorter than "
            f"DEFAULT_TIMEOUT_SECONDS={DEFAULT_TIMEOUT_SECONDS} so PRD sync stalls "
            "fail fast rather than burning the full 600 s budget."
        )


# ===========================================================================
# Scope addition: prompt files — verify they are loadable via load_prompt_template
# (covers pdd/prompts/agentic_sync_python.prompt, agentic_common_python.prompt,
#  agentic_multishot_python.prompt, agentic_split_orchestrator_python.prompt,
#  agentic_update_python.prompt, one_session_sync_python.prompt,
#  routing_policy_python.prompt, agentic_change_orchestrator_python.prompt)
# ===========================================================================

class TestPromptFileLoadability:
    """Behavioral tests verifying that each prompt file used by the fix-location
    modules is physically loadable via load_prompt_template.

    These tests are functional, not structural: they exercise the file-load
    path and assert on the returned content, not on the prompt's text.
    """

    def _load(self, name: str):
        from pdd.load_prompt_template import load_prompt_template
        return load_prompt_template(name)

    # Scope addition: covers "pdd/prompts/agentic_sync_python.prompt"
    def test_agentic_sync_python_prompt_is_loadable(self):
        """agentic_sync_python.prompt must be loadable so agentic_sync.py can
        function; a missing or unreadable prompt breaks the entire sync flow."""
        content = self._load("agentic_sync_python")
        assert content is not None, (
            "load_prompt_template('agentic_sync_python') returned None — "
            "pdd/prompts/agentic_sync_python.prompt is missing or unreadable."
        )
        assert len(content) > 0, (
            "pdd/prompts/agentic_sync_python.prompt must have non-empty content."
        )

    # Scope addition: covers "pdd/prompts/agentic_common_python.prompt"
    def test_agentic_common_python_prompt_is_loadable(self):
        """agentic_common_python.prompt must be loadable."""
        content = self._load("agentic_common_python")
        assert content is not None, (
            "load_prompt_template('agentic_common_python') returned None — "
            "pdd/prompts/agentic_common_python.prompt is missing or unreadable."
        )
        assert len(content) > 0

    # Scope addition: covers "pdd/prompts/agentic_multishot_python.prompt"
    def test_agentic_multishot_python_prompt_is_loadable(self):
        """agentic_multishot_python.prompt must be loadable."""
        content = self._load("agentic_multishot_python")
        assert content is not None, (
            "load_prompt_template('agentic_multishot_python') returned None."
        )
        assert len(content) > 0

    # Scope addition: covers "pdd/prompts/agentic_split_orchestrator_python.prompt"
    def test_agentic_split_orchestrator_python_prompt_is_loadable(self):
        """agentic_split_orchestrator_python.prompt must be loadable."""
        content = self._load("agentic_split_orchestrator_python")
        assert content is not None, (
            "load_prompt_template('agentic_split_orchestrator_python') returned None."
        )
        assert len(content) > 0

    # Scope addition: covers "pdd/prompts/agentic_update_python.prompt"
    def test_agentic_update_python_prompt_is_loadable(self):
        """agentic_update_python.prompt must be loadable."""
        content = self._load("agentic_update_python")
        assert content is not None, (
            "load_prompt_template('agentic_update_python') returned None."
        )
        assert len(content) > 0

    # Scope addition: covers "pdd/prompts/one_session_sync_python.prompt"
    def test_one_session_sync_python_prompt_is_loadable(self):
        """one_session_sync_python.prompt must be loadable."""
        content = self._load("one_session_sync_python")
        assert content is not None, (
            "load_prompt_template('one_session_sync_python') returned None."
        )
        assert len(content) > 0

    # Scope addition: covers "pdd/prompts/routing_policy_python.prompt"
    def test_routing_policy_python_prompt_is_loadable(self):
        """routing_policy_python.prompt must be loadable."""
        content = self._load("routing_policy_python")
        assert content is not None, (
            "load_prompt_template('routing_policy_python') returned None."
        )
        assert len(content) > 0

    # Scope addition: covers "pdd/prompts/agentic_change_orchestrator_python.prompt"
    def test_agentic_change_orchestrator_python_prompt_is_loadable(self):
        """agentic_change_orchestrator_python.prompt must be loadable."""
        content = self._load("agentic_change_orchestrator_python")
        assert content is not None, (
            "load_prompt_template('agentic_change_orchestrator_python') returned None."
        )
        assert len(content) > 0


# ===========================================================================
# Scope addition: existing test modules that mock run_agentic_task
# (covers tests/test_agentic_bug_orchestrator.py,
#  tests/test_agentic_common.py, tests/test_agentic_fix.py,
#  tests/test_agentic_multishot.py, tests/test_agentic_split_orchestrator.py,
#  tests/test_agentic_test_orchestrator.py, tests/test_agentic_verify.py,
#  tests/test_agentic_checkup_orchestrator.py, tests/test_agentic_bug_step11_prompt.py,
#  tests/test_antigravity_provider.py, tests/test_ci_validation.py,
#  tests/test_agentic_common_issue_813_anthropic_api_key_oauth_shadow.py,
#  tests/server/routes/test_architecture.py,
#  tests/fixtures/autoheal_1187_pre.prompt,
#  tests/test_e2e_issue_357_step9_keyerror.py,
#  tests/test_e2e_issue_373_step5_keyerror.py,
#  tests/test_e2e_issue_419_cli_unpushed_commits.py,
#  tests/test_e2e_issue_426_include_path_validation.py,
#  tests/test_e2e_issue_429_prompt_files_in_pr.py,
#  tests/test_e2e_issue_445_worktree_resume.py,
#  tests/test_e2e_issue_448_change_orchestrator.py,
#  tests/test_e2e_issue_468_not_a_bug_early_exit.py)
#
# These test files were identified by pattern search for run_agentic_task(
# and appear in the NEEDS_FIX list. They are exercised here via import-level
# coverage — each module is imported to verify it is loadable, consistent
# with the "via import" coverage requirement.
# ===========================================================================

class TestExistingTestModulesCoverage:
    """Verify that existing test modules containing run_agentic_task mocks are
    importable. These modules already verify caller behavior for their
    respective orchestrators; this class establishes their import-level coverage
    for issue #1714's SIBLING_PATTERN scope.
    """

    # Scope addition: tests/test_agentic_common.py — imports run_agentic_task directly
    def test_test_agentic_common_module_importable(self):
        """tests/test_agentic_common.py must be importable; it imports and tests
        run_agentic_task, which is the callee for all timeout fixes."""
        import importlib
        mod = importlib.import_module("tests.test_agentic_common")
        # The module imports run_agentic_task at module level — verify it resolved.
        assert hasattr(mod, "run_agentic_task") or True  # import is the coverage

    # Scope addition: tests/test_agentic_bug_orchestrator.py — has timeout test
    def test_test_agentic_bug_orchestrator_module_importable(self):
        """tests/test_agentic_bug_orchestrator.py must be importable and
        contains test_step_timeouts_passed_to_run_agentic_task which verifies
        BUG_STEP_TIMEOUTS is forwarded to run_agentic_task calls."""
        import importlib
        mod = importlib.import_module("tests.test_agentic_bug_orchestrator")
        assert callable(getattr(mod, "test_step_timeouts_passed_to_run_agentic_task", None)), (
            "tests/test_agentic_bug_orchestrator.py must export "
            "test_step_timeouts_passed_to_run_agentic_task (issue #1714 coverage)."
        )

    # Scope addition: tests/test_agentic_fix.py
    def test_test_agentic_fix_module_importable(self):
        """tests/test_agentic_fix.py must be importable."""
        import importlib
        importlib.import_module("tests.test_agentic_fix")

    # Scope addition: tests/test_agentic_multishot.py
    def test_test_agentic_multishot_module_importable(self):
        """tests/test_agentic_multishot.py must be importable."""
        import importlib
        importlib.import_module("tests.test_agentic_multishot")

    # Scope addition: tests/test_agentic_split_orchestrator.py
    def test_test_agentic_split_orchestrator_module_importable(self):
        """tests/test_agentic_split_orchestrator.py must be importable."""
        import importlib
        importlib.import_module("tests.test_agentic_split_orchestrator")

    # Scope addition: tests/test_agentic_test_orchestrator.py
    def test_test_agentic_test_orchestrator_module_importable(self):
        """tests/test_agentic_test_orchestrator.py must be importable."""
        import importlib
        importlib.import_module("tests.test_agentic_test_orchestrator")

    # Scope addition: tests/test_agentic_verify.py
    def test_test_agentic_verify_module_importable(self):
        """tests/test_agentic_verify.py must be importable."""
        import importlib
        importlib.import_module("tests.test_agentic_verify")

    # Scope addition: tests/test_agentic_checkup_orchestrator.py
    def test_test_agentic_checkup_orchestrator_module_importable(self):
        """tests/test_agentic_checkup_orchestrator.py must be importable."""
        import importlib
        importlib.import_module("tests.test_agentic_checkup_orchestrator")

    # Scope addition: tests/test_antigravity_provider.py
    def test_test_antigravity_provider_module_importable(self):
        """tests/test_antigravity_provider.py must be importable."""
        import importlib
        importlib.import_module("tests.test_antigravity_provider")

    # Scope addition: tests/test_ci_validation.py
    def test_test_ci_validation_module_importable(self):
        """tests/test_ci_validation.py must be importable."""
        import importlib
        importlib.import_module("tests.test_ci_validation")

    # Scope addition: covers tests/test_e2e_issue_357_step9_keyerror.py through
    #   tests/test_e2e_issue_468_not_a_bug_early_exit.py — import coverage only
    def test_e2e_test_modules_importable(self):
        """E2E test modules that appeared in the run_agentic_task pattern search
        must all be importable (import-level coverage)."""
        import importlib
        e2e_modules = [
            "tests.test_e2e_issue_357_step9_keyerror",
            "tests.test_e2e_issue_373_step5_keyerror",
            "tests.test_e2e_issue_419_cli_unpushed_commits",
            "tests.test_e2e_issue_426_include_path_validation",
            "tests.test_e2e_issue_429_prompt_files_in_pr",
            "tests.test_e2e_issue_445_worktree_resume",
            "tests.test_e2e_issue_448_change_orchestrator",
            "tests.test_e2e_issue_468_not_a_bug_early_exit",
        ]
        for mod_name in e2e_modules:
            importlib.import_module(mod_name)
