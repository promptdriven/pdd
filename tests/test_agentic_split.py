"""Tests for pdd.agentic_split module (CLI wrapper).

Test Plan:
1. run_agentic_split — file not found
2. run_agentic_split — unsupported file extension
3. run_agentic_split — not inside git repo
4. run_agentic_split — no prompt file (warning only, continues)
5. run_agentic_split — no test file (warning only, continues)
6. run_agentic_split — successful delegation to orchestrator
7. run_agentic_split — orchestrator exception caught
8. run_agentic_split — quiet mode suppresses warnings
"""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_split import run_agentic_split

MODULE = "pdd.agentic_split"


def _step4_options_output(child_count: int) -> str:
    """Build parseable step-4 output with a best plan containing child_count children."""
    children = [
        {
            "name": f"child_{idx}",
            "code_file": f"child_{idx}.py",
            "prompt_file": "",
            "example_file": "",
            "test_file": "",
        }
        for idx in range(1, child_count + 1)
    ]
    return json.dumps([
        {
            "name": "best",
            "score": 10.0,
            "risk": "low",
            "rationale": "test",
            "plan": {
                "children": children,
                "parent_changes": {},
                "reference_updates": [],
                "test_ownership": {},
            },
        }
    ])


class TestFileNotFound:
    def test_nonexistent_file(self):
        ok, msg, cost, model, files = run_agentic_split(
            "/nonexistent/path/to/file.py", quiet=True,
        )
        assert ok is False
        assert "does not exist" in msg
        assert cost == 0.0

    def test_directory_not_file(self, tmp_path):
        ok, msg, cost, model, files = run_agentic_split(
            str(tmp_path), quiet=True,
        )
        assert ok is False
        assert "not a file" in msg


class TestUnsupportedExtension:
    def test_unknown_extension(self, tmp_path):
        f = tmp_path / "data.xyz"
        f.write_text("content")
        with patch(f"{MODULE}.get_language", return_value=""):
            ok, msg, cost, model, files = run_agentic_split(
                str(f), quiet=True,
            )
            assert ok is False
            assert "Unsupported" in msg


class TestNotGitRepo:
    def test_no_git_root(self, tmp_path):
        f = tmp_path / "mod.py"
        f.write_text("x = 1")
        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.get_git_root", return_value=None):
            ok, msg, cost, model, files = run_agentic_split(
                str(f), quiet=True,
            )
            assert ok is False
            assert "git" in msg.lower()


class TestPromptDiscovery:
    def test_finds_prompt_in_extensions_path(self, tmp_path):
        """Prompt at extensions/foo/prompts/.../X.prompt should be found (no warning)."""
        f = tmp_path / "mod.py"
        f.write_text("x = 1")
        # Create extensions/foo/prompts/src/mod_Python.prompt (capitalized)
        prompts_path = tmp_path / "extensions" / "foo" / "prompts" / "src"
        prompts_path.mkdir(parents=True)
        (prompts_path / "mod_Python.prompt").write_text("prompt content")

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.run_agentic_split_orchestrator",
                   return_value=(True, "ok", 0.5, "model", [])), \
             patch(f"{MODULE}.console") as mock_console:
            run_agentic_split(str(f), quiet=False)
            # Should NOT print a prompt warning
            prompt_warnings = [
                c for c in mock_console.print.call_args_list
                if "Warning" in str(c) and "prompt" in str(c).lower()
            ]
            assert len(prompt_warnings) == 0, f"Unexpected warnings: {prompt_warnings}"


class TestPromptFileWarning:
    def test_no_prompt_prints_warning(self, tmp_path, capsys):
        f = tmp_path / "mod.py"
        f.write_text("x = 1")
        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.run_agentic_split_orchestrator",
                   return_value=(True, "ok", 0.5, "model", [])), \
             patch(f"{MODULE}.console") as mock_console:
            run_agentic_split(str(f), quiet=False)
            # Should have printed a warning about missing prompt
            warning_calls = [
                c for c in mock_console.print.call_args_list
                if "Warning" in str(c) and "prompt" in str(c).lower()
            ]
            assert len(warning_calls) >= 1


class TestTestFileWarning:
    def test_no_test_prints_warning(self, tmp_path, capsys):
        f = tmp_path / "mod.py"
        f.write_text("x = 1")
        # Create prompt so only test warning fires
        prompts = tmp_path / "prompts"
        prompts.mkdir()
        (prompts / "mod_Python.prompt").write_text("prompt")
        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.run_agentic_split_orchestrator",
                   return_value=(True, "ok", 0.5, "model", [])), \
             patch(f"{MODULE}.console") as mock_console:
            run_agentic_split(str(f), quiet=False)
            warning_calls = [
                c for c in mock_console.print.call_args_list
                if "Warning" in str(c) and "test" in str(c).lower()
            ]
            assert len(warning_calls) >= 1


class TestSuccessfulDelegation:
    def test_delegates_to_orchestrator(self, tmp_path):
        f = tmp_path / "mod.py"
        f.write_text("x = 1")
        expected = (True, "Split complete", 1.5, "model-x", ["a.py"])
        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.run_agentic_split_orchestrator",
                   return_value=expected) as mock_orch:
            ok, msg, cost, model, files = run_agentic_split(
                str(f), quiet=True, diagnose_only=True,
            )
            assert ok is True
            assert msg == "Split complete"
            assert cost == 1.5
            # Verify orchestrator was called with correct args
            call_kwargs = mock_orch.call_args[1]
            assert call_kwargs["diagnose_only"] is True
            assert call_kwargs["cwd"] == tmp_path


class TestOrchestratorException:
    def test_exception_caught(self, tmp_path):
        f = tmp_path / "mod.py"
        f.write_text("x = 1")
        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.run_agentic_split_orchestrator",
                   side_effect=RuntimeError("boom")):
            ok, msg, cost, model, files = run_agentic_split(
                str(f), quiet=True,
            )
            assert ok is False
            assert "boom" in msg
            assert cost == 0.0


class TestQuietMode:
    def test_quiet_suppresses_warnings(self, tmp_path):
        f = tmp_path / "mod.py"
        f.write_text("x = 1")
        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.run_agentic_split_orchestrator",
                   return_value=(True, "ok", 0.5, "model", [])), \
             patch(f"{MODULE}.console") as mock_console:
            run_agentic_split(str(f), quiet=True)
            mock_console.print.assert_not_called()


# -----------------------------------------------------------------------------
# Path sanitization (Errno 63 defense — agentic_bug_orchestrator run, May 5)
# -----------------------------------------------------------------------------


class TestSanitizePathString:
    """Direct tests for the LLM-output path sanitizer."""

    def test_strips_em_dash_prose(self):
        """The exact string that crashed the May 5 run."""
        from pdd.agentic_split_orchestrator import _sanitize_path_string
        polluted = (
            "pdd/agentic_bug_orchestrator.py — keep BUG_STEP_TIMEOUTS, "
            "console, logger, run_agentic_bug_orchestrator (the slimmed step loop)."
        )
        assert _sanitize_path_string(polluted) == "pdd/agentic_bug_orchestrator.py"

    def test_strips_whitespace_prose(self):
        from pdd.agentic_split_orchestrator import _sanitize_path_string
        polluted = "pdd/foo.py    extra notes here"
        assert _sanitize_path_string(polluted) == "pdd/foo.py"

    def test_strips_newline_addendum(self):
        from pdd.agentic_split_orchestrator import _sanitize_path_string
        polluted = "pdd/foo.py\nDescription continues here."
        assert _sanitize_path_string(polluted) == "pdd/foo.py"

    def test_strips_backtick_marker(self):
        from pdd.agentic_split_orchestrator import _sanitize_path_string
        polluted = "pdd/foo.py `inline annotation`"
        assert _sanitize_path_string(polluted) == "pdd/foo.py"

    def test_clean_path_passes_through(self):
        from pdd.agentic_split_orchestrator import _sanitize_path_string
        clean = "extensions/github_pdd_app/src/services/foo/bar.py"
        assert _sanitize_path_string(clean) == clean

    def test_non_string_unchanged(self):
        from pdd.agentic_split_orchestrator import _sanitize_path_string
        assert _sanitize_path_string(None) is None
        assert _sanitize_path_string(42) == 42
        assert _sanitize_path_string({"x": 1}) == {"x": 1}


class TestSanitizeSplitPaths:
    """End-to-end test that polluted SplitOption paths get cleaned."""

    def test_parent_modified_source_sanitized(self):
        from pdd.agentic_split_orchestrator import (
            SplitOption, SplitPlan, _sanitize_split_paths,
        )
        opt = SplitOption(plan=SplitPlan(
            parent_changes={
                "modified_source": "pdd/foo.py — keep CONST, helper",
            },
            children=[],
        ))
        _sanitize_split_paths(opt)
        assert opt.plan.parent_changes["modified_source"] == "pdd/foo.py"

    def test_child_paths_sanitized(self):
        from pdd.agentic_split_orchestrator import (
            SplitOption, SplitPlan, _sanitize_split_paths,
        )
        opt = SplitOption(plan=SplitPlan(
            parent_changes={},
            children=[
                {
                    "code_file": "pdd/child_a.py - host helpers",
                    "prompt_file": "pdd/prompts/child_a_python.prompt",
                },
                {
                    "code_file": "pdd/child_b.py\nWith trailing notes",
                },
            ],
        ))
        _sanitize_split_paths(opt)
        assert opt.plan.children[0]["code_file"] == "pdd/child_a.py"
        assert opt.plan.children[0]["prompt_file"] == "pdd/prompts/child_a_python.prompt"
        assert opt.plan.children[1]["code_file"] == "pdd/child_b.py"

    def test_no_op_when_already_clean(self):
        from pdd.agentic_split_orchestrator import (
            SplitOption, SplitPlan, _sanitize_split_paths,
        )
        opt = SplitOption(plan=SplitPlan(
            parent_changes={"modified_source": "pdd/foo.py"},
            children=[{"code_file": "pdd/bar.py"}],
        ))
        _sanitize_split_paths(opt)
        assert opt.plan.parent_changes["modified_source"] == "pdd/foo.py"
        assert opt.plan.children[0]["code_file"] == "pdd/bar.py"


class TestValidateExtractionLongPathSurvives:
    """validate_extraction must NOT crash on a polluted parent_source."""

    def test_polluted_modified_source_does_not_crash(self, tmp_path):
        from pdd.split_validation import validate_extraction
        from pdd.agentic_split_orchestrator import SplitPlan
        # Build a plan with a parent_source longer than macOS's 255-char
        # filename limit AND containing prose that would survive a naive
        # sanitizer. validate_extraction must trim or skip, never crash.
        plan = SplitPlan(
            parent_changes={
                "modified_source": (
                    "pdd/foo.py — " + "x" * 600
                ),
            },
            children=[],
        )
        # Should not raise OSError (Errno 63).
        result = validate_extraction(plan, tmp_path)
        # validate_extraction returns a ValidationResult; we don't care
        # what its passed/failures contents are — only that it returned.
        assert result is not None


# -----------------------------------------------------------------------------
# Budget guard — --max-cost CLI flag (#1384)
# -----------------------------------------------------------------------------


class TestMaxCostFlagWiring:
    """The CLI flag must thread all the way down to the orchestrator."""

    def test_run_agentic_split_accepts_max_cost(self):
        """run_agentic_split exposes max_cost kwarg."""
        from pdd.agentic_split import run_agentic_split
        import inspect
        sig = inspect.signature(run_agentic_split)
        assert "max_cost" in sig.parameters
        assert sig.parameters["max_cost"].default is None

    def test_orchestrator_accepts_max_cost(self):
        """run_agentic_split_orchestrator exposes max_cost kwarg."""
        from pdd.agentic_split_orchestrator import run_agentic_split_orchestrator
        import inspect
        sig = inspect.signature(run_agentic_split_orchestrator)
        assert "max_cost" in sig.parameters
        assert sig.parameters["max_cost"].default is None

    def test_run_agentic_split_passes_max_cost_through(self, tmp_path):
        """A max_cost value passed to run_agentic_split reaches the orchestrator."""
        f = tmp_path / "mod.py"
        f.write_text("x = 1")
        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.run_agentic_split_orchestrator",
                   return_value=(True, "ok", 0.5, "model", [])) as mock_orch:
            run_agentic_split(str(f), quiet=True, max_cost=42.5)
            kwargs = mock_orch.call_args.kwargs
            assert kwargs["max_cost"] == 42.5


class TestBudgetGuardAbortsAtStepBoundary:
    """When total_cost >= max_cost the orchestrator must save state and exit."""

    def test_zero_max_cost_aborts_before_any_step(self, tmp_path, monkeypatch):
        """Resumed total_cost above max_cost aborts at the next step boundary.

        Verifies the guard's location (top of step loop) and that the
        return signature is the standard 5-tuple with success=False.
        """
        from pdd.agentic_split_orchestrator import run_agentic_split_orchestrator
        target = tmp_path / "small.py"
        target.write_text("def f():\n    return 1\n")
        (tmp_path / ".git").mkdir()

        # Stub state I/O to keep the test hermetic and pre-load a
        # total_cost above the caller's cap.
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.load_workflow_state",
            lambda *a, **kw: ({"total_cost": 5.0,
                               "last_completed_step": "1_survey",
                               "step_outputs": {},
                               "model_used": "anthropic",
                               "changed_files": [],
                               "children_extracted": [],
                               "phase_plans": [],
                               "intent": "REDUCE_MONOLITH",
                               "iteration_count": 0}, None),
        )
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.save_workflow_state",
            lambda *a, **kw: None,
        )
        # Stub language detection so the test does not require PDD_PATH
        # in the environment (the real _detect_language consults the PDD
        # path resolver; without PDD_PATH the test fails at collection
        # time with ValueError).
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator._detect_language",
            lambda _path: "python",
        )

        ok, msg, cost, model, changed = run_agentic_split_orchestrator(
            target_file=str(target),
            cwd=tmp_path,
            quiet=True,
            max_cost=1.0,  # below the loaded total_cost of 5.0
            use_github_state=False,
        )
        assert ok is False
        assert "max-cost" in msg.lower()
        # Stop reason should report both the cap and what was spent.
        assert "1.00" in msg
        assert "5.00" in msg
        assert cost == 5.0  # exactly the resumed total


# ---------------------------------------------------------------------------
# Issue #1384: resume-from-max-cost regression coverage
# ---------------------------------------------------------------------------


class TestStranglerPassesCompleted:
    """The strangler wrapper persists pass-completion count on max-cost abort."""

    def test_resume_loop_starts_at_passes_completed(self):
        """_run_strangler_split loop runs `range(start_idx, total_children)`, not 0."""
        from pdd.agentic_split import _run_strangler_split
        import inspect
        src = inspect.getsource(_run_strangler_split)
        # The pass loop must start at start_idx (resume index), not 0.
        # Without this, a 3-child plan that aborted at pass 2 would re-run
        # pass 1 (already paid) before retrying pass 2.
        assert "range(start_idx, total_children)" in src, (
            "Strangler loop must use range(start_idx, total_children) for resume"
        )
        # start_idx must be derived from saved state's strangler_passes_completed.
        assert 'strangler_passes_completed' in src, (
            "Strangler resume must read strangler_passes_completed from saved state"
        )

    def test_resume_persists_passes_completed_on_abort(self):
        """On max-cost abort, the wrapper writes strangler_passes_completed = idx."""
        from pdd.agentic_split import _run_strangler_split
        import inspect
        src = inspect.getsource(_run_strangler_split)
        # The abort branch must save the aborted pass index so resume
        # picks up at the right place. `idx` is the aborted pass; passes
        # 0..idx-1 completed cleanly.
        assert 'cur_state["strangler_passes_completed"] = idx' in src, (
            "Strangler max-cost abort must persist aborted pass index"
        )

    def test_strangler_cumulative_cost_persisted(self):
        """On abort, wrapper-level cumulative cost is written separately from per-pass cost."""
        from pdd.agentic_split import _run_strangler_split
        import inspect
        src = inspect.getsource(_run_strangler_split)
        # Each orchestrator pass has its own per-pass total_cost. The
        # wrapper's cumulative is tracked in strangler_total_cost so
        # resume can read true cumulative spend, not just the per-pass
        # cost from the orchestrator's own state.
        assert 'cur_state["strangler_total_cost"] = total_cost' in src, (
            "Strangler max-cost abort must persist wrapper-level cumulative cost"
        )
        # Resume must read it back.
        assert 'state.get("strangler_total_cost"' in src, (
            "Strangler resume must read strangler_total_cost from saved state"
        )

    def test_max_cost_abort_persists_original_total_children(self, tmp_path, monkeypatch):
        """Behavioral: abort state records the original strangler pass count."""
        from pdd.agentic_split import _run_strangler_split

        target = tmp_path / "small.py"
        target.write_text("def f():\n    return 1\n")
        (tmp_path / ".git").mkdir()

        propose_state = {"step_outputs": {"4": _step4_options_output(3)}}
        aborted_pass_state = {
            "max_cost_reached": True,
            "step_outputs": {"4": _step4_options_output(1)},
            "total_cost": 0.8,
        }
        loads = iter([None, propose_state, aborted_pass_state])
        saves = []

        def fake_load(*args, **kwargs):
            return next(loads), None

        def fake_save(cwd, split_id, workflow, state, state_dir, *args, **kwargs):
            saves.append(dict(state))
            return None

        def fake_orchestrator(*args, **kwargs):
            if kwargs.get("propose_only"):
                return False, "Propose only complete", 0.1, "mock", []
            return (
                False,
                "Aborted at step 6_extract: --max-cost $10.00 reached (spent $0.80)",
                0.8,
                "mock",
                ["child_1.py"],
            )

        monkeypatch.setattr(
            "pdd.agentic_common.load_workflow_state",
            fake_load,
        )
        monkeypatch.setattr(
            "pdd.agentic_common.save_workflow_state",
            fake_save,
        )
        monkeypatch.setattr(
            "pdd.agentic_common.clear_workflow_state",
            lambda *args, **kwargs: None,
        )
        monkeypatch.setattr(
            "pdd.agentic_split.run_agentic_split_orchestrator",
            fake_orchestrator,
        )

        ok, msg, cost, model, changed = _run_strangler_split(
            target_path=target,
            git_root=tmp_path,
            verbose=False,
            quiet=True,
            timeout_adder=0.0,
            use_github_state=False,
            force_split=False,
            no_verify=False,
            skip_regen_gate=False,
            experimental_language=False,
            intent=None,
            no_phase_extraction=False,
            max_cost=10.0,
        )

        assert ok is False
        assert "Strangler pass 1 failed" in msg
        assert cost == pytest.approx(0.9)
        assert changed == ["child_1.py"]
        assert saves, "Expected max-cost abort to persist strangler resume state"
        assert saves[-1]["strangler_total_children"] == 3
        assert saves[-1]["strangler_passes_completed"] == 0
        assert saves[-1]["strangler_total_cost"] == pytest.approx(0.9)

    def test_resume_uses_saved_total_children_not_aborted_pass_plan(self, tmp_path, monkeypatch):
        """Behavioral: resume count comes from wrapper state, not pass-local step 4."""
        from pdd.agentic_split import _run_strangler_split

        target = tmp_path / "small.py"
        target.write_text("def f():\n    return 1\n")
        (tmp_path / ".git").mkdir()

        saved_state = {
            "max_cost_reached": True,
            "step_outputs": {"4": _step4_options_output(1)},
            "strangler_total_children": 3,
            "strangler_passes_completed": 1,
            "strangler_total_cost": 1.5,
        }
        pass_calls = []

        monkeypatch.setattr(
            "pdd.agentic_common.load_workflow_state",
            lambda *args, **kwargs: (saved_state, None),
        )
        monkeypatch.setattr(
            "pdd.agentic_common.clear_workflow_state",
            lambda *args, **kwargs: None,
        )

        def fake_orchestrator(*args, **kwargs):
            pass_calls.append(kwargs)
            return True, "ok", 0.2, "mock", [f"pass_{len(pass_calls)}.py"]

        monkeypatch.setattr(
            "pdd.agentic_split.run_agentic_split_orchestrator",
            fake_orchestrator,
        )

        ok, msg, cost, model, changed = _run_strangler_split(
            target_path=target,
            git_root=tmp_path,
            verbose=False,
            quiet=True,
            timeout_adder=0.0,
            use_github_state=False,
            force_split=False,
            no_verify=False,
            skip_regen_gate=False,
            experimental_language=False,
            intent=None,
            no_phase_extraction=False,
            max_cost=10.0,
        )

        assert ok is True
        assert "3 orchestrator passes ran" in msg
        assert len(pass_calls) == 2
        assert all(call["propose_only"] is False for call in pass_calls)
        assert cost == pytest.approx(1.9)
        assert changed == ["pass_1.py", "pass_2.py"]


class TestChildResumeGuard:
    """Step 6 child loop skips re-extraction when files exist + max_cost_reached."""

    def test_resume_guard_requires_max_cost_flag(self, tmp_path):
        """Resume guard does NOT engage on a normal run (no max_cost_reached)."""
        # If files happen to exist on a normal run, do not skip extraction.
        # This is enforced by the gate: state.get('max_cost_reached') must be True.
        # We verify the gate logic by inspection — the line in code is:
        #     if (state.get("max_cost_reached") and expected_files and all(...)):
        # so without the flag, the body is skipped.
        from pdd.agentic_split_orchestrator import run_agentic_split_orchestrator
        import inspect
        src = inspect.getsource(run_agentic_split_orchestrator)
        assert 'state.get("max_cost_reached")' in src, (
            "Resume guard must be gated on state['max_cost_reached']"
        )
        # Also verify the guard checks ALL 4 path fields per child (canonical + Step 4 alias).
        assert '"new_example"' in src and '"new_test"' in src, (
            "Resume guard must check new_example and new_test (Step 4 first-class artifacts)"
        )

    def test_resume_guard_clears_flag_after_consuming(self):
        """After RESUMED-credit, max_cost_reached must clear so subsequent children don't blanket-skip."""
        from pdd.agentic_split_orchestrator import run_agentic_split_orchestrator
        import inspect
        src = inspect.getsource(run_agentic_split_orchestrator)
        # The guard block must clear the flag after the RESUMED append.
        assert 'state["max_cost_reached"] = False' in src, (
            "Resume guard must clear max_cost_reached after consuming it"
        )


class TestRefineMaxCostResume:
    """Focused refinement preserves the parsed phase plan across max-cost abort."""

    def test_pending_refine_plan_persisted_before_budget(self):
        """Refinement 6a saves _pending_refine_plan BEFORE budget check."""
        from pdd.agentic_split_orchestrator import run_agentic_split_orchestrator
        import inspect
        src = inspect.getsource(run_agentic_split_orchestrator)
        # The 6a refinement block must persist refine_phase_plan in state
        # before the budget check fires; without this, an abort after a
        # paid 6a call would lose the parsed plan.
        assert 'state["_pending_refine_plan"] = refine_phase_plan' in src, (
            "Refinement 6a must persist _pending_refine_plan before budget check"
        )

    def test_resume_skips_6a_when_plan_persisted(self):
        """Resume reads _pending_refine_plan and skips 6a LLM call."""
        from pdd.agentic_split_orchestrator import run_agentic_split_orchestrator
        import inspect
        src = inspect.getsource(run_agentic_split_orchestrator)
        # Resume must check for a saved plan and short-circuit the 6a LLM call.
        assert 'state.get("_pending_refine_plan")' in src, (
            "Refinement resume must read _pending_refine_plan from saved state"
        )

    def test_iteration_count_deferred_to_success(self):
        """iteration_count incremented at success block, not start of refinement."""
        from pdd.agentic_split_orchestrator import run_agentic_split_orchestrator
        import inspect
        src = inspect.getsource(run_agentic_split_orchestrator)
        # Find the refinement block start and the success block end.
        # The increment must NOT appear between them — it's at the end.
        refine_start = src.find("pending_refine = state.get")
        success_block = src.find("Refinement completed (no budget abort fired)")
        assert refine_start > 0 and success_block > 0
        assert success_block > refine_start
        # Between start and success block, no `iteration_count += 1`.
        between = src[refine_start:success_block]
        assert "iteration_count += 1" not in between, (
            "iteration_count must NOT be incremented before refinement success block — "
            "premature increment locks out resume (MAX_REFINEMENT_ITERATIONS=1)"
        )

    def test_extract_applied_flag_set_before_budget_check(self):
        """_pending_refine_extract_applied set BEFORE step-6 budget check."""
        from pdd.agentic_split_orchestrator import run_agentic_split_orchestrator
        import inspect
        src = inspect.getsource(run_agentic_split_orchestrator)
        # The flag must be set before the budget check fires; without
        # this, a budget abort after the paid step-6 extract would
        # cause resume to re-run the same LLM call.
        # Find the step-6 refine block: look for label "6_refine_iter_"
        # which uniquely identifies it.
        refine_step6_idx = src.find('label=f"6_refine_iter_')
        assert refine_step6_idx > 0
        # In the chunk after the step-6 LLM call, the flag must be set
        # before _check_budget("9_refine_check").
        chunk = src[refine_step6_idx:refine_step6_idx + 4000]
        flag_set = chunk.find('state["_pending_refine_extract_applied"] = True')
        budget_check = chunk.find('_check_budget("9_refine_check")')
        # The SECOND budget check (step-6, not 6a) is what we care about.
        # Find both budget checks; the step-6 one is the second.
        all_bcs = [m.start() for m in __import__("re").finditer(
            r'_check_budget\("9_refine_check"\)', chunk
        )]
        # There should be at least one budget check (step-6); flag set must precede it.
        assert flag_set > 0, "extract-applied flag must be set in step-6 refine block"
        assert all_bcs, "step-6 budget check must exist"
        # Take the budget check that follows the flag set.
        following = [bc for bc in all_bcs if bc > flag_set]
        assert following, (
            "extract-applied flag must be set BEFORE the step-6 budget check"
        )

    def test_resume_skips_step6_when_extract_applied(self):
        """Resume reads _pending_refine_extract_applied and skips step-6 LLM call."""
        from pdd.agentic_split_orchestrator import run_agentic_split_orchestrator
        import inspect
        src = inspect.getsource(run_agentic_split_orchestrator)
        assert 'state.get("_pending_refine_extract_applied")' in src, (
            "Refinement resume must check _pending_refine_extract_applied"
        )

    def test_step9_budget_abort_preserves_pending_refine(self, tmp_path, monkeypatch):
        """Behavioral: step-9 max-cost abort saves the parsed refine decision."""
        from pdd.agentic_split_orchestrator import run_agentic_split_orchestrator

        target = tmp_path / "small.py"
        target.write_text("def f():\n    return 1\n")
        (tmp_path / ".git").mkdir()

        saved_state = {
            "total_cost": 0.0,
            "last_completed_step": "8_repair",
            "step_outputs": {},
            "model_used": "mock",
            "changed_files": ["child.py"],
            "children_extracted": [],
            "phase_plans": [],
            "intent": "REDUCE_MONOLITH",
            "iteration_count": 0,
            "verify_failures": [],
            "quant_metrics": {},
            "worktree_path": str(tmp_path),
        }
        saves = []

        def fake_task(*args, **kwargs):
            assert kwargs.get("label") == "9_refine_check"
            return (
                True,
                json.dumps({
                    "should_refine": True,
                    "target_child_file": "child.py",
                    "reason": "still too monolithic",
                    "suggested_intent": "FOCUSED_EXTRACTION",
                }),
                1.0,
                "mock",
            )

        def fake_save(cwd, split_id, workflow, state, state_dir, *args, **kwargs):
            saves.append(dict(state))
            return None

        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.load_workflow_state",
            lambda *args, **kwargs: (saved_state, None),
        )
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.save_workflow_state",
            fake_save,
        )
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator._detect_language",
            lambda _path: "python",
        )
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.load_prompt_template",
            lambda _name: "refine prompt",
        )
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.run_agentic_task",
            fake_task,
        )

        ok, msg, cost, model, changed = run_agentic_split_orchestrator(
            target_file=str(target),
            cwd=tmp_path,
            quiet=True,
            max_cost=0.5,
            use_github_state=False,
        )

        assert ok is False
        assert "max-cost" in msg.lower()
        assert cost == pytest.approx(1.0)
        assert saves, "Expected budget abort to save workflow state"
        final = saves[-1]
        assert final["max_cost_reached"] is True
        assert final["last_completed_step"] == "9_refine_check"
        assert "9" in final["step_outputs"]
        assert final["_pending_refine"] == {
            "target_child_file": "child.py",
            "reason": "still too monolithic",
            "suggested_intent": "FOCUSED_EXTRACTION",
        }

    def test_modify_only_extract_on_already_tracked_file_sets_applied_flag(self, tmp_path, monkeypatch):
        """Behavioral: successful FILES_MODIFIED on already-tracked file → flag SET.

        Reviewer caught: my round-12 gate counted only newly-appended
        files, so a focused refinement that modifies a child already in
        changed_files (the common case — the main extraction creates
        the child first) would leave the flag unset and cause resume
        to re-pay for the same successful extract.

        Round-13 fix counts 'verified marker paths on disk', which
        includes already-tracked files. This test verifies that:
        ex_success=True + FILES_MODIFIED: child.py + child.py already
        in changed_files → _pending_refine_extract_applied=True.
        """
        from pdd.agentic_split_orchestrator import run_agentic_split_orchestrator
        target = tmp_path / "small.py"
        target.write_text("def f():\n    return 1\n")
        (tmp_path / ".git").mkdir()
        refine_target = tmp_path / "child.py"
        refine_target.write_text("# child\n")

        # Pre-loaded state with child.py already in changed_files
        # (simulating the main extraction having produced it earlier).
        saved_state = {
            "total_cost": 0.0,
            "last_completed_step": "9_refine_check",
            "step_outputs": {f"{i}": "ok" for i in range(10)},
            "model_used": "mock",
            "changed_files": ["child.py"],  # already tracked
            "children_extracted": [],
            "phase_plans": [],
            "intent": "REDUCE_MONOLITH",
            "iteration_count": 0,
            "_pending_refine": {
                "target_child_file": "child.py",
                "reason": "test",
                "suggested_intent": "",
            },
            "selected_option": {
                "name": "test_opt", "score": 1.0, "risk": "low", "rationale": "test",
                "plan": {"children": [{"name": "child", "code_file": "child.py", "prompt_file": ""}],
                         "parent_changes": {}, "reference_updates": [], "test_ownership": {}},
            },
            "verify_failures": [],
            "quant_metrics": {},
            "worktree_path": str(tmp_path),
        }

        saves = []
        def fake_save(cwd, sid, wf, state, sd, *a, **kw):
            saves.append(dict(state))
            return None

        # Mock: 6a returns valid plan, step-6 succeeds with FILES_MODIFIED
        # on child.py (already in changed_files).
        def fake_task(*args, **kwargs):
            label = kwargs.get("label", "")
            if "6a_refine_iter" in label:
                return (
                    True,
                    'PHASE_EXTRACTION_PLAN_BEGIN\n'
                    '{"should_extract": true, "target_symbol": "f",'
                    ' "target_file": "child.py", "phases": [],'
                    ' "parent_shell": "", "rationale": "x"}\n'
                    'PHASE_EXTRACTION_PLAN_END',
                    0.5, "mock",
                )
            if "6_refine_iter" in label:
                # SUCCESSFUL modify of already-tracked file
                return (
                    True,
                    "Refined child.py.\n\nFILES_MODIFIED: child.py\n",
                    0.5, "mock",
                )
            return (True, "ok", 0.0, "mock")

        from dataclasses import dataclass
        @dataclass
        class _FakeVR:
            passed: bool = True
            failures: list = None
            failure_type: str = "none"
            def __post_init__(self):
                if self.failures is None:
                    self.failures = []

        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.load_workflow_state",
            lambda *a, **kw: (saved_state, None),
        )
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.save_workflow_state", fake_save,
        )
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator._detect_language",
            lambda _p: "python",
        )
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.run_agentic_task", fake_task,
        )
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.validate_extraction",
            lambda plan, wt: _FakeVR(),
        )

        # Set max_cost so the budget aborts right after the step-6
        # refine extract — this captures the saved state with the flag
        # set (vs. the success-block clear that comes later).
        # 6a costs 0.5, step-6 costs 0.5 → total 1.0 > 0.6 cap.
        run_agentic_split_orchestrator(
            target_file=str(target),
            cwd=tmp_path,
            quiet=True,
            max_cost=0.6,
            use_github_state=False,
        )

        # The flag must be set despite no NEW file being appended
        # (child.py was already in changed_files from the start).
        # The budget abort persists state, so we should see at least
        # one save with _pending_refine_extract_applied=True.
        assert saves, "Expected save_workflow_state calls"
        saw_flag_true = any(
            s.get("_pending_refine_extract_applied") is True for s in saves
        )
        assert saw_flag_true, (
            "_pending_refine_extract_applied must be set True after a "
            "successful modify-only extract on an already-tracked file. "
            "Without this, resume would re-pay for the same successful extract. "
            f"Saved states: {[(s.get('_pending_refine_extract_applied'), s.get('changed_files')) for s in saves]}"
        )

    def test_no_op_6a_decision_persists_sentinel_plan(self, tmp_path, monkeypatch):
        """Behavioral: 6a returning should_extract=False persists a sentinel plan.

        Reviewer caught: when 6a parses successfully but says no
        extraction warranted, refine_phase_plan stayed None, so
        state['_pending_refine_plan']=None. A budget abort right after
        6a would cause resume to re-pay for the same 6a LLM call
        instead of accepting the no-op decision.

        Round-14 fix: persist a {should_extract: False} sentinel.
        Resume reads non-None plan, skips 6a, and the sentinel's
        should_extract=False makes step-6 skip too — refinement
        completes as 'no extraction warranted' on resume without
        another paid call.
        """
        from pdd.agentic_split_orchestrator import run_agentic_split_orchestrator
        target = tmp_path / "small.py"
        target.write_text("def f():\n    return 1\n")
        (tmp_path / ".git").mkdir()
        refine_target = tmp_path / "child.py"
        refine_target.write_text("# child\n")

        saved_state = {
            "total_cost": 0.0,
            "last_completed_step": "9_refine_check",
            "step_outputs": {f"{i}": "ok" for i in range(10)},
            "model_used": "mock",
            "changed_files": [],
            "children_extracted": [],
            "phase_plans": [],
            "intent": "REDUCE_MONOLITH",
            "iteration_count": 0,
            "_pending_refine": {
                "target_child_file": "child.py",
                "reason": "test",
                "suggested_intent": "",
            },
            "selected_option": {
                "name": "test_opt", "score": 1.0, "risk": "low", "rationale": "test",
                "plan": {"children": [{"name": "child", "code_file": "child.py", "prompt_file": ""}],
                         "parent_changes": {}, "reference_updates": [], "test_ownership": {}},
            },
            "verify_failures": [],
            "quant_metrics": {},
            "worktree_path": str(tmp_path),
        }

        saves = []
        def fake_save(cwd, sid, wf, state, sd, *a, **kw):
            saves.append(dict(state))
            return None

        # 6a returns valid PhaseExtractionPlan with should_extract=False.
        def fake_task(*args, **kwargs):
            label = kwargs.get("label", "")
            if "6a_refine_iter" in label:
                return (
                    True,
                    'PHASE_EXTRACTION_PLAN_BEGIN\n'
                    '{"should_extract": false, "reason": "already small enough"}\n'
                    'PHASE_EXTRACTION_PLAN_END',
                    0.5, "mock",
                )
            # Step 6 should NEVER be called when should_extract=False.
            if "6_refine_iter" in label:
                raise AssertionError(
                    "Step 6 LLM must not run when 6a says should_extract=False"
                )
            return (True, "ok", 0.0, "mock")

        from dataclasses import dataclass
        @dataclass
        class _FakeVR:
            passed: bool = True
            failures: list = None
            failure_type: str = "none"
            def __post_init__(self):
                if self.failures is None:
                    self.failures = []

        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.load_workflow_state",
            lambda *a, **kw: (saved_state, None),
        )
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.save_workflow_state", fake_save,
        )
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator._detect_language",
            lambda _p: "python",
        )
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.run_agentic_task", fake_task,
        )
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.validate_extraction",
            lambda plan, wt: _FakeVR(),
        )

        # max_cost=0.4 forces budget abort right after 6a (cost 0.5)
        run_agentic_split_orchestrator(
            target_file=str(target),
            cwd=tmp_path,
            quiet=True,
            max_cost=0.4,
            use_github_state=False,
        )

        # Assert: at least one saved state has _pending_refine_plan as
        # the sentinel {should_extract: False}, NOT None. Without
        # this, resume would re-run the paid 6a call.
        assert saves, "Expected save_workflow_state calls"
        sentinel_saved = any(
            isinstance(s.get("_pending_refine_plan"), dict)
            and s.get("_pending_refine_plan", {}).get("should_extract") is False
            for s in saves
        )
        assert sentinel_saved, (
            "Successful 6a no-extract decision must persist {should_extract: False} "
            "sentinel as _pending_refine_plan, so resume skips re-running 6a. "
            f"Saved _pending_refine_plan values: "
            f"{[s.get('_pending_refine_plan') for s in saves]}"
        )

    def test_failed_refine_extract_does_not_set_applied_flag(self, tmp_path, monkeypatch):
        """Behavioral: a failed step-6 refine LLM call must NOT set the applied flag.

        Without this, a budget abort after a no-op refine extract would
        cause resume to skip the LLM call entirely — silently losing
        the user's flagged refinement. The flag must be gated on
        (ex_success AND at least one verified file appended).
        """
        from pdd.agentic_split_orchestrator import run_agentic_split_orchestrator
        from pdd.agentic_split_orchestrator import (
            SplitOption, SplitPlan, OptionsConsidered,
        )

        target = tmp_path / "small.py"
        target.write_text("def f():\n    return 1\n")
        (tmp_path / ".git").mkdir()
        # Refinement target — must exist on disk for refine block to enter.
        refine_target = tmp_path / "child.py"
        refine_target.write_text("# child\n")

        # Saved state: all main-pipeline steps complete, refinement pending.
        # ordered_steps in the orchestrator goes through 0..9_refine_check.
        # last_completed_step = "9_refine_check" makes the for-loop skip
        # entirely (start_idx after all steps), and the refinement block
        # runs from the saved _pending_refine.
        saved_state = {
            "total_cost": 0.0,
            "last_completed_step": "9_refine_check",
            "step_outputs": {f"{i}": "ok" for i in range(10)},
            "model_used": "mock",
            "changed_files": [],
            "children_extracted": [],
            "phase_plans": [],
            "intent": "REDUCE_MONOLITH",
            "iteration_count": 0,
            "_pending_refine": {
                "target_child_file": "child.py",
                "reason": "test",
                "suggested_intent": "",
            },
            "selected_option": {
                "name": "test_opt",
                "score": 1.0,
                "risk": "low",
                "rationale": "test",
                "plan": {
                    "children": [{"name": "child", "code_file": "child.py", "prompt_file": ""}],
                    "parent_changes": {},
                    "reference_updates": [],
                    "test_ownership": {},
                },
            },
            "verify_failures": [],
            "quant_metrics": {},
            "worktree_path": str(tmp_path),
        }

        # Capture every saved state for inspection.
        saves = []
        def fake_save(cwd, sid, wf, state, sd, *a, **kw):
            saves.append(dict(state))
            return None

        # Mock run_agentic_task: 6a returns a parseable should_extract=True
        # plan; the step-6 refine extract returns ex_success=False with
        # NO FILES_CREATED markers (the failure case).
        def fake_task(*args, **kwargs):
            label = kwargs.get("label", "")
            if "6a_refine_iter" in label:
                # Return a parseable PhaseExtractionPlan with should_extract=True.
                return (
                    True,
                    'PHASE_EXTRACTION_PLAN_BEGIN\n'
                    '{"should_extract": true, "target_symbol": "f",'
                    ' "target_file": "child.py", "phases": [],'
                    ' "parent_shell": "", "rationale": "x"}\n'
                    'PHASE_EXTRACTION_PLAN_END',
                    0.5,  # cost — below max_cost
                    "mock",
                )
            if "6_refine_iter" in label:
                # FAILED refine extract: ex_success=False, no FILES_CREATED.
                return (False, "Refine LLM failed", 0.5, "mock")
            return (True, "ok", 0.0, "mock")

        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.load_workflow_state",
            lambda *a, **kw: (saved_state, None),
        )
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.save_workflow_state",
            fake_save,
        )
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator._detect_language",
            lambda _p: "python",
        )
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.run_agentic_task",
            fake_task,
        )
        # Stub validate_extraction so post-refine validate doesn't fail
        # the test on missing prompt files / git ops.
        from dataclasses import dataclass
        @dataclass
        class _FakeVR:
            passed: bool = True
            failures: list = None
            failure_type: str = "none"
            def __post_init__(self):
                if self.failures is None:
                    self.failures = []
        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.validate_extraction",
            lambda plan, wt: _FakeVR(),
        )

        # Run with a low max_cost so the budget aborts mid-refinement
        # AFTER the failed step-6 extract has spent its cost.
        run_agentic_split_orchestrator(
            target_file=str(target),
            cwd=tmp_path,
            quiet=True,
            max_cost=0.6,  # 0.5 from 6a + 0.5 from refine extract = 1.0 > 0.6
            use_github_state=False,
        )

        # Find the LAST saved state (after the budget abort or success).
        assert saves, "Expected at least one save_workflow_state call"
        final = saves[-1]
        # The flag must NOT be True since the refine extract FAILED.
        # If the bug returns, this saved state would have
        # _pending_refine_extract_applied=True (false success), which
        # would cause resume to skip the LLM call.
        assert not final.get("_pending_refine_extract_applied"), (
            "Failed refine extract must not set _pending_refine_extract_applied; "
            f"got True. Resume would silently skip the never-completed extract. "
            f"Final state: max_cost_reached={final.get('max_cost_reached')}, "
            f"changed_files={final.get('changed_files')}"
        )
