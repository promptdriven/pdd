"""Unit tests for feat/739-complete.

Covers:
- Step 8.5 pre-flight drift heal (_preflight_drift_heal)
- Step 10.5 contract verifier (_verify_doc_sync_contract)

Does NOT duplicate tests from tests/test_discover_associated_documents.py
(those cover the discovery primitive + Step-10-tag parsing).
"""
from __future__ import annotations

import json
import subprocess
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_change_orchestrator import (
    _preflight_drift_heal,
    _verify_doc_sync_contract,
)


# ---------------------------------------------------------------------------
# Step 10.5 — contract verifier
# ---------------------------------------------------------------------------

class TestVerifyDocSyncContract:
    """Every discovered doc must be either modified or explicitly conflicted."""

    def test_empty_discovered_is_trivial_pass(self) -> None:
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract([], "")
        assert mod == []
        assert conflict == []
        assert dropped == []

    def test_all_modified_no_drops(self) -> None:
        output = "ASSOCIATED_DOCS_MODIFIED: docs/a.md, docs/b.md"
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            ["docs/a.md", "docs/b.md"], output
        )
        assert set(mod) == {"docs/a.md", "docs/b.md"}
        assert conflict == []
        assert dropped == []

    def test_all_conflicted_no_drops(self) -> None:
        output = "ASSOCIATED_DOCS_CONFLICTS: docs/a.md, docs/b.md"
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            ["docs/a.md", "docs/b.md"], output
        )
        assert mod == []
        assert set(conflict) == {"docs/a.md", "docs/b.md"}
        assert dropped == []

    def test_mix_of_modified_and_conflict_no_drops(self) -> None:
        output = (
            "ASSOCIATED_DOCS_MODIFIED: docs/safe.md\n"
            "ASSOCIATED_DOCS_CONFLICTS: docs/risky.md"
        )
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            ["docs/safe.md", "docs/risky.md"], output
        )
        assert mod == ["docs/safe.md"]
        assert conflict == ["docs/risky.md"]
        assert dropped == []

    def test_silent_drop_caught(self) -> None:
        """Core silent-drop failure: doc in discovery but absent from both tags."""
        output = "ASSOCIATED_DOCS_MODIFIED: docs/a.md"
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            ["docs/a.md", "docs/silently_dropped.md"],
            output,
        )
        assert mod == ["docs/a.md"]
        assert dropped == ["docs/silently_dropped.md"]

    def test_silent_drop_when_step10_has_no_tags(self) -> None:
        output = "Arch updated.\nARCHITECTURE_FILES_MODIFIED: architecture.json"
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            ["docs/a.md", "docs/b.md"], output
        )
        assert mod == []
        assert dropped == ["docs/a.md", "docs/b.md"]

    def test_markdown_formatting_stripped_on_tag_parsing(self) -> None:
        output = "ASSOCIATED_DOCS_MODIFIED: **docs/bold.md**, docs/plain.md"
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            ["docs/bold.md", "docs/plain.md"], output
        )
        assert "docs/bold.md" in mod
        assert "docs/plain.md" in mod
        assert dropped == []

    def test_path_normalization_across_backslash_and_slash(self) -> None:
        """A windows-style `docs\\foo.md` from discovery should match
        `docs/foo.md` in Step 10 output."""
        output = "ASSOCIATED_DOCS_MODIFIED: docs/foo.md"
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            [r"docs\foo.md"], output
        )
        assert dropped == []

    def test_empty_tag_line_does_not_swallow_next_marker(self) -> None:
        """Regression for the `\\s*(.*)` greedy bug in the original tag regex.
        An empty ASSOCIATED_DOCS_MODIFIED line must not reach into the
        ARCHITECTURE_FILES_MODIFIED line below it."""
        output = (
            "ASSOCIATED_DOCS_MODIFIED: \n"
            "ARCHITECTURE_FILES_MODIFIED: architecture.json"
        )
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            ["docs/a.md"], output
        )
        # Empty MODIFIED line means no docs modified → a.md is dropped.
        assert mod == []
        assert dropped == ["docs/a.md"]

    def test_overlap_between_modified_and_unchanged_flagged(self) -> None:
        """Reviewer regression: docstring says 'exactly one bucket', so a doc
        appearing in both MODIFIED and UNCHANGED simultaneously must be flagged
        as a contract violation — not silently accepted."""
        output = (
            "ASSOCIATED_DOCS_MODIFIED: README.md\n"
            "ASSOCIATED_DOCS_UNCHANGED: README.md\n"
        )
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            ["README.md"], output
        )
        assert mod == ["README.md"]
        assert unchanged == ["README.md"]
        assert dropped == []
        assert overlapping == ["README.md"]

    def test_overlap_across_all_three_buckets_flagged(self) -> None:
        output = (
            "ASSOCIATED_DOCS_MODIFIED: docs/a.md\n"
            "ASSOCIATED_DOCS_CONFLICTS: docs/a.md\n"
            "ASSOCIATED_DOCS_UNCHANGED: docs/a.md\n"
        )
        _, _, _, dropped, overlapping = _verify_doc_sync_contract(
            ["docs/a.md"], output
        )
        assert dropped == []
        assert overlapping == ["docs/a.md"]

    def test_no_overlap_when_each_doc_in_single_bucket(self) -> None:
        output = (
            "ASSOCIATED_DOCS_MODIFIED: docs/a.md\n"
            "ASSOCIATED_DOCS_UNCHANGED: docs/b.md\n"
        )
        _, _, _, dropped, overlapping = _verify_doc_sync_contract(
            ["docs/a.md", "docs/b.md"], output
        )
        assert dropped == []
        assert overlapping == []

    def test_overlap_detects_only_duplicated_docs_not_siblings(self) -> None:
        """Two different docs in the same bucket is not overlap. Overlap
        means the SAME doc appears in 2+ buckets."""
        output = (
            "ASSOCIATED_DOCS_MODIFIED: docs/a.md, docs/b.md\n"
            "ASSOCIATED_DOCS_UNCHANGED: docs/b.md\n"
        )
        _, _, _, dropped, overlapping = _verify_doc_sync_contract(
            ["docs/a.md", "docs/b.md"], output
        )
        assert dropped == []
        assert overlapping == ["docs/b.md"]

    def test_overlap_path_normalization_catches_backslash_variant(self) -> None:
        """The verifier normalizes paths before bucket comparison, so a
        windows-style path in one bucket and posix in another still counts
        as overlap on the same doc."""
        output = (
            "ASSOCIATED_DOCS_MODIFIED: docs\\api.md\n"
            "ASSOCIATED_DOCS_UNCHANGED: docs/api.md\n"
        )
        _, _, _, dropped, overlapping = _verify_doc_sync_contract(
            ["docs/api.md"], output
        )
        assert dropped == []
        assert overlapping == ["docs/api.md"]

    def test_multiline_marker_value_all_entries_parsed(self) -> None:
        """Reviewer 3rd-pass regression: LLMs wrap long doc lists across
        lines ~5–10% of the time. The original [^\\n]* regex truncated
        after the first line and silently false-positived the remainder.
        The continuation-line regex + payload-line walker must preserve
        every entry regardless of how the LLM wraps the line."""
        output = (
            "ASSOCIATED_DOCS_MODIFIED: README.md, docs/api.md,\n"
            "    docs/schema.md, docs/guide.md\n"
        )
        modified, _, _, dropped, _ = _verify_doc_sync_contract(
            ["README.md", "docs/api.md", "docs/schema.md", "docs/guide.md"],
            output,
        )
        assert set(modified) == {"README.md", "docs/api.md", "docs/schema.md", "docs/guide.md"}
        assert dropped == []

    def test_multiline_marker_bulleted_list_form(self) -> None:
        """Some LLMs render as a bulleted list: the continuation lines
        may start with '- ' or '* '. The entry-strip step must remove
        those leading bullets so each entry normalizes to a bare path."""
        output = (
            "ASSOCIATED_DOCS_MODIFIED: README.md,\n"
            "    - docs/x.md,\n"
            "    * docs/y.md\n"
        )
        modified, _, _, dropped, _ = _verify_doc_sync_contract(
            ["README.md", "docs/x.md", "docs/y.md"], output
        )
        assert set(modified) == {"README.md", "docs/x.md", "docs/y.md"}
        assert dropped == []

    def test_marker_terminator_stops_payload_walk(self) -> None:
        """Continuation lines get absorbed until we hit another known
        marker; the next marker must not be swallowed into the first
        marker's payload."""
        output = (
            "ASSOCIATED_DOCS_MODIFIED: README.md,\n"
            "    docs/schema.md\n"
            "ASSOCIATED_DOCS_UNCHANGED: docs/api.md\n"
        )
        modified, _, unchanged, dropped, _ = _verify_doc_sync_contract(
            ["README.md", "docs/schema.md", "docs/api.md"], output
        )
        assert set(modified) == {"README.md", "docs/schema.md"}
        assert unchanged == ["docs/api.md"]
        assert dropped == []

    def test_dash_prefix_on_single_line_value_stripped(self) -> None:
        """Even the single-line inline form can contain bullet prefixes:
        `ASSOCIATED_DOCS_MODIFIED: - README.md, - docs/x.md` must normalize
        to the bare paths, not the prefixed versions."""
        output = "ASSOCIATED_DOCS_MODIFIED: - README.md, - docs/x.md\n"
        modified, _, _, dropped, _ = _verify_doc_sync_contract(
            ["README.md", "docs/x.md"], output
        )
        assert set(modified) == {"README.md", "docs/x.md"}
        assert dropped == []

    def test_bullet_char_variants_all_stripped(self) -> None:
        """Hyphen, asterisk, and unicode bullet (•) prefixes are all
        common LLM renderings."""
        output = (
            "ASSOCIATED_DOCS_MODIFIED: - a.md, * b.md, • c.md\n"
        )
        modified, _, _, dropped, _ = _verify_doc_sync_contract(
            ["a.md", "b.md", "c.md"], output
        )
        assert set(modified) == {"a.md", "b.md", "c.md"}
        assert dropped == []

    def test_unindented_continuation_lines_parsed(self) -> None:
        """Reviewer 4th-pass regression (bug 1): the prior continuation
        regex required leading whitespace on wrap lines. LLMs frequently
        emit a wrapped list flush-left — those entries vanished and were
        re-flagged as silent drops. The line-walker must accept any
        non-empty continuation line that is not another known marker."""
        output = (
            "ASSOCIATED_DOCS_MODIFIED: README.md,\n"
            "CHANGELOG.md, docs/api.md\n"
            "ASSOCIATED_DOCS_UNCHANGED: \n"
        )
        modified, _, _, dropped, _ = _verify_doc_sync_contract(
            ["README.md", "CHANGELOG.md", "docs/api.md"], output
        )
        assert set(modified) == {"README.md", "CHANGELOG.md", "docs/api.md"}
        assert dropped == []

    def test_pure_newline_separated_bullets_no_commas(self) -> None:
        """Reviewer 4th-pass regression (bug 2): a bulleted list with
        no commas (one entry per line) used to coalesce into a single
        joined entry like '- a.md   - b.md'. Per-line bullet stripping
        before the comma split lets each line yield its own entry."""
        output = (
            "ASSOCIATED_DOCS_MODIFIED:\n"
            "- README.md\n"
            "- CHANGELOG.md\n"
            "- docs/api.md\n"
            "\n"
            "ASSOCIATED_DOCS_UNCHANGED: \n"
        )
        modified, _, _, dropped, _ = _verify_doc_sync_contract(
            ["README.md", "CHANGELOG.md", "docs/api.md"], output
        )
        assert set(modified) == {"README.md", "CHANGELOG.md", "docs/api.md"}
        assert dropped == []

    def test_indented_pure_bullets_no_commas(self) -> None:
        """Indented bullet list, comma-free — same shape as above but
        with a couple spaces in front of each bullet, which is the more
        common LLM rendering."""
        output = (
            "ASSOCIATED_DOCS_MODIFIED:\n"
            "  - README.md\n"
            "  - CHANGELOG.md\n"
        )
        modified, _, _, dropped, _ = _verify_doc_sync_contract(
            ["README.md", "CHANGELOG.md"], output
        )
        assert set(modified) == {"README.md", "CHANGELOG.md"}
        assert dropped == []


# ---------------------------------------------------------------------------
# Step 8.5 — pre-flight drift heal
# ---------------------------------------------------------------------------

class TestPreflightDriftHeal:
    """Detect drift via ci_drift_heal.detect_drift, run pdd update per drift."""

    @pytest.fixture
    def worktree(self, tmp_path: Path) -> Path:
        wt = tmp_path / "worktree"
        wt.mkdir()
        return wt

    def test_nonexistent_worktree_returns_empty(self, tmp_path: Path) -> None:
        healed, failed, _healed_prompts = _preflight_drift_heal(tmp_path / "nonexistent", quiet=True)
        assert healed == []
        assert failed == []

    def test_no_drift_returns_empty(self, worktree: Path) -> None:
        with patch("pdd.ci_drift_heal.detect_drift", return_value=([], [])):
            healed, failed, _healed_prompts = _preflight_drift_heal(worktree, quiet=True)
        assert healed == []
        assert failed == []

    def test_detect_drift_raises_is_graceful(self, worktree: Path) -> None:
        """detect_drift may hit malformed architecture.json etc. Don't crash."""
        with patch(
            "pdd.ci_drift_heal.detect_drift",
            side_effect=RuntimeError("simulated"),
        ):
            healed, failed, _healed_prompts = _preflight_drift_heal(worktree, quiet=True)
        assert healed == []
        assert failed == []

    def test_single_drift_healed_successfully(self, worktree: Path) -> None:
        drift = MagicMock()
        drift.basename = "mod_a"
        drift.code_path = "pdd/mod_a.py"
        with patch(
            "pdd.ci_drift_heal.detect_drift",
            return_value=([drift], []),
        ), patch(
            "pdd.agentic_change_orchestrator.subprocess.run",
            return_value=MagicMock(returncode=0, stderr=""),
        ) as m_run:
            healed, failed, _healed_prompts = _preflight_drift_heal(worktree, quiet=True)
        assert healed == ["mod_a"]
        assert failed == []
        # Verify subprocess was invoked with sys.executable -m pdd (venv parity)
        # + correct cwd. Bare ["pdd", ...] would resolve via PATH and could pick
        # up a different version.
        import sys
        call = m_run.call_args_list[0]
        assert call.args[0] == [sys.executable, "-m", "pdd", "update", "pdd/mod_a.py"]
        assert str(call.kwargs.get("cwd", "")) == str(worktree)

    def test_multiple_drift_each_independently_tracked(self, worktree: Path) -> None:
        drifts = []
        for name in ("mod_a", "mod_b", "mod_c"):
            d = MagicMock()
            d.basename = name
            d.code_path = f"pdd/{name}.py"
            drifts.append(d)

        def fake_run(cmd, **kwargs):
            # mod_b fails; others succeed
            if "mod_b.py" in cmd[-1]:
                return MagicMock(returncode=1, stderr="heal error")
            return MagicMock(returncode=0, stderr="")

        with patch(
            "pdd.ci_drift_heal.detect_drift",
            return_value=(drifts, []),
        ), patch(
            "pdd.agentic_change_orchestrator.subprocess.run",
            side_effect=fake_run,
        ):
            healed, failed, _healed_prompts = _preflight_drift_heal(worktree, quiet=True)
        assert set(healed) == {"mod_a", "mod_c"}
        assert failed == ["mod_b"]

    def test_max_modules_cap_defers_overflow(self, worktree: Path) -> None:
        """Reviewer 4th-pass regression (sharp edge c): an unbounded heal
        fan-out spends N × timeout_per_module seconds before Step 9 starts.
        With max_modules=3 and 5 drifted modules, only the
        alphabetically-first 3 should be healed; the remainder are deferred
        to CI auto-heal."""
        drifts = []
        for name in ("mod_a", "mod_b", "mod_c", "mod_d", "mod_e"):
            d = MagicMock()
            d.basename = name
            d.code_path = f"pdd/{name}.py"
            drifts.append(d)

        captured_calls: list = []

        def fake_run(cmd, **kwargs):
            captured_calls.append(cmd[-1])
            return MagicMock(returncode=0, stderr="")

        with patch(
            "pdd.ci_drift_heal.detect_drift",
            return_value=(drifts, []),
        ), patch(
            "pdd.agentic_change_orchestrator.subprocess.run",
            side_effect=fake_run,
        ):
            healed, failed, _healed_prompts = _preflight_drift_heal(
                worktree, quiet=True, max_modules=3
            )
        assert sorted(healed) == ["mod_a", "mod_b", "mod_c"]
        assert failed == []
        # No subprocess call for deferred modules (mod_d, mod_e).
        assert not any("mod_d.py" in c for c in captured_calls)
        assert not any("mod_e.py" in c for c in captured_calls)

    def test_drift_with_no_code_path_marked_failed(self, worktree: Path) -> None:
        drift = MagicMock()
        drift.basename = "mod_no_code"
        drift.code_path = None
        with patch(
            "pdd.ci_drift_heal.detect_drift",
            return_value=([drift], []),
        ):
            healed, failed, _healed_prompts = _preflight_drift_heal(worktree, quiet=True)
        assert healed == []
        assert failed == ["mod_no_code"]

    def test_subprocess_timeout_marks_failed(self, worktree: Path) -> None:
        drift = MagicMock()
        drift.basename = "slow_mod"
        drift.code_path = "pdd/slow.py"
        with patch(
            "pdd.ci_drift_heal.detect_drift",
            return_value=([drift], []),
        ), patch(
            "pdd.agentic_change_orchestrator.subprocess.run",
            side_effect=subprocess.TimeoutExpired(cmd=["pdd"], timeout=1),
        ):
            healed, failed, _healed_prompts = _preflight_drift_heal(
                worktree, quiet=True, timeout_per_module=0.01
            )
        assert healed == []
        assert failed == ["slow_mod"]

    def test_pdd_module_invocation_works(self) -> None:
        """Regression: ``sys.executable -m pdd`` must succeed.

        Step 8.5 invokes ``[sys.executable, "-m", "pdd", "update", ...]`` for
        venv parity. If ``pdd/__main__.py`` is missing, every heal call fails
        with ``No module named pdd.__main__``. This test catches that
        regression statically (no subprocess) by importing the module."""
        import importlib
        mod = importlib.import_module("pdd.__main__")
        assert hasattr(mod, "cli"), (
            "pdd/__main__.py must expose `cli` so `python -m pdd` works "
            "(used by Step 8.5 subprocess invocation)"
        )

    def test_subprocess_arbitrary_exception_marks_failed(self, worktree: Path) -> None:
        drift = MagicMock()
        drift.basename = "bad_mod"
        drift.code_path = "pdd/bad.py"
        with patch(
            "pdd.ci_drift_heal.detect_drift",
            return_value=([drift], []),
        ), patch(
            "pdd.agentic_change_orchestrator.subprocess.run",
            side_effect=OSError("disk full"),
        ):
            healed, failed, _healed_prompts = _preflight_drift_heal(worktree, quiet=True)
        assert healed == []
        assert failed == ["bad_mod"]

    def test_cwd_restored_even_on_exception(
        self, worktree: Path, tmp_path: Path
    ) -> None:
        """os.chdir into worktree must be reverted no matter what."""
        import os
        original = Path.cwd()
        try:
            with patch(
                "pdd.ci_drift_heal.detect_drift",
                side_effect=RuntimeError("boom"),
            ):
                _preflight_drift_heal(worktree, quiet=True)
            assert Path.cwd() == original, "cwd must be restored after heal"
        finally:
            # Safety: always restore
            os.chdir(original)

    def test_import_failure_is_graceful(self, worktree: Path) -> None:
        """If ci_drift_heal is unavailable for any reason, don't crash."""
        with patch.dict("sys.modules", {"pdd.ci_drift_heal": None}):
            healed, failed, _healed_prompts = _preflight_drift_heal(worktree, quiet=True)
        assert healed == []
        assert failed == []


# ---------------------------------------------------------------------------
# Layer 2 — Integration tests: drive the orchestrator end-to-end with mocked
# LLM and prove the new Step 8.5 + Step 10.5 are wired correctly into the
# overall pipeline (between existing steps, with right state transitions).
# ---------------------------------------------------------------------------

class TestStep85And105Integration:
    """Mock every external dep, then run run_agentic_change_orchestrator and
    inspect what Step 8.5 / Step 10.5 actually did."""

    @pytest.fixture
    def orch_env(self, tmp_path: Path):
        worktree_path = tmp_path / ".pdd" / "worktrees" / "change-issue-99"
        worktree_path.mkdir(parents=True, exist_ok=True)
        (worktree_path / "prompts").mkdir(exist_ok=True)
        (worktree_path / "architecture.json").write_text("[]", encoding="utf-8")

        with patch("pdd.agentic_change_orchestrator.run_agentic_task") as m_run, \
             patch("pdd.agentic_change_orchestrator.load_workflow_state") as m_load, \
             patch("pdd.agentic_change_orchestrator.save_workflow_state") as m_save, \
             patch("pdd.agentic_change_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_change_orchestrator.load_prompt_template") as m_tmpl, \
             patch("pdd.agentic_change_orchestrator.subprocess.run") as m_subproc, \
             patch("pdd.agentic_change_orchestrator.build_dependency_graph") as m_bg, \
             patch("pdd.agentic_change_orchestrator.topological_sort") as m_ts, \
             patch("pdd.agentic_change_orchestrator.get_affected_modules") as m_ga, \
             patch("pdd.agentic_change_orchestrator.generate_sync_order_script"), \
             patch("pdd.agentic_change_orchestrator._check_existing_pr", return_value=None), \
             patch("pdd.agentic_change_orchestrator.substitute_template_variables") as m_sub, \
             patch("pdd.agentic_change_orchestrator.discover_associated_documents") as m_disc, \
             patch("pdd.agentic_change_orchestrator._setup_worktree") as m_setup, \
             patch("pdd.agentic_change_orchestrator._preflight_drift_heal") as m_pre:
            m_load.return_value = (None, None)
            m_save.return_value = 42
            m_tmpl.return_value = MagicMock()
            m_subproc.return_value = MagicMock(stdout=str(tmp_path), returncode=0)
            m_bg.return_value = {}
            m_ts.return_value = ([], [])
            m_ga.return_value = []
            m_sub.side_effect = lambda tmpl, ctx: f"prompt-{sorted(ctx.keys())}"
            m_setup.return_value = (worktree_path, None)
            # Default: no drift to heal
            m_pre.return_value = ([], [], [])

            yield {
                "run": m_run,
                "discover": m_disc,
                "sub": m_sub,
                "preflight": m_pre,
                "tmp_path": tmp_path,
                "worktree_path": worktree_path,
                "save": m_save,
            }

    def _wire_happy_path_steps(self, m_run: MagicMock, step9_files_modified: str = "prompts/foo_python.prompt") -> None:
        """Standard fake responses for steps 1-13 in a happy-path workflow."""
        def fake(instruction, **kwargs):
            label = kwargs.get("label", "")
            if "step9" in label:
                return (True, f"FILES_MODIFIED: {step9_files_modified}", 0.1, "claude")
            if "step10" in label:
                return (True, "Arch updated\nARCHITECTURE_FILES_MODIFIED:", 0.1, "claude")
            if "step11" in label:
                return (True, "No Issues Found", 0.1, "claude")
            if "step13" in label:
                return (True, "PR Created: https://example/pr/1", 0.1, "claude")
            return (True, f"Output for {label}", 0.1, "claude")
        m_run.side_effect = fake

    def test_preflight_runs_exactly_once_per_workflow(self, orch_env: dict) -> None:
        """Step 8.5 must fire exactly once even though step setup branch
        is checked for every step."""
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        m = orch_env
        self._wire_happy_path_steps(m["run"])
        m["discover"].return_value = []

        success, *_ = run_agentic_change_orchestrator(
            issue_url="http://issue", issue_content="x",
            repo_owner="o", repo_name="r", issue_number=99,
            issue_author="me", issue_title="t",
            cwd=m["tmp_path"], quiet=True,
        )
        assert success is True
        assert m["preflight"].call_count == 1, (
            f"Expected pre-flight to fire exactly once, got {m['preflight'].call_count}"
        )

    def test_preflight_called_with_worktree_path(self, orch_env: dict) -> None:
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        m = orch_env
        self._wire_happy_path_steps(m["run"])
        m["discover"].return_value = []

        run_agentic_change_orchestrator(
            issue_url="http://issue", issue_content="x",
            repo_owner="o", repo_name="r", issue_number=99,
            issue_author="me", issue_title="t",
            cwd=m["tmp_path"], quiet=True,
        )
        call = m["preflight"].call_args
        wt = call.kwargs.get("worktree_path") or call.args[0]
        assert wt == m["worktree_path"]

    def test_preflight_not_called_when_worktree_setup_fails(self, tmp_path: Path) -> None:
        """If _setup_worktree returns (None, error), the workflow aborts before
        Step 9, so pre-flight must not fire."""
        with patch("pdd.agentic_change_orchestrator.run_agentic_task") as m_run, \
             patch("pdd.agentic_change_orchestrator.load_workflow_state") as m_load, \
             patch("pdd.agentic_change_orchestrator.save_workflow_state") as m_save, \
             patch("pdd.agentic_change_orchestrator.clear_workflow_state"), \
             patch("pdd.agentic_change_orchestrator.load_prompt_template") as m_tmpl, \
             patch("pdd.agentic_change_orchestrator.subprocess.run") as m_subproc, \
             patch("pdd.agentic_change_orchestrator.build_dependency_graph") as m_bg, \
             patch("pdd.agentic_change_orchestrator.topological_sort") as m_ts, \
             patch("pdd.agentic_change_orchestrator.get_affected_modules") as m_ga, \
             patch("pdd.agentic_change_orchestrator.generate_sync_order_script"), \
             patch("pdd.agentic_change_orchestrator._check_existing_pr", return_value=None), \
             patch("pdd.agentic_change_orchestrator.substitute_template_variables") as m_sub, \
             patch("pdd.agentic_change_orchestrator._setup_worktree", return_value=(None, "simulated")), \
             patch("pdd.agentic_change_orchestrator._preflight_drift_heal") as m_pre:
            m_load.return_value = (None, None)
            m_save.return_value = 42
            m_tmpl.return_value = MagicMock()
            m_subproc.return_value = MagicMock(stdout=str(tmp_path), returncode=0)
            m_bg.return_value = {}
            m_ts.return_value = ([], [])
            m_ga.return_value = []
            m_sub.side_effect = lambda tmpl, ctx: "fake"
            # Steps 1-8 succeed; step 9 will hit the worktree-setup failure
            m_run.return_value = (True, "ok", 0.1, "claude")

            from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
            success, msg, *_ = run_agentic_change_orchestrator(
                issue_url="http://issue", issue_content="x",
                repo_owner="o", repo_name="r", issue_number=99,
                issue_author="me", issue_title="t",
                cwd=tmp_path, quiet=True,
            )
            assert success is False
            assert "Failed to create worktree" in msg
            assert m_pre.call_count == 0

    def test_step10_5_silent_drops_emit_warning_in_step10_output(
        self, orch_env: dict
    ) -> None:
        """When discover returns docs but Step 10 doesn't tag them, the
        verifier appends ORCHESTRATOR_POSTCHECK_WARNINGS + DOC_SYNC_SILENT_DROPS
        to step_output (which is what gets persisted to state)."""
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        m = orch_env
        m["discover"].return_value = ["docs/forgotten.md", "docs/dropped.md"]

        # Step 9 produces the prompt that triggers discovery; Step 10's output
        # does NOT include ASSOCIATED_DOCS_MODIFIED for any of them.
        def fake(instruction, **kwargs):
            label = kwargs.get("label", "")
            if "step9" in label:
                return (True, "FILES_MODIFIED: prompts/foo_python.prompt", 0.1, "claude")
            if "step10" in label:
                return (True, "Arch updated.", 0.1, "claude")
            if "step11" in label:
                return (True, "No Issues Found", 0.1, "claude")
            if "step13" in label:
                return (True, "PR Created: https://example/pr/x", 0.1, "claude")
            return (True, f"out-{label}", 0.1, "claude")
        m["run"].side_effect = fake

        run_agentic_change_orchestrator(
            issue_url="http://issue", issue_content="x",
            repo_owner="o", repo_name="r", issue_number=99,
            issue_author="me", issue_title="t",
            cwd=m["tmp_path"], quiet=True,
        )
        # Inspect the saved state for step 10 — it should now carry the
        # postcheck warnings + DOC_SYNC_SILENT_DROPS marker.
        save_calls = m["save"].call_args_list
        # The state dict is positional arg 3 (cwd, issue_number, "change", state, ...)
        # Find the most recent save where step 10 output is present.
        step10_output_saved = None
        for call in save_calls:
            state_arg = call.args[3]
            if "10" in state_arg.get("step_outputs", {}):
                step10_output_saved = state_arg["step_outputs"]["10"]
        assert step10_output_saved is not None, "step 10 output must be saved"
        assert "DOC_SYNC_SILENT_DROPS:" in step10_output_saved
        assert "docs/forgotten.md" in step10_output_saved
        assert "docs/dropped.md" in step10_output_saved
        assert "ORCHESTRATOR_POSTCHECK_WARNINGS" in step10_output_saved

    def test_step10_5_passes_silently_when_all_docs_handled(
        self, orch_env: dict
    ) -> None:
        """When Step 10 handles all discovered docs, no warnings are added."""
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        m = orch_env
        m["discover"].return_value = ["docs/handled.md"]

        def fake(instruction, **kwargs):
            label = kwargs.get("label", "")
            if "step9" in label:
                return (True, "FILES_MODIFIED: prompts/foo_python.prompt", 0.1, "claude")
            if "step10" in label:
                return (
                    True,
                    "Arch updated.\nASSOCIATED_DOCS_MODIFIED: docs/handled.md",
                    0.1, "claude",
                )
            if "step11" in label:
                return (True, "No Issues Found", 0.1, "claude")
            if "step13" in label:
                return (True, "PR Created: https://example/pr/x", 0.1, "claude")
            return (True, f"out-{label}", 0.1, "claude")
        m["run"].side_effect = fake

        run_agentic_change_orchestrator(
            issue_url="http://issue", issue_content="x",
            repo_owner="o", repo_name="r", issue_number=99,
            issue_author="me", issue_title="t",
            cwd=m["tmp_path"], quiet=True,
        )
        # No silent-drop warnings should appear in any saved step10 output.
        save_calls = m["save"].call_args_list
        step10_outs = []
        for call in save_calls:
            state_arg = call.args[3]
            if "10" in state_arg.get("step_outputs", {}):
                step10_outs.append(state_arg["step_outputs"]["10"])
        assert step10_outs, "step 10 output must be saved"
        for out in step10_outs:
            assert "DOC_SYNC_SILENT_DROPS:" not in out

    def test_step10_5_skipped_when_no_docs_discovered(
        self, orch_env: dict
    ) -> None:
        """If discover returned empty, Step 10.5 should not emit warnings
        even if Step 10 produced no doc tags."""
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        m = orch_env
        m["discover"].return_value = []
        self._wire_happy_path_steps(m["run"])

        run_agentic_change_orchestrator(
            issue_url="http://issue", issue_content="x",
            repo_owner="o", repo_name="r", issue_number=99,
            issue_author="me", issue_title="t",
            cwd=m["tmp_path"], quiet=True,
        )
        save_calls = m["save"].call_args_list
        for call in save_calls:
            state_arg = call.args[3]
            for k, v in state_arg.get("step_outputs", {}).items():
                assert "DOC_SYNC_SILENT_DROPS:" not in v

    def test_step85_state_keys_set_after_run(self, orch_env: dict) -> None:
        """preflight_healed_modules + preflight_failed_heal_modules must be
        recorded in state so they survive resume + show up in the final report."""
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        m = orch_env
        m["preflight"].return_value = (["mod_a", "mod_b"], ["mod_c"], ["prompts/mod_a_python.prompt", "prompts/mod_b_python.prompt"])
        self._wire_happy_path_steps(m["run"])
        m["discover"].return_value = []

        run_agentic_change_orchestrator(
            issue_url="http://issue", issue_content="x",
            repo_owner="o", repo_name="r", issue_number=99,
            issue_author="me", issue_title="t",
            cwd=m["tmp_path"], quiet=True,
        )
        # Find a state-save with the preflight keys set
        save_calls = m["save"].call_args_list
        found = None
        for call in save_calls:
            state_arg = call.args[3]
            if state_arg.get("preflight_drift_healed"):
                found = state_arg
                break
        assert found is not None, "preflight_drift_healed flag must be in state"
        assert found.get("preflight_healed_modules") == ["mod_a", "mod_b"]
        assert found.get("preflight_failed_heal_modules") == ["mod_c"]
        # Reviewer 5th-pass (F2): healed prompt paths recorded so Step 10
        # discovery can sweep them. Without this, Step 8.5 mutations bypass
        # the doc-sync contract and ride into the PR via `git add -A`.
        assert found.get("preflight_healed_prompt_paths") == [
            "prompts/mod_a_python.prompt", "prompts/mod_b_python.prompt"
        ]

    def test_step85_healed_prompts_added_to_step10_discovery(
        self, orch_env: dict, tmp_path: Path
    ) -> None:
        """Reviewer 5th-pass (F2) regression: Step 8.5 healed prompts MUST
        be merged into the Step 10 ``discover_associated_documents`` call.
        Otherwise their <include> docs bypass the doc-sync contract and the
        PR can land healed-prompt mutations whose docs were never verified.
        """
        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        m = orch_env

        # Step 8.5 healed two prompts, neither of which is in Step 9's
        # FILES_MODIFIED. Without F2's wiring, discover would be called
        # only with Step 9's prompt list and would miss these.
        worktree = m["worktree_path"]
        prompts_dir = worktree / "prompts"
        prompts_dir.mkdir(parents=True, exist_ok=True)
        healed_p1 = prompts_dir / "healed_a_python.prompt"
        healed_p2 = prompts_dir / "healed_b_python.prompt"
        healed_p1.write_text("% prompt a\n<include>docs/a.md</include>\n")
        healed_p2.write_text("% prompt b\n<include>docs/b.md</include>\n")

        m["preflight"].return_value = (
            ["healed_a", "healed_b"],
            [],
            [str(healed_p1), str(healed_p2)],
        )

        # Step 9 modifies a totally different prompt that wouldn't on its
        # own pull in docs/a.md or docs/b.md.
        self._wire_happy_path_steps(m["run"], step9_files_modified="prompts/unrelated_python.prompt")
        m["discover"].return_value = []  # discover would still return [] for the test

        run_agentic_change_orchestrator(
            issue_url="http://issue", issue_content="x",
            repo_owner="o", repo_name="r", issue_number=99,
            issue_author="me", issue_title="t",
            cwd=m["tmp_path"], quiet=True,
        )

        # Confirm discover_associated_documents was called with BOTH the
        # healed prompts (F2 wiring) AND Step 9's modified prompt.
        assert m["discover"].called, "discover_associated_documents must run for Step 10"
        call_kwargs = m["discover"].call_args.kwargs
        modified = call_kwargs.get("modified_prompts") or set()
        modified_strs = {str(p) for p in modified}
        # Healed prompt paths from Step 8.5 must be in the discovery set
        assert any("healed_a_python.prompt" in s for s in modified_strs), (
            f"F2 regression: healed_a not merged into discovery set; got {modified_strs}"
        )
        assert any("healed_b_python.prompt" in s for s in modified_strs), (
            f"F2 regression: healed_b not merged into discovery set; got {modified_strs}"
        )


# ---------------------------------------------------------------------------
# Three-state contract: verify the doc-sync classification semantics.
# ---------------------------------------------------------------------------

class TestStep11ReadsStep10Output:
    """Step 10.5 appends DOC_SYNC_SILENT_DROPS to step10_output. For the
    review loop to actually act on those drops (not just rely on Step 11
    LLM noticing doc staleness independently), Step 11's prompt must
    consume {step10_output} as an input."""

    def test_step11_prompt_includes_step10_output_placeholder(self) -> None:
        prompt_path = (
            Path(__file__).parent.parent
            / "pdd" / "prompts"
            / "agentic_change_step11_identify_issues_LLM.prompt"
        )
        text = prompt_path.read_text(encoding="utf-8")
        assert "{step10_output}" in text, (
            "Step 11 must template-substitute {step10_output} so the "
            "DOC_SYNC_SILENT_DROPS warnings Step 10.5 appends are visible "
            "to the review loop. Without this, Step 10.5's contract is a "
            "purely informational broadcast — not a recovery driver."
        )


class TestVerifierThreeStateContract:
    """Behavioral tests for the doc-sync three-state contract.

    Intentionally does NOT assert literal strings in the Step 10 prompt
    template — prompts are LLM-facing instructions and may be reworded
    without semantic change. The contract under test is *behavioral*:

      - Verifier classifies docs into MODIFIED / CONFLICTS / UNCHANGED / dropped
      - Three terminal states partition cleanly (no double-counting)
      - End-to-end orchestrator tests above already exercise the silent-drop
        path; this section pins the semantics of the partition itself.
    """

    def test_verifier_accepts_unchanged_marker(self) -> None:
        """An LLM emission of ASSOCIATED_DOCS_UNCHANGED must satisfy the
        contract for the listed docs (no silent-drop alarm)."""
        from pdd.agentic_change_orchestrator import _verify_doc_sync_contract
        output = "ASSOCIATED_DOCS_UNCHANGED: docs/api.md, docs/spec.md"
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            ["docs/api.md", "docs/spec.md"], output,
        )
        assert set(unchanged) == {"docs/api.md", "docs/spec.md"}
        assert dropped == [], (
            "UNCHANGED docs satisfy the contract — they're explicitly "
            "considered, not silently omitted."
        )

    def test_verifier_three_state_partition_no_overlap(self) -> None:
        """A doc is in MODIFIED, CONFLICTS, OR UNCHANGED — exactly one of
        the three. The verifier must not double-count."""
        from pdd.agentic_change_orchestrator import _verify_doc_sync_contract
        output = (
            "ASSOCIATED_DOCS_MODIFIED: docs/edited.md\n"
            "ASSOCIATED_DOCS_CONFLICTS: docs/risky.md\n"
            "ASSOCIATED_DOCS_UNCHANGED: docs/clean.md\n"
        )
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            ["docs/edited.md", "docs/risky.md", "docs/clean.md"], output,
        )
        assert mod == ["docs/edited.md"]
        assert conflict == ["docs/risky.md"]
        assert unchanged == ["docs/clean.md"]
        assert dropped == []

    def test_partial_unchanged_partial_drop_caught(self) -> None:
        """3 docs discovered; 1 unchanged, 1 modified, 1 silently dropped."""
        from pdd.agentic_change_orchestrator import _verify_doc_sync_contract
        output = (
            "ASSOCIATED_DOCS_MODIFIED: docs/edited.md\n"
            "ASSOCIATED_DOCS_UNCHANGED: docs/clean.md\n"
        )
        mod, conflict, unchanged, dropped, overlapping = _verify_doc_sync_contract(
            ["docs/edited.md", "docs/clean.md", "docs/forgotten.md"], output,
        )
        assert mod == ["docs/edited.md"]
        assert unchanged == ["docs/clean.md"]
        assert dropped == ["docs/forgotten.md"]
