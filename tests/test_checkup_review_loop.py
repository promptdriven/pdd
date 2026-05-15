"""Tests for ``pdd checkup --review-loop`` primary-reviewer/fixer mode."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any, Dict, List, Tuple
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.commands.checkup import checkup


def _ctx(tmp_path: Path):
    from pdd.checkup_review_loop import ReviewLoopContext

    return ReviewLoopContext(
        issue_url="https://github.com/o/r/issues/2",
        issue_content="Title: Fix the workflow\nDescription:\nMake it work.",
        repo_owner="o",
        repo_name="r",
        issue_number=2,
        issue_title="Fix the workflow",
        architecture_json="{}",
        pddrc_content="No .pddrc found.",
        pr_url="https://github.com/o/r/pull/1",
        pr_owner="o",
        pr_repo="r",
        pr_number=1,
        project_root=tmp_path,
    )


def _config(**overrides: Any):
    from pdd.checkup_review_loop import ReviewLoopConfig

    data: Dict[str, Any] = {
        "reviewers": ("codex", "claude"),
        "max_rounds": 3,
        "max_cost": 50.0,
        "max_minutes": 30.0,
        "require_all_reviewers_clean": True,
        "continue_on_reviewer_limit": False,
        "require_final_fresh_review": True,
    }
    data.update(overrides)
    return ReviewLoopConfig(**data)


def _json(status: str, findings: List[Dict[str, str]] | None = None) -> str:
    return json.dumps(
        {
            "status": status,
            "issue_aligned": True,
            "summary": status,
            "findings": findings or [],
        }
    )


class TestCheckupReviewLoopCli:
    def test_review_loop_flags_reach_agentic_checkup_without_forcing_no_fix(self) -> None:
        runner = CliRunner()
        with patch(
            "pdd.commands.checkup.run_agentic_checkup",
            return_value=(True, "ok", 0.0, "model"),
        ) as run_mock:
            result = runner.invoke(
                checkup,
                [
                    "--pr",
                    "https://github.com/o/r/pull/1",
                    "--issue",
                    "https://github.com/o/r/issues/2",
                    "--review-loop",
                    "--reviewers",
                    "codex,claude",
                    "--reviewer",
                    "codex",
                    "--fixer",
                    "claude",
                    "--max-review-rounds",
                    "2",
                    "--max-review-cost",
                    "3.5",
                    "--max-review-minutes",
                    "12",
                    "--require-final-fresh-review",
                    "--no-github-state",
                ],
                obj={},
            )

        assert result.exit_code == 0, result.output
        assert "forces --no-fix" not in result.output
        kwargs = run_mock.call_args.kwargs
        assert kwargs["no_fix"] is False
        assert kwargs["review_loop"] is True
        assert kwargs["review_only"] is False
        assert kwargs["reviewers"] == "codex,claude"
        assert kwargs["reviewer"] == "codex"
        assert kwargs["fixer"] == "claude"
        assert kwargs["max_review_rounds"] == 2
        assert kwargs["max_review_cost"] == 3.5
        assert kwargs["max_review_minutes"] == 12
        assert kwargs["require_final_fresh_review"] is True

    def test_review_loop_rejects_no_fix(self) -> None:
        runner = CliRunner()
        result = runner.invoke(
            checkup,
            [
                "--no-fix",
                "--pr",
                "https://github.com/o/r/pull/1",
                "--issue",
                "https://github.com/o/r/issues/2",
                "--review-loop",
            ],
            obj={},
        )

        assert result.exit_code != 0
        assert "cannot be combined with --no-fix" in result.output

    def test_review_only_reaches_agentic_checkup_and_allows_no_fix(self) -> None:
        runner = CliRunner()
        with patch(
            "pdd.commands.checkup.run_agentic_checkup",
            return_value=(True, "ok", 0.0, "model"),
        ) as run_mock:
            result = runner.invoke(
                checkup,
                [
                    "--no-fix",
                    "--pr",
                    "https://github.com/o/r/pull/1",
                    "--issue",
                    "https://github.com/o/r/issues/2",
                    "--review-loop",
                    "--review-only",
                    "--no-github-state",
                ],
                obj={},
            )

        assert result.exit_code == 0, result.output
        kwargs = run_mock.call_args.kwargs
        assert kwargs["review_loop"] is True
        assert kwargs["review_only"] is True
        assert kwargs["no_fix"] is True

    def test_review_only_requires_review_loop(self) -> None:
        runner = CliRunner()
        result = runner.invoke(
            checkup,
            [
                "--pr",
                "https://github.com/o/r/pull/1",
                "--issue",
                "https://github.com/o/r/issues/2",
                "--review-only",
            ],
            obj={},
        )

        assert result.exit_code != 0
        assert "--review-only requires --review-loop" in result.output


class TestCheckupReviewLoopRuntime:
    def _patch_io(self, monkeypatch: Any, tmp_path: Path) -> None:
        import pdd.checkup_review_loop as mod

        monkeypatch.setattr(mod, "_setup_pr_worktree", lambda *a, **k: (tmp_path, None))
        monkeypatch.setattr(
            mod,
            "_fetch_pr_metadata",
            lambda *a, **k: {
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
            },
        )
        monkeypatch.setattr(mod, "_commit_and_push_if_changed", lambda *a, **k: (True, "pushed"))
        monkeypatch.setattr(mod, "_post_review_loop_report", lambda *a, **k: None)

    def test_clean_pass_requires_primary_reviewer_only(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            calls.append((role, kwargs["label"]))
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, cost, model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert round(cost, 2) == 0.1
        assert model == "codex"
        assert "reviewer-status: codex=clean claude=fixer fresh-final=clean" in report
        assert ("codex", "checkup-review-loop-review-codex-round1") in calls
        assert not any("review-claude" in label for _, label in calls)
        assert not any("fresh-final" in label for _, label in calls)

    def test_cost_cap_after_review_stops_before_fixer_or_push(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[str] = []
        finding = {
            "severity": "medium",
            "area": "test",
            "location": "tests/test_flow.py:12",
            "evidence": "missing assertion",
            "finding": "The PR does not test the new workflow.",
            "required_fix": "Add a regression test.",
        }

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            calls.append(kwargs["label"])
            return True, _json("findings", [finding]), 1.0, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)
        monkeypatch.setattr(
            mod,
            "_commit_and_push_if_changed",
            lambda *a, **k: pytest.fail("must not push after review cost cap"),
        )

        success, report, cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_cost=0.5),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert cost == 1.0
        assert calls == ["checkup-review-loop-review-codex-round1"]
        assert "max-cost-reached: true" in report
        assert "issue_aligned: unknown" in report
        assert "Review loop stopped on a configured safety limit" not in report
        assert "The PR does not test the new workflow." in report

    def test_cost_cap_after_fixer_pushes_then_stops_before_verifier(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[str] = []
        finding = {
            "severity": "critical",
            "area": "api",
            "location": "pdd/api.py:5",
            "evidence": "missing guard",
            "finding": "The API accepts invalid input.",
            "required_fix": "Validate the input before use.",
        }

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append(label)
            if "fix-" in label:
                return True, '{"summary":"fixed","changed_files":["pdd/api.py"]}', 1.0, role
            return True, _json("findings", [finding]), 0.1, role

        pushes: List[str] = []

        monkeypatch.setattr(mod, "_run_role_task", fake_task)
        monkeypatch.setattr(
            mod,
            "_commit_and_push_if_changed",
            lambda *a, **k: pushes.append("pushed") or (True, "pushed"),
        )

        success, report, cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_cost=0.5),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert round(cost, 2) == 1.1
        assert calls == [
            "checkup-review-loop-review-codex-round1",
            "checkup-review-loop-fix-claude-for-codex-round1",
        ]
        assert pushes == ["pushed"]
        assert "max-cost-reached: true" in report
        assert "issue_aligned: unknown" in report
        assert "The API accepts invalid input." in report
        assert "verification=unverified" in report

    def test_codex_findings_are_given_to_claude_then_verified_by_codex(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []
        finding = {
            "severity": "medium",
            "area": "test",
            "location": "tests/test_flow.py:12",
            "evidence": "missing assertion",
            "finding": "The PR does not test the new workflow.",
            "required_fix": "Add a regression test.",
        }

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            if label == "checkup-review-loop-review-codex-round1":
                return True, _json("findings", [finding]), 0.1, role
            if label == "checkup-review-loop-fix-claude-for-codex-round1":
                return True, '{"summary":"fixed","changed_files":["tests/test_flow.py"]}', 0.2, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert ("claude", "checkup-review-loop-fix-claude-for-codex-round1") in calls
        assert ("codex", "checkup-review-loop-verify-codex-round1") in calls
        assert "reviewer-status: codex=clean claude=fixer fresh-final=clean" in report
        assert "The PR does not test the new workflow." not in report
        assert (
            "| info | fixed | - | No findings remain. | No fix required. | "
            "review-loop |"
        ) in report

    def test_unstructured_clean_verifier_is_repaired_and_closes_finding(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []
        finding = {
            "severity": "high",
            "area": "file",
            "location": "src/secrets.py:12",
            "evidence": "token is logged before redaction",
            "finding": "Diagnostics can leak a partial secret.",
            "required_fix": "Redact the full diagnostic before truncating.",
        }

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            if label == "checkup-review-loop-review-codex-round1":
                return True, _json("findings", [finding]), 0.1, role
            if label == "checkup-review-loop-fix-claude-for-codex-round1":
                return True, '{"summary":"fixed","changed_files":["src/secrets.py"]}', 0.2, role
            if label == "checkup-review-loop-verify-codex-round1":
                return True, "No issues remaining. Targeted tests passed.", 0.1, role
            if label == "checkup-review-loop-parse-repair-verify-codex-round1":
                return True, _json("clean"), 0.05, role
            return False, f"unexpected label {label}", 0.0, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert round(cost, 2) == 0.45
        assert (
            ("codex", "checkup-review-loop-parse-repair-verify-codex-round1")
            in calls
        )
        assert "reviewer-status: codex=clean claude=fixer fresh-final=clean" in report
        assert "Diagnostics can leak a partial secret." not in report

    def test_review_only_runs_primary_reviewer_without_fix_or_push(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        monkeypatch.setattr(mod, "_setup_pr_worktree", lambda *a, **k: (tmp_path, None))
        monkeypatch.setattr(
            mod,
            "_fetch_pr_metadata",
            lambda *a, **k: pytest.fail("metadata fetch"),
        )
        monkeypatch.setattr(
            mod,
            "_commit_and_push_if_changed",
            lambda *a, **k: pytest.fail("commit/push should not run"),
        )
        monkeypatch.setattr(mod, "_post_review_loop_report", lambda *a, **k: None)
        calls: List[Tuple[str, str]] = []
        finding = {
            "severity": "critical",
            "area": "workflow",
            "location": "pdd/foo.py:3",
            "evidence": "ev",
            "finding": "manual-style review found a workflow regression.",
            "required_fix": "Fix the workflow regression.",
        }

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            calls.append((role, kwargs["label"]))
            return True, _json("findings", [finding]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, cost, model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(review_only=True),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert round(cost, 2) == 0.1
        assert model == "codex"
        assert calls == [("codex", "checkup-review-loop-review-codex-round1")]
        assert "reviewer-status: codex=findings fresh-final=missing" in report
        assert "Review-only mode: primary reviewer reported findings." in report
        assert "manual-style review found a workflow regression." in report

    def test_required_reviewer_limit_defaults_to_failed_unknown_report(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            if role == "codex":
                return False, "rate limit exceeded", 0.0, ""
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "reviewer-status: codex=failed claude=fixer fresh-final=missing" in report
        assert "Primary reviewer codex could not complete" in report
        assert "issue_aligned: unknown" in report
        assert "No findings remain." not in report
        assert "Required review did not complete" in report

    def test_same_reviewer_and_fixer_is_rejected(self, tmp_path: Path) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(reviewer="codex", fixer="codex"),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "Primary reviewer and fixer must be different roles" in report
        assert "reviewer-status: codex=failed fresh-final=missing" in report

    def test_fixer_is_not_invoked_when_primary_reviewer_is_clean(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            calls.append((role, kwargs["label"]))
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "reviewer-status: codex=clean claude=fixer fresh-final=clean" in report
        assert not any(role == "claude" for role, _ in calls)

    def test_max_round_exhaustion_is_reported_with_open_findings(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        finding = {
            "severity": "medium",
            "area": "api",
            "location": "pdd/checkup.py:1",
            "evidence": "still broken",
            "finding": "The API still does not work.",
            "required_fix": "Make the API work.",
        }

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if "fix-" in label:
                return True, '{"summary":"attempted","changed_files":[]}', 0.1, role
            return True, _json("findings", [finding]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1, require_final_fresh_review=False),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "max-rounds-reached: true" in report
        assert "reviewer-status: codex=findings claude=fixer fresh-final=missing" in report
        assert "The API still does not work." in report

    def test_blocking_severities_prioritize_without_dropping_medium_findings(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """When the gate is narrowed to blocker+critical only, a medium finding
        is still sent to the fixer if the reviewer says it should be fixed."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []
        medium = {
            "severity": "medium",
            "area": "test",
            "location": "tests/test.py:1",
            "evidence": "ev",
            "finding": "non-blocking medium nit",
            "required_fix": "fix the medium finding",
        }
        normalized = mod._normalize_findings([medium], "codex", 1)[0]

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            calls.append((role, kwargs["label"]))
            if "fix-" in kwargs["label"]:
                assert "non-blocking medium nit" in instruction
                return True, json.dumps({
                    "summary": "fixed medium finding",
                    "changed_files": [],
                    "findings": [
                        {
                            "key": normalized.key,
                            "disposition": "fixed",
                            "rationale": "fixed despite not being in the priority list",
                        }
                    ],
                }), 0.1, role
            if "verify-" in kwargs["label"]:
                return True, _json("clean", []), 0.1, role
            return True, _json("findings", [medium]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(blocking_severities=("blocker", "critical")),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "reviewer-status: codex=clean claude=fixer fresh-final=clean" in report
        open_row = (
            "| medium | open | tests/test.py:1 | non-blocking medium nit | "
            "fix the medium finding | codex |"
        )
        assert "No findings remain." in report
        assert open_row not in report
        assert any("fix-" in label for _, label in calls)

    def test_widened_clean_states_cannot_ship_on_degraded_reviewer(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """`clean_reviewer_states` widening cannot override the hard
        not-clean states (failed/degraded/missing). Degraded reviewer keeps
        the loop from declaring all-clean."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            if role == "codex":
                return False, "rate limit exceeded", 0.0, ""
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(
                continue_on_reviewer_limit=True,
                clean_reviewer_states=("clean", "degraded"),
            ),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        # With --continue-on-reviewer-limit, rate/provider/context limit failures
        # are reported as degraded. They still are not clean, so there is no
        # fixer or final clean pass.
        assert "reviewer-status: codex=degraded" in report
        assert "issue_aligned: unknown" in report

    def test_failed_push_aborts_loop_without_running_verifier(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """A push failure must abort the loop before the verifier runs, so
        the verifier never sees a local-only commit and falsely reports fixed."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        monkeypatch.setattr(mod, "_setup_pr_worktree", lambda *a, **k: (tmp_path, None))
        monkeypatch.setattr(
            mod,
            "_fetch_pr_metadata",
            lambda *a, **k: {
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
            },
        )
        monkeypatch.setattr(
            mod, "_commit_and_push_if_changed", lambda *a, **k: (False, "auth failed")
        )
        monkeypatch.setattr(mod, "_post_review_loop_report", lambda *a, **k: None)

        calls: List[Tuple[str, str]] = []
        finding = {
            "severity": "blocker",
            "area": "api",
            "location": "pdd/foo.py:1",
            "evidence": "ev",
            "finding": "broken api",
            "required_fix": "fix it",
        }

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            if "review-codex" in label and "verify" not in label and "fresh-final" not in label:
                return True, _json("findings", [finding]), 0.1, role
            if "fix-" in label:
                return True, '{"summary":"x","changed_files":["pdd/foo.py"]}', 0.1, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        # Verifier label MUST NOT have been invoked after the failed push.
        assert not any("verify-codex" in label for _, label in calls)
        assert "auth failed" in report

    def test_failed_verifier_does_not_mark_findings_fixed(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """A failed verifier must not mark the original findings as
        fixed or declare the reviewer clean.  The finding must remain open and
        the reviewer status must reflect the verifier failure."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        finding = {
            "severity": "blocker",
            "area": "auth",
            "location": "pdd/auth.py:5",
            "evidence": "token not validated",
            "finding": "Token is not validated.",
            "required_fix": "Add token validation.",
        }

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if "verify-codex" in label:
                return False, "rate limit exceeded", 0.0, ""
            if "review-codex" in label:
                return True, _json("findings", [finding]), 0.1, role
            if "fix-" in label:
                return True, '{"summary":"attempted","changed_files":["pdd/auth.py"]}', 0.1, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        # Failed verifier must not produce a clean reviewer status.
        assert "codex=failed" in report
        # The finding must still be listed as open (not moved to fixed).
        assert "Token is not validated." in report

    def test_clean_primary_reviewer_does_not_spawn_fresh_final(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """A clean primary-reviewer pass satisfies the final gate without
        spawning another reviewer model."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[str] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append(label)
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "fresh-final=clean" in report
        assert not any("fresh-final" in label for label in calls)

    def test_partial_verify_marks_absent_original_findings_fixed(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """If a verifier only re-reports part of the original set, the absent
        original findings are fixed and only the remaining findings stay open."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        fixed = {
            "severity": "blocker",
            "area": "api",
            "location": "pdd/api.py:1",
            "evidence": "missing validation",
            "finding": "Finding A should be fixed.",
            "required_fix": "Fix A.",
        }
        still_open = {
            "severity": "blocker",
            "area": "api",
            "location": "pdd/api.py:2",
            "evidence": "missing auth",
            "finding": "Finding B should remain open.",
            "required_fix": "Fix B.",
        }

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if label == "checkup-review-loop-review-codex-round1":
                return True, _json("findings", [fixed, still_open]), 0.1, role
            if label == "checkup-review-loop-fix-claude-for-codex-round1":
                return True, '{"summary":"partially fixed","changed_files":[]}', 0.1, role
            if label == "checkup-review-loop-verify-codex-round1":
                return True, _json("findings", [still_open]), 0.1, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1, require_final_fresh_review=False),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "Finding B should remain open." in report
        assert "Finding A should be fixed." not in report

    def test_plain_text_verify_clean_clears_original_findings(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """A verifier's explicit plain-text clean marker must mark the original
        findings fixed, so a clean final report cannot still list them open."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        finding = {
            "severity": "medium",
            "area": "file",
            "location": "src/review_loop_demo.py:8",
            "evidence": "returns value.lower()",
            "finding": "Whitespace normalization is incomplete.",
            "required_fix": "Strip and collapse whitespace.",
        }

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if label == "checkup-review-loop-review-codex-round1":
                return True, _json("findings", [finding]), 0.1, role
            if label == "checkup-review-loop-fix-claude-for-codex-round1":
                return (
                    True,
                    '{"summary":"fixed","changed_files":["src/review_loop_demo.py"]}',
                    0.1,
                    role,
                )
            if label == "checkup-review-loop-verify-codex-round1":
                return True, "No actionable merge-blocking findings.", 0.1, role
            return True, "No actionable findings.", 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=2),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "reviewer-status: codex=clean claude=fixer fresh-final=clean" in report
        assert "Whitespace normalization is incomplete." not in report
        assert (
            "| info | fixed | - | No findings remain. | No fix required. | "
            "review-loop |"
        ) in report

    def test_repeated_rejection_loops_until_max_rounds(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """A fixer rejection is not final. The reviewer can keep the finding
        open, and the loop stops at max rounds instead of declaring clean."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        finding = {
            "severity": "blocker",
            "area": "workflow",
            "location": "pdd/review.py:9",
            "evidence": "reviewer still disagrees",
            "finding": "The workflow still rejects valid PRs.",
            "required_fix": "Make the verifier accept valid PRs.",
        }
        fix_calls: List[str] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if label.startswith("checkup-review-loop-review-codex"):
                return True, _json("findings", [finding]), 0.1, role
            if label.startswith("checkup-review-loop-fix-claude-for-codex"):
                fix_calls.append(label)
                key = mod._normalize_findings([finding], "codex", 1)[0].key
                return (
                    True,
                    json.dumps(
                        {
                            "summary": "not valid; preserving current behavior",
                            "changed_files": [],
                            "findings": [
                                {
                                    "key": key,
                                    "disposition": "not_valid",
                                    "rationale": "The existing behavior matches the API contract.",
                                }
                            ],
                        }
                    ),
                    0.1,
                    role,
                )
            if label.startswith("checkup-review-loop-verify-codex"):
                return True, _json("findings", [finding]), 0.1, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=3, require_final_fresh_review=False),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert len(fix_calls) == 3
        assert "max-rounds-reached: true" in report
        assert "reviewer-status: codex=findings claude=fixer fresh-final=missing" in report
        assert "| blocker | open | pdd/review.py:9 |" in report
        assert "### Fixer Rationale" in report
        assert "not_valid - The existing behavior matches the API contract." in report

    def test_artifacts_are_persisted_per_round(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Each reviewer/fixer/verifier writes prompt/output/findings; final
        report and final-state json land at the loop directory root."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        finding = {
            "severity": "blocker",
            "area": "api",
            "location": "pdd/foo.py:1",
            "evidence": "ev",
            "finding": "broken api",
            "required_fix": "fix it",
        }

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if "review-codex" in label and "verify" not in label and "fresh-final" not in label:
                return True, _json("findings", [finding]), 0.1, role
            if "fix-claude-for-codex" in label:
                return True, '{"summary":"x","changed_files":["pdd/foo.py"]}', 0.1, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, _report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )
        assert success is True

        artifacts_dir = tmp_path / ".pdd" / "checkup-review-loop" / "issue-2-pr-1"
        # Reviewer artifacts (prompt + output + normalized findings)
        for suffix in ("prompt.txt", "output.txt", "findings.json"):
            assert (artifacts_dir / f"round-1-review-codex.{suffix}").exists()
            assert (artifacts_dir / f"round-1-verify-codex.{suffix}").exists()
            assert (artifacts_dir / f"round-1-fix-claude-for-codex.{suffix}").exists()
        # Cumulative dedup snapshot
        assert (artifacts_dir / "dedup-state-round-1.json").exists()
        # Final outputs
        final_report = (artifacts_dir / "final-report.md").read_text()
        assert final_report.startswith("## Step 7/8: Review Loop Final Report")
        final_state = json.loads((artifacts_dir / "final-state.json").read_text())
        assert "reviewer_status" in final_state
        assert final_state["reviewer_status"]["codex"] == "clean"
        assert final_state["reviewer_status"]["claude"] == "fixer"
        assert final_state["active_reviewer"] == "codex"
        assert "findings" in final_state

    def test_reviewer_diagnostics_are_surfaced_in_report(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """A failed reviewer's stderr/exit-code must reach the final report."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)

        codex_stderr = (
            "rate limit exceeded\n"
            "error: openai responded with 429\n"
            "exit code 7"
        )

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            if role == "codex":
                return False, codex_stderr, 0.0, ""
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "### Reviewer Diagnostics" in report
        assert "rate-limit" in report
        assert "exit code: 7" in report
        assert "rate limit exceeded" in report
        assert "openai responded with 429" in report

    def test_fallback_reviewer_promotes_fixer_when_primary_fails_and_flag_set(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Fallback success must render clean adapter-facing reviewer statuses."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        labels: List[str] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            labels.append(kwargs["label"])
            if role == "codex":
                return False, "exit code 1\nauthentication failed", 0.0, ""
            return True, _json("clean"), 0.2, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(fallback_reviewer_on_failure=True),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert any(
            "fallback-claude" in label or "review-claude" in label
            for label in labels
        ), labels
        assert (
            "reviewer-status: codex=clean claude=clean fresh-final=clean"
            in report
        ), report
        assert "reviewer-status: codex=failed" not in report
        assert "claude=clean" in report
        assert "claude=fixer" not in report
        assert "fallback" in report.lower()
        assert "### Reviewer Diagnostics" in report
        assert "status overridden by fallback" in report
        assert "original=failed" in report
        assert "Primary reviewer codex could not complete" not in report
        assert "fresh-final: clean" in report or "fresh-final=clean" in report

    def test_fallback_does_not_trigger_on_degraded_status(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        roles_called: List[str] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            roles_called.append(role)
            if role == "codex":
                return False, "rate limit exceeded", 0.0, ""
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(
                fallback_reviewer_on_failure=True,
                continue_on_reviewer_limit=True,
            ),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "claude" not in roles_called, roles_called
        assert "codex=degraded" in report
        assert "claude=fixer" in report

    def test_fallback_disabled_preserves_legacy_failed_unknown_report(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        roles_called: List[str] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            roles_called.append(role)
            if role == "codex":
                return False, "rate limit exceeded", 0.0, ""
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "claude" not in roles_called, roles_called
        assert "reviewer-status: codex=failed claude=fixer fresh-final=missing" in report
        assert "Primary reviewer codex could not complete" in report
        assert "issue_aligned: unknown" in report
        assert "Required review did not complete" in report

    def test_fallback_success_yields_ship_verdict_via_cloud_adapter(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        import os
        import sys

        # Discover the pdd_cloud `checkup_verdict_adapter` portably so this
        # contract test runs on any developer checkout and on CI:
        #   1. `PDD_CLOUD_ROOT` env var (CI sets this explicitly when the
        #      sibling repo is checked out under a non-default name/path).
        #   2. Sibling repo: `<parent-of-pdd>/pdd_cloud/...` — the layout we
        #      use in both `~/Desktop/SF/{pdd,pdd_cloud}` and
        #      `~/Documents/{pdd,pdd_cloud}` checkouts.
        #   3. `~/pdd_cloud/...` as a final fallback for flat home layouts.
        # Each candidate is added to `sys.path` so `importorskip` resolves
        # against the first directory that actually contains the module.
        # When no candidate is present, `importorskip` skips cleanly.
        candidates: list[Path] = []
        env_root = os.environ.get("PDD_CLOUD_ROOT")
        if env_root:
            candidates.append(
                Path(env_root) / "extensions" / "github_pdd_app" / "src" / "services"
            )
        repo_root = Path(__file__).resolve().parents[1]
        candidates.append(
            repo_root.parent
            / "pdd_cloud"
            / "extensions"
            / "github_pdd_app"
            / "src"
            / "services"
        )
        candidates.append(
            Path.home()
            / "pdd_cloud"
            / "extensions"
            / "github_pdd_app"
            / "src"
            / "services"
        )
        for candidate in candidates:
            candidate_str = str(candidate)
            if candidate.is_dir() and candidate_str not in sys.path:
                sys.path.insert(0, candidate_str)
        adapter = pytest.importorskip("checkup_verdict_adapter")

        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            if role == "codex":
                return False, "exit code 1\nauthentication failed", 0.0, ""
            return True, _json("clean"), 0.2, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(fallback_reviewer_on_failure=True),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )
        assert success is True

        verdict = adapter.parse_checkup_report(report, exit_code=0)
        assert verdict.verdict == "ship", (verdict.verdict, verdict.reason)
        assert verdict.per_reviewer_status.get("codex") == "clean"
        assert verdict.per_reviewer_status.get("claude") == "clean"

    def test_diagnostics_tail_scrubs_secrets(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        leaky_output = (
            "exit code 7\n"
            "rate limit exceeded\n"
            "Authorization: Bearer sk-proj-AbCdEf1234567890XYZqwerty\n"
            "header X-API-Key: ghp_aBcDeFgHiJkLmNoPqRsTuVwXyZ012345\n"
            "fatal: openai responded with 429"
        )

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            if role == "codex":
                return False, leaky_output, 0.0, ""
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "rate limit exceeded" in report
        assert "openai responded with 429" in report
        assert "sk-proj-AbCdEf1234567890XYZqwerty" not in report
        assert "ghp_aBcDeFgHiJkLmNoPqRsTuVwXyZ012345" not in report
        assert "Bearer sk-proj-AbCdEf1234567890XYZqwerty" not in report
        assert "[REDACTED]" in report

    def test_reviewer_fallback_used_when_primary_fails(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            if role == "codex":
                return False, "ERROR: authentication failed: token expired", 0.0, ""
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(
                continue_on_reviewer_limit=True,
                reviewer_fallback="gemini",
            ),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "codex=degraded" in report
        assert "gemini=clean" in report
        assert "active-reviewer: gemini" in report
        assert "issue_aligned: true" in report
        assert "could not complete" not in report
        assert any(role == "gemini" for role, _ in calls)
        # End-to-end ship_degraded contract: the superseded primary's row
        # in the Per-Reviewer Status table MUST contain the literal
        # `optional` so the pdd_cloud `checkup_verdict_adapter` parser
        # drops codex from the required-reviewer set. Without this the
        # adapter's rule r1 trips on `codex=degraded` and the verdict is
        # forced to `unknown` — the exact failure #923 was opened against.
        assert (
            "| codex | degraded (optional, superseded by gemini) |" in report
        ), report

    def test_no_reviewer_fallback_preserves_legacy_behavior(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            if role == "codex":
                return False, "ERROR: authentication failed: token expired", 0.0, ""
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        # With continue_on_reviewer_limit=False (the _config default), an auth
        # error from the primary reviewer must land as "failed", not
        # "degraded". The earlier OR mask hid regressions in that gate.
        assert "codex=failed" in report
        assert "could not complete" in report
        # Legacy path: no fallback configured, no takeover, so the report
        # MUST NOT carry the `optional` annotation anywhere. If it did, a
        # verdict adapter could mis-classify a hard primary failure as
        # ship_degraded.
        assert "optional" not in report.lower(), report

    def test_reviewer_fallback_equal_to_fixer_is_ignored(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            calls.append((role, kwargs["label"]))
            if role == "codex":
                return False, "ERROR: authentication failed: token expired", 0.0, ""
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(reviewer_fallback="claude"),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "could not complete" in report
        assert not any(label.startswith("checkup-review-loop-review-claude") for _, label in calls)

    def test_reviewer_fallback_provider_alias_of_fixer_is_ignored(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            calls.append((role, kwargs["label"]))
            if role == "codex":
                return False, "ERROR: authentication failed: token expired", 0.0, ""
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(reviewer_fallback="anthropic"),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "could not complete" in report
        assert not any(label.startswith("checkup-review-loop-review-claude") for _, label in calls)
        assert not any(label.startswith("checkup-review-loop-review-anthropic") for _, label in calls)

    def test_reviewer_fallback_provider_alias_of_primary_is_ignored(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            calls.append((role, kwargs["label"]))
            return False, "ERROR: authentication failed: token expired", 0.0, ""

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(reviewer_fallback="openai"),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "could not complete" in report
        codex_review_calls = [
            label for _, label in calls
            if label.startswith("checkup-review-loop-review-codex")
        ]
        assert len(codex_review_calls) == 1

    def test_reviewer_fallback_normalized_alias_takes_over(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            calls.append((role, kwargs["label"]))
            if role == "codex":
                return False, "ERROR: authentication failed: token expired", 0.0, ""
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(reviewer_fallback="google"),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "gemini=clean" in report
        assert any(role == "gemini" for role, _ in calls)

    def test_reviewer_fallback_also_fails_breaks_loop(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            if role == "codex":
                return False, "ERROR: authentication failed: token expired", 0.0, ""
            if role == "gemini":
                return False, "network error: connection refused", 0.0, ""
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(
                continue_on_reviewer_limit=True,
                reviewer_fallback="gemini",
            ),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "codex=degraded" in report
        assert "gemini=degraded" in report
        assert "could not complete" in report
        assert "gemini" in report.lower()
        # Fallback ALSO failed — no successful takeover happened — so
        # neither row may be tagged `optional`. The verdict adapter must
        # continue to see both reviewers as required and short-circuit
        # to `unknown`; silently demoting one to optional would let a
        # fully-broken review-loop ship as ship_degraded.
        assert "optional" not in report.lower(), report

    def test_reviewer_fallback_takes_over_subsequent_rounds(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """After a successful fallback, the fallback role MUST drive every
        subsequent reviewer step — including this round's verify call and any
        later rounds — instead of retrying the original primary that already
        failed once. Spec: prompts/checkup_review_loop_python.prompt §11
        (reviewer_fallback)."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []
        gemini_review_calls = {"count": 0}

        finding = {
            "severity": "blocker",
            "reviewer": "gemini",
            "area": "code",
            "evidence": "test bait",
            "finding": "leftover TODO marker",
            "required_fix": "remove it",
            "location": "pdd/foo.py:1",
        }

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            # Round 1 review: codex (primary) auth-fails — triggers fallback.
            if role == "codex":
                return False, "ERROR: authentication failed: token expired", 0.0, ""
            # Gemini: first review-mode call returns findings (so the fixer
            # runs); every later gemini review-mode call (verify, next-round
            # review) returns clean so the loop terminates cleanly.
            if role == "gemini" and "-review-" in label:
                gemini_review_calls["count"] += 1
                if gemini_review_calls["count"] == 1:
                    return True, _json("findings", [finding]), 0.1, role
                return True, _json("clean"), 0.1, role
            # Verify and any other gemini call → clean. Fixer (claude) success.
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(
                continue_on_reviewer_limit=True,
                reviewer_fallback="gemini",
            ),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True

        # codex must only have been invoked once (the initial round-1 review
        # attempt that failed) — it must NOT be retried after the fallback
        # successfully takes over.
        codex_calls = [(role, label) for role, label in calls if role == "codex"]
        assert len(codex_calls) == 1, (
            f"codex must not be retried after fallback takeover; got {codex_calls!r}"
        )

        # The verify call following the fix MUST be driven by gemini (the
        # fallback), not codex. This is the load-bearing assertion: the
        # fallback role takes over the reviewer slot for the rest of the loop.
        verify_calls = [(role, label) for role, label in calls if "-verify-" in label]
        assert verify_calls, f"expected at least one verify-mode call; got {calls!r}"
        for role, label in verify_calls:
            assert role == "gemini", (
                f"verify must be driven by the fallback gemini, not {role}: {label}"
            )

        # The fixer (claude per _config default) must have run, addressing
        # gemini's findings — i.e. the fallback drives the fix step too.
        fix_calls = [(role, label) for role, label in calls if "-fix-" in label]
        assert fix_calls, f"expected a fix call; got {calls!r}"
        for _role, label in fix_calls:
            assert "for-gemini" in label, (
                f"fix must address gemini's findings (fallback as primary): {label}"
            )

        # Report should reflect codex preserved as degraded, gemini as clean.
        assert "codex=degraded" in report
        assert "gemini=clean" in report
        assert "active-reviewer: gemini" in report
        assert "issue_aligned: true" in report
        # And the takeover must propagate the verdict-adapter contract on
        # the multi-round path too (fix step + verify step + later rounds):
        # the superseded primary's row is tagged `optional` so the verdict
        # adapter's rule r1 ignores codex=degraded and r4 upgrades the
        # ship to ship_degraded.
        assert (
            "| codex | degraded (optional, superseded by gemini) |" in report
        ), report

    # ------------------------------------------------------------------
    # ``fixer_fallback`` (this PR). Mirrors ``reviewer_fallback`` from
    # #923: when the primary fixer can't address the reviewer's findings
    # (because a Claude Code subscription-tier credential is exhausted,
    # for instance) the loop dead-stops instead of trying a second
    # configured fixer. These tests pin the fallback contract.
    # ------------------------------------------------------------------

    def _finding(self) -> Dict[str, str]:
        return {
            "severity": "medium",
            "area": "test",
            "location": "tests/test_flow.py:12",
            "evidence": "missing assertion",
            "finding": "The PR does not test the new workflow.",
            "required_fix": "Add a regression test.",
        }

    def test_fixer_fallback_runs_when_primary_fails(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Primary fixer (claude) fails; configured ``fixer_fallback``
        (gemini) succeeds. The loop must NOT stop on the primary failure —
        it must invoke the fallback fixer and then continue into the
        verify pass.

        This test also pins two contracts the implementer claimed but no
        existing test verified:

        * ``state.fix_attempts_by_key[k]`` increments EXACTLY ONCE per
          logical fix round (not twice — even though both the primary and
          fallback ``FixResult`` are appended to ``state.fixes``). The
          counter is used by the no-progress/oscillation guard, and a
          double-bump would prematurely abort the loop on a perfectly
          healthy primary→fallback rotation.
        * ``state.fixes`` keeps BOTH ``FixResult`` rows after a
          successful fallback round so the audit trail records the
          credential rotation. The primary entry's ``success`` is
          ``False``; the fallback's is ``True`` and its ``fixer`` is the
          configured fallback role.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []
        finding = self._finding()

        # State-capture seam. ``run_checkup_review_loop`` doesn't return
        # state — wrap ``_finalize`` (which receives state at the call
        # site) to capture and forward. Cleaner than refactoring the
        # signature for one test.
        captured_state: List[Any] = []
        real_finalize = mod._finalize

        def capture_finalize(context_arg, state_arg, reviewers_arg, artifacts_dir_arg):
            captured_state.append(state_arg)
            return real_finalize(context_arg, state_arg, reviewers_arg, artifacts_dir_arg)

        monkeypatch.setattr(mod, "_finalize", capture_finalize)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            if label == "checkup-review-loop-review-codex-round1":
                return True, _json("findings", [finding]), 0.1, role
            if label == "checkup-review-loop-fix-claude-for-codex-round1":
                # Primary fixer hits subscription-tier credential exhaustion.
                return (
                    False,
                    'Exit code 1: {"api_error_status":429,"result":"You\'ve hit your limit · resets May 18, 11pm (UTC)"}',
                    0.0,
                    role,
                )
            if label == "checkup-review-loop-fix-gemini-for-codex-round1":
                # Fallback fixer succeeds.
                return True, '{"summary":"fixed","changed_files":["tests/test_flow.py"]}', 0.2, role
            # Subsequent verify and re-review calls are clean.
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(fixer_fallback="gemini"),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        # The fallback fixer's invocation MUST appear; this is the
        # load-bearing signal that ``_maybe_run_fallback_fixer`` fired.
        assert any(
            label == "checkup-review-loop-fix-gemini-for-codex-round1"
            for _, label in calls
        ), f"fixer_fallback did not run; calls={calls!r}"
        # The loop should not have dead-stopped on "could not address".
        assert "could not address" not in report

        # State-driven assertions: must have captured state via _finalize.
        assert captured_state, "_finalize was never called — cannot inspect state"
        state = captured_state[-1]

        # Finding 2: ``_record_fix_attempts`` must be called ONCE per
        # logical fix round (primary attempt). Calling it again for the
        # fallback would double-bump the per-finding counter and would
        # mis-trip the oscillation/no-progress guards downstream.
        assert state.fix_attempts_by_key, (
            "no fix_attempts recorded — primary should have incremented it once"
        )
        for key, count in state.fix_attempts_by_key.items():
            assert count == 1, (
                f"finding {key!r} bumped {count}× in one fix round; "
                f"expected 1× (primary records, fallback does not double-record)"
            )

        # Finding 4: ``state.fixes`` keeps BOTH FixResults — the failed
        # primary AND the succeeding fallback — so the audit trail
        # records the credential rotation.
        assert len(state.fixes) >= 2, (
            f"expected primary+fallback FixResults retained in state.fixes; "
            f"got len={len(state.fixes)}: {[f.fixer for f in state.fixes]!r}"
        )
        primary_entry = state.fixes[0]
        fallback_entry = state.fixes[1]
        assert primary_entry.fixer == "claude" and primary_entry.success is False, (
            f"primary FixResult expected (claude, success=False); got "
            f"({primary_entry.fixer}, success={primary_entry.success})"
        )
        assert fallback_entry.fixer == "gemini" and fallback_entry.success is True, (
            f"fallback FixResult expected (gemini, success=True); got "
            f"({fallback_entry.fixer}, success={fallback_entry.success})"
        )

    def test_fixer_fallback_resets_worktree_before_fallback_runs(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """When the primary fixer dead-stops (e.g. on credential
        exhaustion) it may have left partial edits in the worktree.
        Before invoking the fallback fixer the loop MUST run
        ``git reset --hard HEAD`` + ``git clean -fd`` on the worktree so
        the fallback runs from the same baseline as the primary did and
        the failed primary's untrusted edits cannot leak into the
        eventual ``_commit_and_push_if_changed`` call (codex iter-04 P1).
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []
        finding = self._finding()

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            if label == "checkup-review-loop-review-codex-round1":
                return True, _json("findings", [finding]), 0.1, role
            if label == "checkup-review-loop-fix-claude-for-codex-round1":
                return False, "primary credential-limit dead-stop", 0.0, role
            if label == "checkup-review-loop-fix-gemini-for-codex-round1":
                return True, '{"summary":"fixed","changed_files":["tests/test_flow.py"]}', 0.2, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        # Record all subprocess.run calls so we can assert the
        # reset+clean pair fires between primary failure and fallback
        # invocation. Keep the real subprocess.run behavior — the loop
        # invokes other ``git`` commands that must still succeed.
        real_run = subprocess.run
        subprocess_calls: List[List[str]] = []

        def recording_run(cmd: Any, *args: Any, **kwargs: Any):
            if isinstance(cmd, list):
                subprocess_calls.append(list(cmd))
            return real_run(cmd, *args, **kwargs)

        monkeypatch.setattr(mod.subprocess, "run", recording_run)

        run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(fixer_fallback="gemini"),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        # Locate the indices of the primary failure, the reset/clean
        # pair, and the fallback invocation. The reset+clean must sit
        # strictly between the two role tasks.
        role_labels = [label for _, label in calls]
        primary_idx = role_labels.index(
            "checkup-review-loop-fix-claude-for-codex-round1"
        )
        fallback_idx = role_labels.index(
            "checkup-review-loop-fix-gemini-for-codex-round1"
        )
        assert primary_idx < fallback_idx, (
            f"primary fixer must precede fallback; calls={role_labels!r}"
        )

        # Find a reset+clean pair anywhere in the recorded subprocess
        # calls. They are inserted before the fallback fires; with the
        # bug present, neither command would be issued.
        reset_calls = [
            c for c in subprocess_calls
            if len(c) >= 5 and c[0] == "git" and c[1] == "-C"
            and c[3:5] == ["reset", "--hard"]
        ]
        clean_calls = [
            c for c in subprocess_calls
            if len(c) >= 4 and c[0] == "git" and c[1] == "-C"
            and c[3] == "clean"
        ]
        assert reset_calls, (
            f"expected 'git reset --hard HEAD' before fallback; "
            f"recorded subprocess calls={subprocess_calls!r}"
        )
        assert clean_calls, (
            f"expected 'git clean -fd' before fallback; "
            f"recorded subprocess calls={subprocess_calls!r}"
        )

        # The reset+clean pair must appear in order, and the first
        # reset must precede the first clean.
        first_reset_idx = subprocess_calls.index(reset_calls[0])
        first_clean_idx = subprocess_calls.index(clean_calls[0])
        assert first_reset_idx < first_clean_idx, (
            f"reset must come before clean; "
            f"reset at {first_reset_idx}, clean at {first_clean_idx}"
        )

    def test_fixer_fallback_failure_is_recorded_in_state_fixes(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """When the configured ``fixer_fallback`` runs but also fails,
        its ``FixResult`` must still be appended to ``state.fixes`` so
        the audit trail and ``final-state.json`` show the attempt. A
        ``None`` fallback (never ran) is the only case that should NOT
        leave a row."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []
        finding = self._finding()

        captured_state: List[Any] = []
        real_finalize = mod._finalize

        def capture_finalize(context_arg, state_arg, reviewers_arg, artifacts_dir_arg):
            captured_state.append(state_arg)
            return real_finalize(context_arg, state_arg, reviewers_arg, artifacts_dir_arg)

        monkeypatch.setattr(mod, "_finalize", capture_finalize)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            if label == "checkup-review-loop-review-codex-round1":
                return True, _json("findings", [finding]), 0.1, role
            if label == "checkup-review-loop-fix-claude-for-codex-round1":
                return (
                    False,
                    'Exit code 1: {"api_error_status":429,"result":"You\'ve hit your limit · resets May 18, 11pm (UTC)"}',
                    0.0,
                    role,
                )
            if label == "checkup-review-loop-fix-gemini-for-codex-round1":
                return False, "gemini fixer also failed", 0.05, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(fixer_fallback="gemini"),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "fallback fixer gemini also failed" in report
        assert captured_state, "_finalize was never called — cannot inspect state"
        state = captured_state[-1]
        assert len(state.fixes) >= 2, (
            f"failed fallback must still be appended to state.fixes; "
            f"got len={len(state.fixes)}: {[f.fixer for f in state.fixes]!r}"
        )
        primary_entry, fallback_entry = state.fixes[0], state.fixes[1]
        assert primary_entry.fixer == "claude" and primary_entry.success is False
        assert fallback_entry.fixer == "gemini" and fallback_entry.success is False, (
            f"failed fallback FixResult expected (gemini, success=False); got "
            f"({fallback_entry.fixer}, success={fallback_entry.success})"
        )

    def test_fixer_fallback_not_configured_breaks_loop(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Regression guard for the legacy behavior: with no
        ``fixer_fallback`` configured, the loop MUST still break with a
        ``Fixer ... could not address ...`` stop reason."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []
        finding = self._finding()

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            if label == "checkup-review-loop-review-codex-round1":
                return True, _json("findings", [finding]), 0.1, role
            if label == "checkup-review-loop-fix-claude-for-codex-round1":
                return False, "fixer failed for unrelated reason", 0.0, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "could not address" in report
        # No fallback was configured; no gemini fixer attempt is allowed.
        assert not any(
            label.startswith("checkup-review-loop-fix-gemini-")
            for _, label in calls
        ), f"gemini must not run when fixer_fallback is unset; calls={calls!r}"

    def test_fixer_fallback_same_as_primary_skips(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """When ``fixer_fallback == fixer``, the fallback would be a
        no-op retry on the same role that just failed. Skip it."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []
        finding = self._finding()

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            if "review-codex" in label:
                return True, _json("findings", [finding]), 0.1, role
            if "fix-claude" in label:
                return False, "fixer failed", 0.0, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(fixer_fallback="claude"),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "could not address" in report
        # Only the primary fix-claude call may exist; no second attempt.
        claude_fix_calls = [
            label for _, label in calls
            if label.startswith("checkup-review-loop-fix-claude-")
        ]
        assert len(claude_fix_calls) == 1, (
            f"primary fixer must not be retried as its own fallback; got "
            f"{claude_fix_calls!r}"
        )

    def test_fixer_fallback_normalizes_anthropic_alias_against_claude(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """``--fixer claude --fixer-fallback anthropic`` MUST be treated as
        the same provider — promoting ``anthropic`` to fallback after
        ``claude`` failed would be a no-op retry on the same OAuth
        credential that just hit a subscription-tier weekly limit.
        ``_normalize_reviewers`` maps the alias (``anthropic``) to its
        canonical role (``claude``), so the equality check must operate
        on normalized roles, not literal strings.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []
        finding = self._finding()

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            if "review-codex" in label:
                return True, _json("findings", [finding]), 0.1, role
            if "fix-claude" in label:
                return False, "fixer failed", 0.0, role
            # Any anthropic fix attempt would have its own label; falling
            # through here as "clean" would let it succeed and mask the bug.
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(fixer_fallback="anthropic"),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        # Only ONE fix invocation total (the primary) — fallback skipped
        # because ``anthropic`` normalizes to the same role as ``claude``.
        fix_calls = [
            label for _, label in calls
            if label.startswith("checkup-review-loop-fix-")
        ]
        assert len(fix_calls) == 1, (
            f"expected exactly one fix attempt (primary, no alias fallback); "
            f"got {fix_calls!r}"
        )
        assert "could not address" in report

    def test_fixer_fallback_normalizes_canonical_role(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """``--fixer-fallback Gemini`` (mixed case) or ``--fixer-fallback
        OpenAI`` (provider alias) MUST be canonicalised before reaching
        ``_run_fix`` and ``state.active_fixer``. Downstream code does a
        case-sensitive ``ROLE_TO_PROVIDER.get(role, role)`` lookup — if a
        raw ``"Gemini"`` leaks through, the provider table misses, an
        invalid provider is spawned, and the fallback fails opaquely
        instead of running. The execution path must see the lowercase
        canonical role even when the operator typed an alias or odd
        casing.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []
        finding = self._finding()

        captured_state: List[Any] = []
        real_finalize = mod._finalize

        def capture_finalize(context_arg, state_arg, reviewers_arg, artifacts_dir_arg):
            captured_state.append(state_arg)
            return real_finalize(context_arg, state_arg, reviewers_arg, artifacts_dir_arg)

        monkeypatch.setattr(mod, "_finalize", capture_finalize)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            if label == "checkup-review-loop-review-codex-round1":
                return True, _json("findings", [finding]), 0.1, role
            if label == "checkup-review-loop-fix-claude-for-codex-round1":
                return False, "fixer failed", 0.0, role
            # Fallback path. The label MUST be the lowercase canonical
            # role (``gemini``) — not ``Gemini`` — for the run to
            # succeed at all. If the raw alias leaks through, this
            # branch never matches and the assertion below fires.
            if label == "checkup-review-loop-fix-gemini-for-codex-round1":
                return True, '{"summary":"fixed","changed_files":["tests/test_flow.py"]}', 0.2, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            # Mixed case + provider-name input — both must canonicalise
            # to ``gemini`` before execution.
            config=_config(fixer_fallback="Gemini"),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        fix_labels = [label for _, label in calls if "-fix-" in label]
        assert "checkup-review-loop-fix-gemini-for-codex-round1" in fix_labels, (
            f"fallback did not run with canonical 'gemini' role; "
            f"fix labels seen: {fix_labels!r}"
        )
        # No raw "Gemini" label may appear — that would mean the raw
        # alias reached ``_run_fix`` and we'd be back to the bug.
        assert not any("fix-Gemini" in label for _, label in calls), (
            f"raw 'Gemini' leaked into fix invocation; calls={calls!r}"
        )

        assert captured_state, "_finalize was never called — cannot inspect state"
        state = captured_state[-1]

        # Active-fixer promotion must store the canonical role so later
        # rounds dispatch to a provider the lookup table knows.
        assert state.active_fixer == "gemini", (
            f"state.active_fixer expected 'gemini' (canonical); "
            f"got {state.active_fixer!r}"
        )

        # And the audited FixResult should record the canonical role too.
        fallback_entries = [f for f in state.fixes if f.fixer == "gemini"]
        assert fallback_entries, (
            f"no FixResult recorded with canonical 'gemini' fixer; "
            f"got fixers={[f.fixer for f in state.fixes]!r}"
        )

    def test_fixer_fallback_unknown_role_skips_safely(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """An unrecognized ``fixer_fallback`` (typo, removed provider,
        etc.) MUST be skipped rather than passed through to ``_run_fix``.
        ``ROLE_TO_PROVIDER`` would otherwise return the raw string as
        the provider name, which crashes opaquely. The loop should fall
        through to its normal "could not address" termination instead.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []
        finding = self._finding()

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            if "review-codex" in label:
                return True, _json("findings", [finding]), 0.1, role
            if "fix-claude" in label:
                return False, "fixer failed", 0.0, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(fixer_fallback="not-a-real-role"),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        # Loop terminates on the primary failure; the bogus fallback is
        # never invoked.
        assert success is True
        assert "could not address" in report
        assert not any(
            "fix-not-a-real-role" in label for _, label in calls
        ), f"unknown fallback role should not be executed; calls={calls!r}"

    def test_fixer_fallback_same_as_reviewer_skips(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """When ``fixer_fallback == reviewer``, promoting the reviewer to
        author the fix would collapse the reviewer/fixer role independence
        the review loop exists to enforce. Skip it."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []
        finding = self._finding()

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            if "review-codex" in label:
                return True, _json("findings", [finding]), 0.1, role
            if "fix-claude" in label:
                return False, "fixer failed", 0.0, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(fixer_fallback="codex"),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "could not address" in report
        # codex must NOT have authored a fix. Only its review (and any
        # later verify) calls are allowed.
        codex_fix_calls = [
            label for _, label in calls
            if label.startswith("checkup-review-loop-fix-codex-")
        ]
        assert not codex_fix_calls, (
            f"reviewer must not be promoted to fixer fallback; got {codex_fix_calls!r}"
        )

    def test_fixer_fallback_is_one_shot_across_rounds(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Once the fallback fixer has taken over (succeeded in a prior
        round) it MUST drive every subsequent fix call instead of the
        exhausted primary. The fallback contract is one-shot: re-invoking
        the original primary in round N+1 just to burn another fallback
        invocation defeats the purpose, because credential-limit reset
        windows are hours-to-days. Track this via ``state.active_fixer``
        (parallel to ``state.active_reviewer``).
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []
        finding = self._finding()

        # Capture state via _finalize hook so we can assert active_fixer.
        captured_state: List[Any] = []
        real_finalize = mod._finalize

        def capture_finalize(context_arg, state_arg, reviewers_arg, artifacts_dir_arg):
            captured_state.append(state_arg)
            return real_finalize(context_arg, state_arg, reviewers_arg, artifacts_dir_arg)

        monkeypatch.setattr(mod, "_finalize", capture_finalize)

        # Force the loop to do two fix rounds: round 1's verify still
        # reports findings (so the loop continues into round 2). In
        # round 2 it should NOT call the primary again — the fallback
        # has taken over.
        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            if "review-codex-round1" in label and "verify" not in label:
                return True, _json("findings", [finding]), 0.1, role
            if label == "checkup-review-loop-fix-claude-for-codex-round1":
                # Primary fixer dead-stops on credential exhaustion.
                return False, "primary credential-limit dead-stop", 0.0, role
            if label == "checkup-review-loop-fix-gemini-for-codex-round1":
                # Fallback succeeds — should now drive round 2 too.
                return True, '{"summary":"fixed","changed_files":["a.py"]}', 0.2, role
            if "verify-codex-round1" in label:
                # Verify pass still has findings → loop continues.
                return True, _json("findings", [finding]), 0.1, role
            if label == "checkup-review-loop-fix-gemini-for-codex-round2":
                # Round 2 must use the fallback fixer (active_fixer).
                return True, '{"summary":"fixed","changed_files":["a.py"]}', 0.2, role
            if "verify-codex-round2" in label:
                return True, _json("clean"), 0.1, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(fixer_fallback="gemini"),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        labels = [label for _, label in calls]

        # Round 1 must exercise both the primary (failing) and the
        # fallback fixer (succeeding) — that's how the takeover gets
        # established in the first place.
        assert "checkup-review-loop-fix-claude-for-codex-round1" in labels, (
            f"round 1 primary fixer call missing; calls={labels!r}"
        )
        assert "checkup-review-loop-fix-gemini-for-codex-round1" in labels, (
            f"round 1 fallback fixer call missing; calls={labels!r}"
        )

        # The one-shot contract: round 2 MUST NOT re-invoke the primary
        # claude fixer. The exhausted credential has not reset (and the
        # loop has no way to know that anyway), so retrying it would
        # just consume another fallback invocation needlessly.
        assert "checkup-review-loop-fix-claude-for-codex-round2" not in labels, (
            f"primary fixer was re-invoked in round 2 despite fallback "
            f"takeover; calls={labels!r}"
        )

        # Round 2 must use the fallback as the active fixer.
        assert "checkup-review-loop-fix-gemini-for-codex-round2" in labels, (
            f"active fixer (gemini) did not drive round 2; calls={labels!r}"
        )

        # The fallback helper must run exactly ONCE across the whole
        # loop — round 2's gemini call comes from the main-loop
        # ``active_fixer`` override, not a second helper invocation.
        gemini_fix_calls = [
            label for label in labels
            if label.startswith("checkup-review-loop-fix-gemini-")
        ]
        assert len(gemini_fix_calls) == 2, (
            f"expected exactly one round-1 fallback + one round-2 takeover "
            f"call; got gemini fix calls={gemini_fix_calls!r}"
        )

        # The state must record the takeover so audit + later reasoning
        # can see who the active fixer is.
        assert captured_state, "_finalize was never called — cannot inspect state"
        state = captured_state[-1]
        assert state.active_fixer == "gemini", (
            f"state.active_fixer should be promoted to fallback role; "
            f"got {state.active_fixer!r}"
        )

    def test_fixer_fallback_reset_uses_pre_fix_sha(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """``git reset --hard HEAD`` is insufficient when the failed
        primary fixer creates a commit before returning failure: HEAD has
        already advanced past the safe pre-fix state, so the reset
        becomes a no-op and the failed primary's commit survives. The
        loop MUST capture the pre-fix SHA via ``git rev-parse HEAD``
        BEFORE the primary runs and reset back to that SHA instead.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        finding = self._finding()

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if label == "checkup-review-loop-review-codex-round1":
                return True, _json("findings", [finding]), 0.1, role
            if label == "checkup-review-loop-fix-claude-for-codex-round1":
                return False, "primary failed after committing", 0.0, role
            if label == "checkup-review-loop-fix-gemini-for-codex-round1":
                return True, '{"summary":"fixed","changed_files":["a.py"]}', 0.2, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        # Replace subprocess.run with a stub that records every command
        # and synthesizes the rev-parse output. We use a stub (not a
        # wrapper around the real subprocess.run) because tmp_path isn't
        # a real git repo — the real rev-parse would error and force the
        # safety fallback path. We want to verify the happy-path
        # behavior: rev-parse succeeds, returns a SHA, reset targets
        # that SHA.
        PRE_FIX_SHA = "0123456789abcdef0123456789abcdef01234567"
        subprocess_calls: List[List[str]] = []

        class _StubCompleted:
            def __init__(self, stdout: str = "", returncode: int = 0) -> None:
                self.stdout = stdout
                self.stderr = ""
                self.returncode = returncode

        def stub_run(cmd: Any, *args: Any, **kwargs: Any):
            if isinstance(cmd, list):
                subprocess_calls.append(list(cmd))
                if len(cmd) >= 4 and cmd[0] == "git" and cmd[3] == "rev-parse":
                    return _StubCompleted(stdout=f"{PRE_FIX_SHA}\n")
            return _StubCompleted()

        monkeypatch.setattr(mod.subprocess, "run", stub_run)

        run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(fixer_fallback="gemini"),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        # The reset must target the captured pre-fix SHA, not the literal
        # string "HEAD". With the bug present, the failed primary's
        # commit would survive the reset and leak into the fallback's
        # push.
        reset_calls = [
            c for c in subprocess_calls
            if len(c) >= 5 and c[0] == "git" and c[1] == "-C"
            and c[3:5] == ["reset", "--hard"]
        ]
        assert reset_calls, (
            f"expected a git reset --hard call before the fallback; "
            f"calls={subprocess_calls!r}"
        )
        # The reset target is the 6th argument (index 5).
        reset_target = reset_calls[0][5]
        assert reset_target == PRE_FIX_SHA, (
            f"reset must target the captured pre-fix SHA {PRE_FIX_SHA!r}, "
            f"not {reset_target!r}; with bare 'HEAD' a failed-primary "
            f"commit would survive the reset"
        )

        # A rev-parse HEAD call must precede the reset so the SHA was
        # actually captured (and not pulled from somewhere stale).
        rev_parse_calls = [
            c for c in subprocess_calls
            if len(c) >= 4 and c[0] == "git" and c[3] == "rev-parse"
        ]
        assert rev_parse_calls, (
            f"expected a git rev-parse HEAD before reset; "
            f"calls={subprocess_calls!r}"
        )
        first_rev_parse_idx = subprocess_calls.index(rev_parse_calls[0])
        first_reset_idx = subprocess_calls.index(reset_calls[0])
        assert first_rev_parse_idx < first_reset_idx, (
            f"rev-parse must precede reset; rev-parse at {first_rev_parse_idx}, "
            f"reset at {first_reset_idx}"
        )

    def test_fixer_fallback_budget_exhausted(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """When the budget is already exhausted at the moment the primary
        fixer fails, the fallback must NOT be attempted. The stop reason
        must mention budget exhaustion so the operator sees what gated
        the fallback."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []
        finding = self._finding()

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            if "review-codex" in label:
                return True, _json("findings", [finding]), 0.1, role
            if "fix-claude" in label:
                # Spend the entire $0.30 budget on the primary fixer call
                # so the fallback budget guard trips.
                return False, "fixer failed", 0.30, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(fixer_fallback="gemini", max_cost=0.30),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        # The fallback must NOT have run — the budget gate cut it off.
        assert not any(
            label.startswith("checkup-review-loop-fix-gemini-")
            for _, label in calls
        ), f"fallback fixer must not run after budget exhaustion; calls={calls!r}"
        # The report MUST mention budget exhaustion as the proximate cause
        # so operators know the fallback was gated, not silently skipped.
        assert "max-cost-reached: true" in report

    def test_reviewer_fallback_excludes_active_fixer(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """The reviewer-fallback explicit-path conditional must exclude
        ``state.active_fixer`` (already promoted by an earlier fixer-fallback
        success) on top of the original ``fixer`` and ``reviewer`` exclusions.
        Otherwise a config that names the same role for both
        ``--fixer-fallback`` and ``--reviewer-fallback`` could end up with
        the fixer-fallback role reviewing its own fixes — collapsing the
        reviewer/fixer independence the loop exists to preserve.

        This is a defense-in-depth guard: today's main-loop control flow
        keeps ``pending_findings`` populated after the first round so the
        review-path conditional is hard to reach a second time, but the
        invariant — fallback != active_fixer — must hold for the
        conditional regardless of which path the loop arrives through.
        We assert by pre-seeding ``state.active_fixer`` BEFORE the
        round-1 review fails, then checking the explicit-fallback path
        refuses to promote that same role into the reviewer slot.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[Tuple[str, str]] = []

        # State-capture seam: also use it to side-set ``state.active_fixer``
        # the moment the primary reviewer's failure is recorded, which is
        # the spot the explicit-fallback path runs against. This simulates
        # "fixer-fallback already promoted gemini in a logically prior
        # step" without forcing the main loop through an unreachable
        # pending-findings interleaving.
        captured_state: List[Any] = []
        real_record_review = mod._record_review

        def record_then_seed(state_arg: Any, review_arg: Any) -> Any:
            result = real_record_review(state_arg, review_arg)
            if state_arg.active_fixer is None:
                state_arg.active_fixer = "gemini"
            return result

        monkeypatch.setattr(mod, "_record_review", record_then_seed)

        real_finalize = mod._finalize

        def capture_finalize(context_arg, state_arg, reviewers_arg, artifacts_dir_arg):
            captured_state.append(state_arg)
            return real_finalize(context_arg, state_arg, reviewers_arg, artifacts_dir_arg)

        monkeypatch.setattr(mod, "_finalize", capture_finalize)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append((role, label))
            # Round 1 review: primary reviewer codex auth-fails so the
            # explicit reviewer-fallback conditional is exercised.
            if role == "codex":
                return False, "ERROR: authentication failed: token expired", 0.0, ""
            # Any gemini review-mode call is exactly the regression we are
            # guarding against — returning clean keeps the loop from
            # diverging, but the assertion below fails loud if gemini ever
            # gets called as a reviewer.
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, _report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(
                continue_on_reviewer_limit=True,
                fixer_fallback="gemini",
                reviewer_fallback="gemini",
            ),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert captured_state, "_finalize was never called — cannot inspect state"
        state = captured_state[-1]

        # Pre-seeded active_fixer must still be gemini — nothing in the
        # loop should have cleared it.
        assert state.active_fixer == "gemini", (
            f"test seam should have set state.active_fixer to gemini; "
            f"got {state.active_fixer!r}"
        )

        # Load-bearing assertion: gemini must NOT have been promoted to the
        # active reviewer. The explicit reviewer-fallback path must refuse
        # to use a role that is already the active fixer.
        assert state.active_reviewer != "gemini", (
            f"reviewer-fallback must exclude state.active_fixer; "
            f"state.active_reviewer={state.active_reviewer!r}"
        )

        # gemini must never have been invoked as a reviewer. The label
        # prefix ``checkup-review-loop-review-`` is the marker for
        # review-mode invocations; ``-review-`` also appears in the
        # loop-wide prefix so we anchor on the canonical start.
        gemini_review_calls = [
            label for role, label in calls
            if role == "gemini"
            and label.startswith("checkup-review-loop-review-")
        ]
        assert not gemini_review_calls, (
            f"reviewer-fallback must skip role already active as fixer; "
            f"got gemini review calls={gemini_review_calls!r}"
        )

    def test_fixer_fallback_excludes_active_reviewer(self) -> None:
        """``_maybe_run_fallback_fixer`` already refuses to promote the
        ORIGINAL primary reviewer to author fixes (that would collapse the
        review loop's role independence). The same guard must extend to
        ``state.active_reviewer`` — once a reviewer-fallback has promoted a
        different role into the reviewer slot, the fixer-fallback must not
        name that promoted role either."""
        from pdd.checkup_review_loop import (
            FixResult,
            ReviewFinding,
            ReviewLoopState,
            _maybe_run_fallback_fixer,
        )
        import pdd.checkup_review_loop as mod

        # Original config: primary reviewer = codex, primary fixer = claude,
        # fixer_fallback = gemini. Reviewer-fallback already ran in a prior
        # round and promoted gemini into the reviewer slot — so a later
        # fixer-fallback that also names gemini must be skipped, otherwise
        # gemini would simultaneously review and fix.
        state = ReviewLoopState()
        state.active_reviewer = "gemini"

        finding = ReviewFinding(
            severity="medium",
            reviewer="gemini",
            area="test",
            evidence="missing assertion",
            finding="missing test",
            required_fix="add a test",
            location="tests/test_flow.py:12",
        )
        config = _config(fixer_fallback="gemini")
        ctx = _ctx(Path("/tmp"))

        # If the guard fires, ``_run_fix`` must NOT be called. Patch it to
        # explode so an accidental promotion would surface as a test failure
        # instead of a silent regression.
        def _explode(*_args: Any, **_kwargs: Any) -> Any:
            raise AssertionError(
                "_run_fix must not run when fixer-fallback collides with "
                "state.active_reviewer"
            )

        with patch.object(mod, "_run_fix", side_effect=_explode):
            result = _maybe_run_fallback_fixer(
                primary_fixer="claude",
                reviewer="codex",
                findings=[finding],
                context=ctx,
                worktree=Path("/tmp"),
                round_number=1,
                state=state,
                config=config,
                verbose=False,
                quiet=True,
                artifacts_dir=Path("/tmp"),
                deadline=float("inf"),
            )

        assert result is None, (
            f"fixer-fallback must skip role already active as reviewer; "
            f"got result={result!r}"
        )
        # state.active_fixer must stay unset — no promotion happened.
        assert state.active_fixer is None, (
            f"state.active_fixer must remain unset when fallback is skipped; "
            f"got {state.active_fixer!r}"
        )


class TestPromptInjection:
    """Reviewer and fixer prompts must reflect the configured gate, not the
    hard-coded default. Otherwise the LLM keeps flagging/fixing severities the
    user has narrowed off — the prompt/code drift this feature exists to
    prevent."""

    def _make_config(self, blocking: Tuple[str, ...]):
        from pdd.checkup_review_loop import ReviewLoopConfig

        return ReviewLoopConfig(blocking_severities=blocking)

    def test_review_prompt_lists_configured_blocking_severities(
        self, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import ReviewLoopState, _review_prompt

        context = _ctx(tmp_path)
        context.pr_content = "PR body: this implementation intentionally uses a safer direction."
        prompt = _review_prompt(
            reviewer="codex",
            context=context,
            round_number=1,
            state=ReviewLoopState(),
            config=self._make_config(("blocker", "critical")),
            mode="review",
            findings_to_verify=[],
        )

        assert "Highest-priority severities" in prompt
        assert "blocker, critical" in prompt
        assert "Evaluate issue intent" in prompt
        assert "underlying user problem" in prompt
        assert "Establish PR causality" in prompt
        assert "Pre-existing unrelated bugs" in prompt
        assert "newer authoritative issue comments" in prompt
        assert "scope lock" in prompt
        assert "manual request" in prompt
        assert "does not recreate the same bug class" in prompt
        assert "authoritative sources" in prompt
        assert "model/variant identity" in prompt
        assert "provider roots and aliases" in prompt
        assert "does not collapse distinct Arena variants" in prompt
        assert "Do not collapse independently actionable problems" in prompt
        assert "if maintainers accepted the\n  new direction" in prompt
        assert "Trace the source issue contract explicitly" in prompt
        assert "Trace user-facing option propagation end to end" in prompt
        assert "planning but dropped during execution" in prompt
        assert "runtime data-shape boundaries" in prompt
        assert "opaque dictionaries" in prompt
        assert "defensively coerces arrays" in prompt
        assert "`.map()`" in prompt
        assert "Check state and side-effect ordering" in prompt
        assert "caller-compatibility sweep" in prompt
        assert "targeted read-only-safe repros" in prompt
        assert "repository-local writable TMPDIR" in prompt
        assert "git diff --check" in prompt
        assert "Do not bury actionable failed checks" in prompt
        assert "Do not report external GitHub/CI readiness state" in prompt
        assert "pending/action-required workflow state" in prompt
        assert "out-of-scope operational state" in prompt
        assert "str(e)" in prompt
        assert "logger.warning" in prompt
        assert "redacts before slicing" in prompt
        assert "final runtime\n  environment" in prompt
        assert "this implementation intentionally uses a safer direction" in prompt
        # The narrowed gate must NOT include `medium` in the LLM-facing list.
        assert "blocker, critical, medium" not in prompt

    def test_verify_prompt_requires_full_rereview_until_round_limit(
        self, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import ReviewFinding, ReviewLoopState, _review_prompt

        prompt = _review_prompt(
            reviewer="codex",
            context=_ctx(tmp_path),
            round_number=2,
            state=ReviewLoopState(),
            config=self._make_config(("blocker", "critical")),
            mode="verify",
            findings_to_verify=[
                ReviewFinding(
                    severity="medium",
                    reviewer="codex",
                    area="workflow",
                    evidence="old evidence",
                    finding="Old finding",
                    required_fix="Fix old finding.",
                    round_number=1,
                )
            ],
        )

        assert "This is not a narrow checkbox verification" in prompt
        assert "Then perform a fresh full PR review again" in prompt
        assert "newly visible issues, missed issues" in prompt
        assert "Do not stop just because the previous findings look fixed" in prompt
        assert "repeat until you report no actionable findings" in prompt
        assert "configured max rounds (5, default 5)" in prompt

    def test_fix_prompt_lists_configured_blocking_severities(
        self, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import ReviewLoopState, _fix_prompt

        prompt = _fix_prompt(
            fixer="claude",
            reviewer="codex",
            findings=[],
            context=_ctx(tmp_path),
            round_number=1,
            state=ReviewLoopState(),
            config=self._make_config(("blocker",)),
        )

        assert "prioritizing the blocking severities\n(blocker)" in prompt
        assert "every valid" in prompt
        assert "Do not use\n\"focused\"" in prompt


class TestParseHelpers:
    def test_parse_severity_list_drops_unknowns_and_dedupes(self) -> None:
        from pdd.checkup_review_loop import parse_severity_list

        assert parse_severity_list("blocker,bogus,critical,blocker") == (
            "blocker",
            "critical",
        )
        assert parse_severity_list(None) == ("blocker", "critical", "medium")
        assert parse_severity_list("") == ("blocker", "critical", "medium")

    def test_parse_state_list_blocks_hard_not_clean_states(self) -> None:
        from pdd.checkup_review_loop import parse_state_list

        # Cannot allow ship on degraded/failed/missing — those tokens are
        # silently dropped from the input, never widened into clean_states.
        assert parse_state_list("clean,degraded,failed,missing,findings") == (
            "clean",
            "findings",
        )
        # Empty / all-rejected input falls back to default.
        assert parse_state_list("failed,degraded") == ("clean",)

    def test_failure_status_classifies_auth_error_as_degraded(self) -> None:
        from pdd.checkup_review_loop import _failure_status

        # ---- True positives: real infra-failure strings → "degraded".
        assert _failure_status(
            "ERROR: authentication failed: token expired", allow_degraded=True
        ) == "degraded"
        assert _failure_status(
            "network error: connection refused", allow_degraded=True
        ) == "degraded"
        assert _failure_status(
            "exit code 127: command not found", allow_degraded=True
        ) == "degraded"
        assert _failure_status(
            "Command returned non-zero exit status 2", allow_degraded=True
        ) == "degraded"
        assert _failure_status(
            "process exited with status 64", allow_degraded=True
        ) == "degraded"
        assert _failure_status(
            "permission denied while creating sandbox", allow_degraded=True
        ) == "degraded"
        assert _failure_status(
            "Unauthorized: missing API key", allow_degraded=True
        ) == "degraded"
        assert _failure_status(
            "please log in to continue", allow_degraded=True
        ) == "degraded"
        assert _failure_status(
            "dns resolution failed for api.example.com", allow_degraded=True
        ) == "degraded"
        assert _failure_status(
            "failed to create sandbox: out of disk", allow_degraded=True
        ) == "degraded"

        # ---- True negatives: bait strings that the previous overly broad
        # markers ("auth", "login", "exit code", "subprocess") would have
        # falsely flagged. These must classify as "failed", not "degraded".
        assert _failure_status(
            "Author: Greg <g@example.com>\nfatal: stack trace", allow_degraded=True
        ) == "failed"
        assert _failure_status(
            "DEBUG: logging request payload", allow_degraded=True
        ) == "failed"
        # exit code 0 is a success-y context — must not be flagged degraded.
        assert _failure_status(
            "trace line: exit code 0: ok", allow_degraded=True
        ) == "failed"
        assert _failure_status(
            "trace line: exit status 0: ok", allow_degraded=True
        ) == "failed"
        # "subprocess" appearing in a traceback path must not flag degraded.
        assert _failure_status(
            "trace: subprocess.run() helper called", allow_degraded=True
        ) == "failed"

    def test_failure_status_unrelated_failure_still_failed(self) -> None:
        from pdd.checkup_review_loop import _failure_status

        assert _failure_status("diff parse error", allow_degraded=True) == "failed"

    def test_unparsable_reviewer_output_is_treated_as_failure(self) -> None:
        """When a reviewer returns success=True but output contains no JSON and
        no bracket findings, _parse_review_output must classify it as failed
        (or degraded), never as clean.  Spec §19: unparsable output must never
        count clean regardless of how clean_reviewer_states is widened."""
        from pdd.checkup_review_loop import HARD_NOT_CLEAN_STATES, _parse_review_output

        # Generic prose with no structure — should be "failed".
        result = _parse_review_output(
            "Everything looks fine, no issues.", "codex", 1
        )
        assert result.status in HARD_NOT_CLEAN_STATES, (
            f"Expected failure status, got {result.status!r}"
        )
        assert result.findings == []

        # Rate-limit prose — should be "degraded".
        result_rl = _parse_review_output(
            "Error: rate limit exceeded. Try again later.", "claude", 1
        )
        assert result_rl.status == "degraded"

    def test_explicit_plain_text_clean_markers_are_clean(self) -> None:
        """CLI agents sometimes return concise plain-text clean markers.
        Accept only the explicit forms seen in real runs, while generic prose
        remains covered by the unparsable-output failure test above."""
        from pdd.checkup_review_loop import _parse_review_output

        for output in (
            "Findings: none.\n\nFocused pytest passed.",
            "No actionable findings.\n\nThe PR now matches the issue.",
            "No actionable findings remain.\n\nThe PR now matches the issue.",
            (
                "No actionable code findings.\n\n"
                "The PR removes the raw debug preview and keeps redaction "
                "metadata aligned."
            ),
            "No actionable issues remain.\n\nThe PR now matches the issue.",
            (
                "**Findings**\n\n"
                "No actionable findings. The PR appears aligned with the issue.\n\n"
                "**Verification**\n\nPassed locally."
            ),
            (
                "**Findings**\n\n"
                "No actionable issues found. The PR aligns with the issue and "
                "the prior finding is fixed.\n\n"
                "**Verification**\n\nPassed:\n- pytest"
            ),
            "No actionable merge-blocking findings.\n\nThe PR now matches the issue.",
            "**Findings**\n\nNo actionable PR findings.\n\nThe PR now matches the issue.",
            "No actionable pull request findings remain.\n\nThe PR now matches the issue.",
            "No open findings remain.\n\nThe PR now matches the issue.",
        ):
            result = _parse_review_output(output, "codex", 1)
            assert result.status == "clean"
            assert result.findings == []

    def test_plain_text_clean_marker_with_infra_failure_is_not_clean(self) -> None:
        """A clean-marker line accompanied by an auth/network/sandbox/exit-code
        failure must not be classified as clean — the plain-text path must
        block on the same transient markers `_failure_status` recognizes.

        Regression for #923: previously `_plain_text_clean_review` only
        rejected rate-limit/quota/timeout markers, so an auth or network
        failure that appeared in the same output as a "No actionable
        findings." line slipped past the fallback path."""
        from pdd.checkup_review_loop import HARD_NOT_CLEAN_STATES, _parse_review_output

        infra_failure_outputs = (
            "No actionable findings.\nERROR: authentication failed: token expired",
            "No actionable findings.\nnetwork error: connection refused",
            "No actionable findings.\npermission denied while creating sandbox",
            "No actionable findings.\nUnauthorized: missing API key",
            "No actionable findings.\nfailed to create sandbox: out of disk",
            "No actionable findings.\nCommand returned non-zero exit status 2",
        )
        for output in infra_failure_outputs:
            result = _parse_review_output(output, "codex", 1)
            assert result.status in HARD_NOT_CLEAN_STATES, (
                f"Expected non-clean status for {output!r}, got {result.status!r}"
            )

        # Negative control: a clean marker without any infra failure stays clean.
        result = _parse_review_output(
            "No actionable findings.\n\nThe PR now matches the issue.",
            "codex",
            1,
        )
        assert result.status == "clean"
        assert result.findings == []

    def test_markdown_severity_bullets_are_parsed_as_findings(self) -> None:
        """Codex CLI can return markdown bullets instead of the requested JSON."""
        from pdd.checkup_review_loop import _parse_review_output

        output = """**Findings**
- Medium: [src/review_loop_demo.py](/tmp/work/src/review_loop_demo.py:8) only lowercases the label and preserves whitespace.
- Medium: [tests/test_review_loop_demo.py](/tmp/work/tests/test_review_loop_demo.py:6) only tests lowercasing.
"""
        result = _parse_review_output(output, "codex", 1)

        assert result.status == "findings"
        assert len(result.findings) == 2
        assert result.findings[0].severity == "medium"
        assert result.findings[0].location == "src/review_loop_demo.py:8"
        assert "only lowercases" in result.findings[0].finding

    def test_json_external_status_finding_is_filtered_to_clean(self) -> None:
        """GitHub check readiness is outside the code-fix review loop."""
        from pdd.checkup_review_loop import _parse_review_output

        payload = json.dumps(
            {
                "status": "findings",
                "issue_aligned": True,
                "summary": "checks pending",
                "findings": [
                    {
                        "severity": "info",
                        "area": "workflow",
                        "location": "",
                        "evidence": "auto-heal-pr ACTION_REQUIRED and github-app-ci IN_PROGRESS",
                        "finding": "PR readiness is not established because GitHub checks are pending.",
                        "required_fix": "Rerun Cloud Build or wait for required checks.",
                    }
                ],
            }
        )

        result = _parse_review_output(payload, "codex", 2)

        assert result.status == "clean"
        assert result.findings == []

    def test_markdown_external_status_finding_is_filtered_to_clean(self) -> None:
        """Markdown status-check findings should not keep the fixer looping."""
        from pdd.checkup_review_loop import _parse_review_output

        output = """**Findings**

1. Info: PR readiness is not established.
auto-heal-pr is ACTION_REQUIRED, github-app-ci is IN_PROGRESS, and Cloud Build has a pending check.
Required fix: rerun the external workflow.

**Verification**
Local tests passed.
"""

        result = _parse_review_output(output, "codex", 3)

        assert result.status == "clean"
        assert result.findings == []

    def test_external_status_filter_keeps_file_backed_workflow_finding(self) -> None:
        """Workflow findings with repository-file evidence are still actionable."""
        from pdd.checkup_review_loop import _parse_review_output

        payload = json.dumps(
            {
                "status": "findings",
                "issue_aligned": True,
                "summary": "workflow bug",
                "findings": [
                    {
                        "severity": "medium",
                        "area": "workflow",
                        "location": "pdd/agentic_sync.py:487",
                        "evidence": "The workflow status field is written before child failures are known.",
                        "finding": "Workflow status can be marked complete while checks are pending.",
                        "required_fix": "Move the status write after downstream failure handling.",
                    }
                ],
            }
        )

        result = _parse_review_output(payload, "codex", 1)

        assert result.status == "findings"
        assert len(result.findings) == 1
        assert result.findings[0].location == "pdd/agentic_sync.py:487"

    def test_plain_markdown_file_bullets_are_parsed_as_findings(self) -> None:
        """Codex may emit concrete Findings bullets without explicit severity."""
        from pdd.checkup_review_loop import _parse_review_output

        output = """**Findings**

- [pdd/commands/maintenance.py:268](/tmp/work/pdd/commands/maintenance.py:268) resolves `target_coverage` from the default context, then forwards it to every child `pdd sync`.

- [architecture.json:6925](/tmp/work/architecture.json:6925) documents `run_global_sync(...)` without the new `local: bool` parameter.

**Checks**
`git diff --check` passed.
"""
        result = _parse_review_output(output, "codex", 1)

        assert result.status == "findings"
        assert len(result.findings) == 2
        assert [finding.severity for finding in result.findings] == [
            "medium",
            "medium",
        ]
        assert result.findings[0].location == "pdd/commands/maintenance.py:268"
        assert "default context" in result.findings[0].finding
        assert result.findings[1].location == "architecture.json:6925"
        assert "git diff --check" not in result.findings[1].evidence

    def test_codex_priority_markdown_findings_are_parsed(self) -> None:
        """Codex CLI often emits PR review priorities like [P1]."""
        from pdd.checkup_review_loop import _parse_review_output

        output = """**Findings**
- [P1] [pdd/generate_model_catalog.py](/tmp/work/pdd/generate_model_catalog.py:873) does not fetch scores.
"""
        result = _parse_review_output(output, "codex", 1)

        assert result.status == "findings"
        assert len(result.findings) == 1
        assert result.findings[0].severity == "critical"
        assert result.findings[0].location == "pdd/generate_model_catalog.py:873"
        assert "does not fetch scores" in result.findings[0].finding

    def test_codex_finding_prefix_priority_without_section_is_parsed(self) -> None:
        """Codex exec can emit `Finding: [P2] ...` instead of JSON."""
        from pdd.checkup_review_loop import _parse_review_output

        output = """Finding: [P2] The prompt/architecture contract was not updated for the new step-comment API. `post_step_comment` now accepts `body`, but [agentic_common_python.prompt](/tmp/w/pdd/prompts/agentic_common_python.prompt:18) and [architecture.json](/tmp/w/architecture.json:73) still publish the old signature.

Checks: targeted tests passed.
"""
        result = _parse_review_output(output, "codex", 1)

        assert result.status == "findings"
        assert len(result.findings) == 1
        assert result.findings[0].severity == "medium"
        assert result.findings[0].location == "agentic_common_python.prompt:18"
        assert "step-comment API" in result.findings[0].finding
        assert "targeted tests" not in result.findings[0].evidence

    def test_priority_finding_stops_before_verification_section(self) -> None:
        """Verification summaries are not part of the preceding finding body."""
        from pdd.checkup_review_loop import _parse_review_output

        output = """**Findings**
- [P2] [env_setup.py](/tmp/work/env_setup.py:390) logs the trust flag from base env only.
  Add an attempt-level non-secret log after the final env is assembled.

**Checks**
- `git diff --check main...HEAD` passed.
- Pytest could not run because Python reported no usable temporary directory.
"""
        result = _parse_review_output(output, "codex", 1)

        assert result.status == "findings"
        assert len(result.findings) == 1
        assert result.findings[0].severity == "medium"
        assert result.findings[0].location == "env_setup.py:390"
        assert "attempt-level" in result.findings[0].evidence
        assert "Pytest could not run" not in result.findings[0].evidence

    def test_numbered_priority_findings_are_not_duplicated(self) -> None:
        """Numbered Codex headings with [P1]/[P2] should parse once."""
        from pdd.checkup_review_loop import _parse_review_output

        output = """**Findings**

1. [P1] PR is not merge-ready against current `main`.
`git merge-tree` shows conflicts in [HackathonEvent type](/tmp/w/frontend/src/types/hackathon.ts:131).

2. [P2] Project Gallery link points to a non-existent route.
[page.tsx:586](/tmp/w/frontend/src/app/hackathon/[eventId]/page.tsx:586) links to `/gallery`.

**Checks**
`git diff --check` reports trailing whitespace.
"""
        result = _parse_review_output(output, "codex", 1)

        assert result.status == "findings"
        assert len(result.findings) == 2
        assert [finding.severity for finding in result.findings] == [
            "critical",
            "medium",
        ]
        assert result.findings[0].finding == "PR is not merge-ready against current `main`."
        assert result.findings[1].finding == "Project Gallery link points to a non-existent route."
        assert all("trailing whitespace" not in finding.evidence for finding in result.findings)

    def test_codex_finding_prefix_priority_is_parsed(self) -> None:
        """Codex can prefix priority headings with 'Finding:'."""
        from pdd.checkup_review_loop import _parse_review_output

        output = """**Findings**

Finding: [P2] Fallback comments still bypass sanitization.
Trigger: `post_step_comment(..., body=None)` receives failure output containing a token assignment.
Evidence: [pdd/agentic_common.py:3410](/tmp/w/pdd/agentic_common.py:3410) builds fallback from raw output.

Checks:
`git diff --check` passed.
"""
        result = _parse_review_output(output, "codex", 1)

        assert result.status == "findings"
        assert len(result.findings) == 1
        finding = result.findings[0]
        assert finding.severity == "medium"
        assert finding.finding == "Fallback comments still bypass sanitization."
        assert finding.location == "pdd/agentic_common.py:3410"
        assert "token assignment" in finding.evidence
        assert "git diff --check" not in finding.evidence

    def test_multiple_finding_prefix_priority_blocks_stay_separate(self) -> None:
        """`Finding: [P*]` headings without priority colons split cleanly."""
        from pdd.checkup_review_loop import _parse_review_output

        output = """Finding: [P1] First issue
Evidence: [pdd/a.py:10](/tmp/w/pdd/a.py:10) detail.

Finding: [P2] Second issue
Evidence: [pdd/b.py:20](/tmp/w/pdd/b.py:20) detail.
"""
        result = _parse_review_output(output, "codex", 1)

        assert result.status == "findings"
        assert len(result.findings) == 2
        assert result.findings[0].severity == "critical"
        assert result.findings[0].finding == "First issue"
        assert result.findings[0].location == "pdd/a.py:10"
        assert "Second issue" not in result.findings[0].evidence
        assert result.findings[1].severity == "medium"
        assert result.findings[1].finding == "Second issue"
        assert result.findings[1].location == "pdd/b.py:20"

    def test_bold_priority_colon_bullets_keep_embedded_location(self) -> None:
        """Codex can emit '- **P1:** sentence with inline file links."""
        from pdd.checkup_review_loop import _parse_review_output

        output = """**Findings**
- **P1:** Nested `.pddrc` context resolution can use the wrong root. In [pdd/agentic_sync.py](/tmp/w/pdd/agentic_sync.py:653), `_detect_context_from_basename()` is called without `pddrc_path`.

- **P2:** `architecture.json` is stale for the new `local` parameter. The code signature includes `local` in [pdd/agentic_sync.py](/tmp/w/pdd/agentic_sync.py:487), but metadata omits it at [architecture.json](/tmp/w/architecture.json:6925).

**Checks**
- `git diff --check` passed.
"""
        result = _parse_review_output(output, "codex", 1)

        assert result.status == "findings"
        assert len(result.findings) == 2
        assert result.findings[0].severity == "critical"
        assert result.findings[0].finding.startswith("Nested `.pddrc`")
        assert result.findings[0].location == "pdd/agentic_sync.py:653"
        assert result.findings[1].severity == "medium"
        assert result.findings[1].location == "pdd/agentic_sync.py:487"
        assert "git diff --check" not in result.findings[1].evidence

    def test_manual_numbered_severity_findings_are_parsed(self) -> None:
        """Manual Codex reviews often use numbered Blocking/High findings."""
        from pdd.checkup_review_loop import _parse_review_output

        output = """Findings
1. Blocking: [pdd/generate_model_catalog.py](/tmp/work/pdd/generate_model_catalog.py:743) variant normalization collapses high/default scores.
2. High: manifest provenance is too weak for a source-of-truth file.
3. Low: a doc sentence is stale.
"""
        result = _parse_review_output(output, "codex", 1)

        assert result.status == "findings"
        assert [finding.severity for finding in result.findings] == [
            "blocker",
            "critical",
            "low",
        ]
        assert result.findings[0].location == "pdd/generate_model_catalog.py:743"
        assert "source-of-truth" in result.findings[1].finding

    def test_bold_codex_priority_findings_are_parsed(self) -> None:
        """Codex sometimes emits bold priority labels instead of bracket labels."""
        from pdd.checkup_review_loop import _parse_review_output

        output = """**Findings**

- **P1: Manifest entries are not auditable enough.**
  [pdd/data/arena_elo_manifest.json](/tmp/w/pdd/data/arena_elo_manifest.json:14) has generic provenance.

- **P2: Static fallback still drives public rows.**
  The fallback table leaks into generated output.
"""
        result = _parse_review_output(output, "codex", 1)

        assert result.status == "findings"
        assert [finding.severity for finding in result.findings] == [
            "critical",
            "medium",
        ]
        assert "Manifest entries" in result.findings[0].finding
        assert result.findings[0].location == "pdd/data/arena_elo_manifest.json:14"
        assert "generic provenance" in result.findings[0].evidence
        assert "Static fallback" in result.findings[1].finding

    def test_numbered_bold_codex_findings_without_severity_are_parsed(self) -> None:
        """Codex can return numbered finding headings with no explicit severity."""
        from pdd.checkup_review_loop import _parse_review_output

        output = """**Findings**

1. **Requirements updates are never saved.**
[pdd/incremental_architecture_orchestrator.py](/tmp/w/pdd/incremental_architecture_orchestrator.py:969) records filenames but never writes modified prompts.

2. **Tag sync corrupts prompts with multi-line blocks.**
[pdd/incremental_architecture_orchestrator.py](/tmp/w/pdd/incremental_architecture_orchestrator.py:216) stops at the opening tag.

**Checks Run**
Read-only parsing checks.
"""
        result = _parse_review_output(output, "codex", 1)

        assert result.status == "findings"
        assert len(result.findings) == 2
        assert result.findings[0].severity == "medium"
        assert result.findings[0].finding == "Requirements updates are never saved."
        assert (
            result.findings[0].location
            == "pdd/incremental_architecture_orchestrator.py:969"
        )

    def test_freeform_blocking_numbered_heading_is_blocker(self) -> None:
        """Manual reviews can prefix a numbered heading with a severity phrase."""
        from pdd.checkup_review_loop import _parse_review_output

        output = """Findings

3. Blocking workflow hole: failed Requirements propagation still refreshes the PRD fingerprint.
[pdd/incremental_architecture_orchestrator.py](/tmp/w/pdd/incremental_architecture_orchestrator.py:1151) saves the hash after warnings.
"""
        result = _parse_review_output(output, "codex", 1)

        assert result.status == "findings"
        assert len(result.findings) == 1
        assert result.findings[0].severity == "blocker"
        assert "failed Requirements propagation" in result.findings[0].finding

    def test_numbered_bold_severity_heading_keeps_body_and_location(self) -> None:
        """Bold numbered severity headings should preserve evidence paragraphs."""
        from pdd.checkup_review_loop import _parse_review_output

        output = """**Findings**

1. **High: Total-budget sync reports failure after exact-budget success.**
[pdd/agentic_sync_runner.py](/tmp/w/pdd/agentic_sync_runner.py:458) marks exhausted when remaining budget is zero.
Repro with one module returning success and cost `1.0` under `total_budget=1.0` returns failure.

**Checks**
AST parsing passed.
"""
        result = _parse_review_output(output, "codex", 1)

        assert result.status == "findings"
        assert len(result.findings) == 1
        assert result.findings[0].severity == "critical"
        assert (
            result.findings[0].location
            == "pdd/agentic_sync_runner.py:458"
        )
        assert result.findings[0].finding.startswith("Total-budget")
        assert "Repro with one module" in result.findings[0].evidence
        assert "AST parsing passed" not in result.findings[0].evidence

    def test_json_status_failed_with_no_findings_is_not_rewritten_clean(self) -> None:
        """When the LLM returns valid JSON with status='failed' and an empty findings
        list, the status must NOT be rewritten to 'clean'.  The JSON-success path
        had the same class of bug as the no-JSON path: the condition
        `if status not in {"clean", "findings"}` would rewrite "failed" to "clean"
        when no blocking findings were present.  Spec §19 applies equally here."""
        import json
        from pdd.checkup_review_loop import HARD_NOT_CLEAN_STATES, _parse_review_output

        payload = json.dumps({"status": "failed", "findings": []})
        output = f"```json\n{payload}\n```"
        result = _parse_review_output(output, "codex", 1)
        assert result.status in HARD_NOT_CLEAN_STATES, (
            f"Expected hard-not-clean status, got {result.status!r}"
        )

        # Same with status="degraded" — must not become "clean".
        payload_deg = json.dumps({"status": "degraded", "findings": []})
        output_deg = f"```json\n{payload_deg}\n```"
        result_deg = _parse_review_output(output_deg, "claude", 1)
        assert result_deg.status in HARD_NOT_CLEAN_STATES, (
            f"Expected hard-not-clean status, got {result_deg.status!r}"
        )


class TestPushWithRetryClonedRemote:
    """The review loop pushes to a PR head repo's clone URL, not `origin`.
    Verify push_with_retry handles that path including the auth-retry."""

    def test_push_with_retry_first_attempt_success_uses_clone_url(self, tmp_path: Path) -> None:
        from pdd.agentic_e2e_fix_orchestrator import push_with_retry

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run") as mock_run:
            mock_run.return_value = type(
                "Result", (), {"returncode": 0, "stdout": "", "stderr": ""}
            )()
            success, err = push_with_retry(
                tmp_path,
                repo_owner="o",
                repo_name="r",
                remote="https://github.com/o/r.git",
                refspec="HEAD:feature",
                set_upstream=False,
            )

        assert success is True
        assert err == ""
        cmd = mock_run.call_args.args[0]
        assert cmd == ["git", "push", "https://github.com/o/r.git", "HEAD:feature"]

    def test_push_with_retry_url_remote_uses_token_inline_on_auth_failure(
        self, tmp_path: Path, monkeypatch: Any
    ) -> None:
        """When the remote is a URL (clone_url path used by review-loop), the
        token-rewrite happens inline in the push command — not via
        `git remote set-url`. This guarantees no tokenized URL is ever stored
        in git config for that remote."""
        from pdd.agentic_e2e_fix_orchestrator import push_with_retry

        token_file = tmp_path / "tok"
        token_file.write_text("ghs_secret\n")
        monkeypatch.setenv("PDD_GH_TOKEN_FILE", str(token_file))

        cmds: List[List[str]] = []

        def fake_run(cmd: List[str], **_kwargs: Any):
            cmds.append(list(cmd))
            if cmd[:2] == ["git", "push"]:
                if "x-access-token" in (cmd[2] if len(cmd) > 2 else ""):
                    return type(
                        "R", (), {"returncode": 0, "stdout": "", "stderr": ""}
                    )()
                return type(
                    "R",
                    (),
                    {
                        "returncode": 1,
                        "stdout": "",
                        "stderr": "fatal: Authentication failed",
                    },
                )()
            return type("R", (), {"returncode": 0, "stdout": "", "stderr": ""})()

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run", side_effect=fake_run):
            success, _err = push_with_retry(
                tmp_path,
                repo_owner="o",
                repo_name="r",
                remote="https://github.com/o/r.git",
                refspec="HEAD:feature",
                set_upstream=False,
            )

        assert success is True
        # Token-bearing URL was used in the retry push.
        retry_cmds = [c for c in cmds if c[:2] == ["git", "push"] and len(c) >= 3]
        assert any("x-access-token:" in c[2] for c in retry_cmds)
        # No `git remote set-url` was issued for the URL remote.
        assert not any(c[:3] == ["git", "remote", "set-url"] for c in cmds)


class TestCommitAndPushIfChanged:
    def test_fetch_first_rebases_and_retries_push(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        import pdd.checkup_review_loop as mod

        metadata = {
            "clone_url": "https://github.com/o/r.git",
            "head_ref": "feature",
            "head_owner": "o",
            "head_repo": "r",
        }
        monkeypatch.setattr(mod, "_git_changed_files", lambda _worktree: ["pdd/foo.py"])

        pushes: List[Tuple[str, str, bool]] = []

        def fake_push(_worktree: Path, **kwargs: Any) -> Tuple[bool, str]:
            pushes.append((
                kwargs["remote"],
                kwargs["refspec"],
                kwargs["force_with_lease_on_non_fast_forward"],
            ))
            if len(pushes) == 1:
                return (
                    False,
                    " ! [rejected] HEAD -> feature (fetch first)\n"
                    "hint: Updates were rejected because the remote contains "
                    "work that you do not have locally.",
                )
            return True, ""

        runs: List[List[str]] = []

        def fake_run(cmd: List[str], **_kwargs: Any):
            runs.append(list(cmd))
            return type("R", (), {"returncode": 0, "stdout": "", "stderr": ""})()

        monkeypatch.setattr(mod, "push_with_retry", fake_push)
        monkeypatch.setattr(mod.subprocess, "run", fake_run)

        success, message = mod._commit_and_push_if_changed(
            tmp_path,
            metadata,
            "fix: address findings",
        )

        assert success is True
        assert "rebasing" in message
        assert pushes == [
            ("https://github.com/o/r.git", "HEAD:feature", False),
            ("https://github.com/o/r.git", "HEAD:feature", False),
        ]
        assert [
            "git",
            "fetch",
            "--no-tags",
            "https://github.com/o/r.git",
            "refs/heads/feature",
        ] in runs
        assert ["git", "rebase", "--onto", "FETCH_HEAD", "HEAD~1", "HEAD"] in runs

    def test_non_fast_forward_rebases_instead_of_force_push(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        import pdd.checkup_review_loop as mod

        metadata = {
            "clone_url": "https://github.com/o/r.git",
            "head_ref": "feature",
            "head_owner": "o",
            "head_repo": "r",
        }
        monkeypatch.setattr(mod, "_git_changed_files", lambda _worktree: ["pdd/foo.py"])

        pushes: List[Tuple[str, str, bool]] = []

        def fake_push(_worktree: Path, **kwargs: Any) -> Tuple[bool, str]:
            pushes.append((
                kwargs["remote"],
                kwargs["refspec"],
                kwargs["force_with_lease_on_non_fast_forward"],
            ))
            if len(pushes) == 1:
                return (
                    False,
                    " ! [rejected] HEAD -> feature (non-fast-forward)\n"
                    "hint: Updates were rejected because the tip of your "
                    "current branch is behind.",
                )
            return True, ""

        runs: List[List[str]] = []

        def fake_run(cmd: List[str], **_kwargs: Any):
            runs.append(list(cmd))
            return type("R", (), {"returncode": 0, "stdout": "", "stderr": ""})()

        monkeypatch.setattr(mod, "push_with_retry", fake_push)
        monkeypatch.setattr(mod.subprocess, "run", fake_run)

        success, message = mod._commit_and_push_if_changed(
            tmp_path,
            metadata,
            "fix: address findings",
        )

        assert success is True
        assert "rebasing" in message
        assert pushes == [
            ("https://github.com/o/r.git", "HEAD:feature", False),
            ("https://github.com/o/r.git", "HEAD:feature", False),
        ]
        assert [
            "git",
            "fetch",
            "--no-tags",
            "https://github.com/o/r.git",
            "refs/heads/feature",
        ] in runs
        assert ["git", "rebase", "--onto", "FETCH_HEAD", "HEAD~1", "HEAD"] in runs

    def test_fetch_first_rebase_failure_aborts_before_second_push(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        import pdd.checkup_review_loop as mod

        metadata = {
            "clone_url": "https://github.com/o/r.git",
            "head_ref": "feature",
            "head_owner": "o",
            "head_repo": "r",
        }
        monkeypatch.setattr(mod, "_git_changed_files", lambda _worktree: ["pdd/foo.py"])

        pushes = 0

        def fake_push(_worktree: Path, **_kwargs: Any) -> Tuple[bool, str]:
            nonlocal pushes
            pushes += 1
            return False, " ! [rejected] HEAD -> feature (fetch first)"

        runs: List[List[str]] = []

        def fake_run(cmd: List[str], **_kwargs: Any):
            runs.append(list(cmd))
            if cmd[:2] == ["git", "rebase"] and "--abort" not in cmd:
                return type("R", (), {"returncode": 1, "stdout": "", "stderr": "conflict"})()
            return type("R", (), {"returncode": 0, "stdout": "", "stderr": ""})()

        monkeypatch.setattr(mod, "push_with_retry", fake_push)
        monkeypatch.setattr(mod.subprocess, "run", fake_run)

        success, message = mod._commit_and_push_if_changed(
            tmp_path,
            metadata,
            "fix: address findings",
        )

        assert success is False
        assert pushes == 1
        assert "Failed to rebase fixes" in message
        assert ["git", "rebase", "--abort"] in runs

    def test_fetch_auth_retries_with_tokenized_exact_branch_ref(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        import pdd.checkup_review_loop as mod

        metadata = {
            "clone_url": "https://github.com/o/r.git",
            "head_ref": "feature",
            "head_owner": "o",
            "head_repo": "r",
        }
        token_file = tmp_path / "token"
        token_file.write_text("ghs_secret", encoding="utf-8")
        monkeypatch.setenv("PDD_GH_TOKEN_FILE", str(token_file))
        monkeypatch.setattr(mod, "_git_changed_files", lambda _worktree: ["pdd/foo.py"])

        pushes = 0

        def fake_push(_worktree: Path, **_kwargs: Any) -> Tuple[bool, str]:
            nonlocal pushes
            pushes += 1
            return (pushes > 1, " ! [rejected] HEAD -> feature (fetch first)")

        runs: List[List[str]] = []

        def fake_run(cmd: List[str], **_kwargs: Any):
            runs.append(list(cmd))
            if cmd[:3] == ["git", "fetch", "--no-tags"]:
                if "x-access-token" not in cmd[3]:
                    return type(
                        "R",
                        (),
                        {
                            "returncode": 1,
                            "stdout": "",
                            "stderr": "fatal: could not read Username",
                        },
                    )()
            return type("R", (), {"returncode": 0, "stdout": "", "stderr": ""})()

        monkeypatch.setattr(mod, "push_with_retry", fake_push)
        monkeypatch.setattr(mod.subprocess, "run", fake_run)

        success, message = mod._commit_and_push_if_changed(
            tmp_path,
            metadata,
            "fix: address findings",
        )

        assert success is True
        assert "rebasing" in message
        fetches = [cmd for cmd in runs if cmd[:3] == ["git", "fetch", "--no-tags"]]
        assert fetches[0] == [
            "git",
            "fetch",
            "--no-tags",
            "https://github.com/o/r.git",
            "refs/heads/feature",
        ]
        assert "x-access-token" in fetches[1][3]
        assert fetches[1][4] == "refs/heads/feature"
        assert ["git", "rebase", "--onto", "FETCH_HEAD", "HEAD~1", "HEAD"] in runs

    def test_fetch_auth_failure_redacts_token_in_error(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        import pdd.checkup_review_loop as mod

        token_file = tmp_path / "token"
        token_file.write_text("ghs_secret", encoding="utf-8")
        monkeypatch.setenv("PDD_GH_TOKEN_FILE", str(token_file))

        def fake_run(cmd: List[str], **_kwargs: Any):
            if cmd[:3] == ["git", "fetch", "--no-tags"] and "x-access-token" not in cmd[3]:
                return type(
                    "R",
                    (),
                    {
                        "returncode": 1,
                        "stdout": "",
                        "stderr": "fatal: could not read Username",
                    },
                )()
            return type(
                "R",
                (),
                {
                    "returncode": 1,
                    "stdout": "",
                    "stderr": "fatal: https://x-access-token:ghs_secret@github.com/o/r.git failed",
                },
            )()

        monkeypatch.setattr(mod.subprocess, "run", fake_run)

        success, message = mod._fetch_pr_head_for_rebase(
            tmp_path,
            clone_url="https://github.com/o/r.git",
            head_ref="feature",
            repo_owner="o",
            repo_name="r",
        )

        assert success is False
        assert "ghs_secret" not in message
        assert "[REDACTED]" in message

    def test_push_with_retry_can_leave_non_fast_forward_to_caller(
        self, tmp_path: Path
    ) -> None:
        from pdd.agentic_e2e_fix_orchestrator import push_with_retry

        calls: List[List[str]] = []

        def fake_run(cmd: List[str], **_kwargs: Any):
            calls.append(list(cmd))
            return type(
                "R",
                (),
                {
                    "returncode": 1,
                    "stdout": "",
                    "stderr": " ! [rejected] HEAD -> feature (non-fast-forward)",
                },
            )()

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run", side_effect=fake_run):
            success, err = push_with_retry(
                tmp_path,
                repo_owner="o",
                repo_name="r",
                remote="https://github.com/o/r.git",
                refspec="HEAD:feature",
                set_upstream=False,
                force_with_lease_on_non_fast_forward=False,
            )

        assert success is False
        assert "non-fast-forward" in err
        assert not any("--force-with-lease" in cmd for cmd in calls)


class TestStaticAnalysisCandidateFindingsIntegration:
    """The AST drift scan must actually reach the reviewer prompt that
    `_run_review` sends to the role.  Mocks `_run_role_task` and asserts
    the prompt the mock receives carries the new static-analysis section
    when the worktree contains drift, and omits it when it does not.
    """

    def _make_drift_worktree(self, tmp_path: Path) -> Path:
        worktree = tmp_path / "wt"
        worktree.mkdir()
        sample = worktree / "pkg" / "sample.py"
        sample.parent.mkdir(parents=True)
        sample.write_text(
            'ENV_KEYS = ["FOO", "BAR", "BAZ"]\n'
            "\n"
            "def _canonical_env_keys():\n"
            '    return ["FOO", "BAR", "BAZ", "QUX", "QUUX"]\n',
            encoding="utf-8",
        )
        return worktree

    def test_drift_candidates_are_embedded_in_prompt_when_present(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        import pdd.checkup_review_loop as mod
        from pdd.checkup_review_loop import (
            ReviewLoopState,
            _run_review,
        )

        worktree = self._make_drift_worktree(tmp_path)
        artifacts_dir = tmp_path / "artifacts"
        artifacts_dir.mkdir()

        # Stub the PR diff resolver to claim our drift fixture is the
        # PR-touched file (avoids needing a real git repo for the test).
        # The production code uses ``_pr_changed_python_files`` to derive
        # the change set from ``git diff --name-only BASE...HEAD``.
        monkeypatch.setattr(
            mod,
            "_pr_changed_python_files",
            lambda _wt, _pr_metadata=None: ["pkg/sample.py"],
        )

        captured: Dict[str, str] = {}

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            captured["prompt"] = instruction
            return True, _json("clean"), 0.0, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        _run_review(
            reviewer="codex",
            context=_ctx(tmp_path),
            worktree=worktree,
            round_number=1,
            state=ReviewLoopState(),
            config=_config(),
            verbose=False,
            quiet=True,
            artifacts_dir=artifacts_dir,
            mode="review",
            findings_to_verify=None,
            fix_result=None,
        )

        prompt = captured["prompt"]
        assert "Static-Analysis Candidate Findings" in prompt
        assert "ENV_KEYS" in prompt
        assert "_canonical_env_keys" in prompt
        # The missing items must be visible to the LLM.
        assert "QUX" in prompt and "QUUX" in prompt
        # And the candidate-findings JSON artifact must be persisted.
        artifact = (
            artifacts_dir
            / "round-1-review-static-analysis-candidates.json"
        )
        assert artifact.is_file()

    def test_no_static_section_when_changed_files_are_empty(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        import pdd.checkup_review_loop as mod
        from pdd.checkup_review_loop import (
            ReviewLoopState,
            _run_review,
        )

        worktree = tmp_path / "wt"
        worktree.mkdir()
        artifacts_dir = tmp_path / "artifacts"
        artifacts_dir.mkdir()

        # No PR-changed files -> no scan -> no section in the prompt.
        monkeypatch.setattr(
            mod,
            "_pr_changed_python_files",
            lambda _wt, _pr_metadata=None: [],
        )

        captured: Dict[str, str] = {}

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            captured["prompt"] = instruction
            return True, _json("clean"), 0.0, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        _run_review(
            reviewer="codex",
            context=_ctx(tmp_path),
            worktree=worktree,
            round_number=1,
            state=ReviewLoopState(),
            config=_config(),
            verbose=False,
            quiet=True,
            artifacts_dir=artifacts_dir,
            mode="review",
            findings_to_verify=None,
            fix_result=None,
        )

        assert "Static-Analysis Candidate Findings" not in captured["prompt"]

    def test_detector_fires_on_clean_pr_worktree_via_pr_diff(
        self, tmp_path: Path
    ) -> None:
        """Reviewer's blocker #1 (PR #899): the production path uses a fresh
        ``git fetch pull/N/head`` worktree where ``git status --porcelain``
        is empty by construction.  The detector must derive its changed-file
        list from the PR's merge-base diff (``git diff --name-only
        BASE...HEAD``) so it actually fires on committed changes.

        This test creates a real two-commit-on-a-branch scenario and asserts
        the detector fires WITHOUT staging any uncommitted edits.
        """
        import subprocess

        import pdd.checkup_review_loop as mod

        worktree = tmp_path / "wt"
        worktree.mkdir()

        def run(*args: str) -> None:
            subprocess.run(
                ["git", *args],
                cwd=worktree,
                check=True,
                capture_output=True,
            )

        run("init", "-q", "-b", "main")
        run("config", "user.email", "test@example.com")
        run("config", "user.name", "Test")

        # Base commit: only the canonical source exists.
        canonical = worktree / "pkg" / "common.py"
        canonical.parent.mkdir(parents=True)
        canonical.write_text(
            'CANONICAL = ("FOO", "BAR", "BAZ", "QUX", "QUUX")\n',
            encoding="utf-8",
        )
        run("add", ".")
        run("commit", "-q", "-m", "base")

        # Branch + PR commit: introduce the drift pattern.
        run("checkout", "-q", "-b", "pr-branch")
        bad_test = worktree / "tests" / "test_x.py"
        bad_test.parent.mkdir(parents=True)
        bad_test.write_text(
            'SUBSET = ["FOO", "BAR"]\n',
            encoding="utf-8",
        )
        run("add", ".")
        run("commit", "-q", "-m", "introduce drift")

        # Sanity: ``git status --porcelain`` is empty (the existing helper
        # would yield []), but ``git diff --name-only main...HEAD`` lists
        # the new test file.
        status_porcelain = subprocess.run(
            ["git", "status", "--porcelain"],
            cwd=worktree,
            capture_output=True,
            text=True,
            check=True,
        ).stdout
        assert status_porcelain.strip() == "", (
            "fresh PR worktree must be clean per ``git status``; this is "
            "the production shape that broke the detector"
        )

        artifacts = tmp_path / "artifacts"
        artifacts.mkdir()

        # Production call shape: invoke through the public collector with
        # the base branch resolved from the PR (here we pass it as a kwarg
        # / pr_metadata; see the implementation).  The fix must use the
        # merge-base diff rather than ``_git_changed_files``.
        results = mod._collect_static_analysis_candidate_findings(
            worktree,
            artifacts,
            round_number=1,
            mode="review",
            pr_metadata={"base_ref": "main"},
        )

        # We expect the cross-file pair to be detected even though the
        # canonical file is unchanged.  The new test file alone, when
        # combined with the canonical-source candidates picked up from
        # other Python files in the same package, must yield a finding.
        assert results, (
            "detector must fire on a real PR worktree using the merge-base "
            "diff (not ``git status --porcelain``)"
        )
        # The finding must be the SUBSET-vs-CANONICAL drift.
        names = {r["summary"] for r in results}
        assert any("SUBSET" in name and "CANONICAL" in name for name in names), (
            f"expected SUBSET vs CANONICAL drift, got: {names}"
        )
