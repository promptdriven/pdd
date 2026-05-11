"""Tests for ``pdd checkup --review-loop`` primary-reviewer/fixer mode."""

from __future__ import annotations

import json
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
        issue_body="Title: Fix the workflow\nDescription:\nMake it work.",
        repo_owner="o",
        repo_name="r",
        issue_number=2,
        issue_title="Fix the workflow",
        architecture="{}",
        extra_context="No .pddrc found.",
        pr_url="https://github.com/o/r/pull/1",
        pr_owner="o",
        pr_repo="r",
        pr_number=1,
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
            lambda *a, **k: ({
                "head": {"ref": "change/test", "repo": {"clone_url": "https://github.com/o/r.git", "owner": {"login": "o"}, "name": "r"}},
                "base": {"ref": "main"}
            }, ""),
        )
        monkeypatch.setattr(mod, "_commit_and_push_if_changed", lambda *a, **k: (True, "pushed"))
        monkeypatch.setattr(mod, "_post_to_github", lambda *a, **k: None)

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
        assert "issue_aligned: false" in report
        assert "Review loop stopped on a configured safety limit" not in report
        assert "The PR does not test the new workflow." in report

    def test_cost_cap_after_fixer_stops_before_commit_and_push(
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

        monkeypatch.setattr(mod, "_run_role_task", fake_task)
        monkeypatch.setattr(
            mod,
            "_commit_and_push_if_changed",
            lambda *a, **k: (True, "pushed"),
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
        assert "max-cost-reached: true" in report
        assert "issue_aligned: false" in report
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
        assert ("codex", "checkup-review-loop-verify-codex-round2") in calls
        assert "reviewer-status: codex=clean claude=fixer fresh-final=clean" in report
        assert "The PR does not test the new workflow." not in report

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
            if label == "checkup-review-loop-verify-codex-round2":
                return True, "No issues remaining. Targeted tests passed.", 0.1, role
            if "parse-repair" in label and "verify-codex-round2" in label:
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
            ("codex", "checkup-review-loop-verify-codex-round2 parse-repair")
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
        monkeypatch.setattr(mod, "_post_to_github", lambda *a, **k: None)
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
        assert "reviewer-status: codex=findings claude=fixer fresh-final=missing" in report
        assert "review-only mode reported findings" in report
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
        assert "reviewer-status: codex=clean claude=fixer fresh-final=clean" in report
        assert "Primary reviewer 'codex' was unavailable" in report
        assert "issue_aligned: true" in report

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
        assert "reviewer and fixer must be different roles" in report
        assert "reviewer-status: codex=failed codex=fixer fresh-final=missing" in report

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
        assert "reviewer-status: codex=findings claude=fixer fresh-final=findings" in report
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
        from pdd.checkup_review_loop import ReviewFinding
        finding_key = ReviewFinding(**medium).dedup_key()  # type: ignore

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            calls.append((role, kwargs["label"]))
            if "fix-" in kwargs["label"]:
                assert "non-blocking medium nit" in instruction
                return True, json.dumps({
                    "summary": "fixed medium finding",
                    "changed_files": [],
                    "dispositions": {
                        finding_key: "fixed"
                    },
                    "rationales": {
                        finding_key: "fixed despite not being in the priority list"
                    }
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
                reviewer_fallback=False,
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
        assert "issue_aligned: false" in report

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
            lambda *a, **k: ({
                "head": {"ref": "change/test", "repo": {"clone_url": "https://github.com/o/r.git", "owner": {"login": "o"}, "name": "r"}},
                "base": {"ref": "main"}
            }, ""),
        )
        monkeypatch.setattr(
            mod, "_commit_and_push_if_changed", lambda *a, **k: (False, "auth failed")
        )
        monkeypatch.setattr(mod, "_post_to_github", lambda *a, **k: None)

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
            config=_config(max_rounds=2, reviewer_fallback=False),
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
            config=_config(max_rounds=2, reviewer_fallback=False),
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
            if label == "checkup-review-loop-verify-codex-round2":
                return True, _json("findings", [still_open]), 0.1, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=2, require_final_fresh_review=False),
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
            if label == "checkup-review-loop-verify-codex-round2":
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

        from pdd.checkup_review_loop import ReviewFinding
        finding_key = ReviewFinding(**finding).dedup_key()  # type: ignore

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if label.startswith("checkup-review-loop-review-codex"):
                return True, _json("findings", [finding]), 0.1, role
            if label.startswith("checkup-review-loop-fix-claude-for-codex"):
                fix_calls.append(label)
                return (
                    True,
                    json.dumps(
                        {
                            "summary": "not valid; preserving current behavior",
                            "changed_files": [],
                            "dispositions": {
                                finding_key: "not_valid"
                            },
                            "rationales": {
                                finding_key: "The existing behavior matches the API contract."
                            }
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
        assert "reviewer-status: codex=findings claude=fixer fresh-final=findings" in report
        assert "| blocker | open | pdd/review.py:9 |" in report
        assert "### Fixer Rationale" in report
        assert "not_valid: The existing behavior matches the API contract." in report

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
            assert (artifacts_dir / f"round-2-verify-codex.{suffix}").exists()
            assert (artifacts_dir / f"round-1-fix-claude-for-codex.{suffix}").exists()
        # Cumulative dedup snapshot
        assert (artifacts_dir / "dedup-state-round-1.json").exists()
        # Final outputs
        final_report = (artifacts_dir / "final-report.md").read_text()
        assert final_report.startswith("## Step 7/8: Review Loop Final Report")
        final_state = json.loads((artifacts_dir / "final-state.json").read_text())
        assert "reviewer_status" in final_state
        assert final_state["reviewer_status"] == "clean"
        assert "findings" in final_state


class TestPromptInjection:
    """Reviewer and fixer prompts must reflect the configured gate, not the
    hard-coded default. Otherwise the LLM keeps flagging/fixing severities the
    user has narrowed off — the prompt/code drift this feature exists to
    prevent."""

    def _make_config(self, blocking: Tuple[str, ...]):
        from pdd.checkup_review_loop import ReviewLoopConfig

        return ReviewLoopConfig(blocking_severities=blocking)

    def test_build_review_prompt_lists_configured_blocking_severities(
        self, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import ReviewLoopState, _build_review_prompt

        context = _ctx(tmp_path)
        context.pr_content = "PR body: this implementation intentionally uses a safer direction."
        prompt = _build_review_prompt(
            mode="review",
            reviewer_role="codex",
            config=self._make_config(("blocker", "critical")),
            context=context,
            candidate_section="",
        )

        assert "Highest-priority severities" in prompt
        assert "blocker, critical" in prompt
        assert "Evaluate issue INTENT" in prompt
        assert "underlying user problem" in prompt
        assert "manual request" in prompt
        assert "recreates the same bug class" in prompt
        assert "authoritative sources" in prompt
        assert "model/variant identity" in prompt
        assert "provider roots and aliases" in prompt
        assert "does not collapse distinct Arena variants" in prompt
        assert "blocker, critical, medium" not in prompt

    def test_verify_prompt_requires_full_rereview_until_round_limit(
        self, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import ReviewFinding, ReviewLoopState, _build_review_prompt

        prompt = _build_review_prompt(
            reviewer_role="codex",
            context=_ctx(tmp_path),
            config=self._make_config(("blocker", "critical")),
            mode="verify",
            prior_findings=[
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
            candidate_section="",
            round_number=2,
        )

    def test_build_fixer_prompt_lists_configured_blocking_severities(
        self, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import ReviewLoopState, _build_fixer_prompt

        prompt = _build_fixer_prompt(
            fixer_role="claude",
            findings=[],
            context=_ctx(tmp_path),
            round_number=1,
            config=self._make_config(("blocker",)),
        )

        assert "Highest-priority severities: blocker" in prompt
        assert "EVERY valid" in prompt


