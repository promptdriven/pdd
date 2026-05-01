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
            lambda *a, **k: pytest.fail("must not push after fixer cost cap"),
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
        assert "issue_aligned: unknown" in report
        assert "The API accepts invalid input." in report

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
        assert "findings" in final_state


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
