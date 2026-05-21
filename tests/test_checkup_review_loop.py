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

    def test_review_loop_default_max_review_cost_is_50(self) -> None:
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
                ],
                obj={},
            )

        assert result.exit_code == 0, result.output
        assert run_mock.call_args.kwargs["max_review_cost"] == 50.0

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


class TestPrMetadataFetch:
    def test_fetch_pr_metadata_can_include_api_changed_files(
        self, monkeypatch: Any
    ) -> None:
        import pdd.checkup_review_loop as mod

        calls: List[List[str]] = []

        def fake_run_gh_command(args: List[str]) -> Tuple[bool, str]:
            calls.append(args)
            if args == ["api", "repos/o/r/pulls/1"]:
                return True, json.dumps(
                    {
                        "head": {
                            "ref": "feature",
                            "sha": "a" * 40,
                            "repo": {
                                "name": "r",
                                "clone_url": "https://github.com/o/r.git",
                                "owner": {"login": "o"},
                            },
                        },
                        "base": {"ref": "main"},
                    }
                )
            if "files?per_page=100" in args[2]:
                return (
                    True,
                    "modified\tpdd/a.py\t\n"
                    "renamed\tpdd/new.py\tpdd/old.py\n"
                    "removed\tpdd/deleted.py\t\n",
                )
            raise AssertionError(f"unexpected gh args: {args}")

        monkeypatch.setattr(mod, "_run_gh_command", fake_run_gh_command)

        metadata = mod._fetch_pr_metadata("o", "r", 1, include_changed_files=True)

        assert metadata["head_ref"] == "feature"
        assert metadata["base_ref"] == "main"
        assert metadata["api_changed_files"] == (
            "- MODIFIED: pdd/a.py\n"
            "- RENAMED: pdd/old.py -> pdd/new.py\n"
            "- REMOVED: pdd/deleted.py"
        )
        assert any("--paginate" in call for call in calls)

    def test_fetch_pr_metadata_does_not_fetch_files_by_default(
        self, monkeypatch: Any
    ) -> None:
        import pdd.checkup_review_loop as mod

        calls: List[List[str]] = []

        def fake_run_gh_command(args: List[str]) -> Tuple[bool, str]:
            calls.append(args)
            return True, json.dumps(
                {
                    "head": {"ref": "feature", "repo": {}, "sha": "a" * 40},
                    "base": {"ref": "main"},
                }
            )

        monkeypatch.setattr(mod, "_run_gh_command", fake_run_gh_command)

        metadata = mod._fetch_pr_metadata("o", "r", 1)

        assert metadata["base_ref"] == "main"
        assert "api_changed_files" not in metadata
        assert calls == [["api", "repos/o/r/pulls/1"]]


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
                # Issue #1088: the final-report render re-fetches the
                # remote PR head SHA to detect stale-head drift. Include
                # ``head_sha`` matching the ``_git_rev_parse_head`` stub
                # below so the happy-path stays clean.
                "head_sha": "a" * 40,
            },
        )
        monkeypatch.setattr(mod, "_commit_and_push_if_changed", lambda *a, **k: (True, "pushed"))
        # Issue #1088 trust boundary: ``_git_rev_parse_head`` returns "" on
        # ``tmp_path`` because it is not a real git repo. Return a stable
        # stub SHA so tests model the production case where a successful
        # push always yields an observable HEAD SHA.
        monkeypatch.setattr(
            mod, "_git_rev_parse_head", lambda *a, **k: "a" * 40
        )
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

    def test_budget_exhausted_with_fixer_claim_does_not_show_unverified_fixed(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Issue #1088 regression: the fixer can claim
        ``disposition='fixed'`` with a rationale (``"Added test..."``)
        even when verification is skipped (budget exhausted after the
        fixer pushed). The rendered Fixer Rationale section must not
        contain a bare ``claude: fixed - <prose>`` line — every fixer
        disposition has to be qualified (``fixer_disposition=fixed``)
        and tagged ``verification=unverified`` so the report cannot be
        read as a verifier verdict.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
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
            if "fix-" in label:
                key = mod._normalize_findings([finding], "codex", 1)[0].key
                return (
                    True,
                    json.dumps(
                        {
                            "summary": "Added regression test.",
                            "changed_files": ["pdd/api.py"],
                            "findings": [
                                {
                                    "key": key,
                                    "disposition": "fixed",
                                    "rationale": "Added test covering the validation path.",
                                }
                            ],
                        }
                    ),
                    1.0,
                    role,
                )
            return True, _json("findings", [finding]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)
        monkeypatch.setattr(
            mod,
            "_commit_and_push_if_changed",
            lambda *a, **k: (True, "pushed"),
        )

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_cost=0.5),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "max-cost-reached: true" in report
        # The trust-boundary contract: bare ``claude: fixed - ...``
        # must never appear in the final report, regardless of which
        # section the prose ended up in.
        assert "claude: fixed - " not in report
        # The qualified form must appear instead, alongside the
        # explicit verification state.
        assert "fixer=claude fixer_disposition=fixed" in report
        assert "verification=unverified" in report
        # The rationale text still surfaces — qualification, not
        # suppression — so reviewers see what the fixer claimed.
        assert "Added test covering the validation path." in report

    def test_unparseable_review_at_cost_cap_skips_parse_repair(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        calls: List[str] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            calls.append(kwargs["label"])
            return True, "Needs changes, but not JSON.", 0.5, role

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
        assert cost == 0.5
        assert calls == ["checkup-review-loop-review-codex-round1"]
        assert "max-cost-reached: true" in report

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
        assert "fixer=claude fixer_disposition=not_valid" in report
        assert "The existing behavior matches the API contract." in report
        assert "verification=unverified" in report
        # The bare "claude: <disposition> - <text>" form is the
        # exact trust-boundary confusion issue #1088 forbids — the
        # rendered prose must always qualify the disposition.
        assert "claude: not_valid - " not in report

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

    def test_reviewer_fallback_skips_parse_repair_past_deadline(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """The direct ``reviewer_fallback`` path must propagate ``deadline``
        into ``_run_review`` so a fallback that returns a parseable-but-failed
        payload after the wall-clock deadline does NOT trigger an extra
        parse-repair LLM call.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)

        clock = [1000.0]

        def fake_monotonic() -> float:
            return clock[0]

        monkeypatch.setattr(mod.time, "monotonic", fake_monotonic)

        calls: List[Tuple[str, str]] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            calls.append((role, kwargs["label"]))
            if role == "codex":
                # Primary failure forces the reviewer_fallback path.
                clock[0] += 1.0
                return False, "ERROR: authentication failed: token expired", 0.0, ""
            if role == "gemini":
                # Fallback returns parseable JSON with status=failed and
                # no findings, which without the deadline guard would let
                # ``_should_attempt_parse_repair`` fire. Advance the clock
                # past the deadline so the budget guard must skip the
                # extra parse-repair LLM call.
                clock[0] += 600.0
                return True, _json("failed"), 0.1, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(
                continue_on_reviewer_limit=True,
                reviewer_fallback="gemini",
                max_minutes=1.0,
            ),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        # The fallback reviewer must have been called…
        assert any(role == "gemini" for role, _ in calls), calls
        # …but parse-repair must NOT fire after the deadline has passed.
        assert not any(
            "parse-repair" in label for _, label in calls
        ), calls

    def test_fallback_reviewer_on_failure_skips_parse_repair_past_deadline(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """The ``fallback_reviewer_on_failure`` path (fixer-as-fallback) must
        also propagate ``deadline`` so an exhausted wall-clock budget skips
        the parse-repair LLM call.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)

        clock = [1000.0]

        def fake_monotonic() -> float:
            return clock[0]

        monkeypatch.setattr(mod.time, "monotonic", fake_monotonic)

        calls: List[Tuple[str, str]] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            calls.append((role, kwargs["label"]))
            if role == "codex":
                clock[0] += 1.0
                return False, "ERROR: authentication failed: token expired", 0.0, ""
            if role == "claude" and "fallback" in kwargs["label"]:
                # Fallback fixer-as-reviewer returns parseable-but-failed
                # JSON. Without the deadline guard, parse-repair would
                # fire here — and the fake clock has already advanced
                # past the deadline.
                clock[0] += 600.0
                return True, _json("failed"), 0.1, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(
                fallback_reviewer_on_failure=True,
                max_minutes=1.0,
            ),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        # The fallback fixer-as-reviewer must have been invoked…
        assert any(
            "fallback-claude" in label for _, label in calls
        ), calls
        # …but parse-repair must NOT fire after the deadline has passed.
        assert not any(
            "parse-repair" in label for _, label in calls
        ), calls

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

    def test_fixer_fallback_defangs_failed_primary_summary_in_report(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Failed-primary subprocess output can contain cloud verdict
        adapter trip-wires (``[CRITICAL]``, ``issue_aligned: false``,
        ``max-cost-reached: true``). When the fallback succeeds and
        the run reports verified, those trip-wires must not survive
        into the rendered fixer audit row, or they would falsely
        downgrade the adapter's verdict for an otherwise-clean fix."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        finding = self._finding()

        primary_output = (
            "[CRITICAL] subprocess error; "
            "issue_aligned: false; max-cost-reached: true; "
            'api_error_status:429 "You\'ve hit your limit · resets May 18, 11pm (UTC)"'
        )

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if label == "checkup-review-loop-review-codex-round1":
                return True, _json("findings", [finding]), 0.1, role
            if label == "checkup-review-loop-fix-claude-for-codex-round1":
                return False, primary_output, 0.0, role
            if label == "checkup-review-loop-fix-gemini-for-codex-round1":
                return True, '{"summary":"fixed","changed_files":["a.py"]}', 0.2, role
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
        # Verdict-adapter trip-wires from the failed primary's raw
        # output must not appear verbatim anywhere in the report.
        assert "[CRITICAL]" not in report, (
            "verbatim [CRITICAL] from failed primary leaked through; "
            "cloud verdict adapter would downgrade an otherwise-clean fallback"
        )
        assert "issue_aligned: false" not in report.lower()
        assert "max-cost-reached: true" not in report.lower()

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

    def test_fixer_fallback_excludes_original_reviewer_after_takeover(self) -> None:
        """When a reviewer-fallback has rotated the active reviewer (so
        the ORIGINAL primary reviewer is no longer ``state.active_reviewer``),
        the fixer-fallback must still refuse to promote the original
        reviewer. Otherwise ``--reviewer codex --reviewer-fallback gemini
        --fixer claude --fixer-fallback codex`` would silently run codex
        as the fixer after gemini took over reviewing, contradicting the
        documented "must differ from --reviewer" rule and re-using the
        original reviewer's credential in a role the docs forbid."""
        from pdd.checkup_review_loop import (
            ReviewFinding,
            ReviewLoopState,
            _maybe_run_fallback_fixer,
        )
        import pdd.checkup_review_loop as mod

        # Original reviewer = codex; gemini took over after codex failed,
        # so state.active_reviewer = gemini but state.original_reviewer
        # still = codex. fixer_fallback names codex.
        state = ReviewLoopState()
        state.original_reviewer = "codex"
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
        config = _config(fixer_fallback="codex")
        ctx = _ctx(Path("/tmp"))

        def _explode(*_args: Any, **_kwargs: Any) -> Any:
            raise AssertionError(
                "_run_fix must not run when fixer-fallback collides with "
                "state.original_reviewer"
            )

        with patch.object(mod, "_run_fix", side_effect=_explode):
            result = _maybe_run_fallback_fixer(
                primary_fixer="claude",
                reviewer="gemini",  # current/active reviewer
                findings=[finding],
                context=ctx,
                worktree=Path("/tmp"),
                round_number=2,
                state=state,
                config=config,
                verbose=False,
                quiet=True,
                artifacts_dir=Path("/tmp"),
                deadline=float("inf"),
            )

        assert result is None, (
            f"fixer-fallback must skip role equal to original_reviewer "
            f"even after reviewer rotation; got result={result!r}"
        )
        assert state.active_fixer is None, (
            f"state.active_fixer must remain unset when fallback is skipped; "
            f"got {state.active_fixer!r}"
        )


class TestShaBackedVerificationTrustBoundary:
    """Regressions for issue #1088: a finding may only be promoted to
    ``fixed`` after the verifier clears the SHA the fixer just pushed,
    observed at the rendered report's PR head re-fetch.

    Covers the three acceptance scenarios called out in the issue
    (happy-path-same-SHA, verifier-clean-then-head-advances,
    budget-exhausted-after-fixer-success) plus the no-pushed-SHA guard
    introduced by R-V1/R-V2.
    """

    @staticmethod
    def _finding() -> Dict[str, str]:
        return {
            "severity": "blocker",
            "area": "api",
            "location": "pdd/foo.py:1",
            "evidence": "ev",
            "finding": "broken api",
            "required_fix": "fix it",
        }

    @staticmethod
    def _patch_common(
        monkeypatch: Any,
        tmp_path: Path,
        *,
        head_sha: str = "a" * 40,
        push_result: Tuple[bool, str] = (True, "pushed"),
        rev_parse_head: str = "a" * 40,
    ) -> None:
        import pdd.checkup_review_loop as mod

        monkeypatch.setattr(
            mod, "_setup_pr_worktree", lambda *a, **k: (tmp_path, None)
        )
        monkeypatch.setattr(
            mod,
            "_fetch_pr_metadata",
            lambda *a, **k: {
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_sha": head_sha,
            },
        )
        monkeypatch.setattr(
            mod, "_commit_and_push_if_changed", lambda *a, **k: push_result
        )
        monkeypatch.setattr(
            mod, "_git_rev_parse_head", lambda *a, **k: rev_parse_head
        )
        monkeypatch.setattr(mod, "_post_review_loop_report", lambda *a, **k: None)

    def _fake_task(
        self,
        *,
        finding: Dict[str, str] | None = None,
        verify_clean: bool = True,
    ):
        finding_blob = finding or self._finding()

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if "verify-" in label:
                return (
                    True,
                    _json("clean") if verify_clean else _json("findings", [finding_blob]),
                    0.1,
                    role,
                )
            if "review-" in label:
                return True, _json("findings", [finding_blob]), 0.1, role
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"x","changed_files":["pdd/foo.py"]}',
                    0.1,
                    role,
                )
            return True, _json("clean"), 0.1, role

        return fake_task

    def test_happy_path_same_sha_marks_finding_fixed(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Happy path: fixer pushes SHA-A, verifier clears SHA-A, remote
        re-fetch still observes SHA-A. The finding flips to ``fixed`` and
        ``verification_status_by_round[1]`` is ``"verified"``."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        sha = "f" * 40
        self._patch_common(
            monkeypatch, tmp_path, head_sha=sha, rev_parse_head=sha
        )
        monkeypatch.setattr(mod, "_run_role_task", self._fake_task())

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "fresh-final-review: clean" in report
        assert f"verified-head-sha: {sha}" in report
        assert f"remote-pr-head-sha: {sha}" in report
        assert "verification=verified" in report
        assert "broken api" not in report

        final_state = json.loads(
            (
                tmp_path
                / ".pdd"
                / "checkup-review-loop"
                / "issue-2-pr-1"
                / "final-state.json"
            ).read_text()
        )
        assert final_state["verified_head_sha"] == sha
        assert final_state["remote_pr_head_sha"] == sha
        assert final_state["verification_status_by_round"]["1"] == "verified"
        statuses = {
            f["key"]: f["status"] for f in final_state["findings"]
        }
        assert all(status == "fixed" for status in statuses.values()), statuses
        fixes = final_state["fixes"]
        assert fixes and fixes[0]["push_status"] == "pushed"
        assert fixes[0]["pushed_head_sha"] == sha
        assert fixes[0]["fixer_result"] == "attempted"

    def test_verifier_clean_then_head_advances_reverts_fixed_state(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """The verifier clears SHA-A, but by the time ``_finalize``
        re-fetches the PR head a third party has pushed SHA-B.
        ``final-state.json`` must NOT continue to claim the round
        was verified or the finding fixed (issue #1088)."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        sha_a = "a" * 40
        sha_b = "b" * 40
        self._patch_common(
            monkeypatch, tmp_path, head_sha=sha_b, rev_parse_head=sha_a
        )
        monkeypatch.setattr(mod, "_run_role_task", self._fake_task())

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "fresh-final-review: missing" in report
        assert f"verified-head-sha: {sha_a}" in report
        assert f"remote-pr-head-sha: {sha_b}" in report
        assert "PR head advanced after verification" in report
        assert "verification=verified" not in report

        final_state = json.loads(
            (
                tmp_path
                / ".pdd"
                / "checkup-review-loop"
                / "issue-2-pr-1"
                / "final-state.json"
            ).read_text()
        )
        assert final_state["verification_status_by_round"]["1"] == "stale"
        assert all(
            f["status"] != "fixed" for f in final_state["findings"]
        ), final_state["findings"]

    def test_remote_head_refetch_failure_reverts_fixed_state(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """R-V5 fail-closed: when the render-time PR head re-fetch
        returns no ``head_sha`` we cannot prove the verifier's SHA is
        still current. The round downgrades to ``stale`` and any
        ``fixed`` finding reverts to ``open``."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        sha_a = "a" * 40
        monkeypatch.setattr(
            mod, "_setup_pr_worktree", lambda *a, **k: (tmp_path, None)
        )
        # First call returns ``head_sha`` (used by the worktree setup
        # path); the second call (from ``_finalize``) drops it to model
        # a failed re-fetch.
        metadata_calls: List[int] = []

        def fake_metadata(*_a: Any, **_kw: Any):
            metadata_calls.append(1)
            base = {
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
            }
            if len(metadata_calls) == 1:
                base["head_sha"] = sha_a
            return base

        monkeypatch.setattr(mod, "_fetch_pr_metadata", fake_metadata)
        monkeypatch.setattr(
            mod, "_commit_and_push_if_changed", lambda *a, **k: (True, "pushed")
        )
        monkeypatch.setattr(mod, "_git_rev_parse_head", lambda *a, **k: sha_a)
        monkeypatch.setattr(mod, "_post_review_loop_report", lambda *a, **k: None)
        monkeypatch.setattr(mod, "_run_role_task", self._fake_task())

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert "fresh-final-review: missing" in report
        # Render-time re-fetch returned no SHA — rendered as ``unknown``.
        assert "remote-pr-head-sha: unknown" in report
        assert "Primary reviewer is satisfied" not in report
        assert "verification is treated as unverified" in report

        final_state = json.loads(
            (
                tmp_path
                / ".pdd"
                / "checkup-review-loop"
                / "issue-2-pr-1"
                / "final-state.json"
            ).read_text()
        )
        assert final_state["verification_status_by_round"]["1"] == "stale"
        assert "verification is treated as unverified" in final_state["stop_reason"]
        assert all(
            f["status"] != "fixed" for f in final_state["findings"]
        ), final_state["findings"]

    def test_no_commit_pushed_skips_verifier_and_keeps_finding_open(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """R-V1: when ``_commit_and_push_if_changed`` returns
        ``(True, "No changes to push.")`` the fixer produced no commit.
        The verifier must NOT run and findings must NOT be promoted to
        ``fixed`` (issue #1088)."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_common(
            monkeypatch,
            tmp_path,
            push_result=(True, "No changes to push."),
        )
        calls: List[str] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append(label)
            if "verify-" in label:
                return True, _json("clean"), 0.1, role
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"x","changed_files":[]}',
                    0.1,
                    role,
                )
            return True, _json("findings", [self._finding()]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        # The verifier must NEVER fire when no commit was pushed.
        assert not any("verify-" in lbl for lbl in calls), calls
        # The rendered report must not claim a clean fresh-final.
        assert "fresh-final-review: clean" not in report
        assert "No findings remain" not in report
        assert "verification=verified" not in report
        assert "broken api" in report  # still listed as remaining

        final_state = json.loads(
            (
                tmp_path
                / ".pdd"
                / "checkup-review-loop"
                / "issue-2-pr-1"
                / "final-state.json"
            ).read_text()
        )
        assert final_state["verification_status_by_round"]["1"] == "skipped"
        assert all(
            f["status"] != "fixed" for f in final_state["findings"]
        ), final_state["findings"]
        fixes = final_state["fixes"]
        assert fixes and fixes[0]["push_status"] == "not_attempted"
        assert fixes[0]["pushed_head_sha"] is None
        assert fixes[0]["fixer_result"] == "skipped"

    def test_pushed_but_no_rev_parse_sha_skips_verifier(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """R-V2: the push helper reports success but ``git rev-parse
        HEAD`` returns empty. We cannot prove which SHA landed, so the
        verifier must NOT run and findings must NOT be marked fixed."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_common(
            monkeypatch,
            tmp_path,
            push_result=(True, "pushed"),
            rev_parse_head="",
        )
        calls: List[str] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append(label)
            if "verify-" in label:
                return True, _json("clean"), 0.1, role
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"x","changed_files":["pdd/foo.py"]}',
                    0.1,
                    role,
                )
            return True, _json("findings", [self._finding()]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert not any("verify-" in lbl for lbl in calls), calls
        assert "fresh-final-review: clean" not in report
        assert "verification=verified" not in report

        final_state = json.loads(
            (
                tmp_path
                / ".pdd"
                / "checkup-review-loop"
                / "issue-2-pr-1"
                / "final-state.json"
            ).read_text()
        )
        assert final_state["verification_status_by_round"]["1"] == "skipped"
        assert all(
            f["status"] != "fixed" for f in final_state["findings"]
        ), final_state["findings"]

    def test_budget_exhausted_after_fixer_pushes_leaves_round_unverified(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """R-V6: the fixer's push lands on SHA-A but the budget cap
        trips before the verifier runs. ``final-state.json`` must
        reflect ``unverified`` for the round and the per-round fix
        artifact must persist the trust-boundary fields with the pushed
        SHA captured."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        sha = "c" * 40
        self._patch_common(
            monkeypatch, tmp_path, head_sha=sha, rev_parse_head=sha
        )
        calls: List[str] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append(label)
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"x","changed_files":["pdd/foo.py"]}',
                    1.0,
                    role,
                )
            return True, _json("findings", [self._finding()]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_cost=0.5),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert round(cost, 2) == 1.1
        # Budget exhausted between push and verify — no verify call.
        assert not any("verify-" in lbl for lbl in calls), calls
        assert "max-cost-reached: true" in report
        assert "verification=unverified" in report
        assert "verification=verified" not in report

        final_state = json.loads(
            (
                tmp_path
                / ".pdd"
                / "checkup-review-loop"
                / "issue-2-pr-1"
                / "final-state.json"
            ).read_text()
        )
        assert final_state["verification_status_by_round"]["1"] == "unverified"
        assert all(
            f["status"] != "fixed" for f in final_state["findings"]
        ), final_state["findings"]
        fixes = final_state["fixes"]
        assert fixes and fixes[0]["push_status"] == "pushed"
        assert fixes[0]["pushed_head_sha"] == sha

    def test_per_round_fix_artifact_carries_trust_boundary_fields(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """The per-round ``round-N-fix-...-findings.json`` artifact must
        include ``fixer_result``, ``push_status``,
        ``local_fixer_commit_sha`` and ``pushed_head_sha`` (even as
        ``null`` when not applicable) so the audit trail on disk
        matches the PR prompt contract."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        sha = "d" * 40
        self._patch_common(
            monkeypatch, tmp_path, head_sha=sha, rev_parse_head=sha
        )
        monkeypatch.setattr(mod, "_run_role_task", self._fake_task())

        run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        artifacts_dir = (
            tmp_path / ".pdd" / "checkup-review-loop" / "issue-2-pr-1"
        )
        artifact = json.loads(
            (
                artifacts_dir / "round-1-fix-claude-for-codex.findings.json"
            ).read_text()
        )
        # Trust-boundary fields are present after push/SHA classification.
        for key in (
            "fixer_result",
            "push_status",
            "local_fixer_commit_sha",
            "pushed_head_sha",
            "round_number",
        ):
            assert key in artifact, f"missing trust-boundary key {key!r}"
        assert artifact["push_status"] == "pushed"
        assert artifact["pushed_head_sha"] == sha
        assert artifact["fixer_result"] == "attempted"
        assert artifact["round_number"] == 1

    def test_initial_reviewer_clean_then_remote_head_advances_downgrades(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """R-V5 (round 2): when the FIRST reviewer returns ``clean`` the
        loop never runs a fixer or verifier, so the old
        ``if state.verified_head_sha`` gate in ``_finalize`` skipped the
        render-time re-fetch entirely. The fix records the reviewed PR
        head SHA on every clean reviewer path and the re-fetch now fires
        whenever ``fresh_final_status == "clean"``. If the remote PR
        head has advanced past what the reviewer saw, the report MUST
        NOT render ``fresh-final-review: clean``."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        sha_a = "a" * 40
        sha_b = "b" * 40
        # First metadata fetch (loop start) returns SHA-A — that's what
        # the reviewer sees in the worktree. The render-time re-fetch
        # in ``_finalize`` returns SHA-B — the remote head advanced.
        metadata_calls: List[int] = []

        def fake_metadata(*_a: Any, **_kw: Any):
            metadata_calls.append(1)
            return {
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_sha": sha_a if len(metadata_calls) == 1 else sha_b,
            }

        monkeypatch.setattr(
            mod, "_setup_pr_worktree", lambda *a, **k: (tmp_path, None)
        )
        monkeypatch.setattr(mod, "_fetch_pr_metadata", fake_metadata)
        # No fixer should run. Fail loudly if push/rev-parse is touched.
        monkeypatch.setattr(
            mod,
            "_commit_and_push_if_changed",
            lambda *a, **k: pytest.fail("fixer must not run when reviewer clean"),
        )
        monkeypatch.setattr(mod, "_git_rev_parse_head", lambda *a, **k: sha_a)
        monkeypatch.setattr(mod, "_post_review_loop_report", lambda *a, **k: None)

        calls: List[str] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append(label)
            # First reviewer is clean — no fixer, no verifier.
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
        # Only one reviewer call — no verifier, no fixer.
        assert not any("verify-" in lbl for lbl in calls), calls
        assert not any("fix-" in lbl for lbl in calls), calls
        # The render-time re-fetch must have fired exactly once.
        assert len(metadata_calls) == 2, metadata_calls
        # The rendered report must no longer claim a clean fresh-final.
        assert "fresh-final-review: clean" not in report
        assert "fresh-final-review: missing" in report
        # ``verified-head-sha:`` is ``none`` (no verifier ran), but the
        # remote head was observed at the render boundary.
        assert "verified-head-sha: none" in report
        assert f"remote-pr-head-sha: {sha_b}" in report
        assert "PR head advanced after review" in report

        final_state = json.loads(
            (
                tmp_path
                / ".pdd"
                / "checkup-review-loop"
                / "issue-2-pr-1"
                / "final-state.json"
            ).read_text()
        )
        assert final_state["fresh_final_status"] == "missing"
        assert final_state["remote_pr_head_sha"] == sha_b
        assert final_state["verified_head_sha"] is None

    def test_initial_reviewer_clean_refetch_failure_downgrades(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """R-V5 fail-closed for the no-verifier path: when the first
        reviewer is clean and the render-time PR-head re-fetch returns
        no ``head_sha``, the report MUST downgrade fresh-final to
        ``missing`` and render ``remote-pr-head-sha: unknown`` (the
        re-fetch was attempted but failed)."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        sha_a = "a" * 40
        metadata_calls: List[int] = []

        def fake_metadata(*_a: Any, **_kw: Any):
            metadata_calls.append(1)
            base: Dict[str, str] = {
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
            }
            if len(metadata_calls) == 1:
                base["head_sha"] = sha_a
            # Second call (from ``_finalize``) drops head_sha to model
            # a failed re-fetch.
            return base

        monkeypatch.setattr(
            mod, "_setup_pr_worktree", lambda *a, **k: (tmp_path, None)
        )
        monkeypatch.setattr(mod, "_fetch_pr_metadata", fake_metadata)
        monkeypatch.setattr(
            mod,
            "_commit_and_push_if_changed",
            lambda *a, **k: pytest.fail("fixer must not run when reviewer clean"),
        )
        monkeypatch.setattr(mod, "_git_rev_parse_head", lambda *a, **k: sha_a)
        monkeypatch.setattr(mod, "_post_review_loop_report", lambda *a, **k: None)
        monkeypatch.setattr(
            mod,
            "_run_role_task",
            lambda role, instruction, cwd, **kwargs: (
                True, _json("clean"), 0.1, role
            ),
        )

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert len(metadata_calls) == 2
        assert "fresh-final-review: clean" not in report
        assert "fresh-final-review: missing" in report
        assert "remote-pr-head-sha: unknown" in report
        assert "Primary reviewer is satisfied" not in report
        assert "verification is treated as unverified" in report

        final_state = json.loads(
            (
                tmp_path
                / ".pdd"
                / "checkup-review-loop"
                / "issue-2-pr-1"
                / "final-state.json"
            ).read_text()
        )
        assert final_state["fresh_final_status"] == "missing"
        assert final_state["remote_pr_head_sha"] is None
        assert "verification is treated as unverified" in final_state["stop_reason"]

    def test_budget_exhausted_after_verifier_clean_pins_round_and_sha(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Trust-boundary audit-trail regression: when the verifier
        returns ``clean`` against the pushed head and the budget cap
        trips on the post-verify ``_budget_exhausted`` check, the
        per-round verification status and the verified head SHA must
        already be pinned before the budget break-out — otherwise
        ``final-state.json`` would render ``status='fixed'`` findings
        without a matching ``verification_status_by_round`` entry."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        sha = "e" * 40
        self._patch_common(
            monkeypatch, tmp_path, head_sha=sha, rev_parse_head=sha
        )
        calls: List[str] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append(label)
            if "verify-" in label:
                # Verifier returns clean AND pushes total_cost over the
                # max so the post-verify ``_budget_exhausted`` check
                # trips on the very next line.
                return True, _json("clean"), 0.4, role
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"x","changed_files":["pdd/foo.py"]}',
                    0.1,
                    role,
                )
            # review-: report a finding so the fixer/verifier path runs.
            return True, _json("findings", [self._finding()]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_cost=0.5),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        # review (0.1) + fix (0.1) + verify (0.4) == 0.6 >= 0.5.
        assert round(cost, 2) == 0.6
        # The verifier MUST have run (this is the post-verify trip).
        assert any("verify-" in lbl for lbl in calls), calls
        assert "max-cost-reached: true" in report
        assert f"verified-head-sha: {sha}" in report
        assert f"remote-pr-head-sha: {sha}" in report

        final_state = json.loads(
            (
                tmp_path
                / ".pdd"
                / "checkup-review-loop"
                / "issue-2-pr-1"
                / "final-state.json"
            ).read_text()
        )
        # The trust-boundary audit trail must be intact: verified SHA
        # pinned, per-round status recorded as ``verified``, and the
        # fixed-by-the-verifier findings carry ``status='fixed'``.
        assert final_state["verified_head_sha"] == sha
        assert final_state["verification_status_by_round"]["1"] == "verified"
        assert final_state["max_cost_reached"] is True
        statuses = {
            f["key"]: f["status"] for f in final_state["findings"]
        }
        assert statuses, final_state["findings"]
        assert all(status == "fixed" for status in statuses.values()), statuses

    def test_budget_exhausted_after_verifier_partial_records_unverified(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Partial-acceptance audit-trail regression: when the verifier
        accepts some findings but still reports others against the
        pushed head, and the budget cap trips on the post-verify
        ``_budget_exhausted`` check, the per-round verification status
        must be recorded as ``unverified`` (partial does not advance
        ``verified_head_sha``) — but the verifier-accepted findings
        still carry ``status='fixed'`` from
        ``_mark_findings_fixed``."""
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        sha = "9" * 40
        self._patch_common(
            monkeypatch, tmp_path, head_sha=sha, rev_parse_head=sha
        )
        # Two distinct findings — the verifier will accept (omit) the
        # first and re-report the second.
        accepted = self._finding()
        accepted["location"] = "pdd/foo.py:1"
        accepted["finding"] = "accepted finding"
        remaining = {
            "severity": "blocker",
            "area": "api",
            "location": "pdd/foo.py:99",
            "evidence": "ev2",
            "finding": "remaining finding",
            "required_fix": "fix it harder",
        }
        calls: List[str] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            calls.append(label)
            if "verify-" in label:
                # Verifier accepts ``accepted`` (omits it) but still
                # reports ``remaining``. Cost crosses the budget cap.
                return True, _json("findings", [remaining]), 0.4, role
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"x","changed_files":["pdd/foo.py"]}',
                    0.1,
                    role,
                )
            # review-: report both findings so both reach the fixer.
            return (
                True,
                _json("findings", [accepted, remaining]),
                0.1,
                role,
            )

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, _report, cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_cost=0.5),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        assert round(cost, 2) == 0.6
        assert any("verify-" in lbl for lbl in calls), calls

        final_state = json.loads(
            (
                tmp_path
                / ".pdd"
                / "checkup-review-loop"
                / "issue-2-pr-1"
                / "final-state.json"
            ).read_text()
        )
        # Partial acceptance does NOT pin ``verified_head_sha``.
        assert final_state["verified_head_sha"] is None
        # But the per-round verification status MUST be recorded
        # (previously this entry was absent after partial+budget-out).
        assert final_state["verification_status_by_round"]["1"] == "unverified"
        assert final_state["max_cost_reached"] is True
        # Verifier-accepted finding flipped to ``fixed``; the other
        # still-open finding remains ``open``. Discriminate by status
        # count rather than serialized field name so the test does not
        # depend on the specific finding-dict layout.
        fixed_findings = [
            f for f in final_state["findings"] if f["status"] == "fixed"
        ]
        open_findings = [
            f for f in final_state["findings"] if f["status"] == "open"
        ]
        assert len(fixed_findings) == 1, final_state["findings"]
        assert len(open_findings) == 1, final_state["findings"]

    def test_failed_primary_fixer_writes_trust_boundary_artifact_no_fallback(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Issue #1088 audit-trail completeness: when the primary fixer
        fails and no ``fixer_fallback`` is configured, the loop breaks
        BEFORE the canonical post-push artifact rewrite. The per-round
        ``round-N-fix-...findings.json`` artifact MUST still carry the
        in-memory ``FixResult`` trust-boundary fields (rather than the
        ``null`` placeholders ``_run_fix`` initially writes), so the
        on-disk audit shows ``fixer_result=failed`` and
        ``push_status=not_attempted``.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_common(monkeypatch, tmp_path)
        finding = self._finding()

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if label == "checkup-review-loop-review-codex-round1":
                return True, _json("findings", [finding]), 0.1, role
            if "fix-" in label:
                return False, "primary fixer failed", 0.0, role
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
        artifact = json.loads(
            (
                tmp_path
                / ".pdd"
                / "checkup-review-loop"
                / "issue-2-pr-1"
                / "round-1-fix-claude-for-codex.findings.json"
            ).read_text()
        )
        assert artifact["fixer_result"] == "failed", artifact
        assert artifact["push_status"] == "not_attempted", artifact
        assert artifact["local_fixer_commit_sha"] is None, artifact
        assert artifact["pushed_head_sha"] is None, artifact
        assert artifact["round_number"] == 1, artifact

    def test_failed_primary_and_failed_fallback_write_trust_boundary_artifacts(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Issue #1088 audit-trail completeness: when both the primary
        fixer and the configured ``fixer_fallback`` fail, the loop breaks
        BEFORE the canonical post-push artifact rewrite. Both per-round
        ``round-N-fix-...findings.json`` artifacts (primary's and
        fallback's) MUST carry their in-memory ``FixResult``
        trust-boundary fields — ``fixer_result=failed`` and
        ``push_status=not_attempted`` on each.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_common(monkeypatch, tmp_path)
        finding = self._finding()

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if label == "checkup-review-loop-review-codex-round1":
                return True, _json("findings", [finding]), 0.1, role
            if label == "checkup-review-loop-fix-claude-for-codex-round1":
                return False, "primary fixer failed", 0.0, role
            if label == "checkup-review-loop-fix-gemini-for-codex-round1":
                return False, "fallback fixer also failed", 0.0, role
            return True, _json("clean"), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, _report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(fixer_fallback="gemini"),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        artifacts_dir = (
            tmp_path / ".pdd" / "checkup-review-loop" / "issue-2-pr-1"
        )
        primary_artifact = json.loads(
            (artifacts_dir / "round-1-fix-claude-for-codex.findings.json").read_text()
        )
        fallback_artifact = json.loads(
            (artifacts_dir / "round-1-fix-gemini-for-codex.findings.json").read_text()
        )
        for artifact in (primary_artifact, fallback_artifact):
            assert artifact["fixer_result"] == "failed", artifact
            assert artifact["push_status"] == "not_attempted", artifact
            assert artifact["local_fixer_commit_sha"] is None, artifact
            assert artifact["pushed_head_sha"] is None, artifact
            assert artifact["round_number"] == 1, artifact


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
            if cmd == ["git", "diff", "--cached", "--quiet"]:
                return type("R", (), {"returncode": 1, "stdout": "", "stderr": ""})()
            if cmd == ["git", "rev-parse", "HEAD"]:
                return type(
                    "R",
                    (),
                    {
                        "returncode": 0,
                        "stdout": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n",
                        "stderr": "",
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
        assert [
            "git",
            "-c",
            "user.name=PDD Bot",
            "-c",
            "user.email=pdd-bot@users.noreply.github.com",
            "rebase",
            "--onto",
            "FETCH_HEAD",
            "HEAD~1",
            "HEAD",
        ] in runs

    def test_fetch_first_rebases_again_when_retry_also_races(
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
        force_flags: List[bool] = []

        def fake_push(_worktree: Path, **kwargs: Any) -> Tuple[bool, str]:
            nonlocal pushes
            pushes += 1
            force_flags.append(kwargs.get("force_with_lease_on_non_fast_forward", True))
            if pushes < 3:
                return False, " ! [rejected] HEAD -> feature (fetch first)"
            return True, ""

        rebase_count = 0

        def fake_rebase(_worktree: Path, **_kwargs: Any) -> Tuple[bool, str]:
            nonlocal rebase_count
            rebase_count += 1
            return True, "rebased"

        def fake_run(cmd: List[str], **_kwargs: Any):
            if cmd == ["git", "diff", "--cached", "--quiet"]:
                return type("R", (), {"returncode": 1, "stdout": "", "stderr": ""})()
            if cmd == ["git", "rev-parse", "HEAD"]:
                return type(
                    "R",
                    (),
                    {
                        "returncode": 0,
                        "stdout": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n",
                        "stderr": "",
                    },
                )()
            return type("R", (), {"returncode": 0, "stdout": "", "stderr": ""})()

        monkeypatch.setattr(mod, "push_with_retry", fake_push)
        monkeypatch.setattr(mod, "_rebase_onto_updated_pr_head", fake_rebase)
        monkeypatch.setattr(mod.subprocess, "run", fake_run)

        success, message = mod._commit_and_push_if_changed(
            tmp_path,
            metadata,
            "fix: address findings",
        )

        assert success is True
        assert "rebasing" in message
        assert pushes == 3
        assert rebase_count == 2
        assert force_flags == [False, False, False]

    def test_three_fetch_first_pushes_exhaust_retries_cleanly(
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
        force_flags: List[bool] = []

        def fake_push(_worktree: Path, **kwargs: Any) -> Tuple[bool, str]:
            nonlocal pushes
            pushes += 1
            force_flags.append(kwargs.get("force_with_lease_on_non_fast_forward", True))
            return False, " ! [rejected] HEAD -> feature (fetch first)"

        rebase_count = 0

        def fake_rebase(_worktree: Path, **_kwargs: Any) -> Tuple[bool, str]:
            nonlocal rebase_count
            rebase_count += 1
            return True, "rebased"

        def fake_run(cmd: List[str], **_kwargs: Any):
            if cmd == ["git", "diff", "--cached", "--quiet"]:
                return type("R", (), {"returncode": 1, "stdout": "", "stderr": ""})()
            if cmd == ["git", "rev-parse", "HEAD"]:
                return type(
                    "R",
                    (),
                    {
                        "returncode": 0,
                        "stdout": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n",
                        "stderr": "",
                    },
                )()
            return type("R", (), {"returncode": 0, "stdout": "", "stderr": ""})()

        monkeypatch.setattr(mod, "push_with_retry", fake_push)
        monkeypatch.setattr(mod, "_rebase_onto_updated_pr_head", fake_rebase)
        monkeypatch.setattr(mod.subprocess, "run", fake_run)

        success, message = mod._commit_and_push_if_changed(
            tmp_path,
            metadata,
            "fix: address findings",
        )

        assert success is False
        assert pushes == 3
        assert rebase_count == 2
        assert message.startswith("Failed to push fixes to PR branch:")
        assert "fetch first" in message
        assert force_flags == [False, False, False]

    def test_non_remote_advance_error_on_retry_breaks_out(
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
        force_flags: List[bool] = []

        def fake_push(_worktree: Path, **kwargs: Any) -> Tuple[bool, str]:
            nonlocal pushes
            pushes += 1
            force_flags.append(kwargs.get("force_with_lease_on_non_fast_forward", True))
            if pushes == 1:
                return False, " ! [rejected] HEAD -> feature (fetch first)"
            return False, "fatal: Authentication failed for 'https://github.com/o/r.git'"

        rebase_count = 0

        def fake_rebase(_worktree: Path, **_kwargs: Any) -> Tuple[bool, str]:
            nonlocal rebase_count
            rebase_count += 1
            return True, "rebased"

        def fake_run(cmd: List[str], **_kwargs: Any):
            if cmd == ["git", "diff", "--cached", "--quiet"]:
                return type("R", (), {"returncode": 1, "stdout": "", "stderr": ""})()
            if cmd == ["git", "rev-parse", "HEAD"]:
                return type(
                    "R",
                    (),
                    {
                        "returncode": 0,
                        "stdout": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n",
                        "stderr": "",
                    },
                )()
            return type("R", (), {"returncode": 0, "stdout": "", "stderr": ""})()

        monkeypatch.setattr(mod, "push_with_retry", fake_push)
        monkeypatch.setattr(mod, "_rebase_onto_updated_pr_head", fake_rebase)
        monkeypatch.setattr(mod.subprocess, "run", fake_run)

        success, message = mod._commit_and_push_if_changed(
            tmp_path,
            metadata,
            "fix: address findings",
        )
        assert success is False
        assert pushes == 2
        assert rebase_count == 1
        assert "Authentication failed" in message
        assert force_flags == [False, False]

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
            if cmd == ["git", "diff", "--cached", "--quiet"]:
                return type("R", (), {"returncode": 1, "stdout": "", "stderr": ""})()
            if cmd == ["git", "rev-parse", "HEAD"]:
                return type(
                    "R",
                    (),
                    {
                        "returncode": 0,
                        "stdout": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n",
                        "stderr": "",
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
        assert [
            "git",
            "-c",
            "user.name=PDD Bot",
            "-c",
            "user.email=pdd-bot@users.noreply.github.com",
            "rebase",
            "--onto",
            "FETCH_HEAD",
            "HEAD~1",
            "HEAD",
        ] in runs

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
            if cmd == ["git", "diff", "--cached", "--quiet"]:
                return type("R", (), {"returncode": 1, "stdout": "", "stderr": ""})()
            if cmd == ["git", "rev-parse", "HEAD"]:
                return type(
                    "R",
                    (),
                    {
                        "returncode": 0,
                        "stdout": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n",
                        "stderr": "",
                    },
                )()
            if "rebase" in cmd and "--abort" not in cmd:
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
            if cmd == ["git", "diff", "--cached", "--quiet"]:
                return type("R", (), {"returncode": 1, "stdout": "", "stderr": ""})()
            if cmd == ["git", "rev-parse", "HEAD"]:
                return type(
                    "R",
                    (),
                    {
                        "returncode": 0,
                        "stdout": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n",
                        "stderr": "",
                    },
                )()
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
        assert [
            "git",
            "-c",
            "user.name=PDD Bot",
            "-c",
            "user.email=pdd-bot@users.noreply.github.com",
            "rebase",
            "--onto",
            "FETCH_HEAD",
            "HEAD~1",
            "HEAD",
        ] in runs

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

    def test_rotated_retry_rebases_on_prior_attempt_remote_commit(
        self, tmp_path: Path
    ) -> None:
        import pdd.checkup_review_loop as mod

        def git(cwd: Path, *args: str) -> str:
            result = subprocess.run(
                ["git", *args],
                cwd=cwd,
                capture_output=True,
                check=True,
                text=True,
            )
            return result.stdout.strip()

        def configure_identity(repo: Path) -> None:
            git(repo, "config", "user.name", "Test Bot")
            git(repo, "config", "user.email", "test@example.com")

        remote = tmp_path / "remote.git"
        seed = tmp_path / "seed"
        previous_attempt = tmp_path / "previous-attempt"
        current_attempt = tmp_path / "current-attempt"

        subprocess.run(
            ["git", "init", "--bare", "--initial-branch=main", str(remote)],
            capture_output=True,
            check=True,
            text=True,
        )
        subprocess.run(
            ["git", "init", "--initial-branch=main", str(seed)],
            capture_output=True,
            check=True,
            text=True,
        )
        configure_identity(seed)
        (seed / "base.txt").write_text("base\n", encoding="utf-8")
        git(seed, "add", "base.txt")
        git(seed, "commit", "-m", "base")
        git(seed, "remote", "add", "origin", str(remote))
        git(seed, "push", "origin", "HEAD:feature")

        subprocess.run(
            ["git", "clone", "--branch", "feature", str(remote), str(previous_attempt)],
            capture_output=True,
            check=True,
            text=True,
        )
        subprocess.run(
            ["git", "clone", "--branch", "feature", str(remote), str(current_attempt)],
            capture_output=True,
            check=True,
            text=True,
        )

        configure_identity(previous_attempt)
        (previous_attempt / "prior.txt").write_text("prior attempt\n", encoding="utf-8")
        git(previous_attempt, "add", "prior.txt")
        git(previous_attempt, "commit", "-m", "prior checkup attempt")
        git(previous_attempt, "push", "origin", "HEAD:feature")

        (current_attempt / "current.txt").write_text("current attempt\n", encoding="utf-8")

        success, message = mod._commit_and_push_if_changed(
            current_attempt,
            {
                "clone_url": str(remote),
                "head_ref": "feature",
                "head_owner": "o",
                "head_repo": "r",
            },
            "fix: address findings",
        )

        assert success is True
        assert "rebasing" in message
        verify = tmp_path / "verify"
        subprocess.run(
            ["git", "clone", "--branch", "feature", str(remote), str(verify)],
            capture_output=True,
            check=True,
            text=True,
        )
        assert (verify / "prior.txt").read_text(encoding="utf-8") == "prior attempt\n"
        assert (verify / "current.txt").read_text(encoding="utf-8") == "current attempt\n"

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

    def test_rebase_retry_uses_stable_fixer_sha_after_empty_rebase(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Codex round-3 HIGH regression: a fast-forward / empty-skip on the
        first rebase must not let a second remote-advance retry replay a
        stale remote commit. The retry loop captures the fixer commit's SHA
        right after the bot commit and ``git reset --hard <fixer_sha>``
        before every rebase, so the rebase range always describes the
        original fixer commit even if a prior rebase fast-forwarded HEAD
        past our fix.
        """
        import pdd.checkup_review_loop as mod

        metadata = {
            "clone_url": "https://github.com/o/r.git",
            "head_ref": "feature",
            "head_owner": "o",
            "head_repo": "r",
        }
        monkeypatch.setattr(mod, "_git_changed_files", lambda _worktree: ["pdd/foo.py"])
        monkeypatch.setattr(mod, "_git_untracked_files", lambda _worktree: [])

        # Two fetch-first rejections, then success on the third push.
        pushes = 0

        def fake_push(_worktree: Path, **_kwargs: Any) -> Tuple[bool, str]:
            nonlocal pushes
            pushes += 1
            if pushes < 3:
                return False, " ! [rejected] HEAD -> feature (fetch first)"
            return True, ""

        monkeypatch.setattr(mod, "push_with_retry", fake_push)

        # Force the real ``_rebase_onto_updated_pr_head`` to run so the new
        # ``git reset --hard <fixer_sha>`` step is actually executed.
        monkeypatch.setattr(
            mod,
            "_fetch_pr_head_for_rebase",
            lambda *_a, **_kw: (True, ""),
        )

        captured_fixer_sha = "deadbeefcafebabe1234567890abcdef12345678"
        recorded: List[List[str]] = []
        reset_targets: List[str] = []

        def fake_run(cmd: List[str], **_kwargs: Any):
            recorded.append(list(cmd))
            if cmd == ["git", "diff", "--cached", "--quiet"]:
                # Pretend something is staged so the commit step proceeds.
                return type("R", (), {"returncode": 1, "stdout": "", "stderr": ""})()
            if cmd == ["git", "rev-parse", "HEAD"]:
                return type(
                    "R",
                    (),
                    {
                        "returncode": 0,
                        "stdout": f"{captured_fixer_sha}\n",
                        "stderr": "",
                    },
                )()
            if len(cmd) >= 3 and cmd[:3] == ["git", "reset", "--hard"]:
                reset_targets.append(cmd[3])
                return type("R", (), {"returncode": 0, "stdout": "", "stderr": ""})()
            # Everything else (add, commit, rebase) is a no-op success.
            return type("R", (), {"returncode": 0, "stdout": "", "stderr": ""})()

        monkeypatch.setattr(mod.subprocess, "run", fake_run)

        success, message = mod._commit_and_push_if_changed(
            tmp_path,
            metadata,
            "fix: address findings",
        )

        assert success is True, message
        assert pushes == 3
        # Reset MUST have run exactly twice (once before each of the two
        # rebases) and MUST have targeted the SAME fixer SHA captured at
        # commit-time.
        assert reset_targets == [captured_fixer_sha, captured_fixer_sha], reset_targets

        # And the reset MUST precede each rebase in argv order.
        rebase_cmd_index = [
            i
            for i, cmd in enumerate(recorded)
            if "rebase" in cmd
            and "--onto" in cmd
            and "FETCH_HEAD" in cmd
        ]
        reset_cmd_index = [
            i
            for i, cmd in enumerate(recorded)
            if len(cmd) >= 3 and cmd[:3] == ["git", "reset", "--hard"]
        ]
        assert len(rebase_cmd_index) == 2
        assert len(reset_cmd_index) == 2
        for reset_idx, rebase_idx in zip(reset_cmd_index, rebase_cmd_index):
            assert reset_idx < rebase_idx, (reset_idx, rebase_idx, recorded)

    def test_rebase_resets_to_supplied_fixer_sha_before_running_rebase(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Standalone contract test for ``_rebase_onto_updated_pr_head``: it
        MUST hard-reset the worktree to the supplied ``fixer_sha`` BEFORE
        invoking ``git rebase``, regardless of where HEAD currently sits.
        """
        import pdd.checkup_review_loop as mod

        monkeypatch.setattr(
            mod,
            "_fetch_pr_head_for_rebase",
            lambda *_a, **_kw: (True, ""),
        )

        recorded: List[List[str]] = []

        def fake_run(cmd: List[str], **_kwargs: Any):
            recorded.append(list(cmd))
            return type("R", (), {"returncode": 0, "stdout": "", "stderr": ""})()

        monkeypatch.setattr(mod.subprocess, "run", fake_run)

        sha = "0123456789abcdef0123456789abcdef01234567"
        success, message = mod._rebase_onto_updated_pr_head(
            tmp_path,
            clone_url="https://github.com/o/r.git",
            head_ref="feature",
            repo_owner="o",
            repo_name="r",
            fixer_sha=sha,
        )

        assert success is True, message
        # First subprocess.run call MUST be the reset, second MUST be the
        # rebase. No other commands in between.
        assert recorded[0] == ["git", "reset", "--hard", sha]
        assert recorded[1][:5] == [
            "git",
            "-c",
            "user.name=PDD Bot",
            "-c",
            "user.email=pdd-bot@users.noreply.github.com",
        ]
        assert "rebase" in recorded[1] and "--onto" in recorded[1]


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


# ---------------------------------------------------------------------------
# Issue #1063: deterministic prompt-source guard
#
# The review loop's fixer can patch a generated code file (e.g. ``pdd/foo.py``)
# without updating its owning prompt source (``pdd/prompts/foo_python.prompt``),
# letting prompt/code drift land on the PR head. The guard MUST refuse to push
# any fix whose changed paths include an architecture-registered module whose
# owning prompt is NOT also part of the same change set.
# ---------------------------------------------------------------------------


def _write_arch_json(worktree: Path, modules: List[Dict[str, Any]]) -> Path:
    """Write a bare-list ``architecture.json`` to ``worktree``."""
    path = worktree / "architecture.json"
    path.write_text(json.dumps(modules, indent=2), encoding="utf-8")
    return path


def _commit_arch_to_head(worktree: Path, modules: List[Dict[str, Any]]) -> Path:
    """Initialize a git repo in ``worktree`` and commit ``architecture.json`` to HEAD.

    Required after review pass #3 Finding 2: ``_load_prompt_source_map``
    reads via ``git show HEAD:architecture.json`` (not the worktree
    filesystem) to prevent a fixer from removing its own registry
    entry in the same change set. Tests that previously seeded the
    registry by writing to the worktree alone now need a real commit.
    """
    path = _write_arch_json(worktree, modules)
    subprocess.run(["git", "init", "-q"], cwd=worktree, check=True)
    subprocess.run(
        ["git", "config", "user.email", "test@example.com"],
        cwd=worktree,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Test"], cwd=worktree, check=True
    )
    subprocess.run(
        ["git", "add", "architecture.json"], cwd=worktree, check=True
    )
    subprocess.run(
        ["git", "commit", "-q", "-m", "seed registry"],
        cwd=worktree,
        check=True,
    )
    return path


def _prompt_module(filename: str, filepath: str) -> Dict[str, Any]:
    """Minimal architecture module shape for testing the guard mapping."""
    return {"filename": filename, "filepath": filepath}


class TestPromptSourceGuardHelper:
    """Unit tests for ``_check_prompt_source_guard``.

    The helper is pure-function: it takes a worktree and a list of
    changed-file paths (POSIX, relative to worktree root) and returns
    ``None`` to allow the push or a refusal string for the policy layer
    to stash into ``state.stop_reason``.  All of the behavioural contract
    encoded in issue #1063 lives here so the runtime integration tests
    can stay focused on wiring.
    """

    @staticmethod
    def _seed_prompt(worktree: Path, rel_prompt: str) -> Path:
        """Place a non-empty prompt file at ``worktree / rel_prompt``."""
        prompt_path = worktree / rel_prompt
        prompt_path.parent.mkdir(parents=True, exist_ok=True)
        prompt_path.write_text("prompt body\n", encoding="utf-8")
        return prompt_path

    @staticmethod
    def _seed_code(worktree: Path, rel_code: str) -> Path:
        """Place a non-empty code file at ``worktree / rel_code``.

        Required for tests of the original-#1063 drift case (code
        modified, prompt unchanged) after review pass #3 Finding 1:
        the guard now distinguishes "code persists on disk" from
        "code retired" via ``Path.is_file()``.
        """
        code_path = worktree / rel_code
        code_path.parent.mkdir(parents=True, exist_ok=True)
        code_path.write_text("# generated code\n", encoding="utf-8")
        return code_path

    def test_registered_code_changed_without_prompt_is_refused(
        self, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import _check_prompt_source_guard

        _commit_arch_to_head(
            tmp_path,
            [_prompt_module("agentic_update_python.prompt", "pdd/agentic_update.py")],
        )
        self._seed_code(tmp_path, "pdd/agentic_update.py")
        self._seed_prompt(tmp_path, "pdd/prompts/agentic_update_python.prompt")

        reason = _check_prompt_source_guard(tmp_path, ["pdd/agentic_update.py"])

        assert reason is not None
        # The refusal must name BOTH the code path AND its owning prompt
        # so an operator can act on the message without re-deriving the
        # mapping from architecture.json.
        assert "pdd/agentic_update.py" in reason
        assert "pdd/prompts/agentic_update_python.prompt" in reason
        # The refusal must include the prescribed call-to-action.
        assert "prompt source" in reason.lower()

    def test_registered_code_changed_with_prompt_is_allowed(
        self, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import _check_prompt_source_guard

        _commit_arch_to_head(
            tmp_path,
            [_prompt_module("agentic_update_python.prompt", "pdd/agentic_update.py")],
        )
        self._seed_code(tmp_path, "pdd/agentic_update.py")
        self._seed_prompt(tmp_path, "pdd/prompts/agentic_update_python.prompt")

        reason = _check_prompt_source_guard(
            tmp_path,
            [
                "pdd/agentic_update.py",
                "pdd/prompts/agentic_update_python.prompt",
            ],
        )

        assert reason is None

    def test_unregistered_changed_file_is_allowed(self, tmp_path: Path) -> None:
        from pdd.checkup_review_loop import _check_prompt_source_guard

        # Architecture registers a different module so the guard has a
        # non-empty mapping but the changed file is outside the prompt-
        # owned set.  The guard MUST NOT widen its scope to unregistered
        # paths (tests/ in particular).
        _commit_arch_to_head(
            tmp_path,
            [_prompt_module("agentic_update_python.prompt", "pdd/agentic_update.py")],
        )
        self._seed_prompt(tmp_path, "pdd/prompts/agentic_update_python.prompt")

        reason = _check_prompt_source_guard(
            tmp_path,
            ["tests/test_agentic_update.py", "docs/notes.md"],
        )

        assert reason is None

    def test_multiple_offenders_are_enumerated(self, tmp_path: Path) -> None:
        from pdd.checkup_review_loop import _check_prompt_source_guard

        _commit_arch_to_head(
            tmp_path,
            [
                _prompt_module(
                    "agentic_update_python.prompt", "pdd/agentic_update.py"
                ),
                _prompt_module(
                    "checkup_review_loop_python.prompt",
                    "pdd/checkup_review_loop.py",
                ),
            ],
        )
        self._seed_code(tmp_path, "pdd/agentic_update.py")
        self._seed_code(tmp_path, "pdd/checkup_review_loop.py")
        self._seed_prompt(tmp_path, "pdd/prompts/agentic_update_python.prompt")
        self._seed_prompt(tmp_path, "pdd/prompts/checkup_review_loop_python.prompt")

        reason = _check_prompt_source_guard(
            tmp_path,
            [
                "pdd/agentic_update.py",
                "pdd/checkup_review_loop.py",
            ],
        )

        assert reason is not None
        assert "pdd/agentic_update.py" in reason
        assert "pdd/checkup_review_loop.py" in reason
        assert "pdd/prompts/agentic_update_python.prompt" in reason
        assert "pdd/prompts/checkup_review_loop_python.prompt" in reason

    def test_mixed_changes_block_when_one_pair_is_incomplete(
        self, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import _check_prompt_source_guard

        _commit_arch_to_head(
            tmp_path,
            [
                _prompt_module(
                    "agentic_update_python.prompt", "pdd/agentic_update.py"
                ),
                _prompt_module(
                    "checkup_review_loop_python.prompt",
                    "pdd/checkup_review_loop.py",
                ),
            ],
        )
        self._seed_code(tmp_path, "pdd/agentic_update.py")
        self._seed_code(tmp_path, "pdd/checkup_review_loop.py")
        self._seed_prompt(tmp_path, "pdd/prompts/agentic_update_python.prompt")
        self._seed_prompt(tmp_path, "pdd/prompts/checkup_review_loop_python.prompt")

        reason = _check_prompt_source_guard(
            tmp_path,
            [
                # agentic_update.py has its prompt updated alongside - OK
                "pdd/agentic_update.py",
                "pdd/prompts/agentic_update_python.prompt",
                # checkup_review_loop.py does NOT - this MUST trip the guard
                "pdd/checkup_review_loop.py",
            ],
        )

        assert reason is not None
        assert "pdd/checkup_review_loop.py" in reason
        assert "pdd/prompts/checkup_review_loop_python.prompt" in reason
        # The compliant pair must NOT be named as an offender.
        assert "pdd/agentic_update.py" not in reason.split("checkup_review_loop")[0]

    def test_missing_architecture_json_degrades_gracefully(
        self, tmp_path: Path, caplog: pytest.LogCaptureFixture
    ) -> None:
        from pdd.checkup_review_loop import _check_prompt_source_guard

        # No architecture.json in tmp_path on purpose.
        with caplog.at_level("WARNING", logger="pdd.checkup_review_loop"):
            reason = _check_prompt_source_guard(
                tmp_path, ["pdd/agentic_update.py"]
            )

        assert reason is None
        # The operator must learn the guard was disabled this round.
        assert any(
            "architecture.json" in rec.getMessage() for rec in caplog.records
        )

    def test_malformed_architecture_json_degrades_gracefully(
        self, tmp_path: Path, caplog: pytest.LogCaptureFixture
    ) -> None:
        """Genuinely exercise the JSON-decode failure path against
        HEAD (review pass #3 Finding 2 switched the read source to
        ``git show HEAD:architecture.json``). Commits a malformed
        registry to HEAD so the helper hits the JSONDecodeError
        branch rather than the no-repo / no-HEAD branch.
        """
        from pdd.checkup_review_loop import _check_prompt_source_guard

        # Initialize a real git repo and commit garbage as
        # architecture.json so HEAD's blob is unparseable.
        subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "config", "user.email", "test@example.com"],
            cwd=tmp_path,
            check=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Test"],
            cwd=tmp_path,
            check=True,
        )
        (tmp_path / "architecture.json").write_text(
            "this is not json {", encoding="utf-8"
        )
        subprocess.run(
            ["git", "add", "architecture.json"], cwd=tmp_path, check=True
        )
        subprocess.run(
            ["git", "commit", "-q", "-m", "garbage registry"],
            cwd=tmp_path,
            check=True,
        )

        with caplog.at_level("WARNING", logger="pdd.checkup_review_loop"):
            reason = _check_prompt_source_guard(
                tmp_path, ["pdd/agentic_update.py"]
            )

        assert reason is None
        assert any(
            "unparseable" in rec.getMessage() for rec in caplog.records
        )

    def test_code_missing_with_prompt_missing_is_allowed(
        self, tmp_path: Path
    ) -> None:
        """When the registered code path is in the change set but the
        code file is absent from disk after the change, there is
        nothing to drift from. Allow regardless of the prompt's fate.

        Replaces the round-2 stale-registry-skip-with-warning test:
        review pass #3 Finding 1 swapped the "prompt missing on disk"
        warn-and-skip branch for an unconditional block (because the
        same disk-state shape with code PRESENT is the worst-drift
        attack). The graceful-degradation guarantee now hinges on
        ``code_still_exists``: when the code is gone, the contract is
        irrelevant.
        """
        from pdd.checkup_review_loop import _check_prompt_source_guard

        _commit_arch_to_head(
            tmp_path,
            [_prompt_module("agentic_update_python.prompt", "pdd/agentic_update.py")],
        )
        # Neither file on disk.

        reason = _check_prompt_source_guard(
            tmp_path, ["pdd/agentic_update.py"]
        )

        assert reason is None

    def test_code_present_with_prompt_missing_is_refused(
        self, tmp_path: Path
    ) -> None:
        """The disk-state attack: code persists on disk, prompt is
        missing, and the prompt is NOT in the change set (a pre-
        existing stale-registry state, or a separate deletion the
        fixer is exploiting). Round-2 logged a warning and skipped;
        review pass #3 Finding 1 rejects that as too permissive and
        requires this to BLOCK.

        Rationale: a code edit against a destroyed source of truth
        cannot be regenerated from the prompt later. Brick auto-heal
        on this state rather than let the bot's edits ride.
        """
        from pdd.checkup_review_loop import _check_prompt_source_guard

        _commit_arch_to_head(
            tmp_path,
            [_prompt_module("agentic_update_python.prompt", "pdd/agentic_update.py")],
        )
        # Code present, prompt absent.
        self._seed_code(tmp_path, "pdd/agentic_update.py")

        reason = _check_prompt_source_guard(
            tmp_path, ["pdd/agentic_update.py"]
        )

        assert reason is not None
        assert "pdd/agentic_update.py" in reason
        assert "pdd/prompts/agentic_update_python.prompt" in reason

    def test_guard_reads_registry_from_head_not_worktree(
        self, tmp_path: Path
    ) -> None:
        """The guard MUST consult ``architecture.json`` at HEAD, not
        the worktree filesystem (review pass #3 Finding 2).

        Otherwise a fixer can remove its own registry entry in the
        same change set and slip past the guard. This test commits
        an entry mapping ``pdd/bogus.py -> bogus_python.prompt`` to
        HEAD, then overwrites the worktree's ``architecture.json``
        with an empty list (simulating the fixer's evasion), then
        confirms the guard still blocks because the HEAD registry
        retains the entry.
        """
        from pdd.checkup_review_loop import _check_prompt_source_guard

        _commit_arch_to_head(
            tmp_path,
            [_prompt_module("bogus_python.prompt", "pdd/bogus.py")],
        )
        # Fixer evasion: rewrite the worktree's architecture.json to
        # remove the entry. The HEAD copy still has it.
        _write_arch_json(tmp_path, [])
        self._seed_code(tmp_path, "pdd/bogus.py")
        self._seed_prompt(tmp_path, "pdd/prompts/bogus_python.prompt")

        reason = _check_prompt_source_guard(
            tmp_path,
            ["pdd/bogus.py", "architecture.json"],
        )

        assert reason is not None
        assert "pdd/bogus.py" in reason
        assert "pdd/prompts/bogus_python.prompt" in reason

    def test_no_changed_files_is_allowed(self, tmp_path: Path) -> None:
        from pdd.checkup_review_loop import _check_prompt_source_guard

        # No commit/registry needed: the guard returns None on empty
        # changed_files BEFORE consulting any registry.
        assert _check_prompt_source_guard(tmp_path, []) is None

    def test_code_changed_with_prompt_deleted_in_same_change_set_is_allowed(
        self, tmp_path: Path
    ) -> None:
        """Module retirement is a legitimate, contract-respecting change.

        When the fixer/user deletes BOTH the registered code file AND
        its owning prompt in the same change set (the code is gone
        from disk, not just modified), the source of truth is
        retired together with its generated artifact. The guard MUST
        allow this rather than block on the missing prompt (codex
        review pass #2 Finding B). The distinguishing detail from
        the worse drift case (code persists, prompt deleted) is that
        the code file is also absent on disk.
        """
        from pdd.checkup_review_loop import _check_prompt_source_guard

        # Architecture still lists the module, but BOTH files are
        # absent from disk - this is the retirement scenario where
        # the next commit will drop the registry entry too.
        _commit_arch_to_head(
            tmp_path,
            [_prompt_module("agentic_update_python.prompt", "pdd/agentic_update.py")],
        )
        # Intentionally do NOT create either the code file or the
        # prompt file on disk - both have been deleted in this change
        # set.

        reason = _check_prompt_source_guard(
            tmp_path,
            [
                "pdd/agentic_update.py",
                "pdd/prompts/agentic_update_python.prompt",
            ],
        )

        # Allowed: the code is gone, there is nothing to drift from.
        assert reason is None

    def test_code_modified_with_prompt_deleted_only_is_refused(
        self, tmp_path: Path
    ) -> None:
        """Finding 1 (review pass #3): code persists, prompt deleted.

        The fixer modifies ``pdd/foo.py`` (code still on disk) AND
        deletes ``pdd/prompts/foo_python.prompt`` in the same change
        set. Both paths appear in the change set, but the source of
        truth has been destroyed while the generated artifact
        remains - this is strictly WORSE drift than the original
        #1063 case. The guard MUST block this.

        Round-2's "prompt-in-change-set → allow" branch was scoped to
        module retirement only; this test pins the disk-state check
        that distinguishes retirement (both gone) from the worse
        drift (code persists, prompt gone).
        """
        from pdd.checkup_review_loop import _check_prompt_source_guard

        _commit_arch_to_head(
            tmp_path,
            [_prompt_module("foo_python.prompt", "pdd/foo.py")],
        )
        # Code persists on disk (modified, not deleted).
        (tmp_path / "pdd").mkdir(parents=True, exist_ok=True)
        (tmp_path / "pdd" / "foo.py").write_text(
            "modified code\n", encoding="utf-8"
        )
        # Prompt was deleted in this change set - intentionally NOT
        # creating it on disk.

        reason = _check_prompt_source_guard(
            tmp_path,
            [
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
            ],
        )

        assert reason is not None
        # The refusal MUST name both paths so the operator can act.
        assert "pdd/foo.py" in reason
        assert "pdd/prompts/foo_python.prompt" in reason


class TestPromptSourceGuardChangedFilesParsing:
    """``_git_changed_files`` must surface rename old+new paths.

    Renames are reported by ``git status --porcelain`` as
    ``R  old -> new``. The original parser collapsed that into the
    literal ``"old -> new"`` string, which never matched any
    architecture-registry code-path key — so a registered file could
    be renamed out from under the registry without tripping the
    prompt-source guard (codex review pass #2 Finding A).

    These tests exercise the real ``git`` invocation against a tmp
    git repo. Monkeypatching ``_git_changed_files`` would hide the
    bug because the parsing is the thing being tested.
    """

    @staticmethod
    def _init_repo(worktree: Path) -> None:
        """Initialize a minimal git repo with a deterministic identity."""
        subprocess.run(["git", "init", "-q"], cwd=worktree, check=True)
        subprocess.run(
            ["git", "config", "user.email", "test@example.com"],
            cwd=worktree,
            check=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Test"], cwd=worktree, check=True
        )

    def test_changed_files_includes_both_paths_for_rename(
        self, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import _git_changed_files

        self._init_repo(tmp_path)
        (tmp_path / "pdd").mkdir()
        (tmp_path / "pdd" / "foo.py").write_text("x\n", encoding="utf-8")
        subprocess.run(["git", "add", "-A"], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "commit", "-q", "-m", "init"], cwd=tmp_path, check=True
        )

        # Rename the registered code file.
        subprocess.run(
            ["git", "mv", "pdd/foo.py", "pdd/foo_v2.py"],
            cwd=tmp_path,
            check=True,
        )

        changed = _git_changed_files(tmp_path)

        # BOTH paths must appear so the guard can match the old path
        # against the architecture registry.
        assert "pdd/foo.py" in changed
        assert "pdd/foo_v2.py" in changed
        # And the literal "old -> new" collapsed string MUST NOT appear.
        assert not any("->" in entry for entry in changed)

    def test_guard_handles_renamed_registered_file(
        self, tmp_path: Path
    ) -> None:
        """End-to-end: a rename of a registered code file without its
        prompt change MUST be refused by the guard.
        """
        from pdd.checkup_review_loop import (
            _check_prompt_source_guard,
            _git_changed_files,
        )

        self._init_repo(tmp_path)
        (tmp_path / "pdd" / "prompts").mkdir(parents=True)
        (tmp_path / "pdd" / "agentic_update.py").write_text(
            "code\n", encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "agentic_update_python.prompt").write_text(
            "prompt body\n", encoding="utf-8"
        )
        _write_arch_json(
            tmp_path,
            [
                _prompt_module(
                    "agentic_update_python.prompt", "pdd/agentic_update.py"
                )
            ],
        )
        subprocess.run(["git", "add", "-A"], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "commit", "-q", "-m", "init"], cwd=tmp_path, check=True
        )

        # The fixer renames the registered code file without touching
        # the prompt - exactly the rename-handling drift case.
        subprocess.run(
            ["git", "mv", "pdd/agentic_update.py", "pdd/agentic_update_v2.py"],
            cwd=tmp_path,
            check=True,
        )

        changed = _git_changed_files(tmp_path)
        reason = _check_prompt_source_guard(tmp_path, changed)

        assert reason is not None
        # The refusal must name the registered (old) path that moved
        # out from under its owning prompt.
        assert "pdd/agentic_update.py" in reason
        assert "pdd/prompts/agentic_update_python.prompt" in reason

    def test_changed_files_excludes_collapsed_rename_literal(
        self, tmp_path: Path
    ) -> None:
        """Regression guard: the parser MUST NOT emit ``"a -> b"``
        strings for any rename, even when the staged rename uses
        unusual path characters.
        """
        from pdd.checkup_review_loop import _git_changed_files

        self._init_repo(tmp_path)
        (tmp_path / "pdd").mkdir()
        (tmp_path / "pdd" / "name with space.py").write_text(
            "x\n", encoding="utf-8"
        )
        subprocess.run(["git", "add", "-A"], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "commit", "-q", "-m", "init"], cwd=tmp_path, check=True
        )
        subprocess.run(
            [
                "git",
                "mv",
                "pdd/name with space.py",
                "pdd/renamed_no_space.py",
            ],
            cwd=tmp_path,
            check=True,
        )

        changed = _git_changed_files(tmp_path)

        # Both paths surface as discrete entries (``-z`` preserves
        # paths exactly without quoting, so the space is intact).
        assert "pdd/name with space.py" in changed
        assert "pdd/renamed_no_space.py" in changed
        # And nothing collapsed with the arrow literal.
        assert not any("->" in entry for entry in changed)

    def test_changed_files_surfaces_deleted_files(
        self, tmp_path: Path
    ) -> None:
        """Belt-and-suspenders for Finding B: confirm an ``rm`` of a
        registered prompt surfaces in ``_git_changed_files`` so the
        same-change-set deletion path in ``_check_prompt_source_guard``
        actually receives the deleted prompt in ``changed_files``. The
        guard tests at the unit layer use synthetic lists; this test
        verifies the helper's real-git output makes that synthetic
        shape correspond to actual filesystem reality.
        """
        from pdd.checkup_review_loop import _git_changed_files

        self._init_repo(tmp_path)
        (tmp_path / "pdd" / "prompts").mkdir(parents=True)
        prompt = tmp_path / "pdd" / "prompts" / "agentic_update_python.prompt"
        prompt.write_text("body\n", encoding="utf-8")
        (tmp_path / "pdd" / "agentic_update.py").write_text(
            "code\n", encoding="utf-8"
        )
        subprocess.run(["git", "add", "-A"], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "commit", "-q", "-m", "init"], cwd=tmp_path, check=True
        )

        # Edit code and delete prompt - the module-retirement scenario.
        (tmp_path / "pdd" / "agentic_update.py").write_text(
            "newcode\n", encoding="utf-8"
        )
        prompt.unlink()

        changed = _git_changed_files(tmp_path)

        # Both the modified code and the deleted prompt MUST surface
        # so the guard's "prompt in change set" check at step (2) of
        # the new check order can see it.
        assert "pdd/agentic_update.py" in changed
        assert "pdd/prompts/agentic_update_python.prompt" in changed

    def test_paired_rename_of_code_and_prompt_is_allowed(
        self, tmp_path: Path
    ) -> None:
        """Legitimate-refactor case (advisor reconciliation of
        Findings 1 and A): the fixer renames BOTH the registered
        code file AND its owning prompt in the same change set. The
        registered code-path is no longer on disk (renamed away)
        and the registered prompt-path is also no longer on disk
        (renamed away). Both old paths surface in the change set
        via the rename-detection emitted by ``_git_changed_files``.

        Under the reconciled check order, the "code gone, prompt
        also gone" branch hits the legitimate-retirement / paired-
        refactor allow branch.
        """
        from pdd.checkup_review_loop import (
            _check_prompt_source_guard,
            _git_changed_files,
        )

        self._init_repo(tmp_path)
        (tmp_path / "pdd" / "prompts").mkdir(parents=True)
        (tmp_path / "pdd" / "agentic_update.py").write_text(
            "code\n", encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "agentic_update_python.prompt").write_text(
            "prompt body\n", encoding="utf-8"
        )
        _write_arch_json(
            tmp_path,
            [
                _prompt_module(
                    "agentic_update_python.prompt", "pdd/agentic_update.py"
                )
            ],
        )
        subprocess.run(["git", "add", "-A"], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "commit", "-q", "-m", "init"], cwd=tmp_path, check=True
        )

        # Paired rename: BOTH code and prompt move to new paths.
        subprocess.run(
            ["git", "mv", "pdd/agentic_update.py", "pdd/agentic_update_v2.py"],
            cwd=tmp_path,
            check=True,
        )
        subprocess.run(
            [
                "git",
                "mv",
                "pdd/prompts/agentic_update_python.prompt",
                "pdd/prompts/agentic_update_v2_python.prompt",
            ],
            cwd=tmp_path,
            check=True,
        )

        changed = _git_changed_files(tmp_path)
        # Sanity: both old paths appear in the change set via the
        # ``-z`` rename-detection emit.
        assert "pdd/agentic_update.py" in changed
        assert "pdd/prompts/agentic_update_python.prompt" in changed

        reason = _check_prompt_source_guard(tmp_path, changed)

        # Allowed: this is a legitimate paired refactor, not drift.
        assert reason is None


class TestGitChangedFilesPorcelainDelegation:
    """``_git_changed_files`` must delegate parsing to the shared
    :mod:`pdd.git_porcelain` helper so copies do NOT emit the copy
    source as a "changed" path.

    A copy (``C`` record) means git detected that a new file is a
    duplicate of an existing one. The destination is the new/changed
    path; the source is referenced but not modified. The earlier
    hand-rolled parser at the call site emitted BOTH paths, which would
    cause ``_check_prompt_source_guard`` to incorrectly flag the copy
    source's prompt-owned module as needing a prompt update — a latent
    bug surfaced if ``git config status.renames=copies`` (or equivalent
    copy detection) were ever enabled.

    These tests stub ``subprocess.run`` directly so they don't depend on
    git's copy-detection heuristics, and they pin the exact byte-level
    contract the shared helper expects.
    """

    def test_copy_record_only_emits_destination_not_source(
        self, monkeypatch
    ) -> None:
        """``C  pdd/copied.py\\x00pdd/source.py\\x00 M tests/foo.py\\x00``
        must yield ``["pdd/copied.py", "tests/foo.py"]``. The source
        path of a copy is unchanged and must NOT appear.
        """
        from pdd.checkup_review_loop import _git_changed_files

        class _FakeResult:
            returncode = 0
            stdout = (
                b"C  pdd/copied.py\x00pdd/source.py\x00"
                b" M tests/foo.py\x00"
            )

        def _fake_run(cmd, **kwargs):
            # Match the exact invocation; ensure text-mode is NOT used.
            assert cmd[:3] == ["git", "status", "--porcelain=v1"]
            assert "-z" in cmd
            assert kwargs.get("text") is not True
            return _FakeResult()

        monkeypatch.setattr(
            "pdd.checkup_review_loop.subprocess.run", _fake_run
        )

        result = _git_changed_files(Path("/tmp/does-not-matter"))

        assert result == ["pdd/copied.py", "tests/foo.py"], (
            f"copy source must not appear in changed-files; got {result!r}"
        )
        assert "pdd/source.py" not in result

    def test_rename_record_emits_both_old_and_new_paths(
        self, monkeypatch
    ) -> None:
        """``R  new.py\\x00old.py\\x00`` must yield ``["new.py", "old.py"]``
        — renames surface both sides so the guard sees the registered
        old path move out from under its prompt.
        """
        from pdd.checkup_review_loop import _git_changed_files

        class _FakeResult:
            returncode = 0
            stdout = b"R  new.py\x00old.py\x00"

        def _fake_run(cmd, **kwargs):
            return _FakeResult()

        monkeypatch.setattr(
            "pdd.checkup_review_loop.subprocess.run", _fake_run
        )

        result = _git_changed_files(Path("/tmp/does-not-matter"))

        assert result == ["new.py", "old.py"], (
            f"rename must emit both sides; got {result!r}"
        )


class TestPromptSourceGuardIntegration:
    """Wires the guard into the main review loop.

    Confirms the policy layer (not the push helper) refuses the push,
    keeps affected findings open, and renders an actionable refusal in
    the final report.
    """

    def _patch_io(self, monkeypatch: Any, tmp_path: Path) -> None:
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
        monkeypatch.setattr(mod, "_post_review_loop_report", lambda *a, **k: None)

    def _seed_registry(
        self, tmp_path: Path, modules: List[Dict[str, Any]]
    ) -> None:
        # ``_commit_arch_to_head`` initializes a git repo + commits the
        # registry to HEAD so the post-Finding-2 ``git show
        # HEAD:architecture.json`` read in ``_load_prompt_source_map``
        # finds the registry. Also seed the code file(s) so the
        # post-Finding-1 ``code_still_exists`` check sees them and the
        # original drift case (code modified, prompt unchanged) reaches
        # the drift branch.
        _commit_arch_to_head(tmp_path, modules)
        for entry in modules:
            code_full = tmp_path / entry["filepath"]
            code_full.parent.mkdir(parents=True, exist_ok=True)
            code_full.write_text("# generated code\n", encoding="utf-8")
            prompt_rel = f"pdd/prompts/{entry['filename']}"
            full = tmp_path / prompt_rel
            full.parent.mkdir(parents=True, exist_ok=True)
            full.write_text("prompt body\n", encoding="utf-8")

    def _finding(self, location: str = "pdd/agentic_update.py:1") -> Dict[str, str]:
        return {
            "severity": "blocker",
            "area": "api",
            "location": location,
            "evidence": "broke",
            "finding": "broken api",
            "required_fix": "fix it",
        }

    def test_loop_refuses_push_when_only_generated_code_changed(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        self._seed_registry(
            tmp_path,
            [_prompt_module("agentic_update_python.prompt", "pdd/agentic_update.py")],
        )

        # The fake fixer "edits" agentic_update.py without touching its
        # prompt - exactly the failure mode from commit bf57242d.
        monkeypatch.setattr(
            mod, "_git_changed_files", lambda _wt: ["pdd/agentic_update.py"]
        )
        push_calls: List[Tuple[Any, Any, Any]] = []

        def fake_push(*args: Any, **kwargs: Any) -> Tuple[bool, str]:
            push_calls.append((args, kwargs, "called"))
            return True, "pushed"

        monkeypatch.setattr(mod, "_commit_and_push_if_changed", fake_push)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"edited","changed_files":["pdd/agentic_update.py"]}',
                    0.1,
                    role,
                )
            return True, _json("findings", [self._finding()]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1, require_final_fresh_review=False),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        # ``success`` is the loop's "ran without crashing" signal per the
        # docstring at pdd/checkup_review_loop.py:706-708 — it is NOT the
        # ship gate. The verdict adapter parses ``reviewer-status:`` and
        # ``fresh-final-review:`` markers in the rendered report; we assert
        # those directly below so a future drift between the loop's
        # internal completion flag and the ship-gating signals cannot
        # silently turn this refusal into a green check on the PR. See
        # also ``test_failed_push_aborts_loop_without_running_verifier``
        # which encodes the same ``success=True`` + non-clean-status
        # contract for the analogous push-failure refusal path.
        assert success is True

        # The policy layer MUST refuse before the push helper is invoked.
        assert push_calls == []

        # Ship-gate markers MUST signal non-clean. The verdict adapter
        # treats any reviewer-status row whose status is not in
        # ``clean_reviewer_states`` as non-shippable; ``fresh-final-
        # review: missing`` keeps the final-fresh gate unsatisfied.
        assert "reviewer-status: codex=findings" in report
        assert "fresh-final-review: missing" in report
        assert "issue_aligned: unknown" in report

        # The refusal MUST name both paths so the operator can act.
        assert "pdd/agentic_update.py" in report
        assert "pdd/prompts/agentic_update_python.prompt" in report

        # The original finding stays OPEN in the findings table. Pin the
        # exact row shape so we assert against the verdict-adapter-visible
        # marker (``| <severity> | open |``) rather than substring-greping
        # the whole report. The row appears under the ``### Findings``
        # heading; status ``open`` is what the adapter consumes.
        assert "### Findings" in report
        findings_section = report.split("### Findings", 1)[1].split("### ", 1)[0]
        assert "| blocker | open |" in findings_section
        assert "broken api" in findings_section
        # And confirm the finding was NOT moved to the fixed bucket.
        assert "| blocker | fixed |" not in findings_section

    def test_loop_allows_push_when_prompt_changed_with_code(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        self._seed_registry(
            tmp_path,
            [_prompt_module("agentic_update_python.prompt", "pdd/agentic_update.py")],
        )

        # The fake fixer "edits" BOTH the code and the prompt.
        monkeypatch.setattr(
            mod,
            "_git_changed_files",
            lambda _wt: [
                "pdd/agentic_update.py",
                "pdd/prompts/agentic_update_python.prompt",
            ],
        )
        push_calls: List[str] = []

        def fake_push(*_a: Any, **_kw: Any) -> Tuple[bool, str]:
            push_calls.append("called")
            return True, "pushed"

        monkeypatch.setattr(mod, "_commit_and_push_if_changed", fake_push)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if "verify-" in label:
                return True, _json("clean"), 0.1, role
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"edited","changed_files":["pdd/agentic_update.py","pdd/prompts/agentic_update_python.prompt"]}',
                    0.1,
                    role,
                )
            return True, _json("findings", [self._finding()]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, _report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1, require_final_fresh_review=False),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        # The guard MUST NOT block the compliant change set.
        assert push_calls, "push helper should have been invoked"

    def test_loop_allows_push_when_changed_file_is_unregistered(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        self._seed_registry(
            tmp_path,
            [_prompt_module("agentic_update_python.prompt", "pdd/agentic_update.py")],
        )

        # The fixer changed a file that is NOT in the registry (a test).
        monkeypatch.setattr(
            mod,
            "_git_changed_files",
            lambda _wt: ["tests/test_agentic_update.py"],
        )
        push_calls: List[str] = []

        def fake_push(*_a: Any, **_kw: Any) -> Tuple[bool, str]:
            push_calls.append("called")
            return True, "pushed"

        monkeypatch.setattr(mod, "_commit_and_push_if_changed", fake_push)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if "verify-" in label:
                return True, _json("clean"), 0.1, role
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"edited","changed_files":["tests/test_agentic_update.py"]}',
                    0.1,
                    role,
                )
            return True, _json("findings", [self._finding()]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, _report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1, require_final_fresh_review=False),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        # Unregistered files are out of scope for the guard.
        assert push_calls, "push helper should have been invoked"

    def test_guard_trip_fully_terminates_loop_across_multiple_rounds(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """A guard trip MUST end the entire run, not just the current
        round. With ``max_rounds=3`` and a fixer that would otherwise
        keep producing code-only edits, the loop must invoke the fixer
        once on round 1 and stop — never running rounds 2 or 3, and
        never invoking the push helper at any point.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        self._seed_registry(
            tmp_path,
            [_prompt_module("agentic_update_python.prompt", "pdd/agentic_update.py")],
        )

        monkeypatch.setattr(
            mod, "_git_changed_files", lambda _wt: ["pdd/agentic_update.py"]
        )
        push_calls: List[str] = []

        def fake_push(*_a: Any, **_kw: Any) -> Tuple[bool, str]:
            push_calls.append("called")
            return True, "pushed"

        monkeypatch.setattr(mod, "_commit_and_push_if_changed", fake_push)

        call_labels: List[str] = []

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            call_labels.append(label)
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"edited","changed_files":["pdd/agentic_update.py"]}',
                    0.1,
                    role,
                )
            return True, _json("findings", [self._finding()]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=3, require_final_fresh_review=False),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        # Push helper is never invoked across the whole run.
        assert push_calls == []
        # The fixer ran exactly once (round 1) before the guard tripped.
        fix_calls = [lbl for lbl in call_labels if "fix-" in lbl]
        assert len(fix_calls) == 1, (
            f"fixer must run only once before guard trips, got: {fix_calls}"
        )
        # Round 2/3 review/fix/verify labels MUST NOT appear.
        assert not any("round2" in lbl or "round3" in lbl for lbl in call_labels)
        # The verifier MUST NOT have run either (it only runs after a
        # successful push).
        assert not any("verify-" in lbl for lbl in call_labels)
        # Reviewer-status reflects the refusal, not "clean".
        assert "reviewer-status: codex=findings" in report
        assert "fresh-final-review: missing" in report

    def test_prompt_source_guard_refusal_writes_trust_boundary_artifact(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Issue #1088 audit-trail completeness: when the prompt-source
        guard refuses the push (fixer succeeded but changed only
        generated code), the loop breaks BEFORE the canonical post-push
        artifact rewrite. The per-round ``round-N-fix-...findings.json``
        artifact MUST still carry the in-memory ``FixResult``
        trust-boundary fields — ``fixer_result=attempted`` (the
        subprocess returned success) and ``push_status=not_attempted``
        (the policy layer refused before invoking the push helper).
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        self._seed_registry(
            tmp_path,
            [_prompt_module("agentic_update_python.prompt", "pdd/agentic_update.py")],
        )

        # The fake fixer "edits" agentic_update.py without touching its
        # prompt — exactly the failure mode the guard catches.
        monkeypatch.setattr(
            mod, "_git_changed_files", lambda _wt: ["pdd/agentic_update.py"]
        )

        def fake_push(*_a: Any, **_kw: Any) -> Tuple[bool, str]:
            pytest.fail("push helper must not be invoked when guard refuses")

        monkeypatch.setattr(mod, "_commit_and_push_if_changed", fake_push)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"edited","changed_files":["pdd/agentic_update.py"]}',
                    0.1,
                    role,
                )
            return True, _json("findings", [self._finding()]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, _report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1, require_final_fresh_review=False),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        artifact = json.loads(
            (
                tmp_path
                / ".pdd"
                / "checkup-review-loop"
                / "issue-2-pr-1"
                / "round-1-fix-claude-for-codex.findings.json"
            ).read_text()
        )
        # The fixer subprocess succeeded, so ``fixer_result`` is
        # ``attempted``; the guard refused the push so
        # ``push_status`` stays ``not_attempted`` and both SHA fields
        # remain null.
        assert artifact["fixer_result"] == "attempted", artifact
        assert artifact["push_status"] == "not_attempted", artifact
        assert artifact["local_fixer_commit_sha"] is None, artifact
        assert artifact["pushed_head_sha"] is None, artifact
        assert artifact["round_number"] == 1, artifact
# Issue #1081: architecture-registry edit guard
#
# Coordinated rename + prompt delete + ``architecture.json`` rewrite was
# slipping past the per-entry prompt-source guard (10a). The new guard 10b
# detects registry MUTATIONS themselves: added pair without prompt source on
# disk, removed pair with code still present, or any repoint.
# ---------------------------------------------------------------------------


def _arch_pair(filename: str, filepath: str) -> Dict[str, Any]:
    return {"filename": filename, "filepath": filepath}


def _seed_repo_with_arch(
    worktree: Path,
    modules: List[Dict[str, Any]],
    *,
    extra_files: Dict[str, str] | None = None,
) -> None:
    """Initialize a git repo, commit the architecture registry and the
    code/prompt files for each registered module, plus optional extras.
    """
    subprocess.run(["git", "init", "-q"], cwd=worktree, check=True)
    subprocess.run(
        ["git", "config", "user.email", "test@example.com"],
        cwd=worktree,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Test"], cwd=worktree, check=True
    )
    (worktree / "architecture.json").write_text(
        json.dumps(modules, indent=2), encoding="utf-8"
    )
    for entry in modules:
        code = worktree / entry["filepath"]
        code.parent.mkdir(parents=True, exist_ok=True)
        code.write_text("# generated\n", encoding="utf-8")
        prompt = worktree / "pdd" / "prompts" / entry["filename"]
        prompt.parent.mkdir(parents=True, exist_ok=True)
        prompt.write_text("prompt body\n", encoding="utf-8")
    for rel, body in (extra_files or {}).items():
        path = worktree / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")
    subprocess.run(["git", "add", "-A"], cwd=worktree, check=True)
    subprocess.run(
        ["git", "commit", "-q", "-m", "seed"], cwd=worktree, check=True
    )


class TestArchitectureRegistryEditGuardHelper:
    """Unit tests for ``_check_architecture_registry_edit_guard`` (#1081)."""

    def test_no_architecture_change_is_no_op(self, tmp_path: Path) -> None:
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        # Only a code-only change; architecture.json untouched.
        reason = _check_architecture_registry_edit_guard(
            tmp_path, ["pdd/foo.py"]
        )
        assert reason is None

    def test_coordinated_bypass_with_registry_repoint_is_refused(
        self, tmp_path: Path
    ) -> None:
        """Reproduces issue #1081: rename code, delete prompt, rewrite
        registry. Without 10b, both guards return None and the fix
        lands on the PR.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        # Coordinated mutation:
        #   1. rename pdd/foo.py -> pdd/foo_v2.py
        #   2. delete pdd/prompts/foo_python.prompt
        #   3. rewrite architecture.json to point at the new path
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "foo_v2.py").write_text(
            "# renamed\n", encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        new_arch = [_arch_pair("foo_v2_python.prompt", "pdd/foo_v2.py")]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        changed_files = [
            "architecture.json",
            "pdd/foo_v2.py",
            "pdd/foo.py",
            "pdd/prompts/foo_python.prompt",
        ]
        reason = _check_architecture_registry_edit_guard(
            tmp_path, changed_files
        )
        assert reason is not None
        # The refusal MUST name the added pair so the operator can act.
        assert "pdd/foo_v2.py" in reason
        assert "pdd/prompts/foo_v2_python.prompt" in reason
        assert "without prompt source on disk" in reason
        assert "architecture.json registry edit refused" in reason

    def test_repoint_with_same_prompt_name_is_refused(
        self, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        # Rename code, keep the prompt name (prompt still on disk).
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "foo_v2.py").write_text(
            "# renamed\n", encoding="utf-8"
        )
        new_arch = [_arch_pair("foo_python.prompt", "pdd/foo_v2.py")]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            ["architecture.json", "pdd/foo.py", "pdd/foo_v2.py"],
        )
        assert reason is not None
        assert "repointed" in reason
        assert "pdd/foo.py" in reason
        assert "pdd/foo_v2.py" in reason

    def test_legitimate_retirement_is_allowed(self, tmp_path: Path) -> None:
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [
                _arch_pair("foo_python.prompt", "pdd/foo.py"),
                _arch_pair("bar_python.prompt", "pdd/bar.py"),
            ],
        )
        # Retire foo: delete code, delete prompt, drop from registry.
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        new_arch = [_arch_pair("bar_python.prompt", "pdd/bar.py")]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
            ],
        )
        assert reason is None

    def test_registry_wiped_with_code_present_is_refused(
        self, tmp_path: Path
    ) -> None:
        """If the fixer wipes ``architecture.json`` to ``[]`` while the
        registered code/prompt still exist on disk, that is the #1081
        attack shape under the worktree-empty/HEAD-non-empty branch.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        (tmp_path / "architecture.json").write_text("[]", encoding="utf-8")

        reason = _check_architecture_registry_edit_guard(
            tmp_path, ["architecture.json"]
        )
        assert reason is not None
        assert "code still present" in reason
        assert "pdd/foo.py" in reason

    def test_registry_wiped_with_renamed_new_code_is_refused(
        self, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        # This is the registry-wipe variant of #1081: 10a sees the old
        # code and prompt as legitimately retired, but a new generated
        # code path still lands with no prompt source.
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "foo_v2.py").write_text(
            "# renamed\n", encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text("[]", encoding="utf-8")

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/foo_v2.py",
                "pdd/prompts/foo_python.prompt",
            ],
        )
        assert reason is not None
        assert "removed registered pair while new unregistered code path" in reason
        assert "pdd/foo_v2.py" in reason

    def test_registry_wiped_for_full_retirement_is_allowed(
        self, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text("[]", encoding="utf-8")

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
            ],
        )
        assert reason is None

    def test_added_pair_with_prompt_on_disk_and_in_changeset_is_allowed(
        self, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        # Operator adds a NEW registered module with both code and
        # prompt actually written to disk.
        (tmp_path / "pdd" / "baz.py").write_text("# new\n", encoding="utf-8")
        (tmp_path / "pdd" / "prompts" / "baz_python.prompt").write_text(
            "p\n", encoding="utf-8"
        )
        new_arch = [
            _arch_pair("foo_python.prompt", "pdd/foo.py"),
            _arch_pair("baz_python.prompt", "pdd/baz.py"),
        ]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/baz.py",
                "pdd/prompts/baz_python.prompt",
            ],
        )
        assert reason is None

    def test_added_pair_without_prompt_on_disk_is_refused(
        self, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        # Add a registry entry pointing at a prompt name that was
        # never written.
        (tmp_path / "pdd" / "baz.py").write_text("# new\n", encoding="utf-8")
        new_arch = [
            _arch_pair("foo_python.prompt", "pdd/foo.py"),
            _arch_pair("baz_python.prompt", "pdd/baz.py"),
        ]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            ["architecture.json", "pdd/baz.py"],
        )
        assert reason is not None
        assert "pdd/baz.py" in reason
        assert "without prompt source on disk" in reason

    def test_missing_head_registry_degrades_gracefully(
        self, tmp_path: Path, caplog: pytest.LogCaptureFixture
    ) -> None:
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        # No git repo at all → ``git show HEAD:architecture.json`` fails.
        with caplog.at_level("WARNING", logger="pdd.checkup_review_loop"):
            reason = _check_architecture_registry_edit_guard(
                tmp_path, ["architecture.json"]
            )
        assert reason is None
        assert any(
            "architecture-registry guard" in rec.getMessage()
            for rec in caplog.records
        )

    def test_empty_head_registry_degrades_gracefully(
        self, tmp_path: Path, caplog: pytest.LogCaptureFixture
    ) -> None:
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        # HEAD has an empty registry; guard has nothing to defend.
        _seed_repo_with_arch(tmp_path, [])

        with caplog.at_level("WARNING", logger="pdd.checkup_review_loop"):
            reason = _check_architecture_registry_edit_guard(
                tmp_path, ["architecture.json"]
            )
        assert reason is None

    def test_no_arch_edit_implicit_retirement_with_new_code_is_refused(
        self, tmp_path: Path
    ) -> None:
        """Round-3 finding 1: even when ``architecture.json`` is not in
        the change set, an implicit retirement (HEAD-registered pair
        gone from disk) combined with a new unregistered code path
        must be refused. Otherwise the fixer can rename foo.py to
        foo_v2.py and delete the prompt without touching the registry,
        leaving the registry stale and landing unregistered code.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        # No-arch-edit bypass:
        #   1. delete pdd/foo.py (registered code path)
        #   2. delete pdd/prompts/foo_python.prompt (registered prompt)
        #   3. add pdd/foo_v2.py (unregistered new code)
        #   4. leave architecture.json UNTOUCHED
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "foo_v2.py").write_text(
            "# renamed\n", encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "pdd/foo.py",
                "pdd/foo_v2.py",
                "pdd/prompts/foo_python.prompt",
            ],
        )
        assert reason is not None
        assert "architecture.json registry edit refused" in reason
        assert "pdd/foo_v2.py" in reason
        # No-arch-edit variant uses distinct wording so the operator
        # can tell the two #1081 variants apart.
        assert (
            "retired registered pair on disk while new unregistered "
            "code path"
        ) in reason
        assert "architecture.json not updated" in reason

    def test_legitimate_retirement_with_helper_modification_is_allowed(
        self, tmp_path: Path
    ) -> None:
        """Round-3 finding 2: a legitimate retirement that also
        modifies an existing unregistered helper must NOT trip the
        unregistered-new-code scan. The helper existed at HEAD, so it
        is a modification, not an addition.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [
                _arch_pair("foo_python.prompt", "pdd/foo.py"),
                _arch_pair("bar_python.prompt", "pdd/bar.py"),
            ],
            extra_files={"pdd/utils.py": "# helper\n"},
        )
        # Legitimate retirement of foo + modify the unregistered
        # helper pdd/utils.py (which existed at HEAD).
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "pdd" / "utils.py").write_text(
            "# helper (modified)\n", encoding="utf-8"
        )
        new_arch = [_arch_pair("bar_python.prompt", "pdd/bar.py")]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/utils.py",
            ],
        )
        assert reason is None

    def test_symlink_as_new_code_path_under_no_arch_edit_bypass_is_refused(
        self, tmp_path: Path
    ) -> None:
        """Round-3 finding 3 (scan side, opposite polarity): when an
        attacker drops a symlink as the unregistered new code path
        (e.g. ``pdd/foo_v2.py`` -> ``pdd/bar.py``), the scan must
        still count the symlink as presence and refuse. Otherwise
        rejecting only "real files" silently lets the symlink land.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [
                _arch_pair("foo_python.prompt", "pdd/foo.py"),
                _arch_pair("bar_python.prompt", "pdd/bar.py"),
            ],
        )
        # No-arch-edit bypass with symlink:
        #   1. delete pdd/foo.py
        #   2. delete pdd/prompts/foo_python.prompt
        #   3. add pdd/foo_v2.py as a SYMLINK to pdd/bar.py
        #   4. leave architecture.json UNTOUCHED
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "pdd" / "foo_v2.py").symlink_to(tmp_path / "pdd" / "bar.py")

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "pdd/foo.py",
                "pdd/foo_v2.py",
                "pdd/prompts/foo_python.prompt",
            ],
        )
        assert reason is not None
        assert "architecture.json registry edit refused" in reason
        assert "pdd/foo_v2.py" in reason

    def test_added_pair_with_symlink_prompt_is_refused(
        self, tmp_path: Path
    ) -> None:
        """Round-3 finding 3: an added pair whose prompt is a symlink
        (rather than a real file) must be refused. ``Path.is_file()``
        follows symlinks, so a symlink to any existing file would
        otherwise satisfy the prompt-source presence check.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        # Add a new registered pair with the prompt as a symlink to
        # an existing file (here the foo prompt). The forged "prompt
        # source" must NOT pass the guard.
        (tmp_path / "pdd" / "baz.py").write_text("# new\n", encoding="utf-8")
        sym_target = tmp_path / "pdd" / "prompts" / "foo_python.prompt"
        sym = tmp_path / "pdd" / "prompts" / "baz_python.prompt"
        sym.symlink_to(sym_target)
        new_arch = [
            _arch_pair("foo_python.prompt", "pdd/foo.py"),
            _arch_pair("baz_python.prompt", "pdd/baz.py"),
        ]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/baz.py",
                "pdd/prompts/baz_python.prompt",
            ],
        )
        assert reason is not None
        assert "pdd/baz.py" in reason
        assert "without prompt source on disk" in reason

    def test_added_pair_with_py_prompt_is_refused(
        self, tmp_path: Path
    ) -> None:
        """Round-14 finding (codex review pass #14): a fixer rewrites
        ``architecture.json`` to register ``(pdd/foo_v2.py,
        pdd/prompts/foo_v2.py)`` — pointing the "prompt" at a ``.py``
        file. Both files are added in the change set so the existing
        prompt-on-disk + in-changeset check would allow it, and the
        unregistered-new-code scan would skip ``pdd/prompts/foo_v2.py``
        because it is now in ``worktree_registered_paths`` — letting
        ``pdd.prompts.foo_v2`` land as importable unregistered Python.
        The guard MUST reject the added pair because the registered
        prompt path is not a ``.prompt`` file.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        # Retire the original pair and add the disguised pair.
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "pdd" / "foo_v2.py").write_text(
            "# new\n", encoding="utf-8"
        )
        # The "prompt" is actually a .py file (the bypass shape).
        (tmp_path / "pdd" / "prompts" / "foo_v2.py").write_text(
            "# disguised\n", encoding="utf-8"
        )
        new_arch = [
            {"filename": "foo_v2.py", "filepath": "pdd/foo_v2.py"},
        ]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/foo_v2.py",
                "pdd/prompts/foo_v2.py",
            ],
        )
        assert reason is not None
        # The refusal MUST name the disguised pair distinctively so
        # the operator sees the precise attack shape.
        assert "pdd/foo_v2.py" in reason
        assert "pdd/prompts/foo_v2.py" in reason
        assert "not a .prompt file" in reason
        assert "importable code disguised as a prompt" in reason

    def test_added_pair_with_pyc_prompt_is_refused(
        self, tmp_path: Path
    ) -> None:
        """Round-14 follow-up: same shape but with a ``.pyc`` suffix
        instead of ``.py``. Sourceless bytecode is importable via
        ``importlib.machinery.SourcelessFileLoader``, so ``.pyc`` is
        equally lethal disguised as a prompt.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        (tmp_path / "pdd" / "foo_v2.py").write_text(
            "# new\n", encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "foo_v2.pyc").write_bytes(
            b"\x42\x0d\x0d\x0a"
        )
        new_arch = [
            _arch_pair("foo_python.prompt", "pdd/foo.py"),
            {"filename": "foo_v2.pyc", "filepath": "pdd/foo_v2.py"},
        ]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo_v2.py",
                "pdd/prompts/foo_v2.pyc",
            ],
        )
        assert reason is not None
        assert "pdd/prompts/foo_v2.pyc" in reason
        assert "not a .prompt file" in reason

    def test_added_pair_with_so_prompt_is_refused(
        self, tmp_path: Path
    ) -> None:
        """Round-14 follow-up: native extension ``.so`` disguised as a
        prompt. A C extension imports as ``pdd.prompts.<name>`` via
        ``importlib.machinery.ExtensionFileLoader`` with no Python
        source on disk.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        (tmp_path / "pdd" / "foo_v2.py").write_text(
            "# new\n", encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "foo_v2.so").write_bytes(
            b"\x7fELF"
        )
        new_arch = [
            _arch_pair("foo_python.prompt", "pdd/foo.py"),
            {"filename": "foo_v2.so", "filepath": "pdd/foo_v2.py"},
        ]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo_v2.py",
                "pdd/prompts/foo_v2.so",
            ],
        )
        assert reason is not None
        assert "pdd/prompts/foo_v2.so" in reason
        assert "not a .prompt file" in reason

    def test_repoint_to_py_prompt_is_refused_with_disguise_evidence(
        self, tmp_path: Path
    ) -> None:
        """Round-14 finding (repoint variant): a repoint whose new
        prompt path is a ``.py`` file is the same disguised-prompt
        attack shape, dressed as a repoint instead of an added pair.
        The existing repoint check refuses unconditionally, but the
        refusal message MUST distinguish the disguised-prompt shape
        so the operator sees the precise attack.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        # Repoint the existing code at a .py "prompt".
        (tmp_path / "pdd" / "prompts" / "foo_python.py").write_text(
            "# disguised\n", encoding="utf-8"
        )
        new_arch = [
            {"filename": "foo_python.py", "filepath": "pdd/foo.py"},
        ]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/prompts/foo_python.py",
            ],
        )
        assert reason is not None
        assert "repointed pdd/foo.py" in reason
        assert "pdd/prompts/foo_python.py" in reason
        assert "not a .prompt file" in reason
        assert "importable code disguised as a prompt" in reason

    def test_added_pair_with_prompt_suffix_still_allowed_post_r14(
        self, tmp_path: Path
    ) -> None:
        """Round-14 regression: the legitimate add-new-module flow
        (a real ``.prompt`` file alongside new code, both in the
        change set) must STILL be allowed after the new
        ``.prompt``-suffix check is in place. This is the same shape
        as ``test_added_pair_with_prompt_on_disk_and_in_changeset_is_allowed``
        above, but specifically guards against the R14 check
        accidentally tightening the happy path.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        # Add a new registered module with a real .prompt source.
        (tmp_path / "pdd" / "baz.py").write_text("# new\n", encoding="utf-8")
        (tmp_path / "pdd" / "prompts" / "baz_python.prompt").write_text(
            "p\n", encoding="utf-8"
        )
        new_arch = [
            _arch_pair("foo_python.prompt", "pdd/foo.py"),
            _arch_pair("baz_python.prompt", "pdd/baz.py"),
        ]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/baz.py",
                "pdd/prompts/baz_python.prompt",
            ],
        )
        assert reason is None

    def test_swap_repoint_two_pairs_is_refused_with_both_entries(
        self, tmp_path: Path
    ) -> None:
        """Codex round-4 claimed the filepath repoint loop consumes both
        pairs and the prompt loop skips the second repoint. Empirically
        the loop catches both because ``consumed_added`` only contains
        ``(code, new_prompt)`` from the filepath loop -- not
        ``(new_code, prompt)`` -- so the prompt loop's skip check fails
        and the second repoint is recorded. Regression: both repoints
        must appear in the refusal.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        # Worktree: swap variant. Same filepath repoints to a different
        # prompt; same prompt repoints to a different filepath.
        (tmp_path / "pdd" / "bar.py").write_text(
            "# bar\n", encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "bar_python.prompt").write_text(
            "p\n", encoding="utf-8"
        )
        new_arch = [
            _arch_pair("bar_python.prompt", "pdd/foo.py"),
            _arch_pair("foo_python.prompt", "pdd/bar.py"),
        ]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/bar.py",
                "pdd/prompts/bar_python.prompt",
            ],
        )
        assert reason is not None
        # Both repoints MUST appear in the refusal:
        assert "repointed pdd/foo.py" in reason
        assert "repointed pdd/prompts/foo_python.prompt" in reason
        # And the underlying details:
        assert (
            "pdd/prompts/foo_python.prompt to pdd/prompts/bar_python.prompt"
            in reason
        )
        assert "pdd/foo.py to pdd/bar.py" in reason


class TestArchitectureRegistryEditGuardIntegration:
    """Wires the registry-edit guard into ``run_checkup_review_loop``."""

    def _patch_io(self, monkeypatch: Any, tmp_path: Path) -> None:
        import pdd.checkup_review_loop as mod

        monkeypatch.setattr(
            mod, "_setup_pr_worktree", lambda *a, **k: (tmp_path, None)
        )
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
            mod, "_post_review_loop_report", lambda *a, **k: None
        )

    def _finding(self) -> Dict[str, str]:
        return {
            "severity": "blocker",
            "area": "api",
            "location": "pdd/foo.py:1",
            "evidence": "broke",
            "finding": "broken api",
            "required_fix": "fix it",
        }

    def test_loop_refuses_push_on_1081_bypass(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """End-to-end #1081 regression: a fixer that rewrites the
        registry to a new code path + new prompt name must NOT reach
        ``_commit_and_push_if_changed``.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        # Apply the bypass: simulate the fixer's mutations on the
        # worktree filesystem before the guard reads it.
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "foo_v2.py").write_text(
            "# renamed\n", encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        new_arch = [_arch_pair("foo_v2_python.prompt", "pdd/foo_v2.py")]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        monkeypatch.setattr(
            mod,
            "_git_changed_files",
            lambda _wt: [
                "architecture.json",
                "pdd/foo_v2.py",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
            ],
        )
        push_calls: List[Any] = []

        def fake_push(*args: Any, **kwargs: Any) -> Tuple[bool, str]:
            push_calls.append((args, kwargs))
            return True, "pushed"

        monkeypatch.setattr(mod, "_commit_and_push_if_changed", fake_push)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"edited","changed_files":'
                    '["architecture.json","pdd/foo_v2.py","pdd/foo.py",'
                    '"pdd/prompts/foo_python.prompt"]}',
                    0.1,
                    role,
                )
            return True, _json("findings", [self._finding()]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1, require_final_fresh_review=False),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        # Loop completed with a trustworthy report (success=True per
        # docstring contract); ship gate lives in the report markers.
        assert success is True
        # Push helper was NEVER invoked: the policy layer refused.
        assert push_calls == []
        # Report carries the registry-edit refusal.
        assert "architecture.json registry edit refused" in report
        # Ship-gate markers signal non-clean.
        assert "reviewer-status: codex=findings" in report
        assert "fresh-final-review: missing" in report
        # The original finding stays OPEN.
        assert "### Findings" in report
        findings_section = report.split("### Findings", 1)[1].split("### ", 1)[0]
        assert "| blocker | open |" in findings_section
        assert "| blocker | fixed |" not in findings_section

    def test_loop_refuses_push_on_1081_partial_wipe_bypass(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """End-to-end #1081 partial-wipe regression: the fixer drops ONE
        HEAD pair under the cover of legitimate retirement while landing
        a renamed `_v2.py` not registered in the post-change
        ``architecture.json``. 10b must refuse the push.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        # HEAD has TWO registered pairs; the partial-wipe attack drops
        # one and leaves the other intact.
        _seed_repo_with_arch(
            tmp_path,
            [
                _arch_pair("foo_python.prompt", "pdd/foo.py"),
                _arch_pair("bar_python.prompt", "pdd/bar.py"),
            ],
        )

        # Apply the partial-wipe bypass:
        #   1. delete pdd/foo.py
        #   2. delete pdd/prompts/foo_python.prompt
        #   3. create pdd/foo_v2.py (unregistered)
        #   4. rewrite architecture.json to keep ONLY the bar pair
        # 10a's removed-pair check sees foo as legitimately retired
        # (code gone + prompt gone), so the partial-wipe scan must
        # still catch foo_v2.py.
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "foo_v2.py").write_text(
            "# renamed\n", encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        new_arch = [_arch_pair("bar_python.prompt", "pdd/bar.py")]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        monkeypatch.setattr(
            mod,
            "_git_changed_files",
            lambda _wt: [
                "architecture.json",
                "pdd/foo_v2.py",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
            ],
        )
        push_calls: List[Any] = []

        def fake_push(*args: Any, **kwargs: Any) -> Tuple[bool, str]:
            push_calls.append((args, kwargs))
            return True, "pushed"

        monkeypatch.setattr(mod, "_commit_and_push_if_changed", fake_push)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"edited","changed_files":'
                    '["architecture.json","pdd/foo_v2.py","pdd/foo.py",'
                    '"pdd/prompts/foo_python.prompt"]}',
                    0.1,
                    role,
                )
            return True, _json("findings", [self._finding()]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1, require_final_fresh_review=False),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        # Trustworthy report contract: success=True; ship gate is in
        # the report markers.
        assert success is True
        # Push helper was NEVER invoked.
        assert push_calls == []
        # Report carries the registry-edit refusal with the partial-wipe
        # diagnostic text.
        assert "architecture.json registry edit refused" in report
        assert (
            "removed registered pair while new unregistered code path"
            in report
        )
        assert "pdd/foo_v2.py" in report
        # Ship-gate markers signal non-clean.
        assert "reviewer-status: codex=findings" in report
        assert "fresh-final-review: missing" in report
        # The original finding stays OPEN.
        assert "### Findings" in report
        findings_section = report.split("### Findings", 1)[1].split("### ", 1)[0]
        assert "| blocker | open |" in findings_section
        assert "| blocker | fixed |" not in findings_section

    def test_loop_runs_existing_six_case_discriminator_unchanged(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """The new 10b guard must not regress the existing 10a six-case
        discriminator. A code-only change (no architecture.json edit)
        must still be refused by 10a, not 10b.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        # Pure code-only edit; architecture.json is NOT in the change
        # set, so the 10b registry-edit guard short-circuits to None.
        monkeypatch.setattr(
            mod, "_git_changed_files", lambda _wt: ["pdd/foo.py"]
        )
        push_calls: List[Any] = []

        def fake_push(*args: Any, **kwargs: Any) -> Tuple[bool, str]:
            push_calls.append((args, kwargs))
            return True, "pushed"

        monkeypatch.setattr(mod, "_commit_and_push_if_changed", fake_push)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"edited","changed_files":["pdd/foo.py"]}',
                    0.1,
                    role,
                )
            return True, _json("findings", [self._finding()]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1, require_final_fresh_review=False),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        # Refused — but by the 10a prompt-source guard, not 10b.
        assert push_calls == []
        assert "generated-code-only fix refused" in report
        # Registry-edit refusal MUST NOT appear (no registry edit).
        assert "architecture.json registry edit refused" not in report

    def test_loop_refuses_push_on_1081_no_arch_edit_bypass(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """End-to-end #1081 no-arch-edit regression (round-3 finding
        1): the fixer deletes the registered code and prompt, adds a
        renamed `_v2.py`, and leaves ``architecture.json`` UNTOUCHED.
        10a's check (3) sees code+prompt both gone and allows the
        retirement; without the implicit-retirement trigger, 10b
        short-circuits on the missing arch edit and the unregistered
        new code lands on the PR.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        # No-arch-edit bypass: delete code, delete prompt, add new
        # code, do NOT edit architecture.json.
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "foo_v2.py").write_text(
            "# renamed\n", encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()

        # architecture.json is deliberately NOT in changed_files.
        monkeypatch.setattr(
            mod,
            "_git_changed_files",
            lambda _wt: [
                "pdd/foo.py",
                "pdd/foo_v2.py",
                "pdd/prompts/foo_python.prompt",
            ],
        )
        push_calls: List[Any] = []

        def fake_push(*args: Any, **kwargs: Any) -> Tuple[bool, str]:
            push_calls.append((args, kwargs))
            return True, "pushed"

        monkeypatch.setattr(mod, "_commit_and_push_if_changed", fake_push)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"edited","changed_files":'
                    '["pdd/foo_v2.py","pdd/foo.py",'
                    '"pdd/prompts/foo_python.prompt"]}',
                    0.1,
                    role,
                )
            return True, _json("findings", [self._finding()]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1, require_final_fresh_review=False),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        # Trustworthy report contract: success=True; ship gate is in
        # the report markers.
        assert success is True
        # Push helper was NEVER invoked: the policy layer refused.
        assert push_calls == []
        # Report carries the registry-edit refusal with the
        # no-arch-edit diagnostic text.
        assert "architecture.json registry edit refused" in report
        assert (
            "retired registered pair on disk while new unregistered "
            "code path"
        ) in report
        assert "pdd/foo_v2.py" in report
        assert "architecture.json not updated" in report
        # Ship-gate markers signal non-clean.
        assert "reviewer-status: codex=findings" in report
        assert "fresh-final-review: missing" in report
        # The original finding stays OPEN.
        assert "### Findings" in report
        findings_section = report.split("### Findings", 1)[1].split("### ", 1)[0]
        assert "| blocker | open |" in findings_section
        assert "| blocker | fixed |" not in findings_section

    def test_loop_allows_legitimate_retirement_with_helper_modification(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """End-to-end positive control for round-3 finding 2: a
        legitimate retirement (foo.py + foo prompt gone, registry
        updated to remove the pair) that ALSO modifies an existing
        unregistered helper must NOT be refused by 10b. The
        unregistered-new-code scan must skip the helper because it
        existed at HEAD.
        """
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        # HEAD has TWO registered pairs plus an unregistered helper.
        _seed_repo_with_arch(
            tmp_path,
            [
                _arch_pair("foo_python.prompt", "pdd/foo.py"),
                _arch_pair("bar_python.prompt", "pdd/bar.py"),
            ],
            extra_files={"pdd/utils.py": "# helper\n"},
        )

        # Legitimate retirement of foo + helper modification.
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "pdd" / "utils.py").write_text(
            "# helper (modified)\n", encoding="utf-8"
        )
        new_arch = [_arch_pair("bar_python.prompt", "pdd/bar.py")]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        monkeypatch.setattr(
            mod,
            "_git_changed_files",
            lambda _wt: [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/utils.py",
            ],
        )
        push_calls: List[Any] = []

        def fake_push(*args: Any, **kwargs: Any) -> Tuple[bool, str]:
            push_calls.append((args, kwargs))
            return True, "pushed"

        monkeypatch.setattr(mod, "_commit_and_push_if_changed", fake_push)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"edited","changed_files":'
                    '["architecture.json","pdd/foo.py",'
                    '"pdd/prompts/foo_python.prompt","pdd/utils.py"]}',
                    0.1,
                    role,
                )
            return True, _json("findings", [self._finding()]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1, require_final_fresh_review=False),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        # The registry-edit guard MUST NOT refuse this push.
        assert success is True
        assert "architecture.json registry edit refused" not in report
        # 10a should also not fire: foo.py and foo prompt are both
        # gone (legitimate retirement), helper modification is
        # outside the registry.
        assert "generated-code-only fix refused" not in report


# ---------------------------------------------------------------------------
# Issue #1081 codex review pass #6: untracked-directory bypass + scan scoping.
#
# Finding 1: ``git status --porcelain=v1 -z`` without ``--untracked-files=all``
# collapses an untracked DIRECTORY to a single ``?? dir/`` entry. The 10b
# unregistered-new-code scan's ``Path.is_file()`` check then sees the
# directory path (returns False) and skips it — bypassing the guard with a
# new package at ``pdd/foo_v2/__init__.py``.
#
# Finding 2: the unregistered-new-code scan was overbroad, flagging any
# non-prompt non-arch file. A legitimate retirement that also adds e.g.
# ``tests/test_bar.py`` or ``docs/new.md`` would be falsely refused.
# Restrict the scan to ``pdd/`` paths ending in ``.py``.
# ---------------------------------------------------------------------------


class TestRound6UntrackedDirectoryBypass:
    """Round-6 finding 1: untracked-directory bypass via ``__init__.py``.

    Uses a real git repo so the ``--untracked-files=all`` flag actually
    exercises the parsing path. Monkeypatching ``_git_changed_files``
    would hide the very thing being tested.
    """

    @staticmethod
    def _init_repo(worktree: Path) -> None:
        subprocess.run(["git", "init", "-q"], cwd=worktree, check=True)
        subprocess.run(
            ["git", "config", "user.email", "test@example.com"],
            cwd=worktree,
            check=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Test"],
            cwd=worktree,
            check=True,
        )

    def test_changed_files_enumerates_files_inside_untracked_directory(
        self, tmp_path: Path
    ) -> None:
        """``_git_changed_files`` must list every file inside a new
        untracked directory as a discrete entry, not collapse the
        directory to a single ``dir/`` trailing-slash record.
        """
        from pdd.checkup_review_loop import _git_changed_files

        self._init_repo(tmp_path)
        (tmp_path / "pdd").mkdir()
        (tmp_path / "pdd" / "foo.py").write_text("x\n", encoding="utf-8")
        subprocess.run(["git", "add", "-A"], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "commit", "-q", "-m", "init"], cwd=tmp_path, check=True
        )

        # Create a NEW untracked directory with two files inside it.
        new_pkg = tmp_path / "pdd" / "foo_v2"
        new_pkg.mkdir()
        (new_pkg / "__init__.py").write_text("\n", encoding="utf-8")
        (new_pkg / "core.py").write_text("# core\n", encoding="utf-8")

        changed = _git_changed_files(tmp_path)

        # Individual files MUST appear, not the bare directory.
        assert "pdd/foo_v2/__init__.py" in changed
        assert "pdd/foo_v2/core.py" in changed
        # The directory itself MUST NOT appear (no trailing-slash
        # entries; that was the bypass).
        assert "pdd/foo_v2/" not in changed
        assert not any(entry.endswith("/") for entry in changed)

    def test_guard_refuses_untracked_directory_bypass(
        self, tmp_path: Path
    ) -> None:
        """End-to-end #1081 round-6 finding 1: the fixer deletes the
        registered code+prompt, creates a new package directory at
        ``pdd/foo_v2/__init__.py``, and wipes ``architecture.json``.
        Combined: ``_git_changed_files(worktree)`` must list the new
        ``__init__.py`` individually so the 10b scan can refuse it.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
            _git_changed_files,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        # Apply the bypass shape:
        #   1. delete pdd/foo.py
        #   2. delete pdd/prompts/foo_python.prompt
        #   3. create pdd/foo_v2/__init__.py (UNTRACKED DIRECTORY)
        #   4. wipe architecture.json to []
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        new_pkg = tmp_path / "pdd" / "foo_v2"
        new_pkg.mkdir()
        (new_pkg / "__init__.py").write_text(
            "# package init\n", encoding="utf-8"
        )
        (tmp_path / "architecture.json").write_text(
            "[]", encoding="utf-8"
        )

        changed = _git_changed_files(tmp_path)
        # Sanity: the new file inside the untracked directory MUST
        # surface as a discrete entry.
        assert "pdd/foo_v2/__init__.py" in changed
        assert "pdd/foo_v2/" not in changed

        reason = _check_architecture_registry_edit_guard(tmp_path, changed)
        assert reason is not None
        # The refusal must NAME the bypass file so the operator can act.
        assert "pdd/foo_v2/__init__.py" in reason
        assert "architecture.json registry edit refused" in reason
        assert (
            "removed registered pair while new unregistered code path"
            in reason
        )


class TestRound6UntrackedDirectoryBypassIntegration:
    """Mirror of the unit test above through ``run_checkup_review_loop``.

    Confirms no push happens and the report renders the 10b refusal with
    the bypass file named.
    """

    def _patch_io(self, monkeypatch: Any, tmp_path: Path) -> None:
        import pdd.checkup_review_loop as mod

        monkeypatch.setattr(
            mod, "_setup_pr_worktree", lambda *a, **k: (tmp_path, None)
        )
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
            mod, "_post_review_loop_report", lambda *a, **k: None
        )

    def _finding(self) -> Dict[str, str]:
        return {
            "severity": "blocker",
            "area": "api",
            "location": "pdd/foo.py:1",
            "evidence": "broke",
            "finding": "broken api",
            "required_fix": "fix it",
        }

    def test_loop_refuses_push_on_untracked_directory_bypass(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        # Apply the bypass on the worktree filesystem before the loop
        # reads ``_git_changed_files``.
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        new_pkg = tmp_path / "pdd" / "foo_v2"
        new_pkg.mkdir()
        (new_pkg / "__init__.py").write_text(
            "# package init\n", encoding="utf-8"
        )
        (tmp_path / "architecture.json").write_text(
            "[]", encoding="utf-8"
        )

        # Use the REAL ``_git_changed_files`` so the
        # ``--untracked-files=all`` flag is exercised end-to-end.
        push_calls: List[Any] = []

        def fake_push(*args: Any, **kwargs: Any) -> Tuple[bool, str]:
            push_calls.append((args, kwargs))
            return True, "pushed"

        monkeypatch.setattr(mod, "_commit_and_push_if_changed", fake_push)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"edited","changed_files":'
                    '["architecture.json","pdd/foo_v2/__init__.py",'
                    '"pdd/foo.py","pdd/prompts/foo_python.prompt"]}',
                    0.1,
                    role,
                )
            return True, _json("findings", [self._finding()]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1, require_final_fresh_review=False),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        # The policy layer refused before the push helper.
        assert push_calls == []
        # Refusal carries the bypass file (NOT the bare directory).
        assert "architecture.json registry edit refused" in report
        assert "pdd/foo_v2/__init__.py" in report
        assert "pdd/foo_v2/" not in report.replace(
            "pdd/foo_v2/__init__.py", ""
        )
        # Ship-gate markers signal non-clean.
        assert "reviewer-status: codex=findings" in report
        assert "fresh-final-review: missing" in report


class TestRound6ScanScopeBoundary:
    """Round-6 finding 2: unregistered-new-code scan must be scoped to
    generated prompt-driven code (``pdd/**/*.py``) so it does NOT flag
    legitimate test/doc/script additions during a retirement.
    """

    def test_retirement_with_new_test_file_is_allowed(
        self, tmp_path: Path
    ) -> None:
        """A legitimate retirement of ``pdd/foo.py`` that also adds a
        new test at ``tests/test_bar.py`` must NOT be refused.
        ``tests/`` is outside the registry-mutation scope.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [
                _arch_pair("foo_python.prompt", "pdd/foo.py"),
                _arch_pair("bar_python.prompt", "pdd/bar.py"),
            ],
        )
        # Retire foo and add a new test for bar.
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "tests").mkdir(exist_ok=True)
        (tmp_path / "tests" / "test_bar.py").write_text(
            "def test_bar():\n    pass\n", encoding="utf-8"
        )
        new_arch = [_arch_pair("bar_python.prompt", "pdd/bar.py")]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "tests/test_bar.py",
            ],
        )
        assert reason is None

    def test_retirement_with_new_doc_file_is_allowed(
        self, tmp_path: Path
    ) -> None:
        """A legitimate retirement that also adds ``docs/new.md`` must
        NOT be refused. ``docs/`` is outside the registry-mutation
        scope.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [
                _arch_pair("foo_python.prompt", "pdd/foo.py"),
                _arch_pair("bar_python.prompt", "pdd/bar.py"),
            ],
        )
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "docs").mkdir(exist_ok=True)
        (tmp_path / "docs" / "new.md").write_text(
            "# new\n", encoding="utf-8"
        )
        new_arch = [_arch_pair("bar_python.prompt", "pdd/bar.py")]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "docs/new.md",
            ],
        )
        assert reason is None

    def test_retirement_with_new_script_file_is_allowed(
        self, tmp_path: Path
    ) -> None:
        """A legitimate retirement that also adds ``scripts/release.sh``
        must NOT be refused. Scripts live outside the registry-mutation
        scope.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [
                _arch_pair("foo_python.prompt", "pdd/foo.py"),
                _arch_pair("bar_python.prompt", "pdd/bar.py"),
            ],
        )
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "scripts").mkdir(exist_ok=True)
        (tmp_path / "scripts" / "release.sh").write_text(
            "#!/bin/sh\n", encoding="utf-8"
        )
        new_arch = [_arch_pair("bar_python.prompt", "pdd/bar.py")]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "scripts/release.sh",
            ],
        )
        assert reason is None

    def test_retirement_with_new_pdd_module_is_refused(
        self, tmp_path: Path
    ) -> None:
        """Positive control: a retirement that adds ``pdd/foo_v2.py``
        (in scope: under ``pdd/`` and ending in ``.py``) MUST still be
        refused. This is the existing ``foo_v2.py`` shape, retained.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "foo_v2.py").write_text(
            "# renamed\n", encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text("[]", encoding="utf-8")

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/foo_v2.py",
                "pdd/prompts/foo_python.prompt",
            ],
        )
        assert reason is not None
        assert "pdd/foo_v2.py" in reason

    def test_retirement_with_new_pdd_init_under_subpackage_is_refused(
        self, tmp_path: Path
    ) -> None:
        """Positive control covering round-6 finding 1: a new
        ``pdd/foo_v2/__init__.py`` MUST still be refused even though
        ``__init__.py`` could look "framework-y". Keeping
        ``__init__.py`` in scope is what keeps the untracked-directory
        bypass closed.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )
        (tmp_path / "pdd" / "foo.py").unlink()
        new_pkg = tmp_path / "pdd" / "foo_v2"
        new_pkg.mkdir()
        (new_pkg / "__init__.py").write_text(
            "# init\n", encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text("[]", encoding="utf-8")

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/foo_v2/__init__.py",
                "pdd/prompts/foo_python.prompt",
            ],
        )
        assert reason is not None
        assert "pdd/foo_v2/__init__.py" in reason

    def test_retirement_with_new_pdd_non_py_file_is_allowed(
        self, tmp_path: Path
    ) -> None:
        """A non-``.py`` file under ``pdd/`` (e.g. a data fixture) is
        out of scope for the generated-code scan, even when it lives
        inside the ``pdd/`` tree.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [
                _arch_pair("foo_python.prompt", "pdd/foo.py"),
                _arch_pair("bar_python.prompt", "pdd/bar.py"),
            ],
        )
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "pdd" / "fixture.txt").write_text(
            "data\n", encoding="utf-8"
        )
        new_arch = [_arch_pair("bar_python.prompt", "pdd/bar.py")]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/fixture.txt",
            ],
        )
        assert reason is None


# ---------------------------------------------------------------------------
# Issue #1081 codex review pass #7: symlinked-package bypass.
#
# Round-6 finding 2 narrowed the unregistered-new-code scan to paths under
# ``pdd/`` ending in ``.py``. That filter silently allows a NEW SYMLINK
# under ``pdd/`` whose link path has no ``.py`` suffix — e.g.
# ``pdd/foo_v2 -> ../tests/evil_pkg``. ``git status --untracked-files=all``
# lists the directory-symlink as the bare link path (``pdd/foo_v2``, no
# trailing slash, no ``.py``), the ``.py`` filter skips it, the scan
# returns no offenders, and the bypass succeeds — ``pdd.foo_v2`` is now an
# importable Python package backed by ``tests/evil_pkg`` with no
# registered prompt source.
#
# Fix: under ``pdd/`` (excluding ``pdd/prompts/``), keep any symlink in
# scope regardless of suffix. Generated prompt-driven code is never a
# symlink, so this rule has no legitimate-use false positives.
# ---------------------------------------------------------------------------


class TestRound7SymlinkedPackageBypass:
    """Round-7 finding: a NEW symlink under ``pdd/`` (excluding
    ``pdd/prompts/``) can resolve to importable Python code (a package
    directory or a ``.py`` module) without carrying a ``.py`` suffix on
    the link path itself. The unregistered-new-code scan must keep
    symlinks in scope regardless of suffix.
    """

    @staticmethod
    def _init_repo(worktree: Path) -> None:
        subprocess.run(["git", "init", "-q"], cwd=worktree, check=True)
        subprocess.run(
            ["git", "config", "user.email", "test@example.com"],
            cwd=worktree,
            check=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Test"],
            cwd=worktree,
            check=True,
        )

    def test_guard_refuses_directory_symlink_package_bypass(
        self, tmp_path: Path
    ) -> None:
        """End-to-end #1081 round-7 bypass: the fixer deletes the
        registered code+prompt, wipes ``architecture.json``, and adds a
        directory-symlink ``pdd/foo_v2 -> ../tests/evil_pkg`` backed by
        a real ``tests/evil_pkg/__init__.py``. ``git status
        --untracked-files=all`` lists the symlink as the bare path
        ``pdd/foo_v2`` (no trailing slash, no ``.py``). The 10b scan
        MUST still refuse it because the symlink is under ``pdd/`` and
        a symlink there can resolve to importable Python code.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
            _git_changed_files,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        # Apply the bypass shape:
        #   1. delete pdd/foo.py
        #   2. delete pdd/prompts/foo_python.prompt
        #   3. wipe architecture.json to []
        #   4. create tests/evil_pkg/__init__.py
        #   5. create pdd/foo_v2 as a SYMLINK to ../tests/evil_pkg
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text("[]", encoding="utf-8")
        evil_pkg = tmp_path / "tests" / "evil_pkg"
        evil_pkg.mkdir(parents=True)
        (evil_pkg / "__init__.py").write_text(
            "# unregistered code\n", encoding="utf-8"
        )
        # Relative symlink target so the link works regardless of where
        # the tmp_path lives.
        (tmp_path / "pdd" / "foo_v2").symlink_to(Path("..") / "tests" / "evil_pkg")

        # Use the REAL ``_git_changed_files`` so the
        # ``--untracked-files=all`` listing of the directory-symlink
        # (bare ``pdd/foo_v2``, no trailing slash, no ``.py``) is what
        # the guard actually sees.
        changed = _git_changed_files(tmp_path)
        # Sanity: git reports the symlink as the bare link path.
        assert "pdd/foo_v2" in changed
        assert "pdd/foo_v2/" not in changed

        reason = _check_architecture_registry_edit_guard(tmp_path, changed)
        assert reason is not None
        assert "architecture.json registry edit refused" in reason
        # The refusal must NAME the symlinked-package bypass file.
        assert "pdd/foo_v2" in reason

    def test_guard_refuses_py_symlink_to_external_module(
        self, tmp_path: Path
    ) -> None:
        """A ``.py``-suffixed symlink to a file outside ``pdd/`` (a
        single-file Python module via symlink) is also a bypass shape.
        The existing ``.py`` filter already catches this, plus the
        presence check counts symlinks as presence — confirming the
        end-to-end refusal here keeps the contract regression-tested.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text("[]", encoding="utf-8")
        # Real file outside pdd/ that the symlink will resolve to.
        (tmp_path / "tests").mkdir(exist_ok=True)
        (tmp_path / "tests" / "evil.py").write_text(
            "# unregistered\n", encoding="utf-8"
        )
        (tmp_path / "pdd" / "foo_v2.py").symlink_to(
            Path("..") / "tests" / "evil.py"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/foo_v2.py",
                "pdd/prompts/foo_python.prompt",
            ],
        )
        assert reason is not None
        assert "pdd/foo_v2.py" in reason

    def test_symlink_under_pdd_prompts_is_not_flagged_by_scan(
        self, tmp_path: Path
    ) -> None:
        """The ``pdd/prompts/`` skip wins: a symlink at
        ``pdd/prompts/...`` MUST NOT be flagged by the
        unregistered-new-code scan. (Prompts can legitimately be
        symlinks if a project chooses to layer shared prompt sources.)
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [
                _arch_pair("foo_python.prompt", "pdd/foo.py"),
                _arch_pair("bar_python.prompt", "pdd/bar.py"),
            ],
        )
        # Retire foo and drop an unrelated symlink inside pdd/prompts/.
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "pdd" / "prompts" / "shared_extra.prompt").symlink_to(
            tmp_path / "pdd" / "prompts" / "bar_python.prompt"
        )
        new_arch = [_arch_pair("bar_python.prompt", "pdd/bar.py")]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/prompts/shared_extra.prompt",
            ],
        )
        # The retirement is legitimate AND the symlink inside
        # pdd/prompts/ is skipped before the symlink branch runs.
        assert reason is None


class TestRound7SymlinkedPackageBypassIntegration:
    """Mirror of the round-7 bypass through ``run_checkup_review_loop``.

    Confirms no push happens and the report renders the 10b refusal with
    the symlinked-package path named.
    """

    def _patch_io(self, monkeypatch: Any, tmp_path: Path) -> None:
        import pdd.checkup_review_loop as mod

        monkeypatch.setattr(
            mod, "_setup_pr_worktree", lambda *a, **k: (tmp_path, None)
        )
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
            mod, "_post_review_loop_report", lambda *a, **k: None
        )

    def _finding(self) -> Dict[str, str]:
        return {
            "severity": "blocker",
            "area": "api",
            "location": "pdd/foo.py:1",
            "evidence": "broke",
            "finding": "broken api",
            "required_fix": "fix it",
        }

    def test_loop_refuses_push_on_symlinked_package_bypass(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        from pdd.checkup_review_loop import run_checkup_review_loop
        import pdd.checkup_review_loop as mod

        self._patch_io(monkeypatch, tmp_path)
        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        # Apply the round-7 bypass on the worktree filesystem before
        # the loop reads ``_git_changed_files``.
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text("[]", encoding="utf-8")
        evil_pkg = tmp_path / "tests" / "evil_pkg"
        evil_pkg.mkdir(parents=True)
        (evil_pkg / "__init__.py").write_text(
            "# unregistered\n", encoding="utf-8"
        )
        (tmp_path / "pdd" / "foo_v2").symlink_to(
            Path("..") / "tests" / "evil_pkg"
        )

        # Use the REAL ``_git_changed_files`` so the symlink listing is
        # exercised end-to-end.
        push_calls: List[Any] = []

        def fake_push(*args: Any, **kwargs: Any) -> Tuple[bool, str]:
            push_calls.append((args, kwargs))
            return True, "pushed"

        monkeypatch.setattr(mod, "_commit_and_push_if_changed", fake_push)

        def fake_task(role: str, instruction: str, cwd: Path, **kwargs: Any):
            label = kwargs["label"]
            if "fix-" in label:
                return (
                    True,
                    '{"summary":"edited","changed_files":'
                    '["architecture.json","pdd/foo_v2",'
                    '"pdd/foo.py","pdd/prompts/foo_python.prompt",'
                    '"tests/evil_pkg/__init__.py"]}',
                    0.1,
                    role,
                )
            return True, _json("findings", [self._finding()]), 0.1, role

        monkeypatch.setattr(mod, "_run_role_task", fake_task)

        success, report, _cost, _model = run_checkup_review_loop(
            context=_ctx(tmp_path),
            config=_config(max_rounds=1, require_final_fresh_review=False),
            cwd=tmp_path,
            quiet=True,
            use_github_state=False,
        )

        assert success is True
        # The policy layer refused before the push helper.
        assert push_calls == []
        # Refusal carries the symlinked-package path (no .py suffix).
        assert "architecture.json registry edit refused" in report
        assert "pdd/foo_v2" in report
        # Ship-gate markers signal non-clean.
        assert "reviewer-status: codex=findings" in report
        assert "fresh-final-review: missing" in report


# ---------------------------------------------------------------------------
# Issue #1081 codex review pass #8: sourceless-bytecode bypass.
#
# Round-6 finding 2 narrowed the unregistered-new-code scan to paths under
# ``pdd/`` ending in ``.py``. Round-7 broadened the symlink case. Both still
# leave a hole: Python imports modules under several non-``.py`` suffixes
# (``importlib.machinery.all_suffixes()`` returns ``.py``, ``.pyc``, plus
# platform-specific extension suffixes). A sourceless ``.pyc`` dropped at
# ``pdd/foo_v2.pyc`` is importable as ``pdd.foo_v2`` via
# ``importlib.machinery.SourcelessFileLoader`` with no source on disk;
# native extension modules (``.so`` on POSIX, ``.pyd`` on Windows) are the
# same shape. The scan MUST cover every importable suffix or the
# ``delete-code+prompt + wipe-architecture.json + add bytecode/extension``
# attack succeeds.
#
# Fix: extend the suffix filter in
# ``_check_architecture_registry_edit_guard`` from ``".py"`` to the tuple
# ``_IMPORTABLE_SUFFIXES = (".py", ".pyc", ".pyo", ".so", ".pyd")`` so
# ``str.endswith`` catches every shape Python will load as a module.
# ---------------------------------------------------------------------------


class TestRound8SourcelessBytecodeBypass:
    """Round-8 finding: the unregistered-new-code scan in 10b must reject
    every suffix Python can import as ``pdd.<name>`` — not just ``.py``.
    """

    def test_guard_refuses_sourceless_pyc_bypass(
        self, tmp_path: Path
    ) -> None:
        """The exact round-8 reproduction: delete the registered code+
        prompt, wipe ``architecture.json`` to ``[]``, and drop a valid
        ``pdd/foo_v2.pyc`` compiled from a temporary source (source
        then removed). The bytecode is importable as ``pdd.foo_v2`` via
        ``SourcelessFileLoader`` with no ``.py`` on disk, so a
        ``.py``-only filter would skip it and the bypass would succeed.
        """
        import py_compile

        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        # Apply the bypass shape:
        #   1. delete pdd/foo.py
        #   2. delete pdd/prompts/foo_python.prompt
        #   3. wipe architecture.json to []
        #   4. compile a sourceless .pyc into pdd/foo_v2.pyc
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text(
            json.dumps([]), encoding="utf-8"
        )
        src = tmp_path / "_foo_v2_src.py"
        src.write_text("VALUE = 42\n", encoding="utf-8")
        py_compile.compile(
            str(src),
            cfile=str(tmp_path / "pdd" / "foo_v2.pyc"),
            doraise=True,
        )
        src.unlink()

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/foo_v2.pyc",
            ],
        )
        assert reason is not None
        assert "pdd/foo_v2.pyc" in reason

    def test_guard_refuses_native_extension_so_bypass(
        self, tmp_path: Path
    ) -> None:
        """A bare ``pdd/foo_v2.so`` dropped at the new code path is a
        native extension module — importable as ``pdd.foo_v2`` via the
        extension loader. The guard isn't validating the binary format
        here, only blocking the importable suffix; arbitrary bytes are
        sufficient to reproduce the scan-evasion shape.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text(
            json.dumps([]), encoding="utf-8"
        )
        (tmp_path / "pdd" / "foo_v2.so").write_bytes(b"\x7fELF stub")

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/foo_v2.so",
            ],
        )
        assert reason is not None
        assert "pdd/foo_v2.so" in reason

    def test_guard_refuses_windows_extension_pyd_bypass(
        self, tmp_path: Path
    ) -> None:
        """The Windows counterpart to ``.so``: a ``pdd/foo_v2.pyd``
        native extension. The suffix filter must cover both POSIX and
        Windows extension shapes or attackers targeting Windows
        deployments slip past the scan.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text(
            json.dumps([]), encoding="utf-8"
        )
        (tmp_path / "pdd" / "foo_v2.pyd").write_bytes(b"MZ stub")

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/foo_v2.pyd",
            ],
        )
        assert reason is not None
        assert "pdd/foo_v2.pyd" in reason

    def test_guard_refuses_windows_pyw_source_bypass(
        self, tmp_path: Path
    ) -> None:
        """Round-8 follow-up: a ``pdd/foo_v2.pyw`` is Windows-only Python
        source — on Windows ``importlib.machinery.SOURCE_SUFFIXES``
        includes ``.pyw`` so ``SourceFileLoader`` imports it as
        ``pdd.foo_v2`` exactly like a ``.py`` file. The R8 suffix tuple
        missed it; the follow-up adds ``.pyw`` so the same retirement +
        wipe + add bypass shape is blocked.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text(
            json.dumps([]), encoding="utf-8"
        )
        (tmp_path / "pdd" / "foo_v2.pyw").write_text(
            "VALUE = 42\n", encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/foo_v2.pyw",
            ],
        )
        assert reason is not None
        assert "pdd/foo_v2.pyw" in reason

    def test_guard_refuses_uppercase_py_suffix_bypass(
        self, tmp_path: Path
    ) -> None:
        """Round-9 follow-up: an uppercase ``pdd/foo_v2.PY`` is
        importable as ``pdd.foo_v2`` on case-insensitive filesystems
        (Windows; macOS HFS+/APFS in default case-insensitive mode)
        because Python's ``importlib.machinery`` suffix matching is
        case-insensitive. A case-sensitive ``str.endswith`` against
        the lowercase ``_IMPORTABLE_SUFFIXES`` tuple would let the
        bypass slip past the scan; lowercasing the path side of the
        comparison closes the hole.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text(
            json.dumps([]), encoding="utf-8"
        )
        (tmp_path / "pdd" / "foo_v2.PY").write_text(
            "VALUE = 42\n", encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/foo_v2.PY",
            ],
        )
        assert reason is not None
        assert "pdd/foo_v2.PY" in reason

    def test_guard_refuses_uppercase_pyc_suffix_bypass(
        self, tmp_path: Path
    ) -> None:
        """Round-9 follow-up companion: an uppercase ``pdd/foo_v2.PYC``
        slips past a case-sensitive ``.pyc`` check the same way ``.PY``
        slips past ``.py``. The byte contents don't matter for the
        scan — the filter only inspects the path string — so a stub
        payload reproduces the importable-suffix shape.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text(
            json.dumps([]), encoding="utf-8"
        )
        (tmp_path / "pdd" / "foo_v2.PYC").write_bytes(b"\x00\x00 stub")

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/foo_v2.PYC",
            ],
        )
        assert reason is not None
        assert "pdd/foo_v2.PYC" in reason

    def test_guard_refuses_mixed_case_so_suffix_bypass(
        self, tmp_path: Path
    ) -> None:
        """Round-9 follow-up belt-and-suspenders: a mixed-case
        ``pdd/foo_v2.So`` native-extension suffix must also trip the
        scan. Confirms the case-insensitive comparison handles every
        mixed-case permutation, not just fully uppercase suffixes.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text(
            json.dumps([]), encoding="utf-8"
        )
        (tmp_path / "pdd" / "foo_v2.So").write_bytes(b"\x7fELF stub")

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/foo_v2.So",
            ],
        )
        assert reason is not None
        assert "pdd/foo_v2.So" in reason

    def test_guard_refuses_uppercase_pdd_prefix_bypass(
        self, tmp_path: Path
    ) -> None:
        """Round-12 finding (codex review pass #12), sibling of R9: an
        uppercase ``PDD/foo_v2.py`` directory prefix aliases to
        ``pdd/foo_v2.py`` on case-insensitive filesystems (Windows;
        macOS HFS+/APFS in default case-insensitive mode) and is
        importable as ``pdd.foo_v2``. A case-sensitive
        ``str.startswith("pdd/")`` would skip the path as out-of-scope
        and the bypass would land; lowercasing the path side of the
        prefix comparison closes the hole. Linux is case-sensitive, so
        the test FS itself distinguishes ``PDD`` from ``pdd`` and the
        file actually lives at ``PDD/foo_v2.py`` — the guard logic
        must still flag it because production filesystems can fold the
        two.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text(
            json.dumps([]), encoding="utf-8"
        )
        # ``exist_ok=True`` because the runner FS may be
        # case-insensitive (macOS APFS in default mode), in which
        # case ``PDD`` already exists as ``pdd``. On Linux this
        # creates a sibling ``PDD`` directory; either way the
        # candidate file lives at the uppercase path and the guard
        # is fed the uppercase string.
        (tmp_path / "PDD").mkdir(exist_ok=True)
        (tmp_path / "PDD" / "foo_v2.py").write_text(
            "VALUE = 42\n", encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "PDD/foo_v2.py",
            ],
        )
        assert reason is not None
        assert "PDD/foo_v2.py" in reason

    def test_guard_refuses_mixed_case_pdd_prefix_bypass(
        self, tmp_path: Path
    ) -> None:
        """Round-12 follow-up: a mixed-case ``Pdd/foo_v2.py`` prefix
        must also trip the scan. Confirms the case-insensitive prefix
        comparison handles every mixed-case permutation, not just
        fully uppercase prefixes.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text(
            json.dumps([]), encoding="utf-8"
        )
        (tmp_path / "Pdd").mkdir(exist_ok=True)
        (tmp_path / "Pdd" / "foo_v2.py").write_text(
            "VALUE = 42\n", encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "Pdd/foo_v2.py",
            ],
        )
        assert reason is not None
        assert "Pdd/foo_v2.py" in reason

    def test_guard_skips_uppercase_pdd_prompts_subdirectory(
        self, tmp_path: Path
    ) -> None:
        """Round-12 negative: the ``pdd/prompts/`` exclusion must also
        be case-insensitive. An uppercase ``PDD/PROMPTS/foo.prompt``
        path aliases to ``pdd/prompts/foo.prompt`` on a
        case-insensitive filesystem; it should be SKIPPED as a prompts
        subdir, not flagged. Confirms the prompt-exclusion side of
        the case-insensitive prefix comparison.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text(
            json.dumps([]), encoding="utf-8"
        )
        (tmp_path / "PDD" / "PROMPTS").mkdir(parents=True, exist_ok=True)
        (tmp_path / "PDD" / "PROMPTS" / "foo.prompt").write_text(
            "prompt body\n", encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "PDD/PROMPTS/foo.prompt",
            ],
        )
        # The PDD/PROMPTS path must be excluded by the case-insensitive
        # prompts subdir filter, so it does NOT appear as an offender.
        # The retirement itself is legitimate (no unregistered new
        # code), so the guard should report no reason.
        assert reason is None or "PDD/PROMPTS/foo.prompt" not in reason

    def test_guard_allows_pdd_fixture_txt_under_broadened_filter(
        self, tmp_path: Path
    ) -> None:
        """Negative: a non-importable ``pdd/fixture.txt`` under ``pdd/``
        remains out of scope after the R8 widening. Confirms the R6
        scope-boundary contract — only importable shapes trip the scan,
        and data fixtures still pass.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [
                _arch_pair("foo_python.prompt", "pdd/foo.py"),
                _arch_pair("bar_python.prompt", "pdd/bar.py"),
            ],
        )
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "pdd" / "fixture.txt").write_text(
            "data\n", encoding="utf-8"
        )
        new_arch = [_arch_pair("bar_python.prompt", "pdd/bar.py")]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/fixture.txt",
            ],
        )
        assert reason is None

    def test_guard_allows_pdd_data_json_under_broadened_filter(
        self, tmp_path: Path
    ) -> None:
        """Negative: a ``pdd/data.json`` is also non-importable and must
        not trip the broadened scan. Belt-and-suspenders companion to
        the fixture.txt case, covering a common data-asset extension.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [
                _arch_pair("foo_python.prompt", "pdd/foo.py"),
                _arch_pair("bar_python.prompt", "pdd/bar.py"),
            ],
        )
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "pdd" / "data.json").write_text(
            "{}\n", encoding="utf-8"
        )
        new_arch = [_arch_pair("bar_python.prompt", "pdd/bar.py")]
        (tmp_path / "architecture.json").write_text(
            json.dumps(new_arch), encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/data.json",
            ],
        )
        assert reason is None


class TestRound11SubmoduleBypass:
    """Round-11 finding: a fixer that runs ``git submodule add <repo>
    pdd/foo_v2`` lands importable Python code (the submodule's HEAD
    includes ``__init__.py``) without it appearing as enumerable files
    in ``git status --untracked-files=all``. The gitlink shows as the
    bare directory path ``pdd/foo_v2``; the 10b scan finds no
    importable suffix and no symlink and silently allows it. The
    signal we DO see is ``.gitmodules`` appearing in the change set —
    legitimate refactors do not add a submodule inside ``pdd/``.
    """

    def test_guard_refuses_submodule_bypass(
        self, tmp_path: Path
    ) -> None:
        """The exact round-11 reproduction: delete the registered
        code+prompt, wipe ``architecture.json`` to ``[]``, and stage
        a gitlink at ``pdd/foo_v2`` alongside a new ``.gitmodules``.
        We avoid the actual ``git submodule add`` setup (which would
        require a separate repo) by emulating the on-disk shape:
        ``.gitmodules`` is in the change set and ``pdd/foo_v2/`` is
        a real directory holding ``__init__.py``. The guard sees
        ``.gitmodules`` plus the retirement context and blocks the
        new gitlink directory.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        # Apply the bypass shape:
        #   1. delete pdd/foo.py
        #   2. delete pdd/prompts/foo_python.prompt
        #   3. wipe architecture.json to []
        #   4. add .gitmodules to the worktree
        #   5. drop a real directory at pdd/foo_v2/ holding
        #      __init__.py (emulates the gitlink's checked-out
        #      submodule HEAD)
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text(
            json.dumps([]), encoding="utf-8"
        )
        (tmp_path / ".gitmodules").write_text(
            "[submodule \"pdd/foo_v2\"]\n"
            "\tpath = pdd/foo_v2\n"
            "\turl = ../foo_v2.git\n",
            encoding="utf-8",
        )
        submodule_dir = tmp_path / "pdd" / "foo_v2"
        submodule_dir.mkdir(parents=True, exist_ok=True)
        (submodule_dir / "__init__.py").write_text(
            "VALUE = 42\n", encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                ".gitmodules",
                "pdd/foo_v2",
            ],
        )
        assert reason is not None
        assert "pdd/foo_v2" in reason
        assert "new git submodule" in reason

    def test_guard_allows_gitmodules_change_without_retirement_context(
        self, tmp_path: Path
    ) -> None:
        """Negative: ``.gitmodules`` in the change set with no HEAD
        pair removed or implicitly retired must NOT trip the R11
        submodule check. The retirement-context trigger
        (``removed_only or implicit_retirement``) is False, so the
        check short-circuits even though ``.gitmodules`` is present.
        Build a worktree where the registered pair is untouched, the
        architecture.json edit is metadata-only (re-write of the
        same canonical pair), and a benign ``pdd/foo_v2`` directory
        sits alongside ``.gitmodules`` in the change set.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        # No retirement: keep pdd/foo.py and pdd/prompts/foo_python.prompt
        # on disk, leave architecture.json's canonical pairs unchanged.
        # The .gitmodules edit and the new pdd/foo_v2 directory are
        # the ONLY changes that matter to R11; the retirement-context
        # trigger does not fire because head_pairs == worktree_pairs
        # and every HEAD-registered file is still present.
        (tmp_path / ".gitmodules").write_text(
            "[submodule \"pdd/foo_v2\"]\n"
            "\tpath = pdd/foo_v2\n"
            "\turl = ../foo_v2.git\n",
            encoding="utf-8",
        )
        submodule_dir = tmp_path / "pdd" / "foo_v2"
        submodule_dir.mkdir(parents=True, exist_ok=True)
        (submodule_dir / "__init__.py").write_text(
            "VALUE = 42\n", encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                ".gitmodules",
                "pdd/foo_v2",
            ],
        )
        # No retirement context → R11 must not fire. The trigger
        # condition of the guard itself (architecture.json edit OR
        # implicit retirement) also does not fire here, so the guard
        # short-circuits to None.
        assert reason is None

    def test_guard_does_not_false_positive_r11_on_new_subpackage(
        self, tmp_path: Path
    ) -> None:
        """Negative: a legitimate new directory ``pdd/utils/`` with
        ``__init__.py`` (no ``.gitmodules`` change) is caught by the
        EXISTING round-6 unregistered-new-code scan (``__init__.py``
        matches the importable-suffix filter), not by the R11
        submodule check. Confirm the R11 wording is absent so we know
        the R11 check itself does not false-positive on a plain new
        subpackage.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text(
            json.dumps([]), encoding="utf-8"
        )
        utils_dir = tmp_path / "pdd" / "utils"
        utils_dir.mkdir(parents=True, exist_ok=True)
        (utils_dir / "__init__.py").write_text(
            "VALUE = 42\n", encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/utils/__init__.py",
            ],
        )
        # The round-6 scan catches __init__.py and refuses; the R11
        # wording must NOT appear because no .gitmodules change is
        # in the change set.
        assert reason is not None
        assert "new git submodule" not in reason


class TestRound13PromptsSubdirImportableBypass:
    """Round-13 finding (codex review pass #13): the original
    ``pdd/prompts/`` directory blanket exclusion was too broad. Its
    intent was to skip ``.prompt`` files (canonical prompt sources,
    not importable Python), but ``.py``/``.pyc``/other importable
    suffixes under ``pdd/prompts/`` are still importable Python
    (``pdd.prompts.<name>``). A fixer that wipes the registry,
    retires the registered pair, and drops ``pdd/prompts/foo_v2.py``
    would otherwise slip past the unregistered-new-code scan: the
    new module is importable Python with no prompt source.

    The R14 fix replaces the dir-blanket with a ``.prompt`` suffix
    exclusion in BOTH the 10b unregistered-new-code scan and the R11
    submodule scan. ``.prompt`` files anywhere (not just under
    ``pdd/prompts/``) are skipped because the suffix itself marks
    them as canonical prompt sources; everything else under
    ``pdd/prompts/`` falls through to the standard importable-suffix
    filter.
    """

    def test_guard_refuses_importable_python_under_prompts_dir(
        self, tmp_path: Path
    ) -> None:
        """Positive: HEAD retirement + worktree wipes registry + adds
        ``pdd/prompts/foo_v2.py`` (importable Python under the prompts
        directory). The guard MUST refuse and the offender path MUST
        appear in the refusal text.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        # Apply the R13 bypass shape:
        #   1. delete pdd/foo.py (registered code)
        #   2. delete pdd/prompts/foo_python.prompt (registered prompt)
        #   3. wipe architecture.json to []
        #   4. drop importable Python at pdd/prompts/foo_v2.py
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text(
            json.dumps([]), encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "foo_v2.py").write_text(
            "VALUE = 42\n", encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/prompts/foo_v2.py",
            ],
        )
        assert reason is not None
        assert "pdd/prompts/foo_v2.py" in reason

    def test_guard_refuses_sourceless_bytecode_under_prompts_dir(
        self, tmp_path: Path
    ) -> None:
        """Positive: same bypass shape with a sourceless ``.pyc``
        bytecode file dropped at ``pdd/prompts/foo_v2.pyc``. Loadable
        via ``importlib.machinery.SourcelessFileLoader`` as
        ``pdd.prompts.foo_v2`` — the broad dir-blanket would silently
        allow it. After R14, the ``.prompt``-suffix exclusion lets
        this path fall through to the importable-suffix filter, which
        catches ``.pyc``.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text(
            json.dumps([]), encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "foo_v2.pyc").write_bytes(
            b"\x00\x00 stub"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/prompts/foo_v2.pyc",
            ],
        )
        assert reason is not None
        assert "pdd/prompts/foo_v2.pyc" in reason

    def test_guard_allows_prompt_file_under_prompts_dir(
        self, tmp_path: Path
    ) -> None:
        """Negative: a ``pdd/prompts/foo_v2.prompt`` file in the change
        set (even when unregistered) must still be skipped by the
        unregistered-new-code scan because ``.prompt`` is the
        canonical prompt-source suffix and isn't importable Python.
        The ``.prompt``-suffix exclusion preserves the original
        intent of the dir-blanket while closing the importable-file
        hole.
        """
        from pdd.checkup_review_loop import (
            _check_architecture_registry_edit_guard,
        )

        _seed_repo_with_arch(
            tmp_path,
            [_arch_pair("foo_python.prompt", "pdd/foo.py")],
        )

        # Retirement on disk: registered pair gone, registry wiped,
        # plus an UNREGISTERED .prompt file dropped under the prompts
        # dir. The .prompt suffix must mean the unregistered-new-code
        # scan ignores this path — it's not importable Python.
        (tmp_path / "pdd" / "foo.py").unlink()
        (tmp_path / "pdd" / "prompts" / "foo_python.prompt").unlink()
        (tmp_path / "architecture.json").write_text(
            json.dumps([]), encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "foo_v2.prompt").write_text(
            "prompt body\n", encoding="utf-8"
        )

        reason = _check_architecture_registry_edit_guard(
            tmp_path,
            [
                "architecture.json",
                "pdd/foo.py",
                "pdd/prompts/foo_python.prompt",
                "pdd/prompts/foo_v2.prompt",
            ],
        )
        # The new .prompt file must not appear as an offender. Other
        # checks (added-pair / removed-pair) may legitimately fire on
        # the registry wipe + retirement, but the unregistered-new-
        # code scan must NOT flag the .prompt path.
        if reason is not None:
            assert "pdd/prompts/foo_v2.prompt" not in reason
