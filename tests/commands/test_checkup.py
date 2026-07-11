from __future__ import annotations

import os
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.commands.checkup import (
    _emit_agentic_review_loop_json,
    _prepare_agentic_review_loop_artifact,
    checkup,
)


def test_checkup_review_loop_cli_forwards_reviewer_and_fixer_options() -> None:
    runner = CliRunner()

    with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
        run_checkup.return_value = (True, "clean", 0.25, "codex")

        result = runner.invoke(
            checkup,
            [
                "--pr",
                "https://github.com/org/repo/pull/7",
                "--issue",
                "https://github.com/org/repo/issues/6",
                "--review-loop",
                "--reviewer",
                "codex",
                "--fixer",
                "claude",
                "--reviewer-fallback",
                "gemini",
                "--max-review-rounds",
                "3",
                "--blocking-severities",
                "blocker,critical,medium",
            ],
            obj={"quiet": True, "verbose": False},
        )

    assert result.exit_code == 0
    kwargs = run_checkup.call_args.kwargs
    assert kwargs["review_loop"] is True
    assert kwargs["reviewer"] == "codex"
    assert kwargs["fixer"] == "claude"
    assert kwargs["reviewer_fallback"] == "gemini"
    assert kwargs["allow_same_reviewer_fixer"] is False
    assert kwargs["max_review_rounds"] == 3
    assert kwargs["blocking_severities"] == "blocker,critical,medium"


def test_checkup_review_loop_cli_forwards_same_role_flag() -> None:
    runner = CliRunner()

    with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
        run_checkup.return_value = (True, "clean", 0.25, "codex")

        result = runner.invoke(
            checkup,
            [
                "--pr",
                "https://github.com/org/repo/pull/7",
                "--issue",
                "https://github.com/org/repo/issues/6",
                "--review-loop",
                "--reviewer",
                "codex",
                "--fixer",
                "codex",
                "--allow-same-reviewer-fixer",
            ],
            obj={"quiet": True, "verbose": False},
        )

    assert result.exit_code == 0
    kwargs = run_checkup.call_args.kwargs
    assert kwargs["reviewer"] == "codex"
    assert kwargs["fixer"] == "codex"
    assert kwargs["allow_same_reviewer_fixer"] is True


def test_checkup_review_only_requires_review_loop() -> None:
    runner = CliRunner()

    result = runner.invoke(
        checkup,
        [
            "--pr",
            "https://github.com/org/repo/pull/7",
            "--issue",
            "https://github.com/org/repo/issues/6",
            "--review-only",
        ],
        obj={"quiet": True, "verbose": False},
    )

    assert result.exit_code == 2
    assert "--review-only requires --review-loop" in result.output


def test_checkup_start_step_forwards_override() -> None:
    runner = CliRunner()

    with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
        run_checkup.return_value = (True, "clean", 0.25, "codex")

        result = runner.invoke(
            checkup,
            [
                "--pr",
                "https://github.com/org/repo/pull/7",
                "--issue",
                "https://github.com/org/repo/issues/6",
                "--start-step",
                "7",
            ],
            obj={"quiet": True, "verbose": False},
        )

    assert result.exit_code == 0
    assert run_checkup.call_args.kwargs["start_step_override"] == 7


def test_checkup_start_step_rejected_with_review_loop() -> None:
    runner = CliRunner()

    result = runner.invoke(
        checkup,
        [
            "--pr",
            "https://github.com/org/repo/pull/7",
            "--issue",
            "https://github.com/org/repo/issues/6",
            "--review-loop",
            "--start-step",
            "7",
        ],
        obj={"quiet": True, "verbose": False},
    )

    assert result.exit_code == 2
    assert "--start-step applies to the legacy checkup workflow" in result.output


def test_checkup_test_scope_defaults_to_full() -> None:
    """Default `pdd checkup --pr` must keep the full-suite quality gate."""
    runner = CliRunner()

    with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
        run_checkup.return_value = (True, "clean", 0.25, "codex")

        result = runner.invoke(
            checkup,
            [
                "--pr",
                "https://github.com/org/repo/pull/7",
                "--issue",
                "https://github.com/org/repo/issues/6",
            ],
            obj={"quiet": True, "verbose": False},
        )

    assert result.exit_code == 0
    assert run_checkup.call_args.kwargs["test_scope"] == "full"


def test_checkup_test_scope_targeted_forwarded() -> None:
    runner = CliRunner()

    with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
        run_checkup.return_value = (True, "clean", 0.25, "codex")

        result = runner.invoke(
            checkup,
            [
                "--pr",
                "https://github.com/org/repo/pull/7",
                "--issue",
                "https://github.com/org/repo/issues/6",
                "--test-scope",
                "targeted",
            ],
            obj={"quiet": True, "verbose": False},
        )

    assert result.exit_code == 0
    assert run_checkup.call_args.kwargs["test_scope"] == "targeted"


def test_checkup_test_scope_targeted_requires_pr_mode() -> None:
    """Targeted scope only makes sense with --pr; issue mode rejects it."""
    runner = CliRunner()

    result = runner.invoke(
        checkup,
        [
            "https://github.com/org/repo/issues/6",
            "--test-scope",
            "targeted",
        ],
        obj={"quiet": True, "verbose": False},
    )

    assert result.exit_code == 2
    assert "--test-scope targeted requires --pr" in result.output


def test_checkup_test_scope_rejects_unknown_value() -> None:
    runner = CliRunner()

    result = runner.invoke(
        checkup,
        [
            "--pr",
            "https://github.com/org/repo/pull/7",
            "--issue",
            "https://github.com/org/repo/issues/6",
            "--test-scope",
            "quick",
        ],
        obj={"quiet": True, "verbose": False},
    )

    assert result.exit_code == 2
    assert "'quick'" in result.output or "test-scope" in result.output


# ---------------------------------------------------------------------------
# Issue #1292: make --issue optional in --pr mode (review a PR on its merits)
# ---------------------------------------------------------------------------


def test_checkup_pr_without_issue_runs_merit_review() -> None:
    """`pdd checkup --pr <url>` with no --issue must dispatch a merit review.

    Regression for #1292: PR mode previously hard-required --issue. With no
    issue, the command should still run and forward ``issue_url=None`` so the
    orchestrator reviews the PR on its own merits.
    """
    runner = CliRunner()

    with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
        run_checkup.return_value = (True, "clean", 0.25, "codex")

        result = runner.invoke(
            checkup,
            ["--pr", "https://github.com/org/repo/pull/7"],
            obj={"quiet": True, "verbose": False},
        )

    assert result.exit_code == 0, result.output
    kwargs = run_checkup.call_args.kwargs
    assert kwargs["pr_url"] == "https://github.com/org/repo/pull/7"
    assert kwargs["issue_url"] is None


def test_checkup_pr_with_issue_still_forwards_issue() -> None:
    """With --issue present, PR mode behaviour is unchanged (alignment review)."""
    runner = CliRunner()

    with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
        run_checkup.return_value = (True, "clean", 0.25, "codex")

        result = runner.invoke(
            checkup,
            [
                "--pr",
                "https://github.com/org/repo/pull/7",
                "--issue",
                "https://github.com/org/repo/issues/6",
            ],
            obj={"quiet": True, "verbose": False},
        )

    assert result.exit_code == 0, result.output
    kwargs = run_checkup.call_args.kwargs
    assert kwargs["issue_url"] == "https://github.com/org/repo/issues/6"


def test_checkup_issue_without_pr_rejected() -> None:
    """A bare --issue (no --pr) is rejected; a lone issue belongs in TARGET mode."""
    runner = CliRunner()

    result = runner.invoke(
        checkup,
        ["--issue", "https://github.com/org/repo/issues/6"],
        obj={"quiet": True, "verbose": False},
    )

    assert result.exit_code == 2
    assert "--issue requires --pr" in result.output


def test_checkup_review_loop_requires_issue() -> None:
    """--review-loop keeps requiring --issue (no-issue review loop deferred, #1292)."""
    runner = CliRunner()

    result = runner.invoke(
        checkup,
        [
            "--pr",
            "https://github.com/org/repo/pull/7",
            "--review-loop",
        ],
        obj={"quiet": True, "verbose": False},
    )

    assert result.exit_code == 2
    assert "--review-loop requires --pr and --issue" in result.output


def test_checkup_pr_without_issue_invalid_pr_url_rejected() -> None:
    """An invalid --pr URL is still rejected even when no --issue is supplied."""
    runner = CliRunner()

    result = runner.invoke(
        checkup,
        ["--pr", "not-a-pr-url"],
        obj={"quiet": True, "verbose": False},
    )

    assert result.exit_code == 2
    assert "--pr must be a GitHub pull-request URL" in result.output


# ---------------------------------------------------------------------------
# Issue #1292 acceptance criterion: a real end-to-end run of
# `pdd checkup --pr <PR>` with NO --issue. Opt-in (needs a live PR + gh +
# LLM credentials); skipped in normal/CI runs (`-m "not real"`). Runs with
# --no-fix and GitHub state disabled so it is strictly read-only.
# ---------------------------------------------------------------------------


@pytest.mark.e2e
@pytest.mark.real
def test_checkup_pr_without_issue_real() -> None:
    pr_url = os.environ.get("PDD_REAL_CHECKUP_PR_URL")
    if not pr_url:
        pytest.skip("Set PDD_REAL_CHECKUP_PR_URL to a live PR to run this test.")

    from pdd.agentic_checkup import run_agentic_checkup

    success, message, cost, model = run_agentic_checkup(
        None,  # no --issue: review the PR on its own merits
        pr_url=pr_url,
        no_fix=True,
        use_github_state=False,
        quiet=True,
    )

    # The run must reach a real verdict, not bail out on a missing issue.
    assert isinstance(success, bool)
    assert "Invalid GitHub issue URL" not in message
    assert "must both be provided" not in message
    assert isinstance(cost, float)


# ---------------------------------------------------------------------------
# --agentic-review-loop (issue #1788)
# ---------------------------------------------------------------------------


def test_agentic_review_loop_requires_pr() -> None:
    runner = CliRunner()
    result = runner.invoke(checkup, ["--agentic-review-loop"], obj={"quiet": True})
    assert result.exit_code != 0
    assert "--agentic-review-loop requires --pr." in result.output


def test_agentic_review_loop_conflicts_with_final_gate() -> None:
    runner = CliRunner()
    result = runner.invoke(
        checkup,
        [
            "--agentic-review-loop",
            "--final-gate",
            "--pr",
            "https://github.com/org/repo/pull/7",
        ],
        obj={"quiet": True},
    )
    assert result.exit_code != 0
    assert (
        "--agentic-review-loop cannot be combined with --final-gate." in result.output
    )


def test_agentic_review_loop_forwards_knobs_and_allows_no_fix() -> None:
    runner = CliRunner()
    # Isolate the filesystem: a failed agentic invocation now writes a
    # fail-closed blocking tombstone to the public path, which must not leak
    # into the repo working tree.
    with runner.isolated_filesystem():
        with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
            run_checkup.return_value = (True, "clean", 0.0, "codex")
            result = runner.invoke(
                checkup,
                [
                    "--pr",
                    "https://github.com/org/repo/pull/7",
                    "--agentic-review-loop",
                    "--no-fix",
                    "--adversarial-prompt",
                    "be maximally skeptical",
                    "--fresh-final-review",
                    "gemini",
                ],
                obj={"quiet": True, "verbose": False},
            )
    assert result.exit_code == 1, result.output
    kwargs = run_checkup.call_args.kwargs
    assert kwargs["agentic_review_loop"] is True
    assert kwargs["no_fix"] is True
    assert kwargs["adversarial_prompt"] == "be maximally skeptical"
    assert kwargs["fresh_final_review_role"] == "gemini"


def test_agentic_review_loop_emits_json_wrapper_on_stdout() -> None:
    """Issue #1788: --agentic-review-loop stdout must parse as JSON even when the
    review loop wrote no artifact file (wrapper fallback)."""
    import json

    runner = CliRunner()
    with runner.isolated_filesystem():
        with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
            run_checkup.return_value = (True, "clean", 0.0, "codex")
            result = runner.invoke(
                checkup,
                ["--pr", "https://github.com/org/repo/pull/7", "--agentic-review-loop"],
                obj={"quiet": False, "verbose": False},
            )
    assert result.exit_code == 1, result.output
    payload = json.loads(result.output)
    assert payload["schema_version"] == "pdd.checkup.agentic.v1.wrapper"
    assert payload["status"] == "failed"
    assert payload["artifact_path"].endswith("pdd-checkup-agentic-7.json")


def test_agentic_review_loop_emits_artifact_json_on_stdout() -> None:
    """Issue #1788: when the review loop wrote the artifact file, stdout carries
    that exact pdd.checkup.agentic.v1 object."""
    import json

    runner = CliRunner()
    with runner.isolated_filesystem():

        def run_and_write_artifact(**_kwargs):
            with open(
                _kwargs["agentic_artifact_path"], "w", encoding="utf-8"
            ) as handle:
                json.dump(
                    {
                        "schema_version": "pdd.checkup.agentic.v1",
                        "authority": "canonical_pass_agentic_mirror_clean",
                        "status": "passed",
                        "verdict": {"decision": "pass"},
                    },
                    handle,
                )
            return True, "clean", 0.0, "codex"

        with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
            run_checkup.side_effect = run_and_write_artifact
            result = runner.invoke(
                checkup,
                ["--pr", "https://github.com/org/repo/pull/7", "--agentic-review-loop"],
                obj={"quiet": False, "verbose": False},
            )
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["schema_version"] == "pdd.checkup.agentic.v1"
    assert payload["authority"] == "canonical_pass_agentic_mirror_clean"


def test_agentic_review_loop_blocking_artifact_exits_nonzero() -> None:
    import json

    runner = CliRunner()
    with runner.isolated_filesystem():

        def run_and_write_artifact(**_kwargs):
            with open(
                _kwargs["agentic_artifact_path"], "w", encoding="utf-8"
            ) as handle:
                json.dump(
                    {
                        "schema_version": "pdd.checkup.agentic.v1",
                        "status": "failed",
                        "verdict": {"decision": "block"},
                    },
                    handle,
                )
            return True, "report produced", 0.0, "codex"

        with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
            run_checkup.side_effect = run_and_write_artifact
            result = runner.invoke(
                checkup,
                ["--pr", "https://github.com/org/repo/pull/7", "--agentic-review-loop"],
                obj={"quiet": False, "verbose": False},
            )
    assert result.exit_code == 1
    assert json.loads(result.output)["verdict"]["decision"] == "block"


def test_agentic_review_loop_rejects_stale_passing_artifact() -> None:
    import json

    runner = CliRunner()
    with runner.isolated_filesystem():
        with open("pdd-checkup-agentic-7.json", "w", encoding="utf-8") as handle:
            json.dump(
                {
                    "schema_version": "pdd.checkup.agentic.v1",
                    "status": "passed",
                    "verdict": {"decision": "pass"},
                },
                handle,
            )
        with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
            # Simulate best-effort artifact emission failing in this invocation.
            run_checkup.return_value = (
                True,
                "blocking report with ghp_sensitive_runtime_token",
                12.34,
                "sensitive-provider-model",
            )
            result = runner.invoke(
                checkup,
                ["--pr", "https://github.com/org/repo/pull/7", "--agentic-review-loop"],
                obj={"quiet": False, "verbose": False},
            )
        with open("pdd-checkup-agentic-7.json", encoding="utf-8") as handle:
            persisted = json.load(handle)
    assert result.exit_code == 1
    payload = json.loads(result.output)
    assert payload["schema_version"] == "pdd.checkup.agentic.v1.wrapper"
    assert payload["status"] == "failed"
    assert persisted == {
        "schema_version": "pdd.checkup.agentic.v1.wrapper",
        "success": False,
        "status": "failed",
    }
    assert "ghp_sensitive_runtime_token" not in json.dumps(persisted)
    assert "sensitive-provider-model" not in json.dumps(persisted)
    assert "12.34" not in json.dumps(persisted)
    # P1/security (issue #1788): the stdout wrapper must not carry raw provider/
    # runtime diagnostics either — hosted job logs retain stdout even when the
    # tombstone on disk is scrubbed.
    assert "ghp_sensitive_runtime_token" not in result.output
    assert "sensitive-provider-model" not in result.output
    assert "12.34" not in result.output
    assert "message" not in payload
    assert "cost" not in payload
    assert "model" not in payload


def test_agentic_review_loop_fails_before_run_when_private_path_reservation_fails() -> (
    None
):
    import json

    runner = CliRunner()
    with runner.isolated_filesystem():
        with open("pdd-checkup-agentic-7.json", "w", encoding="utf-8") as handle:
            json.dump(
                {
                    "schema_version": "pdd.checkup.agentic.v1",
                    "status": "passed",
                    "verdict": {"decision": "pass"},
                },
                handle,
            )
        with patch(
            "pdd.commands.checkup.tempfile.NamedTemporaryFile",
            side_effect=PermissionError,
        ):
            with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
                run_checkup.return_value = (
                    True,
                    "blocking report produced",
                    0.0,
                    "codex",
                )
                result = runner.invoke(
                    checkup,
                    [
                        "--pr",
                        "https://github.com/org/repo/pull/7",
                        "--agentic-review-loop",
                    ],
                    obj={"quiet": False, "verbose": False},
                )
        # P1 (issue #1788): a reservation failure must not leave the prior
        # public PASS consumable. Capture its post-run state inside the
        # isolated filesystem before it is torn down.
        stale_public = os.path.join(os.getcwd(), "pdd-checkup-agentic-7.json")
        if os.path.exists(stale_public):
            with open(stale_public, encoding="utf-8") as handle:
                public_after = json.load(handle)
        else:
            public_after = None
    assert result.exit_code == 1
    payload = json.loads(result.output)
    assert payload["schema_version"] == "pdd.checkup.agentic.v1.wrapper"
    assert payload["status"] == "failed"
    run_checkup.assert_not_called()
    # The prior public PASS must be gone (removed or a non-pass tombstone).
    assert public_after is None or (
        public_after.get("status") != "passed"
        and public_after.get("verdict", {}).get("decision") != "pass"
    )


def test_concurrent_agentic_invocations_accept_only_their_own_artifact(
    tmp_path, monkeypatch, capsys
) -> None:
    """Same-PR invocations must not consume each other's verdict artifact."""
    import json

    monkeypatch.chdir(tmp_path)
    pr_url = "https://github.com/org/repo/pull/7"
    first_private, first_public = _prepare_agentic_review_loop_artifact(pr_url)
    second_private, second_public = _prepare_agentic_review_loop_artifact(pr_url)

    assert first_private is not None
    assert second_private is not None
    assert first_private != second_private
    assert first_public == second_public

    second_private.write_text(
        json.dumps(
            {
                "schema_version": "pdd.checkup.agentic.v1",
                "status": "passed",
                "verdict": {"decision": "pass"},
            }
        ),
        encoding="utf-8",
    )

    assert not _emit_agentic_review_loop_json(
        artifact_path=first_private,
        published_artifact_path=first_public,
        failure_category="agentic_artifact_unavailable",
    )
    first_payload = json.loads(capsys.readouterr().out)
    assert first_payload["schema_version"] == "pdd.checkup.agentic.v1.wrapper"
    assert first_payload["status"] == "failed"

    assert _emit_agentic_review_loop_json(
        artifact_path=second_private,
        published_artifact_path=second_public,
    )
    second_payload = json.loads(capsys.readouterr().out)
    assert second_payload["schema_version"] == "pdd.checkup.agentic.v1"
    assert second_payload["status"] == "passed"


def test_agentic_atomic_publish_failure_clears_stale_pass(
    tmp_path, monkeypatch, capsys
) -> None:
    """P1 (issue #1788): if atomic publication fails, a prior public PASS must
    not remain. Even with a valid current-head PASS in the private file, a
    failed ``Path.replace`` must leave the public path non-consumable."""
    import json

    monkeypatch.chdir(tmp_path)
    private, public = _prepare_agentic_review_loop_artifact(
        "https://github.com/org/repo/pull/7"
    )
    assert private is not None and public is not None

    # A prior invocation left a PASSING public artifact.
    public.write_text(
        json.dumps(
            {
                "schema_version": "pdd.checkup.agentic.v1",
                "status": "passed",
                "verdict": {"decision": "pass"},
            }
        ),
        encoding="utf-8",
    )
    # This invocation produced a valid PASS, but every atomic replace fails.
    private.write_text(
        json.dumps(
            {
                "schema_version": "pdd.checkup.agentic.v1",
                "status": "passed",
                "verdict": {"decision": "pass"},
            }
        ),
        encoding="utf-8",
    )

    with patch(
        "pdd.commands.checkup.Path.replace", side_effect=OSError("no rename")
    ):
        emitted = _emit_agentic_review_loop_json(
            artifact_path=private,
            published_artifact_path=public,
            failure_category="agentic_artifact_unavailable",
        )

    assert emitted is False
    payload = json.loads(capsys.readouterr().out)
    assert payload["schema_version"] == "pdd.checkup.agentic.v1.wrapper"
    assert payload["status"] == "failed"
    # The prior public PASS must not survive a failed publication.
    if public.exists():
        persisted = json.loads(public.read_text(encoding="utf-8"))
        assert persisted.get("status") != "passed"
        assert persisted.get("verdict", {}).get("decision") != "pass"


def test_agentic_review_loop_does_not_require_issue() -> None:
    runner = CliRunner()
    with runner.isolated_filesystem():
        with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
            run_checkup.return_value = (True, "clean", 0.0, "codex")
            result = runner.invoke(
                checkup,
                ["--pr", "https://github.com/org/repo/pull/7", "--agentic-review-loop"],
                obj={"quiet": True, "verbose": False},
            )
    # No --issue provided, yet the command must not reject it (own-merits review).
    assert result.exit_code == 1, result.output
    assert "requires --pr and --issue" not in result.output
