"""Tests for ``pdd checkup --pr --cloud-job`` (issue #2295).

Covers:
- Submission: argument vector preservation, JWT forwarding, endpoint routing
- Ownership: job_id returned and forwarded to polling
- Argument validation: --cloud-job requires --pr, rejects --local
- Polling: terminal states, output bounding, sanitization, quiet mode
- Credit settlement: cost, model, billing_source in result
- No-local-fallback: CloudCheckupError raised, never falls back silently
- CLI dispatch: checkup --pr --cloud-job routes to cloud, not local executor
- Provider-limit metadata emitted even in quiet mode
"""

from __future__ import annotations

import json
import time
from typing import Any, Dict, Optional
from unittest.mock import MagicMock, call, patch

import pytest
import requests
from click.testing import CliRunner

from pdd.cloud_checkup_job import (
    CloudCheckupError,
    CloudCheckupJob,
    CloudCheckupResult,
    _build_checkup_args,
    _sanitize_output_lines,
    poll_cloud_checkup_job,
    run_cloud_checkup,
    submit_cloud_checkup_job,
)
from pdd.commands.checkup import checkup


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

PR_URL = "https://github.com/org/repo/pull/42"
ISSUE_URL = "https://github.com/org/repo/issues/10"
FAKE_JWT = "fake.jwt.token"
FAKE_JOB_ID = "abc123def456"


def _mock_submit_response(job_id: str = FAKE_JOB_ID, billing: str = "pdd-cloud") -> MagicMock:
    resp = MagicMock()
    resp.ok = True
    resp.status_code = 200
    resp.json.return_value = {"jobId": job_id, "billingSource": billing}
    return resp


def _mock_poll_response(
    status: str = "succeeded",
    exit_code: int = 0,
    cost: float = 1.23,
    model: str = "cloud-codex",
    message: str = "checkup succeeded",
    output: str = "All tests passed.\nSuccess",
    billing: str = "pdd-cloud",
    report: Optional[str] = None,
    provider_meta: Optional[Dict[str, Any]] = None,
) -> MagicMock:
    resp = MagicMock()
    resp.ok = True
    resp.status_code = 200
    data: Dict[str, Any] = {
        "status": status,
        "exitCode": exit_code,
        "costUsd": cost,
        "model": model,
        "message": message,
        "output": output,
        "billingSource": billing,
    }
    if report is not None:
        data["report"] = report
    if provider_meta is not None:
        data.update(provider_meta)
    resp.json.return_value = data
    return resp


# ---------------------------------------------------------------------------
# _build_checkup_args
# ---------------------------------------------------------------------------

class TestBuildCheckupArgs:
    def test_required_fields_present(self):
        args = _build_checkup_args(
            pr_url=PR_URL,
            issue_url=None,
            test_scope="full",
            full_suite_source="local",
            review_loop=False,
            final_gate=False,
            agentic_review_loop=False,
            reviewer=None,
            fixer=None,
            reviewers="codex,claude",
            reviewer_fallback=None,
            fixer_fallback=None,
            allow_same_reviewer_fixer=False,
            max_review_rounds=5,
            max_review_cost=50.0,
            max_review_minutes=90.0,
            require_all_reviewers_clean=True,
            continue_on_reviewer_limit=False,
            require_final_fresh_review=True,
            blocking_severities=None,
            clean_reviewer_states=None,
            fallback_reviewer_on_failure=False,
            no_fix=False,
            review_only=False,
            fresh_final_review=None,
            adversarial_prompt=None,
            enable_gates=True,
            gate_timeout=60.0,
            gate_allow=(),
            timeout_adder=0.0,
            no_github_state=False,
            terra_sol=False,
            fresh_start=False,
        )
        assert args["pr_url"] == PR_URL
        assert args["test_scope"] == "full"
        assert "issue_url" not in args  # Optional field omitted when None

    def test_optional_fields_included_when_set(self):
        args = _build_checkup_args(
            pr_url=PR_URL,
            issue_url=ISSUE_URL,
            test_scope="targeted",
            full_suite_source="github-checks",
            review_loop=True,
            final_gate=False,
            agentic_review_loop=False,
            reviewer="codex",
            fixer="claude",
            reviewers="codex,claude",
            reviewer_fallback="gemini",
            fixer_fallback=None,
            allow_same_reviewer_fixer=False,
            max_review_rounds=3,
            max_review_cost=25.0,
            max_review_minutes=60.0,
            require_all_reviewers_clean=True,
            continue_on_reviewer_limit=False,
            require_final_fresh_review=True,
            blocking_severities="blocker,critical",
            clean_reviewer_states=None,
            fallback_reviewer_on_failure=True,
            no_fix=False,
            review_only=False,
            fresh_final_review="codex",
            adversarial_prompt="find bugs",
            enable_gates=True,
            gate_timeout=30.0,
            gate_allow=("ruff",),
            timeout_adder=10.0,
            no_github_state=False,
            terra_sol=False,
            fresh_start=True,
        )
        assert args["issue_url"] == ISSUE_URL
        assert args["reviewer"] == "codex"
        assert args["fixer"] == "claude"
        assert args["reviewer_fallback"] == "gemini"
        assert "fixer_fallback" not in args
        assert args["blocking_severities"] == "blocker,critical"
        assert args["fresh_final_review"] == "codex"
        assert args["adversarial_prompt"] == "find bugs"
        assert args["gate_allow"] == ["ruff"]
        assert args["fresh_start"] is True

    def test_gate_allow_tuple_becomes_list(self):
        args = _build_checkup_args(
            pr_url=PR_URL, issue_url=None, test_scope="full",
            full_suite_source="local", review_loop=False, final_gate=False,
            agentic_review_loop=False, reviewer=None, fixer=None,
            reviewers="codex", reviewer_fallback=None, fixer_fallback=None,
            allow_same_reviewer_fixer=False, max_review_rounds=5,
            max_review_cost=50.0, max_review_minutes=90.0,
            require_all_reviewers_clean=True, continue_on_reviewer_limit=False,
            require_final_fresh_review=True, blocking_severities=None,
            clean_reviewer_states=None, fallback_reviewer_on_failure=False,
            no_fix=False, review_only=False, fresh_final_review=None,
            adversarial_prompt=None, enable_gates=True, gate_timeout=60.0,
            gate_allow=("prettier", "ruff"), timeout_adder=0.0,
            no_github_state=False, terra_sol=False, fresh_start=False,
        )
        assert isinstance(args["gate_allow"], list)
        assert args["gate_allow"] == ["prettier", "ruff"]


# ---------------------------------------------------------------------------
# submit_cloud_checkup_job
# ---------------------------------------------------------------------------

class TestSubmitCloudCheckupJob:
    def test_successful_submission_returns_job(self):
        with patch("requests.post", return_value=_mock_submit_response()) as mock_post:
            job = submit_cloud_checkup_job(
                pr_url=PR_URL,
                jwt_token=FAKE_JWT,
                issue_url=ISSUE_URL,
            )
        assert job.job_id == FAKE_JOB_ID
        assert job.pr_url == PR_URL
        assert job.billing_source == "pdd-cloud"
        mock_post.assert_called_once()

    def test_jwt_forwarded_as_bearer_token(self):
        with patch("requests.post", return_value=_mock_submit_response()) as mock_post:
            submit_cloud_checkup_job(pr_url=PR_URL, jwt_token=FAKE_JWT)
        _, kwargs = mock_post.call_args
        assert kwargs["headers"]["Authorization"] == f"Bearer {FAKE_JWT}"

    def test_argument_vector_in_payload(self):
        with patch("requests.post", return_value=_mock_submit_response()) as mock_post:
            submit_cloud_checkup_job(
                pr_url=PR_URL,
                jwt_token=FAKE_JWT,
                issue_url=ISSUE_URL,
                reviewer="codex",
                final_gate=True,
                test_scope="targeted",
            )
        _, kwargs = mock_post.call_args
        payload = kwargs["json"]
        assert payload["checkupArgs"]["pr_url"] == PR_URL
        assert payload["checkupArgs"]["issue_url"] == ISSUE_URL
        assert payload["checkupArgs"]["reviewer"] == "codex"
        assert payload["checkupArgs"]["final_gate"] is True
        assert payload["checkupArgs"]["test_scope"] == "targeted"
        assert payload["billingSource"] == "pdd-cloud"

    def test_401_raises_cloud_checkup_error(self):
        resp = MagicMock()
        resp.ok = False
        resp.status_code = 401
        with patch("requests.post", return_value=resp):
            with pytest.raises(CloudCheckupError, match="authentication failed"):
                submit_cloud_checkup_job(pr_url=PR_URL, jwt_token=FAKE_JWT)

    def test_402_insufficient_credits_raises(self):
        resp = MagicMock()
        resp.ok = False
        resp.status_code = 402
        with patch("requests.post", return_value=resp):
            with pytest.raises(CloudCheckupError, match="credits"):
                submit_cloud_checkup_job(pr_url=PR_URL, jwt_token=FAKE_JWT)

    def test_403_github_app_not_installed_raises(self):
        resp = MagicMock()
        resp.ok = False
        resp.status_code = 403
        with patch("requests.post", return_value=resp):
            with pytest.raises(CloudCheckupError, match="GitHub App"):
                submit_cloud_checkup_job(pr_url=PR_URL, jwt_token=FAKE_JWT)

    def test_connection_error_raises_fail_closed(self):
        with patch("requests.post", side_effect=requests.exceptions.ConnectionError("refused")):
            with pytest.raises(CloudCheckupError, match="Cannot reach"):
                submit_cloud_checkup_job(pr_url=PR_URL, jwt_token=FAKE_JWT)

    def test_timeout_raises_fail_closed(self):
        with patch("requests.post", side_effect=requests.exceptions.Timeout("timed out")):
            with pytest.raises(CloudCheckupError, match="Timed out"):
                submit_cloud_checkup_job(pr_url=PR_URL, jwt_token=FAKE_JWT)

    def test_missing_job_id_raises(self):
        resp = MagicMock()
        resp.ok = True
        resp.status_code = 200
        resp.json.return_value = {}  # no jobId
        with patch("requests.post", return_value=resp):
            with pytest.raises(CloudCheckupError, match="job ID"):
                submit_cloud_checkup_job(pr_url=PR_URL, jwt_token=FAKE_JWT)

    def test_non_json_response_raises(self):
        resp = MagicMock()
        resp.ok = True
        resp.status_code = 200
        resp.json.side_effect = ValueError("not json")
        resp.text = "Internal Server Error"
        with patch("requests.post", return_value=resp):
            with pytest.raises(CloudCheckupError, match="non-JSON"):
                submit_cloud_checkup_job(pr_url=PR_URL, jwt_token=FAKE_JWT)

    def test_no_local_fallback_on_failure(self):
        """Submission failure must raise, not return a local-execution result."""
        resp = MagicMock()
        resp.ok = False
        resp.status_code = 500
        resp.json.return_value = {"error": "server error"}
        resp.text = "server error"
        with patch("requests.post", return_value=resp):
            with pytest.raises(CloudCheckupError):
                submit_cloud_checkup_job(pr_url=PR_URL, jwt_token=FAKE_JWT)


# ---------------------------------------------------------------------------
# poll_cloud_checkup_job
# ---------------------------------------------------------------------------

class TestPollCloudCheckupJob:
    def _make_job(self) -> CloudCheckupJob:
        return CloudCheckupJob(job_id=FAKE_JOB_ID, pr_url=PR_URL)

    def test_immediate_success(self):
        with patch("requests.post", return_value=_mock_poll_response(status="succeeded")):
            result = poll_cloud_checkup_job(
                self._make_job(), jwt_token=FAKE_JWT, quiet=True
            )
        assert result.success is True
        assert result.exit_code == 0
        assert result.job_id == FAKE_JOB_ID

    def test_immediate_failure(self):
        with patch(
            "requests.post",
            return_value=_mock_poll_response(
                status="failed", exit_code=1, message="tests failed"
            ),
        ):
            result = poll_cloud_checkup_job(
                self._make_job(), jwt_token=FAKE_JWT, quiet=True
            )
        assert result.success is False
        assert result.exit_code == 1

    def test_polls_until_terminal(self):
        pending = MagicMock()
        pending.ok = True
        pending.status_code = 200
        pending.json.return_value = {"status": "running", "currentStep": "step 5"}

        terminal = _mock_poll_response(status="succeeded")

        with patch("requests.post", side_effect=[pending, pending, terminal]) as mock_post:
            with patch("time.sleep"):
                result = poll_cloud_checkup_job(
                    self._make_job(), jwt_token=FAKE_JWT, quiet=True, poll_interval=0
                )
        assert result.success is True
        assert mock_post.call_count == 3

    def test_timeout_raises_fail_closed(self):
        pending = MagicMock()
        pending.ok = True
        pending.status_code = 200
        pending.json.return_value = {"status": "running"}

        with patch("requests.post", return_value=pending):
            with patch("time.monotonic", side_effect=[0.0, 0.0, 9999.0]):
                with patch("time.sleep"):
                    with pytest.raises(CloudCheckupError, match="did not complete"):
                        poll_cloud_checkup_job(
                            self._make_job(),
                            jwt_token=FAKE_JWT,
                            quiet=True,
                            poll_interval=0,
                            poll_timeout=1,
                        )

    def test_cost_and_model_in_result(self):
        with patch(
            "requests.post",
            return_value=_mock_poll_response(cost=2.50, model="cloud-codex-4"),
        ):
            result = poll_cloud_checkup_job(
                self._make_job(), jwt_token=FAKE_JWT, quiet=True
            )
        assert result.cost_usd == pytest.approx(2.50)
        assert result.model == "cloud-codex-4"

    def test_billing_source_in_result(self):
        with patch(
            "requests.post",
            return_value=_mock_poll_response(billing="pdd-cloud-enterprise"),
        ):
            result = poll_cloud_checkup_job(
                self._make_job(), jwt_token=FAKE_JWT, quiet=True
            )
        assert result.billing_source == "pdd-cloud-enterprise"

    def test_output_lines_bounded(self):
        long_output = "\n".join(f"line {i}" for i in range(600))
        with patch(
            "requests.post",
            return_value=_mock_poll_response(status="succeeded", output=long_output),
        ):
            result = poll_cloud_checkup_job(
                self._make_job(), jwt_token=FAKE_JWT, quiet=True
            )
        assert len(result.output_lines) <= 501  # 500 + truncation marker
        assert any("omitted" in line for line in result.output_lines)

    def test_report_truncated_when_too_large(self):
        big_report = "x" * (70 * 1024)  # 70 KiB > 64 KiB limit
        with patch(
            "requests.post",
            return_value=_mock_poll_response(status="succeeded", report=big_report),
        ):
            result = poll_cloud_checkup_job(
                self._make_job(), jwt_token=FAKE_JWT, quiet=True
            )
        assert result.report is not None
        assert len(result.report) <= 64 * 1024 + 20  # small tolerance for marker
        assert "truncated" in (result.report or "")

    def test_provider_meta_extracted(self):
        with patch(
            "requests.post",
            return_value=_mock_poll_response(
                status="succeeded",
                provider_meta={"rateLimitInfo": {"remaining": 5}},
            ),
        ):
            result = poll_cloud_checkup_job(
                self._make_job(), jwt_token=FAKE_JWT, quiet=True
            )
        assert result.provider_meta.get("rateLimitInfo") == {"remaining": 5}

    def test_401_during_poll_raises(self):
        resp = MagicMock()
        resp.ok = False
        resp.status_code = 401
        with patch("requests.post", return_value=resp):
            with pytest.raises(CloudCheckupError, match="expired"):
                poll_cloud_checkup_job(self._make_job(), jwt_token=FAKE_JWT, quiet=True)

    def test_network_error_during_poll_raises(self):
        with patch(
            "requests.post", side_effect=requests.exceptions.ConnectionError("refused")
        ):
            with pytest.raises(CloudCheckupError, match="failed"):
                poll_cloud_checkup_job(self._make_job(), jwt_token=FAKE_JWT, quiet=True)


# ---------------------------------------------------------------------------
# _sanitize_output_lines
# ---------------------------------------------------------------------------

class TestSanitizeOutputLines:
    def test_jwt_line_redacted(self):
        lines = ["eyJhbGciOiJSUzI1NiJ9.payload.sig"]
        result = _sanitize_output_lines(lines)
        assert result[0] == "[line redacted: possible credential]"

    def test_github_pat_redacted(self):
        lines = ["token=ghp_abc123def"]
        result = _sanitize_output_lines(lines)
        assert result[0] == "[line redacted: possible credential]"

    def test_normal_lines_pass_through(self):
        lines = ["All tests passed.", "exit_code: 0", "cost: $1.23"]
        result = _sanitize_output_lines(lines)
        assert result == lines

    def test_bearer_header_redacted(self):
        lines = ["Authorization: Bearer somesecret"]
        result = _sanitize_output_lines(lines)
        assert result[0] == "[line redacted: possible credential]"

    def test_mixed_lines(self):
        lines = ["step 5 started", "ghp_token=abc", "step 5 done"]
        result = _sanitize_output_lines(lines)
        assert result[0] == "step 5 started"
        assert result[1] == "[line redacted: possible credential]"
        assert result[2] == "step 5 done"


# ---------------------------------------------------------------------------
# run_cloud_checkup (integration of submit + poll)
# ---------------------------------------------------------------------------

class TestRunCloudCheckup:
    def test_no_jwt_raises_fail_closed(self):
        with patch(
            "pdd.cloud_checkup_job.CloudConfig.get_jwt_token", return_value=None
        ):
            with pytest.raises(CloudCheckupError, match="authentication required"):
                run_cloud_checkup(pr_url=PR_URL)

    def test_submit_then_poll(self):
        with patch(
            "pdd.cloud_checkup_job.CloudConfig.get_jwt_token", return_value=FAKE_JWT
        ):
            with patch(
                "pdd.cloud_checkup_job.submit_cloud_checkup_job",
                return_value=CloudCheckupJob(job_id=FAKE_JOB_ID, pr_url=PR_URL),
            ) as mock_submit:
                with patch(
                    "pdd.cloud_checkup_job.poll_cloud_checkup_job",
                    return_value=CloudCheckupResult(
                        success=True,
                        message="ok",
                        cost_usd=0.5,
                        model="cloud-codex",
                        exit_code=0,
                        output_lines=["done"],
                        report=None,
                        billing_source="pdd-cloud",
                        job_id=FAKE_JOB_ID,
                    ),
                ) as mock_poll:
                    result = run_cloud_checkup(pr_url=PR_URL, quiet=True)

        mock_submit.assert_called_once()
        mock_poll.assert_called_once()
        assert result.success is True

    def test_quiet_mode_suppresses_progress(self, capsys):
        with patch(
            "pdd.cloud_checkup_job.CloudConfig.get_jwt_token", return_value=FAKE_JWT
        ):
            with patch(
                "pdd.cloud_checkup_job.submit_cloud_checkup_job",
                return_value=CloudCheckupJob(job_id=FAKE_JOB_ID, pr_url=PR_URL),
            ):
                with patch(
                    "pdd.cloud_checkup_job.poll_cloud_checkup_job",
                    return_value=CloudCheckupResult(
                        success=True,
                        message="ok",
                        cost_usd=0.5,
                        model="cloud-codex",
                        exit_code=0,
                        output_lines=[],
                        report=None,
                        billing_source="pdd-cloud",
                        job_id=FAKE_JOB_ID,
                    ),
                ):
                    run_cloud_checkup(pr_url=PR_URL, quiet=True)

        captured = capsys.readouterr()
        assert "Submitted" not in captured.out
        assert "Polling" not in captured.out


# ---------------------------------------------------------------------------
# CLI dispatch — checkup --pr --cloud-job
# ---------------------------------------------------------------------------

class TestCheckupCloudJobCli:
    def _runner(self) -> CliRunner:
        return CliRunner()

    def test_cloud_job_requires_pr(self):
        runner = self._runner()
        result = runner.invoke(
            checkup,
            ["--cloud-job", "https://github.com/org/repo/issues/42"],
            catch_exceptions=False,
            obj={"quiet": False, "verbose": False, "local": False},
        )
        assert result.exit_code != 0
        assert "--cloud-job requires --pr" in (result.output or "")

    def test_cloud_job_rejects_local(self):
        runner = self._runner()
        result = runner.invoke(
            checkup,
            ["--pr", PR_URL, "--cloud-job"],
            catch_exceptions=False,
            obj={"quiet": False, "verbose": False, "local": True},
        )
        assert result.exit_code != 0
        output = (result.output or "")
        assert "--cloud-job" in output or "local" in output.lower()

    def test_cloud_job_dispatches_to_cloud_not_local(self):
        """--cloud-job must never call run_agentic_checkup."""
        runner = self._runner()
        fake_result = CloudCheckupResult(
            success=True,
            message="cloud ok",
            cost_usd=0.99,
            model="cloud-codex",
            exit_code=0,
            output_lines=["All tests passed."],
            report=None,
            billing_source="pdd-cloud",
            job_id=FAKE_JOB_ID,
        )
        with patch(
            "pdd.commands.checkup.run_cloud_checkup", return_value=fake_result
        ) as mock_cloud:
            with patch("pdd.commands.checkup.run_agentic_checkup") as mock_local:
                result = runner.invoke(
                    checkup,
                    ["--pr", PR_URL, "--cloud-job"],
                    catch_exceptions=False,
                    obj={"quiet": False, "verbose": False, "local": False},
                )
        mock_cloud.assert_called_once()
        mock_local.assert_not_called()
        assert result.exit_code == 0

    def test_cloud_job_exits_nonzero_on_failure(self):
        runner = self._runner()
        fake_result = CloudCheckupResult(
            success=False,
            message="tests failed",
            cost_usd=0.50,
            model="cloud-codex",
            exit_code=1,
            output_lines=["FAILED: test_main"],
            report=None,
            billing_source="pdd-cloud",
            job_id=FAKE_JOB_ID,
        )
        with patch("pdd.commands.checkup.run_cloud_checkup", return_value=fake_result):
            result = runner.invoke(
                checkup,
                ["--pr", PR_URL, "--cloud-job"],
                catch_exceptions=False,
                obj={"quiet": False, "verbose": False, "local": False},
            )
        assert result.exit_code != 0

    def test_cloud_checkup_error_exits_nonzero(self):
        runner = self._runner()
        with patch(
            "pdd.commands.checkup.run_cloud_checkup",
            side_effect=CloudCheckupError("submission failed"),
        ):
            result = runner.invoke(
                checkup,
                ["--pr", PR_URL, "--cloud-job"],
                catch_exceptions=False,
                obj={"quiet": False, "verbose": False, "local": False},
            )
        assert result.exit_code != 0

    def test_billing_source_shown_before_dispatch(self):
        runner = self._runner()
        fake_result = CloudCheckupResult(
            success=True,
            message="ok",
            cost_usd=0.10,
            model="cloud-codex",
            exit_code=0,
            output_lines=[],
            report=None,
            billing_source="pdd-cloud",
            job_id=FAKE_JOB_ID,
        )
        with patch("pdd.commands.checkup.run_cloud_checkup", return_value=fake_result):
            result = runner.invoke(
                checkup,
                ["--pr", PR_URL, "--cloud-job"],
                catch_exceptions=False,
                obj={"quiet": False, "verbose": False, "local": False},
            )
        assert result.exit_code == 0
        assert "Billing" in result.output

    def test_provider_meta_emitted(self):
        """Provider-limit metadata must appear even in quiet mode."""
        runner = self._runner()
        fake_result = CloudCheckupResult(
            success=True,
            message="ok",
            cost_usd=0.10,
            model="cloud-codex",
            exit_code=0,
            output_lines=[],
            report=None,
            billing_source="pdd-cloud",
            job_id=FAKE_JOB_ID,
            provider_meta={"rateLimitInfo": {"remaining": 3}},
        )
        with patch("pdd.commands.checkup.run_cloud_checkup", return_value=fake_result):
            result = runner.invoke(
                checkup,
                ["--pr", PR_URL, "--cloud-job"],
                catch_exceptions=False,
                obj={"quiet": True, "verbose": False, "local": False},
            )
        assert result.exit_code == 0
        # provider-meta goes to stderr; combine output for inspection
        combined = (result.output or "")
        # CliRunner mixes stdout/stderr by default; check it appears somewhere
        # In quiet mode the billing/status lines are suppressed, but meta must not be
        assert "rateLimitInfo" in combined

    def test_fresh_start_forwarded_to_cloud(self):
        runner = self._runner()
        fake_result = CloudCheckupResult(
            success=True,
            message="ok",
            cost_usd=0.10,
            model="cloud-codex",
            exit_code=0,
            output_lines=[],
            report=None,
            billing_source="pdd-cloud",
            job_id=FAKE_JOB_ID,
        )
        with patch(
            "pdd.commands.checkup.run_cloud_checkup", return_value=fake_result
        ) as mock_cloud:
            runner.invoke(
                checkup,
                ["--pr", PR_URL, "--cloud-job", "--fresh-start"],
                catch_exceptions=False,
                obj={"quiet": False, "verbose": False, "local": False},
            )
        _, kwargs = mock_cloud.call_args
        assert kwargs.get("fresh_start") is True

    def test_without_cloud_job_uses_local_path(self):
        """Without --cloud-job the local executor is invoked."""
        runner = self._runner()
        with patch(
            "pdd.commands.checkup.run_cloud_checkup"
        ) as mock_cloud:
            with patch(
                "pdd.commands.checkup.run_agentic_checkup",
                return_value=(True, "local ok", 0.5, "claude"),
            ) as mock_local:
                runner.invoke(
                    checkup,
                    ["--pr", PR_URL],
                    catch_exceptions=False,
                    obj={"quiet": False, "verbose": False, "local": False,
                         "time": None, "time_explicit": False},
                )
        mock_local.assert_called_once()
        mock_cloud.assert_not_called()
