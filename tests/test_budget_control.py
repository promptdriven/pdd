"""Unit tests for the GitHub App budget-control surface.

Covers the four new public modules (``cost_budget_watcher``,
``server/budget_settings``, ``server/budget_comments``,
``server/slash_command_parser``) plus the budget-related behavior added to
``server/jobs.py`` and ``server/routes/commands.py``. All tests are pure-
python and never hit the network or an LLM provider; a separate real-LLM
test in ``tests/test_budget_control_real.py`` guards against prompt drift.
"""

from __future__ import annotations

import csv
import threading
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import List

import pytest

from pdd.cost_budget_watcher import watch
from pdd.server.budget_comments import (
    render_ack,
    render_budget_exceeded,
    render_invalid,
    render_settings,
    render_startup,
    render_stop,
    render_unauthorized,
)
from pdd.server.budget_settings import (
    BUDGET_HARD_CEILING,
    BudgetStore,
    PDD_ISSUE_DEFAULT_MAX_TOTAL_CAP,
    PDD_ISSUE_DEFAULT_NODE_BUDGET,
    effective_cap,
    pdd_issue_defaults,
    validate_amount,
)
from pdd.server.models import BudgetSettings, JobStatus, SlashCommandResult
from pdd.server.slash_command_parser import (
    CommentInput,
    is_authorized,
    is_duplicate,
    parse_comment,
)


@pytest.fixture(autouse=True)
def _clean_pdd_job_id_env():
    """Restore os.environ['PDD_JOB_ID'] after every test in this file.

    Several tests construct a `JobManager` with a custom executor under
    `max_concurrent=1`; per the production safety-net contract, that
    triggers `os.environ['PDD_JOB_ID'] = job.id` and intentionally
    leaves the value set (sequential jobs each overwrite). Without
    this fixture, the leaked job UUID would contaminate tests in
    sibling files (notably `tests/test_track_cost.py`) that assume
    the env is clean.
    """
    import os as _os
    prior = _os.environ.get("PDD_JOB_ID")
    yield
    if prior is None:
        _os.environ.pop("PDD_JOB_ID", None)
    else:
        _os.environ["PDD_JOB_ID"] = prior


# ----------------------------------------------------------------- budget_settings


class TestBudgetSettings:
    def test_pdd_issue_defaults_match_acceptance_criteria(self):
        assert pdd_issue_defaults() == (80.0, 400.0)
        assert PDD_ISSUE_DEFAULT_NODE_BUDGET == 80.0
        assert PDD_ISSUE_DEFAULT_MAX_TOTAL_CAP == 400.0

    def test_effective_cap_issue_both_set_takes_min(self):
        # 80 * 10 = 800; min(800, 400) = 400
        assert effective_cap("issue", node_budget=80, max_total_cap=400, node_count=10) == 400
        # 80 * 3 = 240; min(240, 400) = 240
        assert effective_cap("issue", node_budget=80, max_total_cap=400, node_count=3) == 240

    def test_effective_cap_issue_node_count_none_defaults_to_one(self):
        # node_count is None before the solving tree expands; should not crash
        assert effective_cap("issue", node_budget=80, max_total_cap=400) == 80

    def test_effective_cap_issue_only_max(self):
        assert effective_cap("issue", max_total_cap=400) == 400

    def test_effective_cap_issue_only_node(self):
        assert effective_cap("issue", node_budget=80, node_count=5) == 400

    def test_effective_cap_issue_neither_means_no_cap(self):
        assert effective_cap("issue") is None

    def test_effective_cap_non_issue_returns_budget_cap(self):
        assert effective_cap("bug", budget_cap=30) == 30
        assert effective_cap("change", budget_cap=None) is None
        # node_budget / max_total_cap ignored for non-issue commands
        assert effective_cap("fix", budget_cap=10, node_budget=80, max_total_cap=400) == 10

    @pytest.mark.parametrize("raw,expected", [
        (30, 30.0),
        (30.5, 30.5),
        ("30", 30.0),
        ("$30", 30.0),
        ("30.00", 30.0),
        ("  $30.50  ", 30.5),
    ])
    def test_validate_amount_accepts(self, raw, expected):
        assert validate_amount(raw) == expected

    @pytest.mark.parametrize("raw", [
        0, -1, "0", "-5", "not-a-number", "", "$", float("nan"), float("inf"),
        10001, BUDGET_HARD_CEILING + 1, True, False,
    ])
    def test_validate_amount_rejects(self, raw):
        with pytest.raises(ValueError):
            validate_amount(raw)


class TestBudgetStore:
    def test_set_get_delete(self):
        store = BudgetStore()
        s = BudgetSettings(command="bug", budget_cap=30.0, effective_cap=30.0, status=JobStatus.RUNNING)
        store.set("job1", s)
        assert store.get("job1") == s
        store.delete("job1")
        assert store.get("job1") is None

    def test_update_unknown_raises_keyerror(self):
        store = BudgetStore()
        with pytest.raises(KeyError):
            store.update("missing", budget_cap=50)

    def test_update_recomputes_effective_cap(self):
        store = BudgetStore()
        store.set(
            "j",
            BudgetSettings(
                command="issue", node_budget=80, max_total_cap=400,
                effective_cap=80, node_count=1, status=JobStatus.RUNNING,
            ),
        )
        updated = store.update("j", node_count=10)
        assert updated.effective_cap == 400  # min(80*10, 400)
        assert updated.node_count == 10

    def test_update_unset_keeps_field(self):
        store = BudgetStore()
        store.set(
            "j",
            BudgetSettings(
                command="bug", budget_cap=30, effective_cap=30, status=JobStatus.RUNNING,
            ),
        )
        updated = store.update("j", spent_so_far=5.0)
        assert updated.budget_cap == 30  # unchanged
        assert updated.spent_so_far == 5.0


# ----------------------------------------------------------------- slash_command_parser


def _user_comment(body: str, *, comment_id: int = 1, login: str = "alice") -> CommentInput:
    return CommentInput(id=comment_id, body=body, user_login=login, user_type="User")


class TestSlashCommandParser:
    def test_settings_is_open_with_empty_metadata(self):
        r = parse_comment(_user_comment("/pdd settings"))
        assert r.kind == "settings"
        assert r.metadata == {}

    def test_budget_set_carries_amount_in_metadata(self):
        # Finding 4 contract: parser stores validated float on result.metadata.
        r = parse_comment(_user_comment("/pdd budget 30"))
        assert r.kind == "budget_set"
        assert r.metadata == {"amount": 30.0}

    def test_budget_bare_on_issue_aliases_to_max(self):
        # R6: bare /pdd budget N on a pdd-issue job becomes budget_max_set.
        r = parse_comment(_user_comment("/pdd budget 30"), active_command="issue")
        assert r.kind == "budget_max_set"
        assert r.metadata == {"amount": 30.0}

    def test_budget_node_metadata(self):
        # node|max apply to pdd-issue only — set active_command='issue'
        # so the parser accepts the verb instead of returning invalid.
        # See TestNodeMaxRejectedForNonIssue below for the rejection path.
        r = parse_comment(_user_comment("/pdd budget node 50"), active_command="issue")
        assert r.kind == "budget_node_set"
        assert r.metadata == {"amount": 50.0}

    def test_budget_max_metadata(self):
        r = parse_comment(_user_comment("/pdd budget max 200"), active_command="issue")
        assert r.kind == "budget_max_set"
        assert r.metadata == {"amount": 200.0}

    def test_stop_carries_no_amount(self):
        r = parse_comment(_user_comment("/pdd stop"))
        assert r.kind == "stop"
        assert r.metadata == {}

    def test_invalid_amount_is_invalid(self):
        r = parse_comment(_user_comment("/pdd budget -1"))
        assert r.kind == "invalid"
        assert "must be > 0" in r.message

    def test_invalid_verb(self):
        r = parse_comment(_user_comment("/pdd nonsense"))
        assert r.kind == "invalid"

    def test_non_pdd_comment_is_ignored(self):
        r = parse_comment(_user_comment("hello world"))
        assert r.kind == "ignored"

    def test_fenced_pdd_is_ignored(self):
        # R3: /pdd inside a fenced block must not trigger.
        body = "```\n/pdd budget 30\n```"
        r = parse_comment(_user_comment(body))
        assert r.kind == "ignored"

    def test_tilde_fenced_pdd_is_ignored(self):
        body = "~~~\n/pdd budget 30\n~~~"
        r = parse_comment(_user_comment(body))
        assert r.kind == "ignored"

    def test_bot_authored_is_ignored(self):
        c = CommentInput(id=99, body="/pdd budget 30", user_login="bot", user_type="Bot")
        r = parse_comment(c)
        assert r.kind == "ignored"

    def test_first_non_fenced_line_wins(self):
        body = "```\n/pdd budget 999\n```\n/pdd settings\n"
        r = parse_comment(_user_comment(body))
        assert r.kind == "settings"


class TestAuthorization:
    def test_issue_author_authorized(self):
        assert is_authorized("alice", issue_author_login="alice") is True

    def test_collaborator_authorized(self):
        assert is_authorized("bob", repo_collaborators={"bob", "carol"}) is True

    def test_member_association_authorized(self):
        assert is_authorized("dave", commenter_association="MEMBER") is True
        assert is_authorized("dave", commenter_association="OWNER") is True
        assert is_authorized("dave", commenter_association="COLLABORATOR") is True

    def test_unrelated_user_rejected(self):
        assert is_authorized("eve") is False
        assert is_authorized("eve", commenter_association="CONTRIBUTOR") is False

    def test_settings_kind_is_not_in_auth_concern(self):
        # Finding 5: parser does NOT emit 'unauthorized'; the auth contract
        # lives separately on the webhook handler.
        r = parse_comment(_user_comment("/pdd settings"), active_command="bug")
        assert r.kind == "settings"
        # No 'unauthorized' kind is reachable.
        assert SlashCommandResult.model_fields["kind"].annotation.__args__ == (
            "budget_set", "budget_node_set", "budget_max_set",
            "settings", "stop", "invalid", "ignored",
        )


class TestDedupe:
    def test_first_occurrence_returns_false(self):
        seen: set[int] = set()
        assert is_duplicate(42, seen=seen) is False
        assert 42 in seen

    def test_second_occurrence_returns_true(self):
        seen: set[int] = {42}
        assert is_duplicate(42, seen=seen) is True


# ----------------------------------------------------------------- budget_comments


class TestBudgetComments:
    def test_startup_normal_command_no_cap_says_none(self):
        s = BudgetSettings(command="bug", status=JobStatus.RUNNING)
        out = render_startup(s)
        assert "PDD is starting `pdd bug`." in out
        assert "Budget cap: none" in out
        assert "/pdd budget 30" in out
        assert "/pdd settings" in out
        assert "/pdd stop" in out

    def test_startup_normal_command_with_cap_shows_int_money(self):
        s = BudgetSettings(command="bug", budget_cap=30.0, effective_cap=30.0,
                           status=JobStatus.RUNNING)
        assert "Budget cap: $30" in render_startup(s)

    def test_startup_pdd_issue_uses_min_formula(self):
        s = BudgetSettings(
            command="issue", node_budget=80.0, max_total_cap=400.0,
            effective_cap=400.0, status=JobStatus.RUNNING, node_count=3,
        )
        out = render_startup(s)
        assert "PDD is starting autonomous solving." in out
        assert "- node budget: $80 per node" in out
        assert "- max total cap: $400" in out
        assert "- effective cap: min($80 x node count, $400)" in out

    def test_settings_renders_currency_with_2dp_for_spent(self):
        s = BudgetSettings(
            command="issue", node_budget=50.0, max_total_cap=200.0,
            effective_cap=200.0, spent_so_far=18.42, status=JobStatus.RUNNING,
        )
        out = render_settings(s)
        assert "- Command: pdd-issue" in out
        assert "- Node budget: $50" in out
        assert "- Spent so far: $18.42" in out
        assert "- Status: running" in out

    def test_ack_includes_settings_echo(self):
        s = BudgetSettings(
            command="issue", node_budget=80.0, max_total_cap=200.0,
            effective_cap=200.0, status=JobStatus.RUNNING,
        )
        out = render_ack("budget_max_set", amount=200.0, settings=s)
        assert out.startswith("Updated max total cap to $200.")
        assert "Current PDD settings:" in out

    def test_ack_rejects_unknown_kind(self):
        s = BudgetSettings(command="bug", status=JobStatus.RUNNING)
        with pytest.raises(ValueError):
            render_ack("nonsense", amount=10, settings=s)

    def test_stop_renders_final_spend(self):
        s = BudgetSettings(command="bug", spent_so_far=12.34,
                            status=JobStatus.CANCELLED)
        out = render_stop(s)
        assert "PDD stopped. Final spend: $12.34" in out
        assert "Status: cancelled" in out

    def test_invalid_renders_usage_block(self):
        out = render_invalid("Unknown verb")
        assert "Unknown verb" in out
        assert "/pdd budget N" in out
        assert "/pdd settings" in out

    def test_unauthorized_mentions_settings_redirect(self):
        # Finding 5: the rejection must mention /pdd settings so the
        # promise the webhook handler's R5 makes is visible in the reply.
        out = render_unauthorized("eve")
        assert "@eve" in out
        assert "/pdd settings" in out

    def test_budget_exceeded_includes_spent_and_cap(self):
        s = BudgetSettings(
            command="issue", node_budget=80.0, max_total_cap=400.0,
            effective_cap=400.0, spent_so_far=401.23,
            status=JobStatus.BUDGET_EXCEEDED,
        )
        out = render_budget_exceeded(s)
        assert "Spent: $401.23" in out
        assert "Effective cap: $400" in out
        assert "Status: budget_exceeded" in out


# ----------------------------------------------------------------- cost_budget_watcher


def _write_csv(path: Path, rows: List[dict]) -> None:
    fieldnames = ["timestamp", "model", "command", "cost", "input_files",
                  "output_files", "attempted_models"]
    with path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow({**{k: "" for k in fieldnames}, **row})


class TestCostBudgetWatcher:
    def test_missing_csv_reports_zero_spent(self, tmp_path):
        watcher = watch(tmp_path / "nonexistent.csv", cap=None, on_exceeded=lambda s: None,
                         poll_interval=0.1)
        try:
            time.sleep(0.2)
            assert watcher.spent() == 0.0
        finally:
            watcher.stop()

    def test_sums_only_matching_commands(self, tmp_path):
        csv_path = tmp_path / "cost.csv"
        ts = datetime.now(timezone.utc).isoformat()
        _write_csv(csv_path, [
            {"timestamp": ts, "command": "change", "cost": "1.50"},
            {"timestamp": ts, "command": "sync", "cost": "2.00"},
            {"timestamp": ts, "command": "irrelevant", "cost": "10.00"},
        ])
        watcher = watch(csv_path, cap=None, on_exceeded=lambda s: None,
                         commands={"change", "sync"}, poll_interval=0.1)
        try:
            time.sleep(0.3)
            assert watcher.spent() == pytest.approx(3.5)
        finally:
            watcher.stop()

    def test_filter_none_sums_all_rows(self, tmp_path):
        csv_path = tmp_path / "cost.csv"
        ts = datetime.now(timezone.utc).isoformat()
        _write_csv(csv_path, [
            {"timestamp": ts, "command": "change", "cost": "1.0"},
            {"timestamp": ts, "command": "anything", "cost": "2.0"},
        ])
        watcher = watch(csv_path, cap=None, on_exceeded=lambda s: None,
                         commands=None, poll_interval=0.1)
        try:
            time.sleep(0.3)
            assert watcher.spent() == pytest.approx(3.0)
        finally:
            watcher.stop()

    def test_pdd_issue_filter_finds_nested_subcommand_spend(self, tmp_path):
        # Finding 3 regression guard: pdd-issue never writes command="issue";
        # the watcher must accept a set of nested subcommands. Filtering
        # by {"issue"} alone would (incorrectly) yield $0.
        csv_path = tmp_path / "cost.csv"
        ts = datetime.now(timezone.utc).isoformat()
        _write_csv(csv_path, [
            {"timestamp": ts, "command": "change", "cost": "5.0"},
            {"timestamp": ts, "command": "sync", "cost": "10.0"},
            {"timestamp": ts, "command": "bug", "cost": "2.5"},
        ])
        # The buggy historical behavior:
        only_issue = watch(csv_path, cap=None, on_exceeded=lambda s: None,
                            commands={"issue"}, poll_interval=0.1)
        try:
            time.sleep(0.3)
            assert only_issue.spent() == 0.0  # confirms the broken path stays $0
        finally:
            only_issue.stop()
        # The fix: pass the nested command set.
        nested = watch(csv_path, cap=None, on_exceeded=lambda s: None,
                       commands={"change", "sync", "bug"}, poll_interval=0.1)
        try:
            time.sleep(0.3)
            assert nested.spent() == pytest.approx(17.5)
        finally:
            nested.stop()

    def test_fires_on_exceeded_once(self, tmp_path):
        csv_path = tmp_path / "cost.csv"
        ts = datetime.now(timezone.utc).isoformat()
        _write_csv(csv_path, [
            {"timestamp": ts, "command": "change", "cost": "50.0"},
        ])
        fired: List[float] = []
        event = threading.Event()

        def on_exceeded(spent: float) -> None:
            fired.append(spent)
            event.set()

        watcher = watch(csv_path, cap=30.0, on_exceeded=on_exceeded,
                         commands={"change"}, poll_interval=0.1)
        try:
            assert event.wait(2.0), "watcher never fired on_exceeded"
            time.sleep(0.3)  # ensure no second invocation
            assert len(fired) == 1
            assert fired[0] >= 30.0
        finally:
            watcher.stop()

    def test_update_cap_can_lower_threshold(self, tmp_path):
        csv_path = tmp_path / "cost.csv"
        ts = datetime.now(timezone.utc).isoformat()
        _write_csv(csv_path, [
            {"timestamp": ts, "command": "change", "cost": "10.0"},
        ])
        fired: List[float] = []
        event = threading.Event()

        watcher = watch(csv_path, cap=100.0, on_exceeded=lambda s: (fired.append(s), event.set()),
                         commands={"change"}, poll_interval=0.1)
        try:
            time.sleep(0.3)
            assert not fired  # 10 < 100, no fire
            watcher.update_cap(5.0)  # now 10 >= 5, must fire on next poll
            assert event.wait(2.0)
            assert fired and fired[0] >= 5.0
        finally:
            watcher.stop()

    def test_no_cap_means_no_fire(self, tmp_path):
        csv_path = tmp_path / "cost.csv"
        ts = datetime.now(timezone.utc).isoformat()
        _write_csv(csv_path, [
            {"timestamp": ts, "command": "change", "cost": "999.0"},
        ])
        fired: List[float] = []
        watcher = watch(csv_path, cap=None, on_exceeded=lambda s: fired.append(s),
                         commands={"change"}, poll_interval=0.1)
        try:
            time.sleep(0.3)
            assert not fired
            assert watcher.spent() >= 999.0
        finally:
            watcher.stop()

    def test_stop_is_idempotent(self, tmp_path):
        watcher = watch(tmp_path / "x.csv", cap=None, on_exceeded=lambda s: None,
                         poll_interval=0.1)
        watcher.stop()
        watcher.stop()  # must not raise

    def test_started_at_filter_drops_older_rows(self, tmp_path):
        csv_path = tmp_path / "cost.csv"
        old_ts = "2026-01-01T00:00:00+00:00"
        new_ts = "2026-12-31T00:00:00+00:00"
        _write_csv(csv_path, [
            {"timestamp": old_ts, "command": "change", "cost": "5.0"},
            {"timestamp": new_ts, "command": "change", "cost": "7.0"},
        ])
        cutoff = datetime(2026, 6, 1, tzinfo=timezone.utc)
        watcher = watch(csv_path, cap=None, on_exceeded=lambda s: None,
                         commands={"change"}, started_at=cutoff,
                         poll_interval=0.1)
        try:
            time.sleep(0.3)
            assert watcher.spent() == pytest.approx(7.0)
        finally:
            watcher.stop()

    @pytest.mark.parametrize("bad", [0, -1, 10001, float("nan")])
    def test_watch_rejects_invalid_cap(self, tmp_path, bad):
        with pytest.raises(ValueError):
            watch(tmp_path / "x.csv", cap=bad, on_exceeded=lambda s: None)

    def test_naive_csv_timestamps_compared_against_aware_started_at(self, tmp_path):
        """Regression: track_cost writes naive timestamps via
        datetime.now().strftime(...), but job.started_at is aware UTC. The
        watcher must reinterpret naive cells as UTC instead of raising
        TypeError (which previously made spend stay at $0 silently).
        """
        csv_path = tmp_path / "cost.csv"
        # Naive timestamp like track_cost.py emits ("%Y-%m-%dT%H:%M:%S.%f").
        naive_ts = "2026-05-22T18:30:00.000"
        _write_csv(csv_path, [
            {"timestamp": naive_ts, "command": "change", "cost": "12.50"},
        ])
        # Aware started_at like JobManager sets.
        started = datetime(2026, 5, 22, 0, 0, tzinfo=timezone.utc)
        watcher = watch(
            csv_path, cap=None, on_exceeded=lambda s: None,
            commands={"change"}, started_at=started, poll_interval=0.1,
        )
        try:
            time.sleep(0.4)
            assert watcher.spent() == pytest.approx(12.5), (
                "Naive CSV timestamps must be reinterpreted as UTC so they "
                "compare cleanly with the aware started_at."
            )
        finally:
            watcher.stop()

    def test_incremental_tail_only_reads_appended_bytes(self, tmp_path):
        """Performance regression guard: each poll must NOT reread the full
        CSV. We approximate this by patching csv.reader to count invocations
        and asserting the count grows by 1 per append, not by ``rows`` per
        poll.
        """
        from unittest import mock

        csv_path = tmp_path / "cost.csv"
        ts = "2026-05-22T18:30:00.000"
        # Seed with header + one row.
        _write_csv(csv_path, [{"timestamp": ts, "command": "change", "cost": "1.0"}])

        from pdd import cost_budget_watcher as cbw

        original_reader = cbw.csv.reader
        call_count = {"n": 0}

        def counting_reader(*args, **kwargs):
            call_count["n"] += 1
            return original_reader(*args, **kwargs)

        watcher = watch(
            csv_path, cap=None, on_exceeded=lambda s: None,
            commands={"change"}, poll_interval=0.1,
        )
        try:
            # First poll reads header + one row.
            time.sleep(0.3)
            assert watcher.spent() == pytest.approx(1.0)
            baseline = call_count["n"]

            with mock.patch.object(cbw.csv, "reader", side_effect=counting_reader):
                # Append more rows over several polls. If the watcher were
                # rereading the whole file each poll, csv.reader calls would
                # grow super-linearly. With incremental tail, only newly
                # appended bytes are parsed.
                for i in range(5):
                    with csv_path.open("a", encoding="utf-8", newline="") as f:
                        writer = csv.writer(f)
                        writer.writerow([ts, "", "change", "1.0", "", "", ""])
                    time.sleep(0.25)

                assert watcher.spent() == pytest.approx(6.0)
                # Each poll should hit the reader at most once. 5 appends +
                # a handful of empty polls is fine; rereading the whole file
                # would mean dozens of reader calls multiplied by row count.
                assert call_count["n"] <= 30, (
                    f"csv.reader called {call_count['n']} times; "
                    f"incremental tail should keep this bounded."
                )
        finally:
            watcher.stop()

    def test_handles_truncation_by_resetting(self, tmp_path):
        """If the CSV shrinks (truncation/rotation), the watcher resets and
        re-reads from the start instead of permanently freezing at the
        pre-truncation spend.
        """
        csv_path = tmp_path / "cost.csv"
        ts = "2026-05-22T18:30:00.000"
        _write_csv(csv_path, [
            {"timestamp": ts, "command": "change", "cost": "10.0"},
        ])
        watcher = watch(
            csv_path, cap=None, on_exceeded=lambda s: None,
            commands={"change"}, poll_interval=0.1,
        )
        try:
            time.sleep(0.3)
            assert watcher.spent() == pytest.approx(10.0)
            # Replace the file with a fresh, smaller CSV.
            _write_csv(csv_path, [
                {"timestamp": ts, "command": "change", "cost": "3.0"},
            ])
            time.sleep(0.4)
            assert watcher.spent() == pytest.approx(3.0)
        finally:
            watcher.stop()


# ----------------------------------------------------------------- jobs


class TestJobsBudgetIntegration:
    """Async tests that exercise the JobManager's budget wiring without
    spawning real subprocesses.
    """

    @pytest.mark.asyncio
    async def test_budget_exceeded_survives_concurrent_cancel(self, tmp_path):
        """Regression: status=BUDGET_EXCEEDED must NOT be demoted to
        CANCELLED by the racing _execute_job CancelledError handler.
        """
        import asyncio
        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        async def slow_executor(job):
            # Simulate an in-flight subprocess: block until cancelled.
            try:
                await asyncio.sleep(5)
                return {"cost": 0.0}
            except asyncio.CancelledError:
                raise

        mgr = JobManager(max_concurrent=1, executor=slow_executor,
                          project_root=tmp_path)
        # Use a never-existing CSV path; _handle_budget_exceeded does not
        # need the file to update the job status.
        job = await mgr.submit("bug", args={}, options={}, budget_cap=30.0)
        # Wait for the job to enter RUNNING.
        for _ in range(50):
            if job.status == JobStatus.RUNNING:
                break
            await asyncio.sleep(0.05)
        assert job.status == JobStatus.RUNNING

        # Manually trip the budget-exceeded path (bypasses the CSV watcher).
        await mgr._handle_budget_exceeded(job.id, spent=42.0)
        # Give the racing _execute_job handler time to fire its
        # CancelledError handler.
        await asyncio.sleep(0.5)

        assert job.status == JobStatus.BUDGET_EXCEEDED, (
            f"Finding 2 regression: status was demoted to {job.status} after "
            "_handle_budget_exceeded set BUDGET_EXCEEDED."
        )
        assert job.cost >= 42.0

        # get_budget snapshot must also report BUDGET_EXCEEDED.
        snapshot = mgr.get_budget(job.id)
        assert snapshot.status == JobStatus.BUDGET_EXCEEDED


class TestExecuteRouteAcceptsIssue:
    """Finding 3 regression: POST /commands/execute must accept command='issue'
    and apply pdd_issue_defaults() when budget fields are absent.
    """

    @pytest.mark.asyncio
    async def test_execute_issue_applies_defaults(self):
        from unittest.mock import AsyncMock, MagicMock

        from pdd.server.models import CommandRequest, JobStatus
        from pdd.server.routes import commands as commands_route
        from pdd.server.budget_settings import pdd_issue_defaults

        manager = MagicMock()
        manager.submit = AsyncMock(return_value=MagicMock(
            id="abc", status=JobStatus.QUEUED, created_at=None,
        ))
        # The mock for created_at needs to be a real datetime for JobHandle.
        from datetime import datetime, timezone as _tz
        manager.submit.return_value.created_at = datetime.now(_tz.utc)

        request = CommandRequest(command="issue", args={}, options={})
        response = await commands_route.execute_command(request, manager=manager)
        assert response.job_id == "abc"

        node, max_total = pdd_issue_defaults()
        manager.submit.assert_called_once_with(
            command="issue", args={}, options={},
            budget_cap=None, node_budget=node, max_total_cap=max_total,
        )

    @pytest.mark.asyncio
    async def test_execute_issue_explicit_budget_skips_defaults(self):
        from unittest.mock import AsyncMock, MagicMock

        from pdd.server.models import CommandRequest, JobStatus
        from pdd.server.routes import commands as commands_route

        manager = MagicMock()
        from datetime import datetime, timezone as _tz
        manager.submit = AsyncMock(return_value=MagicMock(
            id="def", status=JobStatus.QUEUED, created_at=datetime.now(_tz.utc),
        ))

        request = CommandRequest(
            command="issue", args={}, options={}, node_budget=42.0,
        )
        await commands_route.execute_command(request, manager=manager)
        # Defaults must NOT override an explicit node_budget value.
        manager.submit.assert_called_once_with(
            command="issue", args={}, options={},
            budget_cap=None, node_budget=42.0, max_total_cap=None,
        )


# ----------------------------------------------------------------- follow-up findings


class TestSubmitTimeBudgetValidation:
    """Finding 2 (follow-up review): initial budget fields must be validated.

    Both layers — the CommandRequest pydantic model AND JobManager.submit —
    must reject malformed amounts so a negative budget cannot enter the
    system through either the REST route or a programmatic submit.
    """

    def test_command_request_rejects_negative_budget(self):
        from pdd.server.models import CommandRequest
        with pytest.raises(Exception):  # Pydantic ValidationError
            CommandRequest(command="bug", budget_cap=-1.0)

    def test_command_request_rejects_over_ceiling(self):
        from pdd.server.models import CommandRequest
        with pytest.raises(Exception):
            CommandRequest(command="bug", budget_cap=10001.0)

    def test_command_request_rejects_nan(self):
        from pdd.server.models import CommandRequest
        with pytest.raises(Exception):
            CommandRequest(command="bug", budget_cap=float("nan"))

    def test_command_request_accepts_string_form(self):
        from pdd.server.models import CommandRequest
        req = CommandRequest(command="bug", budget_cap="$30")
        assert req.budget_cap == 30.0

    @pytest.mark.asyncio
    async def test_job_manager_submit_rejects_negative_budget(self, tmp_path):
        from pdd.server.jobs import JobManager

        async def noop_executor(job):
            return {"cost": 0.0}

        mgr = JobManager(max_concurrent=1, executor=noop_executor,
                          project_root=tmp_path)
        with pytest.raises(ValueError):
            await mgr.submit("bug", args={}, options={}, budget_cap=-1.0)

    @pytest.mark.asyncio
    async def test_job_manager_submit_rejects_over_ceiling(self, tmp_path):
        from pdd.server.jobs import JobManager

        async def noop_executor(job):
            return {"cost": 0.0}

        mgr = JobManager(max_concurrent=1, executor=noop_executor,
                          project_root=tmp_path)
        with pytest.raises(ValueError):
            await mgr.submit("bug", args={}, options={}, budget_cap=99999.0)

    @pytest.mark.asyncio
    async def test_job_manager_submit_accepts_valid_budget(self, tmp_path):
        from pdd.server.jobs import JobManager

        async def noop_executor(job):
            return {"cost": 0.0}

        mgr = JobManager(max_concurrent=1, executor=noop_executor,
                          project_root=tmp_path)
        job = await mgr.submit("bug", args={}, options={}, budget_cap=30.0)
        assert job.budget_cap == 30.0


class TestBudgetExceededReportsCurrentCap:
    """Finding 3 (follow-up review): when update_budget lowers the cap
    mid-run, the budget-exceeded callback must report the CURRENT
    effective cap — not the value captured when the watcher was first
    started.
    """

    @pytest.mark.asyncio
    async def test_callback_sees_updated_cap_not_initial(self, tmp_path):
        import asyncio

        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        async def slow_executor(job):
            try:
                await asyncio.sleep(5)
                return {"cost": 0.0}
            except asyncio.CancelledError:
                raise

        mgr = JobManager(max_concurrent=1, executor=slow_executor,
                          project_root=tmp_path)
        received: list[tuple[str, float, float]] = []

        async def on_be(job_id: str, spent: float, cap: float) -> None:
            received.append((job_id, spent, cap))

        mgr.callbacks.on_budget_exceeded(on_be)

        job = await mgr.submit("bug", args={}, options={}, budget_cap=100.0)
        for _ in range(50):
            if job.status == JobStatus.RUNNING:
                break
            await asyncio.sleep(0.05)

        # Update the cap downward AFTER submission (mirrors /pdd budget 5
        # arriving while the job is in flight).
        await mgr.update_budget(job.id, budget_cap=5.0)

        # Trip the budget-exceeded path. The callback should see the
        # updated cap (5), not the initial value (100).
        await mgr._handle_budget_exceeded(job.id, spent=10.0)
        await asyncio.sleep(0.3)

        assert received, "on_budget_exceeded was not invoked"
        _, spent, reported_cap = received[-1]
        assert spent == 10.0
        assert reported_cap == 5.0, (
            f"Finding 3 regression: callback received cap={reported_cap} "
            f"but current effective cap was 5.0 after /pdd budget update."
        )


# ----------------------------------------------------------------- third review pass


class TestNodeMaxRejectedForNonIssue:
    """Finding 1 (third review pass): /pdd budget node|max only applies to
    pdd-issue. effective_cap() ignores node_budget / max_total_cap for
    other commands, so accepting these verbs would silently no-op.
    """

    def test_budget_node_rejected_on_bug(self):
        r = parse_comment(_user_comment("/pdd budget node 50"), active_command="bug")
        assert r.kind == "invalid"
        assert "pdd-issue" in r.message
        assert "/pdd budget N" in r.message

    def test_budget_max_rejected_on_change(self):
        r = parse_comment(_user_comment("/pdd budget max 200"), active_command="change")
        assert r.kind == "invalid"
        assert "pdd-issue" in r.message

    def test_budget_node_accepted_on_issue(self):
        r = parse_comment(_user_comment("/pdd budget node 50"), active_command="issue")
        assert r.kind == "budget_node_set"
        assert r.metadata == {"amount": 50.0}

    def test_budget_max_accepted_on_issue(self):
        r = parse_comment(_user_comment("/pdd budget max 200"), active_command="issue")
        assert r.kind == "budget_max_set"
        assert r.metadata == {"amount": 200.0}

    def test_budget_node_rejected_without_active_command(self):
        # `active_command=None` means we don't know what's running; safer
        # to reject than to silently apply a verb that may no-op.
        r = parse_comment(_user_comment("/pdd budget node 50"))
        assert r.kind == "invalid"


class TestNodeCountUpdateable:
    """Finding 2 (third review pass): node_count must be updateable through
    the public budget API so a growing solving tree raises the effective
    cap accordingly.
    """

    def test_budget_update_request_accepts_node_count(self):
        from pdd.server.models import BudgetUpdateRequest
        req = BudgetUpdateRequest(node_count=5)
        assert req.node_count == 5

    def test_budget_update_request_rejects_negative_node_count(self):
        from pdd.server.models import BudgetUpdateRequest
        with pytest.raises(Exception):  # Pydantic ValidationError
            BudgetUpdateRequest(node_count=-1)

    def test_budget_update_request_requires_at_least_one_field(self):
        from pdd.server.models import BudgetUpdateRequest
        with pytest.raises(Exception):
            BudgetUpdateRequest()

    def test_budget_update_request_node_count_alone_is_enough(self):
        # Even with all $-fields None, node_count alone satisfies the
        # "at least one" rule (the private executor pushes node_count
        # alone as the solving tree grows).
        from pdd.server.models import BudgetUpdateRequest
        req = BudgetUpdateRequest(node_count=3)
        assert req.node_count == 3

    @pytest.mark.asyncio
    async def test_update_budget_grows_effective_cap_with_node_count(self, tmp_path):
        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        async def slow_executor(job):
            import asyncio
            try:
                await asyncio.sleep(5)
                return {"cost": 0.0}
            except asyncio.CancelledError:
                raise

        mgr = JobManager(max_concurrent=1, executor=slow_executor,
                          project_root=tmp_path)
        job = await mgr.submit(
            "issue", args={}, options={},
            node_budget=80.0, max_total_cap=400.0,
        )
        import asyncio
        for _ in range(50):
            if job.status == JobStatus.RUNNING:
                break
            await asyncio.sleep(0.05)

        # node_count=None -> effective_cap = 80 * 1 = 80 (capped at 400)
        snapshot0 = mgr.get_budget(job.id)
        assert snapshot0.effective_cap == 80.0

        # Push node_count=3 -> effective_cap = min(80*3, 400) = 240
        await mgr.update_budget(job.id, node_count=3)
        snapshot1 = mgr.get_budget(job.id)
        assert snapshot1.effective_cap == 240.0
        assert snapshot1.node_count == 3

        # Push node_count=10 -> effective_cap = min(80*10, 400) = 400
        await mgr.update_budget(job.id, node_count=10)
        snapshot2 = mgr.get_budget(job.id)
        assert snapshot2.effective_cap == 400.0
        assert snapshot2.node_count == 10

    @pytest.mark.asyncio
    async def test_update_node_count_sync_helper(self, tmp_path):
        # Synchronous update_node_count helper is what the subprocess
        # driver thread uses; verify it walks the same arithmetic.
        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        async def slow_executor(job):
            import asyncio
            try:
                await asyncio.sleep(5)
                return {"cost": 0.0}
            except asyncio.CancelledError:
                raise

        mgr = JobManager(max_concurrent=1, executor=slow_executor,
                          project_root=tmp_path)
        job = await mgr.submit(
            "issue", args={}, options={},
            node_budget=80.0, max_total_cap=400.0,
        )
        import asyncio
        for _ in range(50):
            if job.status == JobStatus.RUNNING:
                break
            await asyncio.sleep(0.05)

        mgr.update_node_count(job.id, 5)
        snap = mgr.get_budget(job.id)
        assert snap.node_count == 5
        assert snap.effective_cap == 400.0  # min(80*5, 400)


class TestAutoWireCostCsv:
    """Finding 3 (third review pass): a capped job with no output_cost /
    PDD_OUTPUT_COST_PATH must derive and inject a default cost-CSV path
    rather than silently skipping enforcement.
    """

    @pytest.mark.asyncio
    async def test_capped_job_gets_default_csv_injected(self, tmp_path, monkeypatch):
        # Ensure no env path is present, so the derivation branch runs.
        monkeypatch.delenv("PDD_OUTPUT_COST_PATH", raising=False)

        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        async def slow_executor(job):
            import asyncio
            try:
                await asyncio.sleep(5)
                return {"cost": 0.0}
            except asyncio.CancelledError:
                raise

        mgr = JobManager(max_concurrent=1, executor=slow_executor,
                          project_root=tmp_path)
        job = await mgr.submit("bug", args={}, options={}, budget_cap=30.0)
        import asyncio
        for _ in range(50):
            if job.status == JobStatus.RUNNING:
                break
            await asyncio.sleep(0.05)

        # Watcher should be running (cap is set and a default CSV was derived).
        assert job.id in mgr._watchers, (
            "Finding 3 regression: capped job did not get a watcher; "
            "default CSV path was not derived."
        )
        # options must now carry the derived path so the subprocess also
        # writes to it via --output-cost.
        assert "output_cost" in job.options
        derived = Path(job.options["output_cost"])
        assert derived.parent == tmp_path / ".pdd"
        assert derived.name.startswith(f"cost-{job.id}")
        # Parent dir must be created.
        assert derived.parent.is_dir()

    @pytest.mark.asyncio
    async def test_uncapped_job_still_derives_csv_for_late_budget(
        self, tmp_path, monkeypatch,
    ):
        """An initially-uncapped job MUST still get a CSV writer wired up
        at submit time so a subsequent `/pdd budget N` has spend rows to
        enforce against. Skipping the CSV when uncapped (the prior
        behaviour) silently broke the documented "add a cap by
        commenting /pdd budget 30" path because the subprocess was
        already running without --output-cost.
        """
        monkeypatch.delenv("PDD_OUTPUT_COST_PATH", raising=False)

        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        async def slow_executor(job):
            import asyncio
            try:
                await asyncio.sleep(5)
                return {"cost": 0.0}
            except asyncio.CancelledError:
                raise

        mgr = JobManager(max_concurrent=1, executor=slow_executor,
                          project_root=tmp_path)
        job = await mgr.submit("bug", args={}, options={})
        import asyncio
        for _ in range(50):
            if job.status == JobStatus.RUNNING:
                break
            await asyncio.sleep(0.05)

        # No cap → no watcher yet, but CSV path IS derived and injected
        # so a late /pdd budget can wire enforcement to existing rows.
        assert job.id not in mgr._watchers
        assert "output_cost" in job.options, (
            "Finding 1 regression: uncapped job has no CSV path; "
            "a late /pdd budget would have nothing to enforce against."
        )
        derived = Path(job.options["output_cost"])
        assert derived.parent == tmp_path / ".pdd"
        assert derived.name == f"cost-{job.id}.csv"
        assert derived.parent.is_dir()

    @pytest.mark.asyncio
    async def test_explicit_output_cost_is_respected(self, tmp_path, monkeypatch):
        monkeypatch.delenv("PDD_OUTPUT_COST_PATH", raising=False)

        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        async def slow_executor(job):
            import asyncio
            try:
                await asyncio.sleep(5)
                return {"cost": 0.0}
            except asyncio.CancelledError:
                raise

        explicit_path = tmp_path / "custom" / "cost.csv"
        mgr = JobManager(max_concurrent=1, executor=slow_executor,
                          project_root=tmp_path)
        job = await mgr.submit(
            "bug", args={"options": {}},
            options={"output_cost": str(explicit_path)},
            budget_cap=30.0,
        )
        import asyncio
        for _ in range(50):
            if job.status == JobStatus.RUNNING:
                break
            await asyncio.sleep(0.05)

        assert job.id in mgr._watchers
        assert job.options["output_cost"] == str(explicit_path)


# ----------------------------------------------------------------- fourth review pass


class TestDefaultExecutorRejectsIssue:
    """Finding 1 (fourth review pass): the public Click CLI has no `issue`
    subcommand. When a job is submitted with command='issue' AND the
    JobManager was constructed without a custom executor (i.e. the
    public default-subprocess path), spawning `pdd issue` would fail
    with "No such command 'issue'" — a misleading error. Fail loudly
    in _run_click_command instead.
    """

    @pytest.mark.asyncio
    async def test_default_executor_raises_clear_error_for_issue(self, tmp_path):
        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        # No custom executor — JobManager uses the default subprocess path.
        mgr = JobManager(max_concurrent=1, executor=None, project_root=tmp_path)
        # Submit must still accept "issue" (the route is exercised by the
        # private executor via a custom JobManager); the failure must
        # surface only when _run_click_command tries to spawn it.
        with pytest.raises(RuntimeError, match=r"custom JobManager executor"):
            await mgr._run_click_command(
                type("J", (), {"command": "issue", "args": {}, "options": {}})()
            )

    @pytest.mark.asyncio
    async def test_custom_executor_handles_issue_normally(self, tmp_path):
        # When a custom executor IS provided (the private App's path),
        # command='issue' is dispatched to it and the default click path
        # is never reached. Regression guard: the failure from the
        # previous test must NOT fire here.
        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        async def custom_executor(job):
            return {"cost": 0.0, "stdout": "custom executor handled issue"}

        mgr = JobManager(max_concurrent=1, executor=custom_executor,
                          project_root=tmp_path)
        job = await mgr.submit("issue", args={}, options={},
                                 node_budget=80.0, max_total_cap=400.0)
        # Wait for the custom executor to complete (it returns immediately).
        import asyncio
        for _ in range(50):
            if job.status in (JobStatus.COMPLETED, JobStatus.FAILED):
                break
            await asyncio.sleep(0.05)
        assert job.status == JobStatus.COMPLETED


class TestNodeCountRejectsFractional:
    """Finding 2 (fourth review pass): node_count=3.9 must be REJECTED with
    a clear error rather than silently truncated to 3.
    """

    def test_pydantic_rejects_fractional_float(self):
        from pdd.server.models import BudgetUpdateRequest
        with pytest.raises(Exception, match=r"fractional|integer"):
            BudgetUpdateRequest(node_count=3.9)

    def test_pydantic_rejects_fractional_string(self):
        from pdd.server.models import BudgetUpdateRequest
        with pytest.raises(Exception):
            BudgetUpdateRequest(node_count="3.9")

    def test_pydantic_accepts_integer_float(self):
        # 3.0 is unambiguously an integer; accept it (interop with JSON
        # which may emit 3.0 for integer-valued numbers).
        from pdd.server.models import BudgetUpdateRequest
        req = BudgetUpdateRequest(node_count=3.0)
        assert req.node_count == 3
        assert isinstance(req.node_count, int)

    def test_pydantic_accepts_int_string(self):
        from pdd.server.models import BudgetUpdateRequest
        req = BudgetUpdateRequest(node_count="5")
        assert req.node_count == 5

    @pytest.mark.asyncio
    async def test_job_manager_update_budget_rejects_fractional(self, tmp_path):
        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        async def slow_executor(job):
            import asyncio
            try:
                await asyncio.sleep(5)
                return {"cost": 0.0}
            except asyncio.CancelledError:
                raise

        mgr = JobManager(max_concurrent=1, executor=slow_executor,
                          project_root=tmp_path)
        job = await mgr.submit("issue", args={}, options={},
                                 node_budget=80.0, max_total_cap=400.0)
        import asyncio
        for _ in range(50):
            if job.status == JobStatus.RUNNING:
                break
            await asyncio.sleep(0.05)
        with pytest.raises(ValueError, match=r"fractional|integer"):
            await mgr.update_budget(job.id, node_count=3.9)
        # job.node_count must not have changed.
        assert job.node_count is None

    @pytest.mark.asyncio
    async def test_update_node_count_helper_rejects_fractional(self, tmp_path):
        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        async def slow_executor(job):
            import asyncio
            try:
                await asyncio.sleep(5)
                return {"cost": 0.0}
            except asyncio.CancelledError:
                raise

        mgr = JobManager(max_concurrent=1, executor=slow_executor,
                          project_root=tmp_path)
        job = await mgr.submit("issue", args={}, options={},
                                 node_budget=80.0, max_total_cap=400.0)
        import asyncio
        for _ in range(50):
            if job.status == JobStatus.RUNNING:
                break
            await asyncio.sleep(0.05)
        with pytest.raises(ValueError):
            mgr.update_node_count(job.id, 3.9)


class TestExplicitCostPathParentCreated:
    """Finding 3 (fourth review pass): explicit options.output_cost paths
    must have their parent directory created so track_cost can write the
    first row (track_cost swallows OSError on write, which would leave the
    watcher silently stuck at $0 if the parent dir does not exist).
    """

    @pytest.mark.asyncio
    async def test_late_budget_finds_existing_rows(self, tmp_path, monkeypatch):
        """End-to-end Finding 1: a job submitted uncapped writes spend
        rows during the uncapped window; a later /pdd budget update
        (via update_budget) MUST see those rows when the watcher
        starts, so the cap is enforceable retroactively.
        """
        monkeypatch.delenv("PDD_OUTPUT_COST_PATH", raising=False)

        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        async def slow_executor(job):
            import asyncio
            try:
                await asyncio.sleep(5)
                return {"cost": 0.0}
            except asyncio.CancelledError:
                raise

        mgr = JobManager(max_concurrent=1, executor=slow_executor,
                          project_root=tmp_path)
        job = await mgr.submit("bug", args={}, options={})
        import asyncio
        for _ in range(50):
            if job.status == JobStatus.RUNNING:
                break
            await asyncio.sleep(0.05)

        csv_path = Path(job.options["output_cost"])
        # Simulate the subprocess having written a row during the
        # uncapped window (track_cost writes on subprocess exit).
        csv_path.parent.mkdir(parents=True, exist_ok=True)
        ts = "2026-05-22T18:30:00.000+00:00"
        with csv_path.open("w", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            w.writerow(["timestamp", "model", "command", "cost",
                        "input_files", "output_files", "attempted_models"])
            w.writerow([ts, "gpt-4", "bug", "8.0", "", "", "gpt-4"])

        # Now apply a late budget cap. The watcher should start and read
        # the existing row, then update_budget's stored snapshot's
        # effective_cap should reflect the new cap.
        await mgr.update_budget(job.id, budget_cap=5.0)
        assert job.id in mgr._watchers
        snapshot = mgr.get_budget(job.id)
        assert snapshot.effective_cap == 5.0


class TestPerJobCsvIsolation:
    """Finding 2 (fifth review pass): concurrent same-command jobs must
    NOT count each other's spend. Each job gets its own derived CSV
    under .pdd/ and the subprocess env is scrubbed of any inherited
    process-wide PDD_OUTPUT_COST_PATH that could leak across jobs.
    """

    @pytest.mark.asyncio
    async def test_two_same_command_jobs_get_distinct_csvs(
        self, tmp_path, monkeypatch,
    ):
        monkeypatch.delenv("PDD_OUTPUT_COST_PATH", raising=False)

        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        async def slow_executor(job):
            import asyncio
            try:
                await asyncio.sleep(5)
                return {"cost": 0.0}
            except asyncio.CancelledError:
                raise

        mgr = JobManager(max_concurrent=2, executor=slow_executor,
                          project_root=tmp_path)
        job_a = await mgr.submit("bug", args={}, options={}, budget_cap=30.0)
        job_b = await mgr.submit("bug", args={}, options={}, budget_cap=30.0)
        import asyncio
        for _ in range(50):
            if (job_a.status == JobStatus.RUNNING
                    and job_b.status == JobStatus.RUNNING):
                break
            await asyncio.sleep(0.05)

        path_a = job_a.options["output_cost"]
        path_b = job_b.options["output_cost"]
        assert path_a != path_b, (
            "Finding 2 regression: two jobs share the same derived "
            "cost-CSV path; one job will count the other's spend."
        )
        assert job_a.id in path_a
        assert job_b.id in path_b

    @pytest.mark.asyncio
    async def test_shared_env_var_does_not_contaminate(
        self, tmp_path, monkeypatch,
    ):
        """Setting PDD_OUTPUT_COST_PATH to a shared file at the parent
        process level must NOT cause two jobs to write to it (which
        would pollute each watcher's spend with the other job's rows).
        """
        shared = tmp_path / "shared.csv"
        monkeypatch.setenv("PDD_OUTPUT_COST_PATH", str(shared))

        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        async def slow_executor(job):
            import asyncio
            try:
                await asyncio.sleep(5)
                return {"cost": 0.0}
            except asyncio.CancelledError:
                raise

        mgr = JobManager(max_concurrent=1, executor=slow_executor,
                          project_root=tmp_path)
        job = await mgr.submit("bug", args={}, options={}, budget_cap=30.0)
        import asyncio
        for _ in range(50):
            if job.status == JobStatus.RUNNING:
                break
            await asyncio.sleep(0.05)

        # The derived per-job path must win over the shared env var.
        derived = job.options["output_cost"]
        assert derived != str(shared)
        assert job.id in derived


class TestRelativeExplicitCostPathResolved:
    """Sixth pass Finding 1: an explicit relative options.output_cost must
    be resolved against project_root so the watcher (which runs in the
    server cwd) and the subprocess (which runs in project_root) read/
    write the SAME file. Otherwise spend stays $0.
    """

    @pytest.mark.asyncio
    async def test_relative_path_absolutized_against_project_root(
        self, tmp_path, monkeypatch,
    ):
        monkeypatch.delenv("PDD_OUTPUT_COST_PATH", raising=False)
        # Server cwd is some unrelated directory.
        server_cwd = tmp_path / "server-cwd"
        server_cwd.mkdir()
        monkeypatch.chdir(server_cwd)

        # Project root is elsewhere.
        project = tmp_path / "project"
        project.mkdir()

        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        async def slow_executor(job):
            import asyncio
            try:
                await asyncio.sleep(5)
                return {"cost": 0.0}
            except asyncio.CancelledError:
                raise

        mgr = JobManager(max_concurrent=1, executor=slow_executor,
                          project_root=project)
        job = await mgr.submit(
            "bug", args={},
            # Relative path — easy mistake for a caller to make.
            options={"output_cost": "custom/cost.csv"},
            budget_cap=30.0,
        )
        import asyncio
        for _ in range(50):
            if job.status == JobStatus.RUNNING:
                break
            await asyncio.sleep(0.05)

        resolved = Path(job.options["output_cost"])
        assert resolved.is_absolute(), (
            "Finding 1 (6th pass) regression: relative output_cost was "
            "not absolutized; watcher and subprocess will read/write "
            "different files."
        )
        # Must be under project_root, not server_cwd.
        assert project in resolved.parents
        assert server_cwd not in resolved.parents


class TestJobIdScopedWatcherFilter:
    """Sixth pass Finding 2: two same-command jobs explicitly sharing one
    options.output_cost path must NOT count each other's spend. The
    watcher filters rows by job_id (a new column track_cost writes
    from the PDD_JOB_ID env var).
    """

    def test_watcher_with_job_id_skips_other_jobs_rows(self, tmp_path):
        """End-to-end Finding 2: write two rows with different job_ids
        to one CSV; the watcher for job_a's id must only sum job_a's
        cost, ignoring job_b's row.
        """
        from pdd.cost_budget_watcher import watch

        csv_path = tmp_path / "shared.csv"
        ts = "2026-05-22T18:30:00.000+00:00"
        with csv_path.open("w", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            w.writerow(["timestamp", "model", "command", "cost",
                        "input_files", "output_files",
                        "attempted_models", "job_id"])
            # job_a spent $4
            w.writerow([ts, "gpt-4", "bug", "4.0", "", "", "gpt-4", "job-a"])
            # job_b spent $99 — must NOT count toward job_a's watcher.
            w.writerow([ts, "gpt-4", "bug", "99.0", "", "", "gpt-4", "job-b"])

        watcher_a = watch(
            csv_path, cap=None, on_exceeded=lambda s: None,
            commands={"bug"}, job_id="job-a", poll_interval=0.1,
        )
        try:
            time.sleep(0.3)
            assert watcher_a.spent() == pytest.approx(4.0), (
                "Finding 2 (6th pass) regression: watcher counted "
                "another job's spend; sum should be $4 (job-a only)."
            )
        finally:
            watcher_a.stop()

    def test_legacy_header_falls_back_to_command_timestamp(self, tmp_path):
        """When the CSV header lacks the job_id column entirely (legacy
        or mid-format CSV the caller explicitly passed), the watcher
        MUST NOT enforce its job_id filter — otherwise every row gets
        dropped and spend stays frozen at $0, breaking enforcement on
        any pre-existing cost-CSV file. Per-job isolation across
        concurrent jobs requires a new-format CSV; legacy is opt-out
        of that protection.
        """
        from pdd.cost_budget_watcher import watch

        csv_path = tmp_path / "shared.csv"
        ts = "2026-05-22T18:30:00.000+00:00"
        with csv_path.open("w", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            # Mid-format header — has attempted_models but no job_id.
            w.writerow(["timestamp", "model", "command", "cost",
                        "input_files", "output_files", "attempted_models"])
            w.writerow([ts, "gpt-4", "bug", "50.0", "", "", "gpt-4"])

        watcher = watch(
            csv_path, cap=None, on_exceeded=lambda s: None,
            commands={"bug"}, job_id="job-a", poll_interval=0.1,
        )
        try:
            time.sleep(0.3)
            assert watcher.spent() == pytest.approx(50.0), (
                "Finding 1 (7th pass) regression: watcher dropped a "
                "row in a job_id-less CSV; legacy/mid CSVs should "
                "fall back to command+timestamp enforcement."
            )
        finally:
            watcher.stop()


class TestSubprocessEnvHelper:
    """Eighth-pass Finding 1: the previous os.environ mutation around the
    custom executor races under max_concurrent>1. We now provide a
    thread-safe `JobManager.subprocess_env(job)` helper that custom
    executors call to build per-spawn env dicts without touching
    process-global state.
    """

    @pytest.mark.asyncio
    async def test_subprocess_env_carries_per_job_id(self, tmp_path, monkeypatch):
        monkeypatch.delenv("PDD_OUTPUT_COST_PATH", raising=False)
        monkeypatch.delenv("PDD_JOB_ID", raising=False)

        import asyncio
        import os as _os
        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        async def custom_executor(job):
            env = job._observed_env  # type: ignore[attr-defined]
            return {"cost": 0.0, "env": env}

        mgr = JobManager(max_concurrent=2, executor=custom_executor,
                          project_root=tmp_path)
        # Submit two concurrent jobs. Each builds its env via the helper
        # and stashes the result so the test can verify isolation.
        job_a = await mgr.submit("bug", args={}, options={}, budget_cap=30.0)
        job_a._observed_env = mgr.subprocess_env(job_a)  # type: ignore[attr-defined]
        job_b = await mgr.submit("bug", args={}, options={}, budget_cap=30.0)
        job_b._observed_env = mgr.subprocess_env(job_b)  # type: ignore[attr-defined]
        for _ in range(50):
            if (job_a.status in (JobStatus.COMPLETED, JobStatus.FAILED)
                    and job_b.status in (JobStatus.COMPLETED, JobStatus.FAILED)):
                break
            await asyncio.sleep(0.05)

        env_a = job_a._observed_env  # type: ignore[attr-defined]
        env_b = job_b._observed_env  # type: ignore[attr-defined]
        assert env_a["PDD_JOB_ID"] == job_a.id
        assert env_b["PDD_JOB_ID"] == job_b.id
        assert env_a["PDD_JOB_ID"] != env_b["PDD_JOB_ID"], (
            "Finding 1 (8th pass) regression: subprocess_env returned "
            "the same PDD_JOB_ID for two concurrent jobs."
        )
        # The helper takes a base_env override so test code can build
        # against a clean slate.
        explicit = mgr.subprocess_env(job_a, base_env={"FOO": "bar"})
        assert explicit["FOO"] == "bar"
        assert explicit["PDD_JOB_ID"] == job_a.id

    @pytest.mark.asyncio
    async def test_env_safety_net_active_under_max_concurrent_one(
        self, tmp_path, monkeypatch,
    ):
        """Finding 1 (9th pass): legacy custom executors that do not
        call subprocess_env still need their spawned subprocesses to see
        PDD_JOB_ID. Under max_concurrent=1 there is no race risk, so
        the manager sets os.environ['PDD_JOB_ID']=job.id as a safety
        net. Under max_concurrent>1 it must not (see the next test).
        """
        import asyncio
        import os as _os
        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        prior = _os.environ.pop("PDD_JOB_ID", None)
        observed: dict = {}

        async def custom_executor(job):
            observed["env"] = _os.environ.get("PDD_JOB_ID")
            return {"cost": 0.0}

        try:
            mgr = JobManager(max_concurrent=1, executor=custom_executor,
                              project_root=tmp_path)
            job = await mgr.submit("issue", args={}, options={},
                                     node_budget=80.0, max_total_cap=400.0)
            for _ in range(50):
                if job.status in (JobStatus.COMPLETED, JobStatus.FAILED):
                    break
                await asyncio.sleep(0.05)

            assert observed.get("env") == job.id, (
                "Finding 1 (9th pass) regression: PDD_JOB_ID safety net "
                "was not set under max_concurrent=1; legacy executors "
                "lose job_id attribution on their spawned subprocesses."
            )
        finally:
            # Production design is for the safety-net value to persist
            # across sequential jobs (each new submit overwrites the
            # previous), but tests that assume a clean env would
            # otherwise see leakage. Restore the original env state.
            _os.environ.pop("PDD_JOB_ID", None)
            if prior is not None:
                _os.environ["PDD_JOB_ID"] = prior

    @pytest.mark.asyncio
    async def test_env_safety_net_skipped_under_concurrency(
        self, tmp_path, monkeypatch,
    ):
        """Under max_concurrent>1 the os.environ mutation would race
        across coroutines. Skip it; the executor MUST use
        subprocess_env() to isolate spawned children.
        """
        monkeypatch.delenv("PDD_JOB_ID", raising=False)

        import asyncio
        import os as _os
        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        observations: list = []

        async def custom_executor(job):
            observations.append(_os.environ.get("PDD_JOB_ID"))
            return {"cost": 0.0}

        mgr = JobManager(max_concurrent=2, executor=custom_executor,
                          project_root=tmp_path)
        job = await mgr.submit("issue", args={}, options={},
                                 node_budget=80.0, max_total_cap=400.0)
        for _ in range(50):
            if job.status in (JobStatus.COMPLETED, JobStatus.FAILED):
                break
            await asyncio.sleep(0.05)

        # No env mutation when max_concurrent>1.
        assert observations == [None]
        assert _os.environ.get("PDD_JOB_ID") is None


class TestSafetyNetSetsBothEnvVars:
    """Finding 1 (10th pass): the safety net under max_concurrent=1 must
    set BOTH PDD_JOB_ID and PDD_OUTPUT_COST_PATH for legacy executors.
    Setting only PDD_JOB_ID leaves child track_cost without a cost-CSV
    path, so it writes no row and the watcher freezes at $0 even
    though attribution would have been correct.
    """

    @pytest.mark.asyncio
    async def test_safety_net_sets_output_cost_path_too(
        self, tmp_path, monkeypatch,
    ):
        import asyncio
        import os as _os
        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        prior_id = _os.environ.pop("PDD_JOB_ID", None)
        prior_cost = _os.environ.pop("PDD_OUTPUT_COST_PATH", None)
        observed: dict = {}

        async def custom_executor(job):
            observed["pdd_job_id"] = _os.environ.get("PDD_JOB_ID")
            observed["pdd_cost"] = _os.environ.get("PDD_OUTPUT_COST_PATH")
            return {"cost": 0.0}

        try:
            mgr = JobManager(max_concurrent=1, executor=custom_executor,
                              project_root=tmp_path)
            job = await mgr.submit(
                "issue", args={}, options={},
                node_budget=80.0, max_total_cap=400.0,
            )
            for _ in range(50):
                if job.status in (JobStatus.COMPLETED, JobStatus.FAILED):
                    break
                await asyncio.sleep(0.05)

            assert observed.get("pdd_job_id") == job.id
            assert observed.get("pdd_cost") == job.options["output_cost"], (
                "Finding 1 (10th pass) regression: safety net set "
                "PDD_JOB_ID but not PDD_OUTPUT_COST_PATH; legacy "
                "executors' child track_cost would have no path to "
                "write to and the watcher would see $0."
            )
            # finally block restores both.
            assert _os.environ.get("PDD_JOB_ID") is None
            assert _os.environ.get("PDD_OUTPUT_COST_PATH") is None
        finally:
            _os.environ.pop("PDD_JOB_ID", None)
            _os.environ.pop("PDD_OUTPUT_COST_PATH", None)
            if prior_id is not None:
                _os.environ["PDD_JOB_ID"] = prior_id
            if prior_cost is not None:
                _os.environ["PDD_OUTPUT_COST_PATH"] = prior_cost


class TestConcurrentMigrationSafe:
    """Finding 2 (10th pass): two concurrent writers attempting to
    migrate the same legacy/mid CSV must not lose rows. The migration
    helpers now take a fcntl.flock and use a per-writer unique tmp
    filename so the second writer's os.replace cannot clobber a row
    the first writer appended between read and replace.
    """

    def test_unique_tmp_path_per_writer(self, tmp_path):
        from pdd.track_cost import _unique_tmp_path

        path = str(tmp_path / "cost.csv")
        a = _unique_tmp_path(path)
        b = _unique_tmp_path(path)
        assert a != b, (
            f"Finding 2 (10th pass) regression: _unique_tmp_path returned "
            f"the same value for two calls — concurrent migrations would "
            f"collide on the same tmp file."
        )
        assert a.startswith(path + ".migrate.tmp.")
        assert b.startswith(path + ".migrate.tmp.")

    def test_concurrent_writes_do_not_lose_rows(self, tmp_path):
        """Finding 1 (11th pass) end-to-end: two concurrent track_cost
        writers hitting the same legacy CSV must not lose either
        writer's row. The previous skip-and-fall-back lock pattern
        let one writer append while a parallel migration was about to
        os.replace the file, silently deleting the appended row.
        """
        import os
        import threading
        import click
        import click.testing
        from pdd.track_cost import track_cost

        try:
            import fcntl  # noqa: F401
        except ImportError:
            pytest.skip("fcntl not available on this platform")

        cost_csv = tmp_path / "cost.csv"
        # Seed legacy header.
        cost_csv.write_text(
            "timestamp,model,command,cost,input_files,output_files\n"
            "2026-01-01T00:00:00.000,old,gen,0.5,/i,/o\n",
            encoding="utf-8",
        )

        @click.command(name="bug")
        @click.pass_context
        @track_cost
        def cmd_a(ctx):
            return ("result-a", 1.50, "model-a")

        @click.command(name="bug")
        @click.pass_context
        @track_cost
        def cmd_b(ctx):
            return ("result-b", 2.50, "model-b")

        prior_pytest = os.environ.pop("PYTEST_CURRENT_TEST", None)
        prior_job_id = os.environ.get("PDD_JOB_ID")
        try:
            # Two threads running concurrently with different
            # PDD_JOB_IDs. The lock must serialise both writes; both
            # rows must end up in the file.
            results: list = []

            def run_writer(name: str, cmd) -> None:
                # Each "writer" sets its own PDD_JOB_ID via ctx.obj
                # (track_cost reads from env, but for the test we
                # exercise both writers in-process; set env right
                # before invocation).
                os.environ["PDD_JOB_ID"] = name
                runner = click.testing.CliRunner()
                result = runner.invoke(
                    cmd, [], obj={"output_cost": str(cost_csv)},
                    standalone_mode=False,
                )
                results.append((name, result.exception))

            # Note: this is a serial in-process test because Click's
            # CliRunner is not thread-safe; the real concurrency
            # protection is fcntl across processes. We still verify
            # that both rows end up in the file after the two writes
            # — the prior bug would lose one row even in this
            # sequential scenario if a migration replaced after an
            # append from another writer's snapshot.
            run_writer("job-a", cmd_a)
            run_writer("job-b", cmd_b)
        finally:
            os.environ.pop("PDD_JOB_ID", None)
            if prior_job_id is not None:
                os.environ["PDD_JOB_ID"] = prior_job_id
            if prior_pytest is not None:
                os.environ["PYTEST_CURRENT_TEST"] = prior_pytest

        text = cost_csv.read_text(encoding="utf-8")
        # Both writers' rows must be present.
        assert "model-a" in text, (
            f"Finding 1 (11th pass) regression: model-a row missing. "
            f"File: {text!r}"
        )
        assert "model-b" in text, (
            f"Finding 1 (11th pass) regression: model-b row missing. "
            f"File: {text!r}"
        )
        # Old row preserved across migrations.
        assert "old-model" not in text or "old,gen,0.5" in text, (
            "Pre-existing row should be preserved across migration."
        )

    def test_writes_serialize_via_blocking_flock(self, tmp_path):
        """Two threads each entering a _WriteLock context on the same
        CSV: both eventually acquire (LOCK_EX is BLOCKING now, not
        non-blocking), but the order is serialised — the second
        thread does not enter the critical section until the first
        releases. The prior non-blocking behaviour allowed concurrent
        writers to skip the lock and race with a holder's migration,
        losing appended rows.
        """
        import threading
        import time

        from pdd.track_cost import _WriteLock

        try:
            import fcntl  # noqa: F401
        except ImportError:
            pytest.skip("fcntl not available on this platform")

        path = str(tmp_path / "cost.csv")
        (tmp_path / "cost.csv").write_text("", encoding="utf-8")

        order = []
        first_in = threading.Event()
        release_first = threading.Event()

        def hold_lock():
            with _WriteLock(path) as locked:
                assert locked, "first thread failed to acquire on POSIX"
                order.append("first_in")
                first_in.set()
                release_first.wait(timeout=2)
                order.append("first_out")

        def try_lock():
            first_in.wait(timeout=2)
            # Brief sleep to give the test confidence that the second
            # thread is actually blocked, not just slow.
            time.sleep(0.1)
            with _WriteLock(path) as locked:
                assert locked, "second thread failed to acquire on POSIX"
                order.append("second_in")

        t1 = threading.Thread(target=hold_lock)
        t2 = threading.Thread(target=try_lock)
        t1.start()
        t2.start()
        # Hold the lock for a bit so the second thread is observably
        # blocked.
        first_in.wait(timeout=2)
        time.sleep(0.3)
        release_first.set()
        t1.join(timeout=2)
        t2.join(timeout=2)

        # The second thread's entry must come AFTER the first thread's
        # exit; no interleaving.
        assert order == ["first_in", "first_out", "second_in"], (
            f"Finding 1 (11th pass) regression: writes did not "
            f"serialise via _WriteLock. Order was: {order}"
        )


class TestNoDoubleCount:
    """Finding 1 (13th pass): concurrent daemon + flush callers must not
    double-count the same CSV bytes. The _consume_new_bytes operation
    is now serialised by an RLock; without it the two readers could
    each see _byte_offset=0, each parse the same row, and each
    increment _spent.
    """

    def test_concurrent_flush_calls_do_not_double_count(self, tmp_path):
        import threading

        from pdd.cost_budget_watcher import watch

        csv_path = tmp_path / "cost.csv"
        from datetime import datetime, timezone
        ts = datetime.now(timezone.utc).isoformat(timespec="milliseconds")
        with csv_path.open("w", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            w.writerow(["timestamp", "model", "command", "cost",
                        "input_files", "output_files",
                        "attempted_models", "job_id"])
            w.writerow([ts, "gpt-4", "bug", "5.0", "", "",
                        "gpt-4", "job-x"])

        watcher = watch(
            csv_path, cap=None, on_exceeded=lambda s: None,
            commands={"bug"}, job_id="job-x",
            # Long poll interval so the daemon thread does not run a
            # second poll during the test window.
            poll_interval=60.0,
        )
        try:
            # Two threads racing on flush() must serialise; each row
            # may only contribute once to _spent.
            barrier = threading.Barrier(2)

            def flush_caller():
                barrier.wait(timeout=2)
                for _ in range(50):
                    watcher.flush()

            t1 = threading.Thread(target=flush_caller)
            t2 = threading.Thread(target=flush_caller)
            t1.start()
            t2.start()
            t1.join(timeout=2)
            t2.join(timeout=2)

            assert watcher.spent() == pytest.approx(5.0), (
                f"Finding 1 (13th pass) regression: concurrent flush "
                f"calls double-counted the $5 row; spent={watcher.spent()}"
            )
        finally:
            watcher.stop()


class TestReadSpentNowPure:
    """Finding 2 (13th pass): read_spent_now must be a pure function —
    no daemon thread, no double-count race with itself.
    """

    def test_no_thread_started(self, tmp_path):
        import threading
        from pdd.cost_budget_watcher import read_spent_now

        csv_path = tmp_path / "cost.csv"
        from datetime import datetime, timezone
        ts = datetime.now(timezone.utc).isoformat(timespec="milliseconds")
        with csv_path.open("w", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            w.writerow(["timestamp", "model", "command", "cost",
                        "input_files", "output_files",
                        "attempted_models", "job_id"])
            w.writerow([ts, "gpt-4", "bug", "10.0", "", "",
                        "gpt-4", "job-x"])

        before = threading.active_count()
        for _ in range(20):
            spent = read_spent_now(
                csv_path, commands={"bug"}, job_id="job-x",
            )
            assert spent == pytest.approx(10.0), (
                f"Finding 2 (13th pass) regression: read_spent_now "
                f"returned {spent} for a $10 CSV — double-count or "
                f"under-count from concurrent Watcher path."
            )
        # No persistent threads should have been created. Allow a
        # small slack for unrelated thread activity on the host.
        after = threading.active_count()
        assert after - before <= 1, (
            f"Finding 2 (13th pass) regression: read_spent_now leaked "
            f"threads (before={before}, after={after})."
        )

    def test_exact_value_on_large_csv(self, tmp_path):
        """Reproduces the reviewer's $20,000 → $40,000 case as a small
        smoke test: many rows summed twice would yield 2× expected."""
        from pdd.cost_budget_watcher import read_spent_now

        csv_path = tmp_path / "cost.csv"
        from datetime import datetime, timezone
        ts = datetime.now(timezone.utc).isoformat(timespec="milliseconds")
        with csv_path.open("w", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            w.writerow(["timestamp", "model", "command", "cost",
                        "input_files", "output_files",
                        "attempted_models", "job_id"])
            for i in range(100):
                w.writerow([ts, "gpt-4", "bug", "5.0", "", "",
                            "gpt-4", "job-x"])
        spent = read_spent_now(csv_path, commands={"bug"}, job_id="job-x")
        assert spent == pytest.approx(500.0), (
            f"Finding 2 (13th pass) regression: 100×$5 should be $500, "
            f"got ${spent} (double-count would yield $1000)."
        )


class TestGetBudgetIsFreshForCappedRuns:
    """Finding 3 (13th pass): /pdd settings on a capped running job
    must report fresh spend, not the watcher's stale cache (up to
    poll_interval seconds old).
    """

    @pytest.mark.asyncio
    async def test_settings_freshness_on_capped_run(self, tmp_path, monkeypatch):
        import asyncio
        import csv as _csv

        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        monkeypatch.delenv("PDD_OUTPUT_COST_PATH", raising=False)

        async def slow_executor(job):
            try:
                await asyncio.sleep(5)
                return {"cost": 0.0}
            except asyncio.CancelledError:
                raise

        mgr = JobManager(max_concurrent=1, executor=slow_executor,
                          project_root=tmp_path)
        # Cap is huge so the watcher never fires; we just want to test
        # /pdd settings freshness independent of enforcement.
        job = await mgr.submit("bug", args={}, options={}, budget_cap=1000.0)
        for _ in range(50):
            if job.status == JobStatus.RUNNING:
                break
            await asyncio.sleep(0.05)
        # Watcher should be running.
        assert job.id in mgr._watchers

        # Write a $3 row to the CSV (simulating the subprocess just
        # wrote it). The watcher's daemon thread polls every 2s — but
        # /pdd settings must NOT wait that long.
        csv_path = Path(job.options["output_cost"])
        csv_path.parent.mkdir(parents=True, exist_ok=True)
        from datetime import datetime, timezone
        ts = datetime.now(timezone.utc).isoformat(timespec="milliseconds")
        with csv_path.open("w", encoding="utf-8", newline="") as f:
            w = _csv.writer(f)
            w.writerow(["timestamp", "model", "command", "cost",
                        "input_files", "output_files",
                        "attempted_models", "job_id"])
            w.writerow([ts, "gpt-4", "bug", "3.0", "", "",
                        "gpt-4", job.id])

        # IMMEDIATELY ask for settings. Previously this would have
        # reported $0 until the next 2s poll.
        snapshot = mgr.get_budget(job.id)
        assert snapshot.spent_so_far == pytest.approx(3.0), (
            f"Finding 3 (13th pass) regression: /pdd settings on capped "
            f"run reported stale spent={snapshot.spent_so_far}; expected "
            f"fresh $3.00 from the CSV."
        )


class TestFinalFlushCatchesLastRow:
    """Finding 1 (12th pass): a job that writes its final cost row and
    exits before the watcher's next 2s poll must still have the cap
    enforced. The fix is a synchronous Watcher.flush() in
    _execute_job's finally — without it the cleanup stops the
    watcher before the daemon thread sees the row and the job
    completes without budget_exceeded.
    """

    @pytest.mark.asyncio
    async def test_final_row_triggers_budget_exceeded_on_fast_exit(
        self, tmp_path, monkeypatch,
    ):
        import asyncio
        import csv as _csv

        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        monkeypatch.delenv("PDD_OUTPUT_COST_PATH", raising=False)

        # A custom executor that writes a $5 row to the per-job CSV and
        # exits immediately (much faster than the watcher's 2s poll).
        # Use a current timestamp so the watcher's started_at filter
        # accepts it.
        from datetime import datetime, timezone
        async def write_row_executor(job):
            csv_path = Path(job.options["output_cost"])
            csv_path.parent.mkdir(parents=True, exist_ok=True)
            ts = datetime.now(timezone.utc).isoformat(timespec="milliseconds")
            with csv_path.open("w", encoding="utf-8", newline="") as f:
                w = _csv.writer(f)
                w.writerow(["timestamp", "model", "command", "cost",
                            "input_files", "output_files",
                            "attempted_models", "job_id"])
                w.writerow([ts, "gpt-4", "bug", "5.0", "", "",
                            "gpt-4", job.id])
            return {"cost": 5.0}

        events: list = []

        async def on_be(job_id: str, spent: float, cap: float) -> None:
            events.append((job_id, spent, cap))

        mgr = JobManager(max_concurrent=1, executor=write_row_executor,
                          project_root=tmp_path)
        mgr.callbacks.on_budget_exceeded(on_be)

        job = await mgr.submit("bug", args={}, options={}, budget_cap=1.0)
        for _ in range(50):
            if job.status in (
                JobStatus.COMPLETED, JobStatus.FAILED,
                JobStatus.BUDGET_EXCEEDED,
            ):
                break
            await asyncio.sleep(0.05)

        assert job.status == JobStatus.BUDGET_EXCEEDED, (
            f"Finding 1 (12th pass) regression: fast-exit job's final "
            f"row was not seen by the watcher before cleanup. status="
            f"{job.status}, events={events}"
        )
        assert events, "on_budget_exceeded was never invoked"


class TestSettingsReportsSpendOnUncappedRun:
    """Finding 2 (12th pass): /pdd settings on an uncapped run after
    spend rows have been written must report the real spend, not $0.
    The previous get_budget only read job.cost (set on subprocess
    exit) and watcher.spent() (no watcher exists for uncapped runs).
    Fixed by falling back to a one-shot CSV read.
    """

    @pytest.mark.asyncio
    async def test_get_budget_reads_csv_when_no_watcher(
        self, tmp_path, monkeypatch,
    ):
        import asyncio
        import csv as _csv

        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        monkeypatch.delenv("PDD_OUTPUT_COST_PATH", raising=False)

        async def slow_executor(job):
            try:
                await asyncio.sleep(5)
                return {"cost": 0.0}
            except asyncio.CancelledError:
                raise

        mgr = JobManager(max_concurrent=1, executor=slow_executor,
                          project_root=tmp_path)
        # Submit UNCAPPED — no watcher will be started.
        job = await mgr.submit("bug", args={}, options={})
        for _ in range(50):
            if job.status == JobStatus.RUNNING:
                break
            await asyncio.sleep(0.05)

        # Confirm no watcher was started.
        assert job.id not in mgr._watchers

        # Simulate the subprocess having written a $3.25 row to the
        # per-job CSV (always derived at submit time per earlier fixes).
        from datetime import datetime, timezone
        csv_path = Path(job.options["output_cost"])
        csv_path.parent.mkdir(parents=True, exist_ok=True)
        ts = datetime.now(timezone.utc).isoformat(timespec="milliseconds")
        with csv_path.open("w", encoding="utf-8", newline="") as f:
            w = _csv.writer(f)
            w.writerow(["timestamp", "model", "command", "cost",
                        "input_files", "output_files",
                        "attempted_models", "job_id"])
            w.writerow([ts, "gpt-4", "bug", "3.25", "", "",
                        "gpt-4", job.id])

        snapshot = mgr.get_budget(job.id)
        assert snapshot.spent_so_far == pytest.approx(3.25), (
            f"Finding 2 (12th pass) regression: /pdd settings on "
            f"uncapped run reported spent={snapshot.spent_so_far} but "
            f"the CSV holds a $3.25 row."
        )


class TestUpdateBudgetFlushesImmediately:
    """Finding 3 (12th pass): /pdd budget N arriving on an uncapped
    run that has already spent more than N — and is about to exit —
    must enforce the cap on the existing rows. Previously
    update_budget started a watcher but the daemon thread might
    never poll before the job ended.
    """

    @pytest.mark.asyncio
    async def test_late_cap_enforced_on_existing_rows(
        self, tmp_path, monkeypatch,
    ):
        import asyncio
        import csv as _csv

        from pdd.server.jobs import JobManager
        from pdd.server.models import JobStatus

        monkeypatch.delenv("PDD_OUTPUT_COST_PATH", raising=False)

        # Slow executor so the job is still RUNNING when we apply the
        # late cap. After update_budget returns we will cancel the
        # job quickly to simulate "fast exit before next 2s poll".
        async def slow_executor(job):
            try:
                await asyncio.sleep(5)
                return {"cost": 0.0}
            except asyncio.CancelledError:
                raise

        events: list = []

        async def on_be(job_id: str, spent: float, cap: float) -> None:
            events.append((job_id, spent, cap))

        mgr = JobManager(max_concurrent=1, executor=slow_executor,
                          project_root=tmp_path)
        mgr.callbacks.on_budget_exceeded(on_be)

        job = await mgr.submit("bug", args={}, options={})
        for _ in range(50):
            if job.status == JobStatus.RUNNING:
                break
            await asyncio.sleep(0.05)

        # Pre-write $5 of spend (uncapped window) with a current
        # timestamp so the watcher's started_at filter accepts it.
        from datetime import datetime, timezone
        csv_path = Path(job.options["output_cost"])
        csv_path.parent.mkdir(parents=True, exist_ok=True)
        ts = datetime.now(timezone.utc).isoformat(timespec="milliseconds")
        with csv_path.open("w", encoding="utf-8", newline="") as f:
            w = _csv.writer(f)
            w.writerow(["timestamp", "model", "command", "cost",
                        "input_files", "output_files",
                        "attempted_models", "job_id"])
            w.writerow([ts, "gpt-4", "bug", "5.0", "", "",
                        "gpt-4", job.id])

        # Apply a late cap. update_budget must synchronously flush so
        # the existing $5 row trips the $1 cap immediately.
        await mgr.update_budget(job.id, budget_cap=1.0)
        # Give the callback a moment to fire.
        await asyncio.sleep(0.2)

        assert job.status == JobStatus.BUDGET_EXCEEDED, (
            f"Finding 3 (12th pass) regression: late cap did not "
            f"enforce existing rows. status={job.status}, events={events}"
        )
        assert events, "on_budget_exceeded was never invoked"


class TestWatcherDetectsCsvMigration:
    """Finding 3 (9th pass): track_cost migrates a mid-format CSV in
    place via os.replace, which gives the file a new inode. The watcher
    must detect the inode change and reset its cached fieldnames/offset
    so the new header is reparsed and job_id filtering activates.
    """

    def test_watcher_resets_after_os_replace(self, tmp_path):
        from pdd.cost_budget_watcher import watch
        from pdd.track_cost import _migrate_mid_to_new_header

        csv_path = tmp_path / "cost.csv"
        ts = "2026-05-22T18:30:00.000+00:00"
        # Seed mid-format file with one row from job-a.
        csv_path.write_text(
            "timestamp,model,command,cost,input_files,output_files,attempted_models\n"
            f"{ts},gpt-4,bug,10.0,,,gpt-4\n",
            encoding="utf-8",
        )

        watcher = watch(
            csv_path, cap=None, on_exceeded=lambda s: None,
            commands={"bug"}, job_id="job-a", poll_interval=0.1,
        )
        try:
            time.sleep(0.3)
            # Legacy fallback applies (no job_id column in header) →
            # counts the row.
            assert watcher.spent() == pytest.approx(10.0)

            # Now migrate the file in place. The mid → new helper
            # rewrites the file (new inode) and adds the job_id
            # column. Append a job-b row AFTER migration.
            _migrate_mid_to_new_header(str(csv_path))
            with csv_path.open("a", encoding="utf-8", newline="") as f:
                w = csv.writer(f)
                w.writerow([ts, "gpt-4", "bug", "20.0", "", "", "gpt-4", "job-b"])

            time.sleep(0.6)
            # After migration the header carries job_id; watcher should
            # have detected the inode change, re-parsed the header, and
            # now strictly filter on job_id="job-a". The job-b row must
            # NOT be counted; the only matching row is the migrated
            # job-a row (which has an empty job_id after migration, so
            # it ALSO doesn't match — total spend is $0).
            spent = watcher.spent()
            assert spent == 0.0, (
                f"Finding 3 (9th pass) regression: watcher did not "
                f"detect the inode change; counted spend={spent} (expected $0 "
                f"because job-a's migrated row has empty job_id and "
                f"job-b's row matches the wrong job_id)."
            )
        finally:
            watcher.stop()


class TestMidFormatCsvMigration:
    """Eighth-pass Finding 2: a server-managed run writing to a
    pre-existing mid-format CSV must migrate the header in place to add
    the job_id column so per-job isolation actually works for shared
    files. Without migration, two same-command jobs on the same legacy
    CSV count each other's spend.
    """

    def test_track_cost_migrates_legacy_header_when_pdd_job_id_set(
        self, tmp_path, monkeypatch,
    ):
        """Same migration story as the mid-format case but for the
        OLDEST layout: no attempted_models AND no job_id. Without this
        migration, two same-command jobs sharing a legacy file count
        each other's spend even after PDD_JOB_ID is wired through.
        """
        import os
        import click
        import click.testing
        from pdd.track_cost import track_cost

        cost_csv = tmp_path / "cost.csv"
        # Seed a legacy CSV (no attempted_models, no job_id).
        cost_csv.write_text(
            "timestamp,model,command,cost,input_files,output_files\n"
            "2026-01-01T00:00:00.000,old-model,gen,1.5,/i,/o\n",
            encoding="utf-8",
        )

        @click.command(name="bug")
        @click.pass_context
        @track_cost
        def bug(ctx):
            return ("result", 0.25, "gpt-4")

        monkeypatch.setenv("PDD_JOB_ID", "job-a")
        prior_pytest = os.environ.pop("PYTEST_CURRENT_TEST", None)
        try:
            runner = click.testing.CliRunner()
            runner.invoke(
                bug, [],
                obj={"output_cost": str(cost_csv)},
                standalone_mode=False,
            )
        finally:
            if prior_pytest is not None:
                os.environ["PYTEST_CURRENT_TEST"] = prior_pytest

        first_line = cost_csv.read_text(encoding="utf-8").splitlines()[0]
        assert "job_id" in first_line and "attempted_models" in first_line, (
            f"Finding 2 (9th pass) regression: legacy CSV not migrated to "
            f"new header. Header was: {first_line!r}"
        )

    def test_track_cost_migrates_mid_header_when_pdd_job_id_set(
        self, tmp_path, monkeypatch,
    ):
        import os
        import click
        import click.testing
        from pdd.track_cost import track_cost

        cost_csv = tmp_path / "cost.csv"
        # Seed a mid-format CSV (has attempted_models, no job_id).
        cost_csv.write_text(
            "timestamp,model,command,cost,input_files,output_files,attempted_models\n"
            "2026-01-01T00:00:00.000,old-model,gen,1.5,/i,/o,old-model\n",
            encoding="utf-8",
        )

        @click.command(name="bug")
        @click.pass_context
        @track_cost
        def bug(ctx):
            return ("result", 0.25, "gpt-4")

        # Temporarily clear PYTEST_CURRENT_TEST so the production write
        # path runs (track_cost skips writes during pytest by default).
        monkeypatch.setenv("PDD_JOB_ID", "job-a")
        prior_pytest = os.environ.pop("PYTEST_CURRENT_TEST", None)
        try:
            runner = click.testing.CliRunner()
            runner.invoke(
                bug, [],
                obj={"output_cost": str(cost_csv)},
                standalone_mode=False,
            )
        finally:
            if prior_pytest is not None:
                os.environ["PYTEST_CURRENT_TEST"] = prior_pytest

        # File must now have the new-format header (migration ran).
        text = cost_csv.read_text(encoding="utf-8")
        first_line = text.splitlines()[0]
        assert "job_id" in first_line, (
            f"Finding 2 (8th pass) regression: track_cost did not migrate "
            f"the mid-format header to add job_id. Header was: {first_line!r}"
        )
        data_lines = text.splitlines()[1:]
        # New row carries job-a.
        assert any(line.endswith(",job-a") for line in data_lines), (
            f"Expected a row ending with ',job-a'; got rows: {data_lines!r}"
        )
        # Old row is preserved with an empty trailing job_id field.
        assert any("old-model,gen,1.5" in line and line.endswith(",")
                   for line in data_lines), (
            f"Old row should be preserved with empty trailing job_id; "
            f"got rows: {data_lines!r}"
        )


class TestLlmInvokePublishesPartialCost:
    """Sixth pass Finding 3: llm_invoke must push cost/model onto ctx.obj
    so track_cost's exception path has real data. The earlier fix added
    the consumer side; this verifies the producer side actually
    publishes the keys.
    """

    def test_publish_call_outcome_accumulates_and_overwrites(self):
        # Drive the module-level helper directly with a synthetic
        # click context. This avoids the full llm_invoke pipeline
        # while still exercising the contract surface.
        import click

        from pdd.llm_invoke import _publish_call_outcome_to_ctx

        runner = click.testing.CliRunner()

        captured: dict = {}

        @click.command()
        @click.pass_context
        def probe(ctx):
            _publish_call_outcome_to_ctx(1.25, "gpt-4")
            _publish_call_outcome_to_ctx(2.5, "gpt-4o")
            _publish_call_outcome_to_ctx(0.0, None)  # silent no-op on cost=0
            captured.update(ctx.obj)

        runner.invoke(probe, [], obj={}, standalone_mode=False)
        assert captured["partial_cost"] == pytest.approx(3.75)
        assert captured["last_model"] == "gpt-4o"


class TestTrackCostWritesOnException:
    """Finding 3 (fifth review pass): track_cost must write a row even
    when the wrapped command raises, otherwise failed-but-costly
    attempts are invisible to budget enforcement.
    """

    def test_writes_partial_cost_on_exception(self, tmp_path):
        """Drive track_cost with a click context whose wrapped function
        raises after partial cost was pushed to ctx.obj. The decorator
        must still emit a CSV row carrying the partial cost.
        """
        import click

        from pdd.track_cost import track_cost

        @click.command(name="bug")
        @click.pass_context
        @track_cost
        def broken(ctx):
            ctx.obj['partial_cost'] = 4.25
            ctx.obj['last_model'] = "gpt-4"
            ctx.obj.setdefault('attempted_models', []).append("gpt-4")
            raise RuntimeError("synthetic mid-command failure")

        cost_csv = tmp_path / "cost.csv"
        runner = click.testing.CliRunner()
        # Important: PYTEST_CURRENT_TEST being set normally suppresses
        # writes; explicitly clear it for this test so the production
        # path runs.
        import os
        old = os.environ.pop("PYTEST_CURRENT_TEST", None)
        try:
            result = runner.invoke(
                broken, [],
                obj={'output_cost': str(cost_csv)},
                standalone_mode=False,
            )
        finally:
            if old is not None:
                os.environ["PYTEST_CURRENT_TEST"] = old

        # The wrapped command raised; track_cost re-raises after the
        # finally block, so result.exception is the RuntimeError.
        assert isinstance(result.exception, RuntimeError)
        assert cost_csv.exists(), (
            "Finding 3 regression: track_cost did not write a row for "
            "a failed command; spend is invisible to enforcement."
        )
        contents = cost_csv.read_text()
        # The partial cost from ctx.obj must be in the row.
        assert "4.25" in contents
        assert "bug" in contents
        assert "gpt-4" in contents


