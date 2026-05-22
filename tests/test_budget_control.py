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
        r = parse_comment(_user_comment("/pdd budget node 50"))
        assert r.kind == "budget_node_set"
        assert r.metadata == {"amount": 50.0}

    def test_budget_max_metadata(self):
        r = parse_comment(_user_comment("/pdd budget max 200"))
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
