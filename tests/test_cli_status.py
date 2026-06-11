"""Tests for the PDD CLI status & progress messaging system (pdd/cli_status.py).

These assert on message *shape* and on plain-text console output captured from a
non-terminal Rich console — so there are no wall-clock, spinner-frame, or
ANSI-color assertions, and the suite stays deterministic (no timing flakes).
"""

import sys
from io import StringIO
from pathlib import Path

# Prioritize local code.
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import pytest
from rich.console import Console

from pdd import cli_status
from pdd.cli_status import (
    GLYPHS,
    ROLES,
    Status,
    StatusMessage,
    StatusReporter,
    from_context,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
def plain_console():
    """A non-terminal console that renders plain text into a buffer."""
    buf = StringIO()
    con = Console(file=buf, force_terminal=False, no_color=True, width=100)
    return con, buf


def reporter(**kwargs):
    con, buf = plain_console()
    return StatusReporter(console=con, **kwargs), buf


# ---------------------------------------------------------------------------
# Primitives: there are exactly five, each with one glyph and one theme role.
# ---------------------------------------------------------------------------
def test_five_primitives():
    assert [s.name for s in Status] == [
        "START",
        "STEP",
        "WAITING",
        "SUCCESS",
        "FAILURE",
    ]


def test_every_primitive_has_glyph_and_role():
    for status in Status:
        assert status in GLYPHS and GLYPHS[status]
        assert status in ROLES and ROLES[status]


def test_roles_are_real_theme_roles():
    # Roles must resolve against the central color system, not be raw colors.
    from pdd.cli_theme import SEMANTIC_STYLES

    for role in ROLES.values():
        assert role in SEMANTIC_STYLES, f"{role!r} is not a semantic role"


# ---------------------------------------------------------------------------
# StatusMessage rendering
# ---------------------------------------------------------------------------
def test_plain_render_includes_glyph_and_text():
    msg = StatusMessage(Status.STEP, "doing the thing")
    out = msg.render_plain()
    assert GLYPHS[Status.STEP] in out
    assert "doing the thing" in out


def test_waiting_render_names_what_it_waits_on():
    msg = StatusMessage(Status.WAITING, "calling the model", waiting_on="LLM")
    assert "waiting on LLM" in msg.render_plain()
    assert "waiting on LLM" in msg.render_markup()


def test_failure_render_has_cause_and_suggestions():
    msg = StatusMessage(
        Status.FAILURE,
        "reading the change file",
        reason="file not found",
        suggestions=("check the path", "run with --verbose"),
    )
    out = msg.render_plain()
    assert "reading the change file" in out  # what failed
    assert "Why: file not found" in out       # why
    assert "Try: check the path" in out       # what to try (1)
    assert "Try: run with --verbose" in out   # what to try (2)


def test_success_render_has_next_step():
    msg = StatusMessage(Status.SUCCESS, "done", next_step="run pdd sync")
    assert "Next: run pdd sync" in msg.render_plain()


def test_start_headline_includes_command():
    msg = StatusMessage(Status.START, "beginning", command="pdd detect")
    assert "pdd detect: beginning" in msg.render_plain()


def test_markup_uses_semantic_role():
    msg = StatusMessage(Status.SUCCESS, "ok")
    markup = msg.render_markup()
    assert f"[{ROLES[Status.SUCCESS]}]" in markup


def test_markup_escapes_user_text():
    # Brackets in content must not be interpreted as Rich markup.
    msg = StatusMessage(Status.FAILURE, "boom", reason="value was [red]bad[/red]")
    markup = msg.render_markup()
    assert r"\[red]" in markup


# ---------------------------------------------------------------------------
# StatusReporter: recording + emission
# ---------------------------------------------------------------------------
def test_methods_record_and_return_messages():
    rep, _ = reporter(command="pdd detect")
    m_start = rep.start("checking 3 prompts", next_step="review")
    m_step = rep.step("comparing")
    m_ok = rep.success("2 need changes", next_step="run pdd change")
    m_bad = rep.failure("detecting", reason="oops", suggestions=["retry"])

    assert [m.status for m in rep.messages] == [
        Status.START,
        Status.STEP,
        Status.SUCCESS,
        Status.FAILURE,
    ]
    assert m_start.command == "pdd detect" and m_start.next_step == "review"
    assert m_step.status == Status.STEP
    assert m_ok.next_step == "run pdd change"
    assert m_bad.reason == "oops" and m_bad.suggestions == ("retry",)


def test_emit_prints_when_not_quiet():
    rep, buf = reporter()
    rep.start("hello world")
    assert "hello world" in buf.getvalue()


def test_quiet_suppresses_output_but_still_records():
    rep, buf = reporter(quiet=True)
    rep.start("hello world")
    rep.success("done")
    assert buf.getvalue() == ""              # nothing printed
    assert len(rep.messages) == 2            # but still recorded


def test_consecutive_duplicate_is_collapsed():
    rep, buf = reporter()
    rep.step("same line")
    rep.step("same line")  # identical, immediately after -> collapsed
    assert buf.getvalue().count("same line") == 1
    # Both are still recorded (de-dup is about not spamming the terminal).
    assert len(rep.messages) == 2


def test_non_consecutive_duplicate_is_not_collapsed():
    rep, buf = reporter()
    rep.step("line A")
    rep.step("line B")
    rep.step("line A")  # same text but not immediately after -> printed again
    assert buf.getvalue().count("line A") == 2


# ---------------------------------------------------------------------------
# JSON mode: status must not pollute stdout
# ---------------------------------------------------------------------------
def test_json_mode_routes_to_stderr_by_default():
    rep = StatusReporter(json_mode=True)
    assert rep.console.stderr is True


# ---------------------------------------------------------------------------
# waiting(): records a WAITING event, inert (no spinner) on a non-terminal.
# ---------------------------------------------------------------------------
def test_waiting_records_and_yields_message():
    rep, buf = reporter()
    with rep.waiting("calling the model", on="LLM") as msg:
        assert isinstance(msg, StatusMessage)
        assert msg.status == Status.WAITING
        assert msg.waiting_on == "LLM"
    # Recorded exactly once, regardless of how long the block ran.
    waits = [m for m in rep.messages if m.status == Status.WAITING]
    assert len(waits) == 1
    assert "calling the model" in buf.getvalue()


def test_waiting_inert_when_quiet():
    rep, buf = reporter(quiet=True)
    with rep.waiting("calling the model", on="network"):
        pass
    assert buf.getvalue() == ""
    assert rep.messages[0].waiting_on == "network"


def test_waiting_does_not_swallow_exceptions():
    rep, _ = reporter()
    with pytest.raises(ValueError):
        with rep.waiting("calling the model"):
            raise ValueError("boom")


# ---------------------------------------------------------------------------
# from_context
# ---------------------------------------------------------------------------
class _Ctx:
    def __init__(self, obj):
        self.obj = obj


def test_from_context_inherits_quiet():
    rep = from_context(_Ctx({"quiet": True}), command="pdd x")
    assert rep.quiet is True
    assert rep.command == "pdd x"


def test_from_context_defaults_quiet_false_without_obj():
    rep = from_context(_Ctx(None))
    assert rep.quiet is False


# ---------------------------------------------------------------------------
# Full skim: a covered command emits start -> step/waiting -> success.
# ---------------------------------------------------------------------------
def test_typical_command_flow_shape():
    rep, buf = reporter(command="pdd detect")
    rep.start("checking 3 prompt(s) against the change description")
    with rep.waiting("asking the model which prompts need changes", on="LLM"):
        pass
    rep.success("2 prompt(s) need changes", next_step="run `pdd change`")

    kinds = [m.status for m in rep.messages]
    assert kinds == [Status.START, Status.WAITING, Status.SUCCESS]
    text = buf.getvalue()
    # User can tell: what started, that it waited on the LLM, and the next action.
    assert "pdd detect:" in text
    assert "waiting on LLM" in text
    assert "Next:" in text
