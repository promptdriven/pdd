"""Tests for multi-color token rendering in ``pdd context`` (EPIC #1540, PR #3).

These assert the *shape* of the colored output — that category color markers are
present and that ordering/spacing is stable — without pinning exact ANSI byte
sequences in the box-content assertions (a regex strips ANSI for structural
checks). They also lock the two invariants the PR must preserve: the no-color
path is byte-for-byte identical to the uncolored render, and JSON output is
unchanged and never colored.
"""
from __future__ import annotations

import json
import re

import pytest
from click.testing import CliRunner

from pdd.cli_theme import (
    ANSI_FAINT,
    ANSI_RESET,
    BREAK_RED,
    DIFF_YELLOW,
    ELECTRIC_CYAN,
    LUMEN_PURPLE,
    hex_to_ansi,
)
import importlib

context_mod = importlib.import_module("pdd.commands.context")
from pdd.commands.context import (
    _FREE_GLYPH,
    _UNAVAILABLE_GLYPH,
    _USED_GLYPH,
    _color_enabled,
    _glyph_for,
    _make_painter,
    _render_usage_box,
    context,
)
from pdd.context_audit import AuditRow, ContextAudit

_ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")


def _strip_ansi(text: str) -> str:
    return _ANSI_RE.sub("", text)


@pytest.fixture
def fake_audit():
    """A controlled audit covering every category the box can color."""
    rows = [
        AuditRow(source="prompt_body", tokens=200, status="body"),
        AuditRow(source="context/a.txt", tokens=80, status="resolved"),
        AuditRow(
            source="context/dynamic", tokens=20, status="deferred", note="deferred query_include"
        ),
        AuditRow(
            source="context/missing.prompt", tokens=0, status="unresolved", note="unresolved"
        ),
    ]
    return ContextAudit(
        model="gpt-4o",
        total_tokens=300,
        context_limit=1000,
        percent_used=30.0,
        rows=rows,
        warnings=["unresolved include: context/missing.prompt"],
    )


@pytest.fixture
def patched(monkeypatch, fake_audit):
    """Make the CLI return ``fake_audit`` without hydrating/counting anything."""
    monkeypatch.setattr(context_mod, "audit_prompt_file", lambda *a, **k: fake_audit)
    return fake_audit


@pytest.fixture
def prompt_file(tmp_path):
    p = tmp_path / "p.prompt"
    p.write_text("hello")
    return str(p)


def _invoke(args, prompt_file, env=None):
    return CliRunner().invoke(context, [prompt_file, *args], obj={}, env=env or {})


# --------------------------------------------------------------------------- #
# Color is multi-color, by category, and on the expected brand hues.
# --------------------------------------------------------------------------- #
def test_forced_color_emits_each_category_color(patched, prompt_file):
    res = _invoke(["--color"], prompt_file)
    assert res.exit_code == 0, res.output
    out = res.output
    # Every category present in the audit contributes its brand color marker.
    assert hex_to_ansi(ELECTRIC_CYAN) in out  # body
    assert hex_to_ansi(LUMEN_PURPLE) in out  # resolved include
    assert hex_to_ansi(DIFF_YELLOW) in out  # deferred
    assert hex_to_ansi(BREAK_RED) in out  # unresolved
    assert ANSI_FAINT in out  # free space
    assert ANSI_RESET in out
    # More than one distinct color → genuinely multi-color, not a single hue.
    distinct = set(_ANSI_RE.findall(out))
    assert len(distinct) >= 4


def test_forced_color_preserves_box_shape(patched, prompt_file):
    """Stripping ANSI from the colored box yields exactly the uncolored box."""
    colored = _strip_ansi(_invoke(["--color"], prompt_file).output)
    plain = _invoke(["--no-color"], prompt_file).output
    assert colored == plain


# --------------------------------------------------------------------------- #
# No-color path is byte-identical to the uncolored render (CI logs / pipes).
# --------------------------------------------------------------------------- #
def test_no_color_has_no_ansi(patched, prompt_file):
    out = _invoke(["--no-color"], prompt_file).output
    assert "\x1b" not in out
    assert "Context Usage" in out
    assert "Estimated usage by category" in out


def test_no_color_matches_direct_render(patched, fake_audit, prompt_file):
    """--no-color output equals calling the renderer with no painter at all."""
    # CliRunner mixes stderr into .output; the box itself is the non-WARN lines.
    raw = _invoke(["--no-color"], prompt_file).output
    cli_out = "\n".join(
        ln for ln in raw.split("\n") if not ln.startswith("WARN:")
    ).rstrip("\n")
    direct = _render_usage_box(
        fake_audit.rows,
        fake_audit.total_tokens,
        fake_audit.context_limit,
        fake_audit.model,
        fake_audit.percent_used,
    )
    assert cli_out == direct


def test_auto_detect_disables_color_when_not_a_tty(patched, prompt_file):
    # Under CliRunner stdout is not a TTY, so auto-detect must stay plain.
    out = _invoke([], prompt_file).output
    assert "\x1b" not in out


def test_no_color_env_disables_in_auto_mode(patched, prompt_file):
    out = _invoke([], prompt_file, env={"NO_COLOR": "1"}).output
    assert "\x1b" not in out


# --------------------------------------------------------------------------- #
# Ordering is stable: categories appear in the core's row order, free last.
# --------------------------------------------------------------------------- #
def test_legend_ordering_stable(patched, prompt_file):
    out = _strip_ansi(_invoke(["--color"], prompt_file).output)
    order = [
        out.index("prompt_body:"),
        out.index("context/a.txt:"),
        out.index("context/dynamic:"),
        out.index("context/missing.prompt:"),
        out.index("Free space:"),
    ]
    assert order == sorted(order)


# --------------------------------------------------------------------------- #
# JSON output is unchanged and never colored, regardless of the color flag.
# --------------------------------------------------------------------------- #
def test_json_is_identical_with_and_without_color(patched, prompt_file):
    a = _invoke(["--json", "--color"], prompt_file).output
    b = _invoke(["--json", "--no-color"], prompt_file).output
    c = _invoke(["--json"], prompt_file).output
    assert a == b == c
    assert "\x1b" not in a


def test_json_payload_shape_unchanged(patched, prompt_file):
    payload = json.loads(_invoke(["--json", "--color"], prompt_file).output)
    assert set(payload) == {
        "total_tokens",
        "context_limit",
        "percent_used",
        "model",
        "rows",
        "warnings",
        "threshold_exceeded",
    }
    assert payload["total_tokens"] == 300
    assert [r["status"] for r in payload["rows"]] == [
        "body",
        "resolved",
        "deferred",
        "unresolved",
    ]


# --------------------------------------------------------------------------- #
# Table mode: color the Source cell only, alignment intact.
# --------------------------------------------------------------------------- #
def test_table_color_keeps_alignment(patched, prompt_file):
    colored = _strip_ansi(_invoke(["--table", "--color"], prompt_file).output)
    plain = _invoke(["--table", "--no-color"], prompt_file).output
    assert colored == plain
    assert "\x1b" not in plain


def test_table_forced_color_has_markers(patched, prompt_file):
    out = _invoke(["--table", "--color"], prompt_file).output
    assert hex_to_ansi(LUMEN_PURPLE) in out
    assert ANSI_RESET in out


# --------------------------------------------------------------------------- #
# Unit-level: the color-enable decision and the painter seam.
# --------------------------------------------------------------------------- #
class _Stream:
    def __init__(self, tty):
        self._tty = tty

    def isatty(self):
        return self._tty


def test_color_enabled_explicit_wins_over_env(monkeypatch):
    monkeypatch.setenv("NO_COLOR", "1")
    # Explicit --color forces color even when NO_COLOR is set / stream is a pipe.
    assert _color_enabled(True, _Stream(False)) is True
    # Explicit --no-color forces off even on a TTY.
    assert _color_enabled(False, _Stream(True)) is False


def test_color_enabled_auto(monkeypatch):
    monkeypatch.delenv("NO_COLOR", raising=False)
    assert _color_enabled(None, _Stream(True)) is True
    assert _color_enabled(None, _Stream(False)) is False
    # NO_COLOR with any value (including empty) disables in auto mode.
    monkeypatch.setenv("NO_COLOR", "")
    assert _color_enabled(None, _Stream(True)) is False


def test_painter_disabled_is_noop():
    paint = _make_painter(False)
    assert paint("body", "x") == "x"
    assert paint("free", "⛶") == "⛶"


def test_painter_enabled_wraps_known_category_only():
    paint = _make_painter(True)
    assert paint("body", "x") == f"{hex_to_ansi(ELECTRIC_CYAN)}x{ANSI_RESET}"
    # Unknown category falls back to plain text rather than emitting a bad code.
    assert paint("does-not-exist", "x") == "x"


# --------------------------------------------------------------------------- #
# Glyph scheme: counted categories share ONE glyph (color tells them apart);
# unavailable and free space keep their own distinct glyphs.
# --------------------------------------------------------------------------- #
def test_glyph_for_scheme():
    # Every counted category collapses to the one shared glyph.
    for status in ("body", "resolved", "deferred", "unresolved"):
        assert _glyph_for(status) == _USED_GLYPH
    # unavailable is the lone status with its own glyph.
    assert _glyph_for("unavailable") == _UNAVAILABLE_GLYPH
    # The three glyphs that can appear are mutually distinct.
    assert len({_USED_GLYPH, _UNAVAILABLE_GLYPH, _FREE_GLYPH}) == 3


def _audit_with_unavailable():
    rows = [
        AuditRow(source="prompt_body", tokens=200, status="body"),
        AuditRow(source="context/a.txt", tokens=80, status="resolved"),
        AuditRow(source="context/b.txt", tokens=20, status="resolved"),
        AuditRow(source="grounding", tokens=0, status="unavailable", note="requires cloud"),
    ]
    return ContextAudit(
        model="gpt-4o", total_tokens=300, context_limit=1000, percent_used=30.0, rows=rows
    )


def test_counted_categories_share_glyph_in_legend():
    audit = _audit_with_unavailable()
    box = _render_usage_box(
        audit.rows, audit.total_tokens, audit.context_limit, audit.model, audit.percent_used
    )
    # body + two resolved rows all lead with the same shared glyph...
    for label in ("prompt_body", "context/a.txt", "context/b.txt"):
        line = next(ln for ln in box.splitlines() if f"{label}:" in ln)
        assert line.strip().startswith(_USED_GLYPH)
    # ...while unavailable and free keep their own.
    unavail = next(ln for ln in box.splitlines() if "grounding:" in ln)
    free = next(ln for ln in box.splitlines() if "Free space:" in ln)
    assert unavail.strip().startswith(_UNAVAILABLE_GLYPH)
    assert free.strip().startswith(_FREE_GLYPH)


def test_color_distinguishes_the_shared_glyph(patched, prompt_file):
    """Same glyph, different category → different color in front of it."""
    out = _invoke(["--color"], prompt_file).output
    # body (cyan) and resolved (purple) both wear _USED_GLYPH, told apart by color.
    assert f"{hex_to_ansi(ELECTRIC_CYAN)}{_USED_GLYPH}" in out
    assert f"{hex_to_ansi(LUMEN_PURPLE)}{_USED_GLYPH}" in out
