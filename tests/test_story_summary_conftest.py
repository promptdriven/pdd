"""Tests for the story-regression CI summary harness in ``tests/conftest.py``.

Covers pdd#1889 V-F4: the summary miscounts because ``_story_id`` never looked
up the ``story_id=`` kwarg (the one every story test actually uses), setup-phase
skips were dropped, and a skip-only story was reported as PASS.
"""
from __future__ import annotations

from types import SimpleNamespace

from tests.conftest import (
    _story_id,
    _story_report_counts,
    _story_summary_status,
)


class _FakeMark:
    def __init__(self, *args, **kwargs):
        self.args = args
        self.kwargs = kwargs


class _FakeItem:
    def __init__(self, nodeid: str):
        self.nodeid = nodeid


def test_story_id_resolves_story_id_kwarg():
    """V-F4: ``@pytest.mark.story(story_id="checkout")`` must resolve to the
    story id, not fall back to the file path."""
    item = _FakeItem("tests/story_regression/test_story_checkout.py::test_it")
    mark = _FakeMark(story_id="checkout")
    assert _story_id(item, mark) == "checkout"


def test_story_id_still_supports_positional_and_name_and_id():
    item = _FakeItem("tests/test_x.py::test_it")
    assert _story_id(item, _FakeMark("pos")) == "pos"
    assert _story_id(item, _FakeMark(name="named")) == "named"
    assert _story_id(item, _FakeMark(id="ided")) == "ided"


def test_story_id_falls_back_to_file_path_when_bare():
    item = _FakeItem("tests/story_regression/test_bare.py::test_it")
    assert _story_id(item, _FakeMark()) == "tests/story_regression/test_bare.py"


def test_report_counts_includes_setup_phase_skip():
    """V-F4: a @pytest.mark.skip-decorated story emits only a *setup*-phase skip
    (no call report) and must still be tallied, not vanish."""
    setup_skip = SimpleNamespace(when="setup", skipped=True, failed=False, outcome="skipped")
    assert _story_report_counts(setup_skip) is True
    # A normal passing setup phase must NOT be counted (only its call phase is).
    setup_pass = SimpleNamespace(when="setup", skipped=False, failed=False, outcome="passed")
    assert _story_report_counts(setup_pass) is False
    call_pass = SimpleNamespace(when="call", skipped=False, failed=False, outcome="passed")
    assert _story_report_counts(call_pass) is True


def test_summary_status_skip_only_is_skip_not_pass():
    """V-F4: a story that only skipped must render as SKIP, not PASS."""
    assert _story_summary_status({"passed": 0, "failed": 0, "skipped": 1}) == "SKIP"
    assert _story_summary_status({"passed": 1, "failed": 0, "skipped": 1}) == "PASS"
    assert _story_summary_status({"passed": 2, "failed": 0, "skipped": 0}) == "PASS"
    assert _story_summary_status({"passed": 1, "failed": 1, "skipped": 0}) == "FAIL"
