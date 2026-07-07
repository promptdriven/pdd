"""Failure-class precedence, incl. the agent_error path (adversarial review)."""

from harness.runner.metrics import FAILURE_CLASSES, classify_failure

_NO_EDITS = {"forbidden": [], "wrong_file": [], "target": [], "in_scope": []}


def test_hidden_pass_has_no_failure_class():
    assert classify_failure(
        hidden_pass=True, visible_pass=True, timed_out=False,
        edit_classes=_NO_EDITS, target_read_into_context=True,
        context_overflow=False, agent_error=False,
    ) is None


def test_agent_error_wins_over_other_failures():
    # A crashed agent that also happened to time out / edit wrong files is
    # still classified agent_error — its edits are not a localization signal.
    edits = {"forbidden": [], "wrong_file": ["x.py"], "target": [], "in_scope": []}
    assert classify_failure(
        hidden_pass=False, visible_pass=False, timed_out=True,
        edit_classes=edits, target_read_into_context=False,
        context_overflow=True, agent_error=True,
    ) == "agent_error"


def test_agent_error_is_a_registered_class():
    assert "agent_error" in FAILURE_CLASSES


def test_non_agent_error_paths_unchanged():
    # Regression: without agent_error, precedence is forbidden → timeout → …
    forbidden = {"forbidden": ["hidden/x"], "wrong_file": [], "target": [], "in_scope": []}
    assert classify_failure(
        hidden_pass=False, visible_pass=False, timed_out=True,
        edit_classes=forbidden, target_read_into_context=False,
        context_overflow=False,
    ) == "forbidden_access"
    assert classify_failure(
        hidden_pass=False, visible_pass=False, timed_out=True,
        edit_classes=_NO_EDITS, target_read_into_context=True,
        context_overflow=False,
    ) == "timeout"
