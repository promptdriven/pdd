import subprocess
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.checkup_interactive_session import (
    ApprovedPatch,
    FakeInteractiveSession,
    RepairOption,
    _pi_available,
)


def _patch(kind: str = "vocab_definition") -> ApprovedPatch:
    return ApprovedPatch(
        kind=kind,
        target=Path("prompts/refund_python.prompt"),
        anchor={"finding_id": "finding-1", "line": 42},
        replacement="- Remaining refundable amount: captured minus refunded.",
    )


def _option(label: str = "A", kind: str = "vocab_definition") -> RepairOption:
    return RepairOption(
        label=label,
        preview="--- prompt\n+++ prompt\n@@\n+definition",
        patch=_patch(kind),
    )


# --- FakeInteractiveSession ---

def test_fake_session_run_marks_ran() -> None:
    session = FakeInteractiveSession([_patch()])
    session.seed({"findings": []})
    assert not session.ran
    session.run()
    assert session.ran


def test_fake_session_returns_seeded_patches() -> None:
    p = _patch()
    session = FakeInteractiveSession([p])
    session.run()
    assert session.approved_patches() == [p]


def test_fake_session_returns_empty_when_no_patches() -> None:
    session = FakeInteractiveSession()
    session.run()
    assert session.approved_patches() == []


def test_fake_session_returns_fresh_copy() -> None:
    session = FakeInteractiveSession([_patch()])
    session.run()
    first = session.approved_patches()
    first[0].anchor["line"] = 99
    second = session.approved_patches()
    assert second[0].anchor["line"] == 42


def test_fake_session_seed_stores_report() -> None:
    session = FakeInteractiveSession()
    report = {"findings": [{"finding_id": "F-1"}]}
    session.seed(report)
    assert session.report == report


# --- ApprovedPatch ---

def test_approved_patch_coerces_string_target_to_path() -> None:
    p = ApprovedPatch(
        kind="vocab_definition",
        target="prompts/refund_python.prompt",  # type: ignore[arg-type]
        anchor={"line": 1},
        replacement="x",
    )
    assert isinstance(p.target, Path)
    assert p.target == Path("prompts/refund_python.prompt")


def test_approved_patch_coerces_anchor_to_dict() -> None:
    p = ApprovedPatch(kind="k", target=Path("f.prompt"), anchor={"a": 1}, replacement="r")
    assert isinstance(p.anchor, dict)


# --- _pi_available ---

def _npm_ok() -> MagicMock:
    """Return a mock subprocess.CompletedProcess indicating npm probe success."""
    m = MagicMock()
    m.returncode = 0
    return m


def test_pi_available_false_when_node_missing() -> None:
    with patch("shutil.which", return_value=None):
        assert not _pi_available()


def test_pi_available_false_when_node_version_too_low() -> None:
    with patch("shutil.which", return_value="/usr/bin/node"), \
         patch("subprocess.check_output", return_value="v20.0.0"):
        assert not _pi_available()


def test_pi_available_true_when_node_22_plus_and_package_installed() -> None:
    with patch("shutil.which", return_value="/usr/bin/node"), \
         patch("subprocess.check_output", return_value="v22.19.0"), \
         patch("subprocess.run", return_value=_npm_ok()):
        assert _pi_available()


def test_pi_available_false_when_npm_package_missing() -> None:
    with patch("shutil.which", return_value="/usr/bin/node"), \
         patch("subprocess.check_output", return_value="v22.19.0"), \
         patch("subprocess.run", side_effect=subprocess.CalledProcessError(1, "node")):
        assert not _pi_available()


def test_pi_available_false_on_subprocess_error() -> None:
    with patch("shutil.which", return_value="/usr/bin/node"), \
         patch("subprocess.check_output", side_effect=OSError("fail")):
        assert not _pi_available()
