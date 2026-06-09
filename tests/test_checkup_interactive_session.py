import json
import subprocess
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.checkup_interactive_session import (
    NON_APPROVING_PATCH_KINDS,
    ApprovedPatch,
    FakeInteractiveSession,
    LlmInteractiveSession,
    PiInteractiveSession,
    _PatchProposal,
    _ProposalSet,
    _pi_available,
    make_session,
)


def _patch(kind: str = "vocab_definition", finding_id: str = "F-1") -> ApprovedPatch:
    return ApprovedPatch(
        kind=kind,
        target=Path("prompts/refund_python.prompt"),
        anchor={"line": 42},
        replacement="- Remaining refundable amount: captured minus refunded.",
        finding_id=finding_id,
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


def test_approved_patch_finding_id_defaults_to_empty_string() -> None:
    p = ApprovedPatch(kind="k", target=Path("f.prompt"), anchor={}, replacement="r")
    assert p.finding_id == ""


def test_approved_patch_preserves_finding_id() -> None:
    p = ApprovedPatch(kind="k", target=Path("f.prompt"), anchor={}, replacement="r", finding_id="F-42")
    assert p.finding_id == "F-42"


# --- PiInteractiveSession.run() ---

def _bridge_writer(bridge_output: dict):
    """Return a subprocess.run side_effect that writes bridge_output to the output path."""
    def _run(cmd, check, **kwargs):
        Path(cmd[-1]).write_text(json.dumps(bridge_output), encoding="utf-8")
        return MagicMock(returncode=0)
    return _run


def test_pi_session_run_parses_approved_patches() -> None:
    bridge_output = {"approved_patches": [
        {"kind": "vocab_definition", "target": "p.prompt",
         "anchor": {"line": 1}, "replacement": "x", "finding_id": "F-1"},
    ]}
    with patch("shutil.which", return_value="/usr/bin/node"), \
         patch("subprocess.run", side_effect=_bridge_writer(bridge_output)):
        session = PiInteractiveSession()
        session.seed({"findings": []})
        session.run()

    patches = session.approved_patches()
    assert len(patches) == 1
    assert patches[0].kind == "vocab_definition"
    assert patches[0].finding_id == "F-1"


def test_pi_session_run_filters_non_approving_kinds() -> None:
    bridge_output = {"approved_patches": [
        {"kind": "skip", "target": "p.prompt", "anchor": {}, "replacement": "", "finding_id": "F-1"},
        {"kind": "custom_no_patch", "target": "p.prompt", "anchor": {}, "replacement": "", "finding_id": "F-1"},
        {"kind": "no_patch", "target": "p.prompt", "anchor": {}, "replacement": "", "finding_id": "F-1"},
        {"kind": "vocab_definition", "target": "p.prompt", "anchor": {}, "replacement": "x", "finding_id": "F-1"},
    ]}
    with patch("shutil.which", return_value="/usr/bin/node"), \
         patch("subprocess.run", side_effect=_bridge_writer(bridge_output)):
        session = PiInteractiveSession()
        session.seed({})
        session.run()

    patches = session.approved_patches()
    assert len(patches) == 1
    assert patches[0].kind == "vocab_definition"
    assert all(p.kind not in NON_APPROVING_PATCH_KINDS for p in patches)


def test_pi_session_run_raises_on_bridge_error() -> None:
    with patch("shutil.which", return_value="/usr/bin/node"), \
         patch("subprocess.run", side_effect=subprocess.CalledProcessError(1, "node")):
        session = PiInteractiveSession()
        session.seed({})
        with pytest.raises(subprocess.CalledProcessError):
            session.run()


def test_pi_session_run_raises_when_bridge_writes_no_output() -> None:
    def _run_no_output(cmd, check, **kwargs):
        return MagicMock(returncode=0)

    with patch("shutil.which", return_value="/usr/bin/node"), \
         patch("subprocess.run", side_effect=_run_no_output):
        session = PiInteractiveSession()
        session.seed({})
        with pytest.raises(RuntimeError, match="without writing output"):
            session.run()


def test_pi_session_run_resets_patches_before_each_run() -> None:
    good_output = {"approved_patches": [
        {"kind": "vocab_definition", "target": "p.prompt",
         "anchor": {}, "replacement": "x", "finding_id": "F-1"},
    ]}
    with patch("shutil.which", return_value="/usr/bin/node"), \
         patch("subprocess.run", side_effect=_bridge_writer(good_output)):
        session = PiInteractiveSession()
        session.seed({})
        session.run()
    assert len(session.approved_patches()) == 1

    # Second run fails — patches must be cleared, not left from the first run.
    with patch("shutil.which", return_value="/usr/bin/node"), \
         patch("subprocess.run", side_effect=subprocess.CalledProcessError(1, "node")):
        with pytest.raises(subprocess.CalledProcessError):
            session.run()
    assert session.approved_patches() == []


def test_pi_session_run_ignores_extra_fields_from_bridge() -> None:
    bridge_output = {"approved_patches": [
        {"kind": "vocab_definition", "target": "p.prompt", "anchor": {},
         "replacement": "x", "finding_id": "F-1", "rationale": "extra", "confidence": 0.9},
    ]}
    with patch("shutil.which", return_value="/usr/bin/node"), \
         patch("subprocess.run", side_effect=_bridge_writer(bridge_output)):
        session = PiInteractiveSession()
        session.seed({})
        session.run()
    patches = session.approved_patches()
    assert len(patches) == 1
    assert patches[0].kind == "vocab_definition"


def test_pi_session_run_raises_on_invalid_json_output() -> None:
    def _write_bad_json(cmd, check, **kwargs):
        Path(cmd[-1]).write_text("not valid json {{{", encoding="utf-8")
        return MagicMock(returncode=0)

    with patch("shutil.which", return_value="/usr/bin/node"), \
         patch("subprocess.run", side_effect=_write_bad_json):
        session = PiInteractiveSession()
        session.seed({})
        with pytest.raises(RuntimeError, match="invalid JSON"):
            session.run()


def test_pi_session_accepts_timeout_parameter() -> None:
    bridge_output = {"approved_patches": []}
    with patch("shutil.which", return_value="/usr/bin/node") as _wh, \
         patch("subprocess.run", side_effect=_bridge_writer(bridge_output)) as mock_run:
        session = PiInteractiveSession(timeout=30.0)
        session.seed({})
        session.run()
    call_kwargs = mock_run.call_args
    assert call_kwargs.kwargs.get("timeout") == 30.0


# --- _pi_available ---

def _npm_ok() -> MagicMock:
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


# --- LlmInteractiveSession ---

_SAMPLE_PROPOSALS = [
    {
        "kind": "vocab_definition",
        "target": "prompts/refund.prompt",
        "anchor": {"section": "Vocabulary"},
        "replacement": "- refund_window: 30 calendar days from purchase",
        "label": "Add refund window definition",
        "rationale": "Removes ambiguity about the refund period",
    },
    {
        "kind": "contract_rule",
        "target": "prompts/refund.prompt",
        "anchor": {"pattern": "as soon as possible"},
        "replacement": "within 3 business days of approval",
        "label": "Replace vague timeline with exact deadline",
        "rationale": "Specifies a concrete, testable deadline",
    },
]


def _proposal_set(items: list[dict] | None = None) -> _ProposalSet:
    return _ProposalSet(proposals=[_PatchProposal(**p) for p in (items or _SAMPLE_PROPOSALS)])


def _llm_ok(items: list[dict] | None = None) -> dict:
    return {"result": _proposal_set(items), "cost": 0.001, "model_name": "test"}


def test_llm_session_run_returns_approved_patch_on_selection() -> None:
    report = {"findings": [{"finding_id": "F-1", "summary": "Ambiguous refund window"}]}
    with patch("pdd.llm_invoke.llm_invoke", return_value=_llm_ok()), \
         patch("click.prompt", return_value="1"), \
         patch("click.echo"):
        session = LlmInteractiveSession()
        session.seed(report)
        session.run()

    patches = session.approved_patches()
    assert len(patches) == 1
    assert patches[0].kind == "vocab_definition"
    assert patches[0].finding_id == "F-1"
    assert patches[0].target == Path("prompts/refund.prompt")


def test_llm_session_run_approves_multiple_patches() -> None:
    report = {"findings": [{"finding_id": "F-1", "summary": "test"}]}
    with patch("pdd.llm_invoke.llm_invoke", return_value=_llm_ok()), \
         patch("click.prompt", return_value="1 2"), \
         patch("click.echo"):
        session = LlmInteractiveSession()
        session.seed(report)
        session.run()

    patches = session.approved_patches()
    assert len(patches) == 2
    assert patches[0].kind == "vocab_definition"
    assert patches[1].kind == "contract_rule"


def test_llm_session_run_skips_finding_on_s_input() -> None:
    report = {"findings": [{"finding_id": "F-1", "summary": "test"}]}
    with patch("pdd.llm_invoke.llm_invoke", return_value=_llm_ok()), \
         patch("click.prompt", return_value="s"), \
         patch("click.echo"):
        session = LlmInteractiveSession()
        session.seed(report)
        session.run()

    assert session.approved_patches() == []


def test_llm_session_run_handles_multiple_findings() -> None:
    report = {"findings": [
        {"finding_id": "F-1", "summary": "first"},
        {"finding_id": "F-2", "summary": "second"},
    ]}
    with patch("pdd.llm_invoke.llm_invoke", return_value=_llm_ok([_SAMPLE_PROPOSALS[0]])), \
         patch("click.prompt", return_value="1"), \
         patch("click.echo"):
        session = LlmInteractiveSession()
        session.seed(report)
        session.run()

    patches = session.approved_patches()
    assert len(patches) == 2
    assert patches[0].finding_id == "F-1"
    assert patches[1].finding_id == "F-2"


def test_llm_session_run_handles_llm_error_gracefully() -> None:
    report = {"findings": [{"finding_id": "F-1", "summary": "test"}]}
    with patch("pdd.llm_invoke.llm_invoke", side_effect=RuntimeError("API error")), \
         patch("click.echo"):
        session = LlmInteractiveSession()
        session.seed(report)
        session.run()

    assert session.approved_patches() == []


def test_llm_session_run_resets_patches_on_each_run() -> None:
    report = {"findings": [{"finding_id": "F-1", "summary": "test"}]}
    with patch("pdd.llm_invoke.llm_invoke", return_value=_llm_ok([_SAMPLE_PROPOSALS[0]])), \
         patch("click.prompt", return_value="1"), \
         patch("click.echo"):
        session = LlmInteractiveSession()
        session.seed(report)
        session.run()
    assert len(session.approved_patches()) == 1

    # Second run with LLM error — patches reset to empty
    with patch("pdd.llm_invoke.llm_invoke", side_effect=RuntimeError("fail")), \
         patch("click.echo"):
        session.run()
    assert session.approved_patches() == []


def test_llm_session_returns_deep_copies() -> None:
    report = {"findings": [{"finding_id": "F-1", "summary": "test"}]}
    with patch("pdd.llm_invoke.llm_invoke", return_value=_llm_ok([_SAMPLE_PROPOSALS[0]])), \
         patch("click.prompt", return_value="1"), \
         patch("click.echo"):
        session = LlmInteractiveSession()
        session.seed(report)
        session.run()

    first = session.approved_patches()
    first[0].anchor["mutated"] = True
    second = session.approved_patches()
    assert "mutated" not in second[0].anchor


# --- make_session ---

def test_make_session_returns_pi_when_available() -> None:
    with patch("pdd.checkup_interactive_session._pi_available", return_value=True):
        session = make_session()
    assert isinstance(session, PiInteractiveSession)


def test_make_session_returns_llm_when_pi_unavailable() -> None:
    with patch("pdd.checkup_interactive_session._pi_available", return_value=False):
        session = make_session()
    assert isinstance(session, LlmInteractiveSession)
