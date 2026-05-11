"""Tests for ``pdd.metadata_tags.generate_metadata_tags``.

Test plan (each entry maps to one or more tests below):

Requirement 1 — Public entrypoint & return shape
  - test_return_dict_keys: result has all required keys and types
  - test_invalid_source_raises: source not in {'prompt-code','architecture'} -> ValueError
  - test_missing_prompt_file_returns_error: nonexistent prompt_path -> success=False with error
Requirement 2 — Tag preservation
  - test_preserve_valid_existing_tags: force=False keeps valid existing tags, only synthesizes missing
  - test_force_regenerates_all: force=True regenerates all three tags
Requirement 3 — Source 'prompt-code' (LLM synthesis)
  - test_prompt_code_calls_llm_invoke: llm_invoke is called via _synthesize helper
  - test_prompt_code_reason_truncated: reasons > 120 chars are truncated with ellipsis
  - test_prompt_code_retry_on_invalid_interface: validator failure feeds back and retries once
  - test_prompt_code_fails_after_two_invalid_attempts: success=False with errors
Requirement 4 — Source 'architecture'
  - test_architecture_source_uses_entry: lookup helper provides tags
  - test_architecture_entry_not_found: success=False with specific error message
  - test_architecture_source_cost_is_zero: cost == 0.0
Requirement 5 — Deterministic validation guardrail
  - test_validates_interface_via_helper: validate_interface_structure called for final content
Requirement 6 — Idempotent in-place merge
  - test_existing_include_directives_preserved: non-PDD lines untouched
  - test_invariant_hash_check: non-PDD content not mutated (sha256 invariant)
Requirement 7 — Output behavior
  - test_dry_run_does_not_write_returns_diff: dry_run=True populates diff and skips write
  - test_output_path_used_when_provided: writes to `output` not `prompt_path`
  - test_writes_in_place_when_no_output: writes to prompt_path
Requirement 8 — Cost tracking
  - test_cost_accumulates_from_llm_invoke: cost field reflects llm_invoke cost (prompt-code)
  - test_architecture_source_cost_is_zero: (re-uses above)
Requirement 9 — Errors handled gracefully
  - test_invalid_source_raises (ValueError)
  - test_missing_prompt_file_returns_error
  - test_architecture_entry_not_found
Requirement 10 — Logging
  - test_verbose_prints_summary_table: verbose=True triggers console output
  - test_verbose_false_no_summary: verbose=False skips console table
"""

from __future__ import annotations

import json
import os
import sys
import re
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

# Ensure project root is importable
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from pdd import metadata_tags as mt  # noqa: E402
from pdd.metadata_tags import generate_metadata_tags  # noqa: E402


# ---------------------------------------------------------------------------
# Fixtures / helpers
# ---------------------------------------------------------------------------

VALID_INTERFACE = {
    "type": "module",
    "module": {
        "functions": [
            {
                "name": "demo",
                "signature": "() -> None",
                "returns": "None",
            }
        ]
    },
}


def _valid_payload(reason="A useful module that does important things now.",
                   interface=None,
                   deps=None):
    return {
        "reason": reason,
        "interface": interface or VALID_INTERFACE,
        "dependencies": deps if deps is not None else ["llm_invoke_python.prompt"],
    }


def _write_prompt(tmp_path: Path, body: str = "% A simple prompt.\n",
                  name: str = "demo_python.prompt") -> Path:
    p = tmp_path / name
    p.write_text(body, encoding="utf-8")
    return p


def _patch_synth(payload, cost=0.001, errors=None):
    """Patch the synthesis helper to a controlled response."""
    if errors is None:
        errors = []
    return patch.object(
        mt,
        "_synthesize_tags_from_prompt_code",
        return_value=(payload, cost, errors),
    )


# ---------------------------------------------------------------------------
# Requirement 1 — Public entrypoint & return shape
# ---------------------------------------------------------------------------

def test_return_dict_keys(tmp_path):
    p = _write_prompt(tmp_path)
    with _patch_synth(_valid_payload()):
        result = generate_metadata_tags(str(p), source="prompt-code")
    assert set(result.keys()) == {
        "success", "prompt_path", "tags_added", "tags_preserved",
        "cost", "diff", "errors",
    }
    assert isinstance(result["success"], bool)
    assert isinstance(result["prompt_path"], str)
    assert isinstance(result["tags_added"], list)
    assert isinstance(result["tags_preserved"], list)
    assert isinstance(result["cost"], float)
    assert isinstance(result["diff"], str)
    assert isinstance(result["errors"], list)


def test_invalid_source_raises(tmp_path):
    p = _write_prompt(tmp_path)
    with pytest.raises(ValueError):
        generate_metadata_tags(str(p), source="invalid-source")


def test_missing_prompt_file_returns_error(tmp_path):
    missing = tmp_path / "nope.prompt"
    result = generate_metadata_tags(str(missing), source="prompt-code")
    assert result["success"] is False
    assert any("not found" in e.lower() for e in result["errors"])


# ---------------------------------------------------------------------------
# Requirement 2 — Tag preservation
# ---------------------------------------------------------------------------

def test_preserve_valid_existing_tags(tmp_path):
    """Pre-existing valid reason and interface should be preserved; only
    missing dependency synthesized."""
    iface_json = json.dumps(VALID_INTERFACE, indent=2)
    body = (
        "<pdd-reason>An existing valid reason that is long enough.</pdd-reason>\n"
        f"<pdd-interface>\n{iface_json}\n</pdd-interface>\n"
        "% Body\n"
    )
    p = _write_prompt(tmp_path, body=body)

    # Synthesis would normally be called for the missing 'dependency'.
    payload = _valid_payload(
        reason="should-not-be-used",
        deps=["llm_invoke_python.prompt"],
    )
    with _patch_synth(payload):
        result = generate_metadata_tags(str(p), source="prompt-code", force=False)

    assert result["success"] is True
    assert "reason" in result["tags_preserved"]
    assert "interface" in result["tags_preserved"]
    assert "dependency" in result["tags_added"]

    new_content = p.read_text(encoding="utf-8")
    # Existing reason value still present
    assert "An existing valid reason that is long enough." in new_content
    # New synthesized reason NOT inserted
    assert "should-not-be-used" not in new_content


def test_force_regenerates_all(tmp_path):
    body = (
        "<pdd-reason>An existing valid reason that is long enough.</pdd-reason>\n"
        "<pdd-dependency>old_dep.prompt</pdd-dependency>\n"
        "% Body\n"
    )
    p = _write_prompt(tmp_path, body=body)
    payload = _valid_payload(
        reason="Brand new regenerated reason from force-mode.",
        deps=["new_dep.prompt"],
    )
    with _patch_synth(payload):
        result = generate_metadata_tags(str(p), source="prompt-code", force=True)

    assert result["success"] is True
    assert set(result["tags_added"]) >= {"reason", "interface", "dependency"}
    assert result["tags_preserved"] == []

    new_content = p.read_text(encoding="utf-8")
    assert "Brand new regenerated reason from force-mode." in new_content
    assert "An existing valid reason that is long enough." not in new_content


# ---------------------------------------------------------------------------
# Requirement 3 — Source 'prompt-code'
# ---------------------------------------------------------------------------

def test_prompt_code_calls_llm_invoke(tmp_path):
    """The synthesis helper is invoked when tags need generation."""
    p = _write_prompt(tmp_path)
    with patch.object(mt, "_synthesize_tags_from_prompt_code") as m_synth:
        m_synth.return_value = (_valid_payload(), 0.0042, [])
        result = generate_metadata_tags(str(p), source="prompt-code")
    m_synth.assert_called_once()
    assert result["success"] is True
    assert result["cost"] == pytest.approx(0.0042)


def test_prompt_code_reason_truncated():
    """Reasons > 120 chars are truncated at word boundary + … (inside synth)."""
    # 25 words of 6 chars + space => 174 chars; > 120 but < 200 (Pydantic limit)
    long_reason = ("longer " * 25).strip()
    response = {
        "result": {
            "reason": long_reason,
            "interface": VALID_INTERFACE,
            "dependencies": [],
        },
        "cost": 0.001,
        "model_name": "m",
    }
    with patch("pdd.llm_invoke.llm_invoke", return_value=response):
        payload, _cost, errors = mt._synthesize_tags_from_prompt_code(
            prompt_text="prompt",
            code_text=None,
            existing_tags={"reason": None, "interface": None, "dependencies": []},
            needs={"reason": True, "interface": True, "dependency": True},
            strength=0.5,
            temperature=0.0,
            verbose=False,
        )
    assert payload is not None, errors
    assert payload["reason"].endswith("…")
    assert len(payload["reason"]) <= 121
    # Direct test of the truncate helper too
    truncated = mt._truncate_reason("a" * 130)
    assert truncated.endswith("…")


def test_prompt_code_retry_on_invalid_interface(tmp_path):
    """Direct test of the synthesis helper: invalid interface triggers retry."""
    p = _write_prompt(tmp_path)

    bad_interface = {"type": "module", "module": {}}  # missing functions
    good_interface = VALID_INTERFACE

    responses = [
        {
            "result": {
                "reason": "A reason that is long enough for the schema.",
                "interface": bad_interface,
                "dependencies": [],
            },
            "cost": 0.001,
            "model_name": "m",
        },
        {
            "result": {
                "reason": "A reason that is long enough for the schema.",
                "interface": good_interface,
                "dependencies": [],
            },
            "cost": 0.002,
            "model_name": "m",
        },
    ]

    with patch("pdd.llm_invoke.llm_invoke", side_effect=responses) as m_llm:
        payload, cost, errors = mt._synthesize_tags_from_prompt_code(
            prompt_text="some prompt",
            code_text=None,
            existing_tags={"reason": None, "interface": None, "dependencies": []},
            needs={"reason": True, "interface": True, "dependency": True},
            strength=0.5,
            temperature=0.0,
            verbose=False,
        )

    assert payload is not None
    assert m_llm.call_count == 2
    assert cost == pytest.approx(0.003)
    assert errors == []


def test_prompt_code_fails_after_two_invalid_attempts(tmp_path):
    bad_interface = {"type": "module", "module": {}}  # missing functions
    bad_response = {
        "result": {
            "reason": "A reason long enough to pass min_length validation here.",
            "interface": bad_interface,
            "dependencies": [],
        },
        "cost": 0.001,
        "model_name": "m",
    }
    with patch("pdd.llm_invoke.llm_invoke", side_effect=[bad_response, bad_response]):
        payload, cost, errors = mt._synthesize_tags_from_prompt_code(
            prompt_text="some prompt",
            code_text=None,
            existing_tags={"reason": None, "interface": None, "dependencies": []},
            needs={"reason": True, "interface": True, "dependency": True},
            strength=0.5,
            temperature=0.0,
            verbose=False,
        )
    assert payload is None
    assert cost == pytest.approx(0.002)
    assert errors and "validation" in errors[-1].lower()


# ---------------------------------------------------------------------------
# Requirement 4 — Source 'architecture'
# ---------------------------------------------------------------------------

def test_architecture_source_uses_entry(tmp_path):
    p = _write_prompt(tmp_path, name="arch_python.prompt")
    entry = {
        "filename": "arch_python.prompt",
        "reason": "Architecture-sourced reason text long enough now.",
        "interface": VALID_INTERFACE,
        "dependencies": ["llm_invoke_python.prompt"],
    }
    with patch.object(mt, "get_architecture_entry_for_prompt", return_value=entry), \
         patch.object(mt, "generate_tags_from_architecture", return_value="<pdd-reason>x</pdd-reason>"):
        result = generate_metadata_tags(str(p), source="architecture")
    assert result["success"] is True
    assert "reason" in result["tags_added"]
    assert "interface" in result["tags_added"]
    assert "dependency" in result["tags_added"]
    new_content = p.read_text(encoding="utf-8")
    assert "Architecture-sourced reason text long enough now." in new_content


def test_architecture_entry_not_found(tmp_path):
    p = _write_prompt(tmp_path, name="missing_python.prompt")
    with patch.object(mt, "get_architecture_entry_for_prompt", return_value=None):
        result = generate_metadata_tags(str(p), source="architecture")
    assert result["success"] is False
    assert any(
        "architecture entry not found for missing_python.prompt" in e
        for e in result["errors"]
    )


def test_architecture_source_cost_is_zero(tmp_path):
    p = _write_prompt(tmp_path, name="arch_python.prompt")
    entry = {
        "filename": "arch_python.prompt",
        "reason": "Architecture-sourced reason text long enough now.",
        "interface": VALID_INTERFACE,
        "dependencies": ["dep.prompt"],
    }
    with patch.object(mt, "get_architecture_entry_for_prompt", return_value=entry), \
         patch.object(mt, "generate_tags_from_architecture", return_value="<pdd-reason>x</pdd-reason>"):
        result = generate_metadata_tags(str(p), source="architecture")
    assert result["cost"] == 0.0


# ---------------------------------------------------------------------------
# Requirement 5 — Deterministic validation guardrail
# ---------------------------------------------------------------------------

def test_validates_interface_via_helper(tmp_path):
    """Final-content validation calls validate_interface_structure."""
    p = _write_prompt(tmp_path)
    with _patch_synth(_valid_payload()), \
         patch.object(mt, "validate_interface_structure",
                      wraps=mt.validate_interface_structure) as m_val:
        result = generate_metadata_tags(str(p), source="prompt-code")
    assert result["success"] is True
    # Called at least once during final validation
    assert m_val.call_count >= 1


# ---------------------------------------------------------------------------
# Requirement 6 — Idempotent in-place merge
# ---------------------------------------------------------------------------

def test_existing_include_directives_preserved(tmp_path):
    body = (
        "% Role\nYou are X.\n\n"
        "<include>other.prompt</include>\n"
        "% More prose here.\n"
    )
    p = _write_prompt(tmp_path, body=body)
    with _patch_synth(_valid_payload()):
        result = generate_metadata_tags(str(p), source="prompt-code")
    assert result["success"] is True
    new_content = p.read_text(encoding="utf-8")
    assert "<include>other.prompt</include>" in new_content
    assert "% Role" in new_content
    assert "% More prose here." in new_content


def test_invariant_hash_check(tmp_path):
    body = "% Role\nA prose section.\n\n% Requirements\n- Do things.\n"
    p = _write_prompt(tmp_path, body=body)
    original_hash = mt._content_invariant_hash(body)
    with _patch_synth(_valid_payload()):
        generate_metadata_tags(str(p), source="prompt-code")
    new_content = p.read_text(encoding="utf-8")
    assert mt._content_invariant_hash(new_content) == original_hash


# ---------------------------------------------------------------------------
# Requirement 7 — Output behavior
# ---------------------------------------------------------------------------

def test_dry_run_does_not_write_returns_diff(tmp_path):
    body = "% Original content.\n"
    p = _write_prompt(tmp_path, body=body)
    with _patch_synth(_valid_payload()):
        result = generate_metadata_tags(str(p), source="prompt-code", dry_run=True)
    assert result["success"] is True
    assert result["diff"]  # non-empty
    assert "<pdd-reason>" in result["diff"]
    # File on disk unchanged
    assert p.read_text(encoding="utf-8") == body


def test_output_path_used_when_provided(tmp_path):
    body = "% Body\n"
    p = _write_prompt(tmp_path, body=body)
    out = tmp_path / "elsewhere.prompt"
    with _patch_synth(_valid_payload()):
        result = generate_metadata_tags(
            str(p), source="prompt-code", output=str(out)
        )
    assert result["success"] is True
    # Original is untouched
    assert p.read_text(encoding="utf-8") == body
    # Output file written
    assert out.exists()
    assert "<pdd-reason>" in out.read_text(encoding="utf-8")


def test_writes_in_place_when_no_output(tmp_path):
    p = _write_prompt(tmp_path, body="% Body\n")
    with _patch_synth(_valid_payload()):
        result = generate_metadata_tags(str(p), source="prompt-code")
    assert result["success"] is True
    assert "<pdd-reason>" in p.read_text(encoding="utf-8")


# ---------------------------------------------------------------------------
# Requirement 8 — Cost tracking
# ---------------------------------------------------------------------------

def test_cost_accumulates_from_llm_invoke(tmp_path):
    p = _write_prompt(tmp_path)
    with _patch_synth(_valid_payload(), cost=0.0123):
        result = generate_metadata_tags(str(p), source="prompt-code")
    assert result["cost"] == pytest.approx(0.0123)


# ---------------------------------------------------------------------------
# Requirement 10 — Logging
# ---------------------------------------------------------------------------

def test_verbose_prints_summary_table(tmp_path, capsys):
    p = _write_prompt(tmp_path)
    with _patch_synth(_valid_payload()):
        generate_metadata_tags(str(p), source="prompt-code", verbose=True)
    captured = capsys.readouterr()
    out = captured.out + captured.err
    assert "PDD Metadata Tags Summary" in out


def test_verbose_false_no_summary(tmp_path, capsys):
    p = _write_prompt(tmp_path)
    with _patch_synth(_valid_payload()):
        generate_metadata_tags(str(p), source="prompt-code", verbose=False)
    captured = capsys.readouterr()
    out = captured.out + captured.err
    assert "PDD Metadata Tags Summary" not in out
