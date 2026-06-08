"""
Tests for the lean prompt mode research harness.

All tests are deterministic and require no API key or network access.
They use the frozen fixtures under fixtures/ or synthetic in-process prompts.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

# Make harness importable without installing
_HARNESS_DIR = Path(__file__).resolve().parent.parent
if str(_HARNESS_DIR) not in sys.path:
    sys.path.insert(0, str(_HARNESS_DIR))

from lean_prompt import (
    _parse_sections,
    _prune,
    _compute_structural_floor,
    run,
    Section,
    _REQUIRED_XML_TAGS,
)

# ---------------------------------------------------------------------------
# Fixture paths
# ---------------------------------------------------------------------------

FIXTURES = _HARNESS_DIR / "fixtures"
SCHEMAS = _HARNESS_DIR / "schemas"
CURRENT_FIXTURE = FIXTURES / "current_prompt.txt"
LEAN_FIXTURE = FIXTURES / "lean_prompt.txt"
POLICY_FIXTURE = FIXTURES / "prompt_policy.json"
AUDIT_FIXTURE = FIXTURES / "prompt_token_audit.json"

# ---------------------------------------------------------------------------
# Synthetic prompts for unit tests
# ---------------------------------------------------------------------------

_MINIMAL_PROMPT = """\
% You are an expert Python engineer. Implement foo.

<pdd-reason>Does foo.</pdd-reason>

<responsibility>
Implements foo.
</responsibility>

<contract_rules>
R1 - Always return something.
For every call, the system MUST return a value.
</contract_rules>

<capabilities>
- MAY read inputs.
- MUST NOT write to disk.
</capabilities>

<output_files>
pdd/foo.py
</output_files>

<verifier>
pytest tests/test_foo.py -v
</verifier>

% Requirements

1. Function: foo() -> str
2. Return "ok".

% Deliverables

Generate the implementation only.
"""

_PROMPT_WITH_REMOVABLE = """\
% You are an expert Python engineer. Implement bar.

<include>context/python_preamble.prompt</include>

<pdd-reason>Does bar.</pdd-reason>

<responsibility>
Implements bar.
</responsibility>

% Role & Scope

This module is the entry point for bar operations. It was introduced to centralise
processing that was previously scattered across multiple call sites.

% Background

Historically, bar logic was duplicated in three places. This module unifies them.

<contract_rules>
R1 - Must return valid result.
For every call, the system MUST return a BarResult.
</contract_rules>

<capabilities>
- MAY read input data.
- MUST NOT call external services.
</capabilities>

<output_files>
pdd/bar.py
</output_files>

<verifier>
pytest tests/test_bar.py -v
</verifier>

% Requirements

1. Function: bar(x) -> BarResult
2. Validate x is non-empty.

% Instructions

- Keep module stateless.
- Do not implement the BarResult class here.

% Deliverables

Generate the implementation only.
"""

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _load_schema(name: str) -> dict:
    return json.loads((SCHEMAS / name).read_text(encoding="utf-8"))


def _validate_schema(instance: dict, schema: dict) -> None:
    """Validate a dict against a JSON Schema using jsonschema if available."""
    try:
        import jsonschema
        jsonschema.validate(instance=instance, schema=schema)
    except ImportError:
        # jsonschema not installed — perform manual required-field checks
        for key in schema.get("required", []):
            assert key in instance, f"Missing required field: {key}"


# ---------------------------------------------------------------------------
# Section parsing tests
# ---------------------------------------------------------------------------

class TestSectionParsing:
    def test_required_xml_tags_parsed(self):
        sections = _parse_sections(_MINIMAL_PROMPT)
        ids = [s.section_id for s in sections]
        # contract_rules, capabilities, output_files, verifier should appear
        contents = " ".join(s.content for s in sections)
        assert "<contract_rules>" in contents
        assert "<capabilities>" in contents
        assert "<output_files>" in contents
        assert "<verifier>" in contents

    def test_pct_role_scope_detected_as_removable(self):
        sections = _parse_sections(_PROMPT_WITH_REMOVABLE)
        removable = [s for s in sections if not s.required]
        reasons = [s.removal_reason for s in removable]
        assert "workflow_narrative" in reasons

    def test_pct_background_detected_as_removable(self):
        sections = _parse_sections(_PROMPT_WITH_REMOVABLE)
        removable = [s for s in sections if not s.required]
        reasons = [s.removal_reason for s in removable]
        assert "explanatory_boilerplate" in reasons

    def test_preamble_include_detected_as_removable(self):
        sections = _parse_sections(_PROMPT_WITH_REMOVABLE)
        removable = [s for s in sections if not s.required]
        # The preamble include should appear as either a section with 'preamble' in
        # its id or with reason shared_preamble_boilerplate
        assert any(
            "preamble" in s.section_id or s.removal_reason == "shared_preamble_boilerplate"
            for s in removable
        ), f"No preamble section found. Removable: {[(s.section_id, s.removal_reason) for s in removable]}"

    def test_requirements_section_is_required(self):
        sections = _parse_sections(_MINIMAL_PROMPT)
        req_sections = [s for s in sections if s.required]
        req_content = " ".join(s.content for s in req_sections)
        assert "% Requirements" in req_content

    def test_deliverables_section_is_required(self):
        sections = _parse_sections(_MINIMAL_PROMPT)
        req_sections = [s for s in sections if s.required]
        req_content = " ".join(s.content for s in req_sections)
        assert "% Deliverables" in req_content


# ---------------------------------------------------------------------------
# Contamination check tests
# ---------------------------------------------------------------------------

class TestContaminationCheck:
    def test_contaminated_instructions_section_preserved(self):
        """Instructions section containing MUST NOT is not pruned."""
        prompt = _MINIMAL_PROMPT + "\n% Instructions\n\n- MUST NOT call external APIs.\n"
        sections = _parse_sections(prompt)
        instructions = [s for s in sections if "instructions" in s.section_id]
        assert instructions, "instructions section should be parsed"
        assert instructions[0].required, (
            "instructions section containing MUST NOT should be preserved"
        )

    def test_clean_instructions_section_is_removable(self):
        prompt = _MINIMAL_PROMPT + "\n% Instructions\n\n- Keep module stateless.\n"
        sections = _parse_sections(prompt)
        instructions = [s for s in sections if "instructions" in s.section_id]
        assert instructions, "instructions section should be parsed"
        assert not instructions[0].required, (
            "instructions section without required markers should be removable"
        )


# ---------------------------------------------------------------------------
# Pruner invariant tests
# ---------------------------------------------------------------------------

class TestPrunerInvariants:
    def _run_prune(self, prompt: str) -> tuple[str, list[dict]]:
        sections = _parse_sections(prompt)
        result = _prune(sections)
        return result.lean_text, result.removed_sections

    def test_contract_rules_preserved(self):
        lean, _ = self._run_prune(_PROMPT_WITH_REMOVABLE)
        assert "<contract_rules>" in lean

    def test_capabilities_preserved(self):
        lean, _ = self._run_prune(_PROMPT_WITH_REMOVABLE)
        assert "<capabilities>" in lean

    def test_output_files_preserved(self):
        lean, _ = self._run_prune(_PROMPT_WITH_REMOVABLE)
        assert "<output_files>" in lean

    def test_verifier_preserved(self):
        lean, _ = self._run_prune(_PROMPT_WITH_REMOVABLE)
        assert "<verifier>" in lean

    def test_responsibility_preserved(self):
        lean, _ = self._run_prune(_PROMPT_WITH_REMOVABLE)
        assert "<responsibility>" in lean

    def test_role_scope_removed(self):
        lean, _ = self._run_prune(_PROMPT_WITH_REMOVABLE)
        assert "% Role & Scope" not in lean

    def test_background_removed(self):
        lean, _ = self._run_prune(_PROMPT_WITH_REMOVABLE)
        assert "% Background" not in lean

    def test_removed_sections_list_populated(self):
        _, removed = self._run_prune(_PROMPT_WITH_REMOVABLE)
        assert len(removed) >= 2  # at minimum: role_scope, background

    def test_removed_sections_have_required_keys(self):
        _, removed = self._run_prune(_PROMPT_WITH_REMOVABLE)
        for entry in removed:
            assert "section_id" in entry
            assert "reason" in entry
            assert "token_delta" in entry

    def test_structural_floor_le_lean(self):
        sections = _parse_sections(_PROMPT_WITH_REMOVABLE)
        result = _prune(sections)
        lean_tokens = len(result.lean_text) // 4  # rough approx for test
        floor_tokens = _compute_structural_floor(sections, "claude-sonnet-4-20250514")
        assert floor_tokens <= lean_tokens + 10  # allow small approximation error


# ---------------------------------------------------------------------------
# Default mode regression (current mode must not change prompt)
# ---------------------------------------------------------------------------

class TestDefaultMode:
    def test_current_mode_leaves_prompt_unchanged(self, tmp_path):
        prompt_file = tmp_path / "test_module.prompt"
        prompt_file.write_text(_PROMPT_WITH_REMOVABLE, encoding="utf-8")

        result = run(prompt_file=prompt_file, mode="current", out_dir=tmp_path)

        assert result["lean_text"] == _PROMPT_WITH_REMOVABLE, (
            "current mode must return the prompt unchanged"
        )

    def test_current_mode_policy_has_no_removed_sections(self, tmp_path):
        prompt_file = tmp_path / "test_module.prompt"
        prompt_file.write_text(_PROMPT_WITH_REMOVABLE, encoding="utf-8")

        result = run(prompt_file=prompt_file, mode="current", out_dir=tmp_path)

        policy = json.loads(result["policy_path"].read_text(encoding="utf-8"))
        assert policy["mode"] == "current"
        assert policy["removed_sections"] == []

    def test_current_mode_audit_lean_eq_current(self, tmp_path):
        prompt_file = tmp_path / "test_module.prompt"
        prompt_file.write_text(_MINIMAL_PROMPT, encoding="utf-8")

        result = run(prompt_file=prompt_file, mode="current", out_dir=tmp_path)

        audit = json.loads(result["audit_path"].read_text(encoding="utf-8"))
        task = audit["tasks"][0]
        assert task["current_tokens"] == task["lean_tokens"]
        assert task["ratio"] == pytest.approx(1.0, abs=0.01)


# ---------------------------------------------------------------------------
# Lean mode output tests
# ---------------------------------------------------------------------------

class TestLeanMode:
    def test_lean_mode_reduces_tokens(self, tmp_path):
        prompt_file = tmp_path / "bar.prompt"
        prompt_file.write_text(_PROMPT_WITH_REMOVABLE, encoding="utf-8")

        result = run(prompt_file=prompt_file, mode="lean", out_dir=tmp_path)

        assert result["audit"]["lean_tokens"] < result["audit"]["current_tokens"], (
            "lean mode should reduce token count for a prompt with removable sections"
        )

    def test_lean_mode_ratio_lt_one(self, tmp_path):
        prompt_file = tmp_path / "bar.prompt"
        prompt_file.write_text(_PROMPT_WITH_REMOVABLE, encoding="utf-8")

        result = run(prompt_file=prompt_file, mode="lean", out_dir=tmp_path)

        assert result["audit"]["ratio"] < 1.0

    def test_lean_mode_structural_floor_le_lean_tokens(self, tmp_path):
        prompt_file = tmp_path / "bar.prompt"
        prompt_file.write_text(_PROMPT_WITH_REMOVABLE, encoding="utf-8")

        result = run(prompt_file=prompt_file, mode="lean", out_dir=tmp_path)

        assert result["audit"]["structural_floor_tokens"] <= result["audit"]["lean_tokens"]

    def test_lean_mode_emits_output_file(self, tmp_path):
        prompt_file = tmp_path / "bar.prompt"
        prompt_file.write_text(_MINIMAL_PROMPT, encoding="utf-8")

        result = run(prompt_file=prompt_file, mode="lean", out_dir=tmp_path)

        assert result["lean_out"].exists()
        assert result["policy_path"].exists()
        assert result["audit_path"].exists()

    def test_lean_mode_policy_mode_field(self, tmp_path):
        prompt_file = tmp_path / "bar.prompt"
        prompt_file.write_text(_PROMPT_WITH_REMOVABLE, encoding="utf-8")

        result = run(prompt_file=prompt_file, mode="lean", out_dir=tmp_path)

        policy = json.loads(result["policy_path"].read_text(encoding="utf-8"))
        assert policy["mode"] == "lean"
        assert policy["compression_method"] == "deterministic_section_pruning"


# ---------------------------------------------------------------------------
# JSON schema validation tests
# ---------------------------------------------------------------------------

class TestSchemaValidation:
    def test_policy_schema_valid(self, tmp_path):
        prompt_file = tmp_path / "bar.prompt"
        prompt_file.write_text(_PROMPT_WITH_REMOVABLE, encoding="utf-8")
        result = run(prompt_file=prompt_file, mode="lean", out_dir=tmp_path)
        policy = json.loads(result["policy_path"].read_text(encoding="utf-8"))
        schema = _load_schema("prompt_policy.schema.json")
        _validate_schema(policy, schema)

    def test_audit_schema_valid(self, tmp_path):
        prompt_file = tmp_path / "bar.prompt"
        prompt_file.write_text(_PROMPT_WITH_REMOVABLE, encoding="utf-8")
        result = run(prompt_file=prompt_file, mode="lean", out_dir=tmp_path)
        audit = json.loads(result["audit_path"].read_text(encoding="utf-8"))
        schema = _load_schema("prompt_token_audit.schema.json")
        _validate_schema(audit, schema)

    def test_fixture_policy_schema_valid(self):
        if not POLICY_FIXTURE.exists():
            pytest.skip("fixture not present")
        policy = json.loads(POLICY_FIXTURE.read_text(encoding="utf-8"))
        schema = _load_schema("prompt_policy.schema.json")
        _validate_schema(policy, schema)

    def test_fixture_audit_schema_valid(self):
        if not AUDIT_FIXTURE.exists():
            pytest.skip("fixture not present")
        audit = json.loads(AUDIT_FIXTURE.read_text(encoding="utf-8"))
        schema = _load_schema("prompt_token_audit.schema.json")
        _validate_schema(audit, schema)


# ---------------------------------------------------------------------------
# Golden fixture regression tests
# ---------------------------------------------------------------------------

class TestGoldenFixtures:
    def test_fixtures_exist(self):
        for path in [CURRENT_FIXTURE, LEAN_FIXTURE, POLICY_FIXTURE, AUDIT_FIXTURE]:
            assert path.exists(), f"Fixture missing: {path}"

    def test_lean_fixture_preserves_contract_rules(self):
        if not LEAN_FIXTURE.exists():
            pytest.skip("fixture not present")
        lean = LEAN_FIXTURE.read_text(encoding="utf-8")
        assert "<contract_rules>" in lean

    def test_lean_fixture_preserves_capabilities(self):
        if not LEAN_FIXTURE.exists():
            pytest.skip("fixture not present")
        lean = LEAN_FIXTURE.read_text(encoding="utf-8")
        assert "<capabilities>" in lean

    def test_lean_fixture_preserves_output_files(self):
        if not LEAN_FIXTURE.exists():
            pytest.skip("fixture not present")
        lean = LEAN_FIXTURE.read_text(encoding="utf-8")
        assert "<output_files>" in lean

    def test_lean_fixture_preserves_verifier(self):
        if not LEAN_FIXTURE.exists():
            pytest.skip("fixture not present")
        lean = LEAN_FIXTURE.read_text(encoding="utf-8")
        assert "<verifier>" in lean

    def test_lean_fixture_shorter_than_current(self):
        if not (CURRENT_FIXTURE.exists() and LEAN_FIXTURE.exists()):
            pytest.skip("fixtures not present")
        current = CURRENT_FIXTURE.read_text(encoding="utf-8")
        lean = LEAN_FIXTURE.read_text(encoding="utf-8")
        assert len(lean) < len(current), (
            "Lean fixture should be shorter than current fixture"
        )

    def test_fixture_audit_ratio_lt_one(self):
        if not AUDIT_FIXTURE.exists():
            pytest.skip("fixture not present")
        audit = json.loads(AUDIT_FIXTURE.read_text(encoding="utf-8"))
        ratio = audit["aggregate"]["aggregate_ratio"]
        assert ratio < 1.0, f"Expected ratio < 1.0, got {ratio}"

    def test_fixture_audit_floor_le_lean(self):
        if not AUDIT_FIXTURE.exists():
            pytest.skip("fixture not present")
        audit = json.loads(AUDIT_FIXTURE.read_text(encoding="utf-8"))
        agg = audit["aggregate"]
        assert agg["structural_floor_tokens"] <= agg["total_lean_tokens"]
