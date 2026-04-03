"""
Tests for cross-step consistency in bug workflow prompts.

Two categories:
1. Unit tests (no LLM calls) — verify prompt template formatting and context wiring
2. Integration tests (@pytest.mark.integration) — verify LLM actually follows
   the scope-expansion instructions with a real API call

Issue #577: Cross-step mock consistency
Issue #1071: Proposed fix validation / scope expansion defense
"""
from pathlib import Path
from textwrap import dedent
import os
import pytest

PROMPTS_DIR = Path(__file__).parent.parent / "pdd" / "prompts"


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def step6_content() -> str:
    path = PROMPTS_DIR / "agentic_bug_step6_root_cause_LLM.prompt"
    assert path.exists()
    return path.read_text()

@pytest.fixture
def step8_content() -> str:
    path = PROMPTS_DIR / "agentic_bug_step8_test_plan_LLM.prompt"
    assert path.exists()
    return path.read_text()

@pytest.fixture
def step9_content() -> str:
    path = PROMPTS_DIR / "agentic_bug_step9_generate_LLM.prompt"
    assert path.exists()
    return path.read_text()

@pytest.fixture
def step10_content() -> str:
    path = PROMPTS_DIR / "agentic_bug_step10_verify_LLM.prompt"
    assert path.exists()
    return path.read_text()


# ---------------------------------------------------------------------------
# Unit tests: Prompt template formatting (no LLM calls)
# These verify that the prompt templates can be loaded, preprocessed, and
# formatted with realistic context without errors — proving the wiring works.
# ---------------------------------------------------------------------------

class TestStep6TemplateFormatting:
    """Step 6 prompt formats correctly with scope-expansion context."""

    def test_step6_template_formats_with_issue_containing_proposed_fix(self, step6_content: str):
        """Verify Step 6 template accepts context with a proposed fix in the issue body."""
        # Collapse double-curlies then substitute (same as orchestrator)
        processed = step6_content.replace("{{", "{").replace("}}", "}")

        context = {
            "issue_url": "https://github.com/owner/repo/issues/999",
            "issue_content": dedent("""\
                ## Bug
                The TIMEOUTS dict is missing entries for steps 11 and 12.
                ## Proposed Fix
                Add entries: 11: 2000.0, 12: 240.0
            """),
            "repo_owner": "owner",
            "repo_name": "repo",
            "issue_number": "999",
            "issue_author": "testuser",
            "step1_output": "No duplicates found",
            "step2_output": "Confirmed bug",
            "step3_output": "FAST_TRACK: missing timeout entries",
            "step4_output": "Step 4 skipped (fast-track)",
            "step5_output": "Step 5 skipped (fast-track)",
        }
        for key, value in context.items():
            processed = processed.replace(f"{{{key}}}", str(value))

        # The formatted prompt should contain the issue's proposed fix text
        assert "Proposed Fix" in processed
        assert "steps 11 and 12" in processed
        # And should contain the Proposed Fix Validation instruction
        assert "Proposed Fix Validation" in processed


class TestStep8TemplateFormatting:
    """Step 8 prompt formats correctly with Step 6 scope-expansion output."""

    def test_step8_template_includes_step6_output_with_scope_expansion(self, step8_content: str):
        """Verify Step 8 sees Step 6's SCOPE_EXPANSION in its formatted context."""
        processed = step8_content.replace("{{", "{").replace("}}", "}")

        step6_output_with_expansion = dedent("""\
            ## Step 6: Root Cause Analysis
            ### Proposed Fix Validation
            - **Scope classification:** SCOPE_EXPANSION
            - **Issue-proposed scope:** steps 11, 12
            - **Step 6 full scope:** steps 4-12 (all shifted due to api_research insertion)
            - **Expansion items:** steps 4, 5, 6, 7, 8, 9, 10
        """)

        context = {
            "issue_url": "https://github.com/owner/repo/issues/999",
            "issue_content": "Bug: missing timeout entries for steps 11-12",
            "repo_owner": "owner",
            "repo_name": "repo",
            "issue_number": "999",
            "step1_output": "No duplicates",
            "step2_output": "Confirmed",
            "step3_output": "Fast-track",
            "step4_output": "Skipped",
            "step5_output": "Skipped",
            "step6_output": step6_output_with_expansion,
            "step7_output": "DEFECT_TYPE: code",
            "fix_locations": "pdd/agentic_bug_orchestrator.py",
        }
        for key, value in context.items():
            processed = processed.replace(f"{{{key}}}", str(value))

        # Step 8 should see Step 6's SCOPE_EXPANSION and expansion items
        assert "SCOPE_EXPANSION" in processed
        assert "steps 4, 5, 6, 7, 8, 9, 10" in processed


class TestStep10TemplateFormatting:
    """Step 10 prompt uses WARNING (not FAIL) for scope gaps."""

    def test_step10_scope_check_uses_warning_not_fail(self, step10_content: str):
        """Step 10 should warn about incomplete scope, not hard-stop the workflow."""
        # The scope completeness section should use WARNING
        content_lower = step10_content.lower()
        # Find the scope completeness section
        scope_section_start = content_lower.find("scope completeness")
        assert scope_section_start != -1, "Step 10 must have a scope completeness verification section"

        # Extract just the scope section (next ~500 chars)
        scope_section = content_lower[scope_section_start:scope_section_start + 800]

        assert "warning" in scope_section, (
            "Step 10 scope completeness section must use WARNING, not FAIL, "
            "to avoid false-positive hard stops from LLM-to-LLM parsing."
        )
        # Must NOT have a FAIL for scope issues (existing FAILs for structural
        # tests and mock contradictions are fine — they're different checks)
        assert "**fail:" not in scope_section and "report: fail" not in scope_section, (
            "Step 10 scope completeness section must NOT use FAIL — "
            "false-positive risk from LLM parsing structured sections is too high."
        )


# ---------------------------------------------------------------------------
# Existing unit tests (from issue #577) — cross-step mock consistency
# ---------------------------------------------------------------------------

class TestStep8CrossStepConsistency:
    """Step 8 (test plan) must instruct cross-referencing mocks against Steps 4-6."""

    def test_prompt_requires_mock_validation_against_prior_steps(self, step8_content: str) -> None:
        content_lower = step8_content.lower()
        has_instruction = any([
            "cross-reference" in content_lower and "steps 4" in content_lower,
            "cross-validate" in content_lower and "investigation" in content_lower,
            "consistent with" in content_lower and ("step 4" in content_lower or "step 5" in content_lower or "step 6" in content_lower),
        ])
        assert has_instruction, (
            "Step 8 prompt must instruct cross-referencing planned mocks/assumptions "
            "against investigation findings from Steps 4-6."
        )

    def test_prompt_requires_contradiction_resolution(self, step8_content: str) -> None:
        content_lower = step8_content.lower()
        has_instruction = "contradict" in content_lower and ("redesign" in content_lower or "document" in content_lower or "resolution" in content_lower)
        assert has_instruction, (
            "Step 8 prompt must instruct resolving contradictions between test "
            "assumptions and investigation findings, not silently proceeding."
        )


class TestStep9MockAccuracyValidation:
    """Step 9 (generate test) must instruct validating mocks against investigation."""

    def test_prompt_requires_mock_consistency_with_investigation(self, step9_content: str) -> None:
        content_lower = step9_content.lower()
        has_instruction = any([
            "re-read steps 4" in content_lower,
            "verify" in content_lower and "mock" in content_lower and ("step 4" in content_lower or "step 5" in content_lower or "step 6" in content_lower),
            "mock" in content_lower and "investigation findings" in content_lower,
        ])
        assert has_instruction, (
            "Step 9 prompt must instruct verifying mock responses against "
            "investigation findings from Steps 4-6."
        )

    def test_prompt_flags_impossible_mocks(self, step9_content: str) -> None:
        content_lower = step9_content.lower()
        has_instruction = any([
            "flag" in content_lower and "impossible" in content_lower,
            "signal" in content_lower and "fix direction" in content_lower,
            "better to flag" in content_lower,
        ])
        assert has_instruction, (
            "Step 9 prompt must instruct flagging when no mock can be both "
            "consistent with investigation AND demonstrate the fix working."
        )


class TestStep10CrossValidation:
    """Step 10 (verify) must cross-validate test mocks against investigation."""

    def test_prompt_requires_mock_vs_investigation_check(self, step10_content: str) -> None:
        content_lower = step10_content.lower()
        has_instruction = any([
            "cross-validate" in content_lower and ("step 4" in content_lower or "step 5" in content_lower or "step 6" in content_lower),
            "mock" in content_lower and "contradict" in content_lower and "investigation" in content_lower,
            "verify" in content_lower and "mock" in content_lower and "real" in content_lower and "behavior" in content_lower,
        ])
        assert has_instruction, (
            "Step 10 prompt must instruct cross-validating test mocks against "
            "investigation findings from Steps 4-6."
        )

    def test_prompt_can_fail_for_assumption_mismatch(self, step10_content: str) -> None:
        has_fail_signal = "mock assumptions contradict investigation" in step10_content.lower()
        assert has_fail_signal, (
            "Step 10 prompt must define a FAIL condition for when mock assumptions "
            "contradict investigation findings (enables orchestrator hard stop)."
        )


# ---------------------------------------------------------------------------
# Integration tests: Real LLM calls (issue #1071)
# These verify the LLM actually follows the scope-expansion instructions.
# Marked @pytest.mark.integration — skipped in CI, run on demand.
# ---------------------------------------------------------------------------

def has_llm_credentials() -> bool:
    """Check if any LLM credentials are available for integration tests."""
    if os.environ.get("ANTHROPIC_API_KEY"):
        return True
    project = os.environ.get("VERTEXAI_PROJECT", "")
    location = os.environ.get("VERTEXAI_LOCATION", "")
    return bool(project and location)


@pytest.mark.integration
@pytest.mark.skipif(not has_llm_credentials(), reason="No LLM credentials available")
class TestStep6ScopeExpansionIntegration:
    """Integration: verify Step 6 LLM produces SCOPE_EXPANSION for incomplete proposed fixes."""

    def test_step6_detects_incomplete_proposed_fix(self, tmp_path):
        """Given an issue with a partial fix, Step 6 should classify as SCOPE_EXPANSION."""
        from pdd.agentic_common import run_agentic_task

        template = (PROMPTS_DIR / "agentic_bug_step6_root_cause_LLM.prompt").read_text()
        processed = template.replace("{{", "{").replace("}}", "}")

        # Craft context: issue proposes fixing only 2 of 5 known problems
        context = {
            "issue_url": "https://github.com/test/repo/issues/1",
            "issue_content": dedent("""\
                ## Bug
                The `COLORS` dict has entries for 'red' and 'blue' but is missing
                'green', 'yellow', and 'purple'. Only 'red' and 'blue' work.

                ## Proposed Fix
                Add the missing 'green' entry to the COLORS dict:
                ```python
                COLORS['green'] = '#00ff00'
                ```
                This should fix the issue.
            """),
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": "1",
            "issue_author": "testuser",
            "step1_output": "No duplicates found.",
            "step2_output": "Confirmed bug — COLORS dict is incomplete.",
            "step3_output": "FAST_TRACK: Issue provides file path and fix snippet.",
            "step4_output": "Step 4 skipped (fast-track): COLORS dict missing entries.",
            "step5_output": "Step 5 skipped (fast-track): COLORS dict missing entries.",
        }
        for key, value in context.items():
            processed = processed.replace(f"{{{key}}}", str(value))

        # Run the formatted prompt through a real LLM
        # Use quiet mode and short timeout — we just need the classification
        success, output, cost, model = run_agentic_task(
            instruction=processed,
            cwd=tmp_path,
            quiet=True,
            label="test-step6-scope-expansion",
            timeout=120.0,
        )

        assert success, f"Step 6 LLM call failed: {output[:500]}"

        output_lower = output.lower()

        # The LLM should detect that the proposed fix only covers 'green'
        # but the bug also affects 'yellow' and 'purple'
        has_scope_expansion = (
            "scope_expansion" in output_lower
            or "scope expansion" in output_lower
            or ("partial" in output_lower and "proposed fix" in output_lower)
        )
        assert has_scope_expansion, (
            f"Step 6 should classify the incomplete proposed fix as SCOPE_EXPANSION "
            f"(or similar), but output did not contain scope expansion classification.\n"
            f"Output (first 1000 chars): {output[:1000]}"
        )

        # The LLM should identify the missing items (yellow, purple)
        has_expansion_items = (
            "yellow" in output_lower
            or "purple" in output_lower
        )
        assert has_expansion_items, (
            f"Step 6 should list expansion items (yellow, purple) that the proposed "
            f"fix missed, but they were not found in the output.\n"
            f"Output (first 1000 chars): {output[:1000]}"
        )
