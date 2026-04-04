"""
Tests for cross-step consistency in bug workflow prompts.

Two categories:
1. Unit tests (no LLM calls) — verify orchestrator parser and prompt placeholder wiring
2. Integration tests (@pytest.mark.integration) — skipped in CI

Issue #577: Cross-step mock consistency
Issue #1071: Proposed fix validation / scope expansion defense
"""
from pathlib import Path
from textwrap import dedent
from unittest.mock import patch, MagicMock
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
# Unit tests: _parse_expansion_items helper (orchestrator)
# ---------------------------------------------------------------------------

class TestParseExpansionItems:
    """Unit tests for _parse_expansion_items helper."""

    def test_parses_single_item(self):
        """EXPANSION_ITEMS with one item returns it."""
        from pdd.agentic_bug_orchestrator import _parse_expansion_items
        output = "Some analysis\nEXPANSION_ITEMS: step 6 wrong timeout\nMore text"
        assert _parse_expansion_items(output) == "step 6 wrong timeout"

    def test_parses_multiple_items(self):
        """EXPANSION_ITEMS with comma-separated items returns full string."""
        from pdd.agentic_bug_orchestrator import _parse_expansion_items
        output = "EXPANSION_ITEMS: step 6 timeout, step 7 timeout, step 8 timeout"
        result = _parse_expansion_items(output)
        assert "step 6 timeout" in result
        assert "step 7 timeout" in result
        assert "step 8 timeout" in result

    def test_returns_none_when_no_marker(self):
        """No EXPANSION_ITEMS marker returns 'none'."""
        from pdd.agentic_bug_orchestrator import _parse_expansion_items
        output = "Root cause found. FIX_LOCATIONS: pdd/foo.py"
        assert _parse_expansion_items(output) == "none"

    def test_returns_none_for_scope_match(self):
        """EXPANSION_ITEMS: none returns 'none' (SCOPE_MATCH case)."""
        from pdd.agentic_bug_orchestrator import _parse_expansion_items
        output = "EXPANSION_ITEMS: none"
        assert _parse_expansion_items(output) == "none"

    def test_strips_whitespace(self):
        """Leading/trailing whitespace in the value is stripped."""
        from pdd.agentic_bug_orchestrator import _parse_expansion_items
        output = "EXPANSION_ITEMS:   step 6 timeout, step 7 timeout   "
        result = _parse_expansion_items(output)
        assert result == "step 6 timeout, step 7 timeout"


# ---------------------------------------------------------------------------
# Unit tests: Orchestrator injects step6_expansion_items into context
# ---------------------------------------------------------------------------

class TestExpansionItemsFlowToDownstreamSteps:
    """Orchestrator parses EXPANSION_ITEMS from Step 6 and injects into Steps 8/9/10."""

    STEP6_WITH_EXPANSION = (
        "## Root Cause\nBUG_STEP_TIMEOUTS dict has stale step numbers.\n\n"
        "FIX_LOCATIONS: pdd/agentic_bug_orchestrator.py\n"
        "EXPANSION_ITEMS: step 6 timeout wrong, step 7 timeout wrong, step 8 timeout wrong\n"
    )

    STEP6_SCOPE_MATCH = (
        "## Root Cause\nSingle function missing guard.\n\n"
        "FIX_LOCATIONS: pdd/agentic_common.py\n"
        "EXPANSION_ITEMS: none\n"
    )

    def _make_base_template(self) -> str:
        """Minimal template with both fix_locations and step6_expansion_items placeholders."""
        return (
            "Issue {issue_number}.\n"
            "<step6_output>{step6_output}</step6_output>\n"
            "<fix_locations>{fix_locations}</fix_locations>\n"
            "<step6_expansion_items>{step6_expansion_items}</step6_expansion_items>\n"
        )

    def _run_orchestrator_to_step8(self, tmp_path, step6_output: str):
        """Run orchestrator through step 6 and return (captured, exc).

        exc is set if the orchestrator raised before completing normally; the
        tests include it in assertion messages so failures are self-diagnosing.
        """
        from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

        captured = {}

        def mock_run_side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            captured[label] = kwargs.get("instruction", "")
            if label == "step6":
                return (True, step6_output, 0.1, "model")
            if label == "step8":
                return (True, "## Test Plan\nPLANNED_TEST_COUNT: 3", 0.1, "model")
            if label == "step9":
                return (True, "Generated tests\nFILES_CREATED: tests/test_fix.py", 0.1, "model")
            if label == "step10":
                return (True, "PASS: Tests correct\nE2E_NEEDED: no", 0.1, "model")
            return (True, f"Output for {label}", 0.1, "model")

        template = self._make_base_template()

        worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
        worktree_path.mkdir(parents=True, exist_ok=True)

        exc = None
        with patch("pdd.agentic_bug_orchestrator.run_agentic_task", side_effect=mock_run_side_effect), \
             patch("pdd.agentic_bug_orchestrator.load_prompt_template", return_value=template), \
             patch("pdd.agentic_bug_orchestrator.console"), \
             patch("pdd.agentic_bug_orchestrator._setup_worktree", return_value=(worktree_path, None)), \
             patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
             patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
             patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)), \
             patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
             patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
             patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"):
            try:
                run_agentic_bug_orchestrator(
                    issue_url="https://github.com/owner/repo/issues/1",
                    issue_content="Bug description",
                    repo_owner="owner",
                    repo_name="repo",
                    issue_number=1,
                    issue_author="user",
                    issue_title="Bug Title",
                    cwd=tmp_path,
                    quiet=True,
                )
            except Exception as e:
                exc = e  # captured so tests can include it in assertion messages

        return captured, exc

    def test_expansion_items_injected_into_step8_when_scope_expansion(self, tmp_path):
        """When Step 6 emits EXPANSION_ITEMS, Step 8 instruction contains the items."""
        captured, exc = self._run_orchestrator_to_step8(tmp_path, self.STEP6_WITH_EXPANSION)
        step8_instruction = captured.get("step8", "")
        assert "step 6 timeout wrong" in step8_instruction, (
            "Orchestrator must inject EXPANSION_ITEMS into Step 8's instruction. "
            f"Step 8 instruction: {step8_instruction[:500]}"
            + (f"\nOrchestrator raised before step8: {exc}" if exc and not step8_instruction else "")
        )

    def test_expansion_items_is_none_when_scope_match(self, tmp_path):
        """When Step 6 emits EXPANSION_ITEMS: none, Step 8 sees 'none'."""
        captured, exc = self._run_orchestrator_to_step8(tmp_path, self.STEP6_SCOPE_MATCH)
        step8_instruction = captured.get("step8", "")
        assert "<step6_expansion_items>none</step6_expansion_items>" in step8_instruction, (
            "Orchestrator must inject 'none' for SCOPE_MATCH into Step 8's instruction. "
            f"Step 8 instruction: {step8_instruction[:500]}"
            + (f"\nOrchestrator raised before step8: {exc}" if exc and not step8_instruction else "")
        )


# ---------------------------------------------------------------------------
# Unit tests: Prompts contain {step6_expansion_items} placeholder
# ---------------------------------------------------------------------------

class TestExpansionItemsPlaceholderInPrompts:
    """Steps 8, 9, 10 prompts must use {step6_expansion_items} placeholder."""

    def test_step8_has_expansion_items_placeholder(self, step8_content: str):
        """Step 8 prompt must reference {step6_expansion_items} so orchestrator injection works."""
        assert "{step6_expansion_items}" in step8_content, (
            "Step 8 prompt must contain {step6_expansion_items} placeholder — "
            "this is the structured variable the orchestrator injects after parsing Step 6."
        )

    def test_step9_has_expansion_items_placeholder(self, step9_content: str):
        """Step 9 prompt must reference {step6_expansion_items} so orchestrator injection works."""
        assert "{step6_expansion_items}" in step9_content, (
            "Step 9 prompt must contain {step6_expansion_items} placeholder — "
            "this is the structured variable the orchestrator injects after parsing Step 6."
        )

    def test_step10_has_expansion_items_placeholder(self, step10_content: str):
        """Step 10 prompt must reference {step6_expansion_items} so orchestrator injection works."""
        assert "{step6_expansion_items}" in step10_content, (
            "Step 10 prompt must contain {step6_expansion_items} placeholder — "
            "this is the structured variable the orchestrator injects after parsing Step 6."
        )

    def test_step6_emits_expansion_items_marker_instruction(self, step6_content: str):
        """Step 6 prompt must instruct the LLM to emit the EXPANSION_ITEMS: marker."""
        assert "EXPANSION_ITEMS:" in step6_content, (
            "Step 6 prompt must instruct the LLM to output an EXPANSION_ITEMS: marker — "
            "this is what the orchestrator parses to populate {step6_expansion_items}."
        )


# ---------------------------------------------------------------------------
# Unit tests: Step 10 uses WARNING not FAIL for scope gaps
# ---------------------------------------------------------------------------

class TestStep10ScopeWarning:
    """Step 10 scope completeness check must use WARNING, not FAIL."""

    def test_step10_scope_check_uses_warning_not_fail(self, step10_content: str):
        """Step 10 scope section should warn about incomplete scope, not hard-stop."""
        content_lower = step10_content.lower()
        scope_section_start = content_lower.find("scope completeness")
        assert scope_section_start != -1, "Step 10 must have a scope completeness verification section"

        scope_section = content_lower[scope_section_start:scope_section_start + 800]

        assert "warning" in scope_section, (
            "Step 10 scope completeness section must use WARNING — "
            "a FAIL would risk killing valid workflows via _check_hard_stop()."
        )
        assert "**fail:" not in scope_section and "report: fail" not in scope_section, (
            "Step 10 scope completeness section must NOT use FAIL."
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

    def test_coverage_check_requires_issue_symptom_coverage(self, step8_content: str) -> None:
        """Coverage check must still instruct covering issue symptoms, not just expansion items.

        When step6_expansion_items is 'none' (SCOPE_MATCH / NO_PROPOSED_FIX — the majority
        of bugs), the expansion-items check is a no-op. Without the issue-symptom baseline,
        the LLM gets no coverage guidance at all for those cases.
        """
        content_lower = step8_content.lower()
        has_instruction = (
            "re-read the issue description" in content_lower
            or "every distinct symptom" in content_lower
        )
        assert has_instruction, (
            "Step 8 coverage check must instruct re-reading the issue description "
            "to enumerate symptoms — otherwise SCOPE_MATCH and NO_PROPOSED_FIX cases "
            "get no baseline coverage guidance."
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
