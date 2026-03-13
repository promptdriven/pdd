"""
E2E Test for Issue #838: pdd bug generates structural tests instead of behavioral tests.

These tests exercise the full prompt rendering pipeline that the bug orchestrator
uses: load prompt file → preprocess() (expand <include> tags, escape braces) →
str.replace() variable substitution.

Unlike the unit tests in test_cross_step_consistency_prompts.py (which read raw
prompt files), these E2E tests verify that the **rendered instruction** sent to
run_agentic_task() contains structural anti-pattern blocking guidance after the
full preprocessing and variable-substitution pipeline.

This matters because:
1. preprocess() expands <include> tags — content could theoretically be
   diluted or overwritten by included files
2. The double-curly-brace escaping + str.replace() substitution pipeline
   could corrupt guidance text containing braces
3. The template variable substitution fills in {step1_output}, {issue_url},
   etc. — we verify the anti-pattern guidance survives this process

Bug: The Step 8 (test plan) and Step 9 (test code generation) prompts lacked
explicit anti-pattern guidance against inspect.signature(), hasattr(), and
sig.parameters structural tests, allowing the LLM to generate shape-checking
tests that pass without implementing actual behavior.
"""

from pathlib import Path

import pytest

from pdd.preprocess import preprocess

# Prompt files live relative to this test file
_PROMPTS_DIR = Path(__file__).parent.parent / "pdd" / "prompts"

# Minimal context dict matching what the orchestrator passes to Step 8/9 prompts
_STUB_CONTEXT = {
    "issue_url": "https://github.com/test/repo/issues/1",
    "repo_owner": "test",
    "repo_name": "repo",
    "issue_number": "1",
    "issue_content": "Test issue content",
    "step1_output": "Step 1 output",
    "step2_output": "Step 2 output",
    "step3_output": "Step 3 output",
    "step4_output": "Step 4 output",
    "step5_output": "Step 5 output",
    "step6_output": "Step 6 output",
    "step7_output": "Step 7 output",
    "step8_output": "Step 8 output",
    "worktree_path": "/tmp/test-worktree",
}


def _render_prompt(prompt_filename: str, context: dict) -> str:
    """Reproduce the orchestrator's prompt rendering pipeline exactly.

    This mirrors agentic_bug_orchestrator.py lines 467-484:
      1. Load the prompt template from the prompt file
      2. preprocess(template, recursive=True, double_curly_brackets=True, exclude_keys=...)
      3. Un-double braces and str.replace() substitution
    """
    prompt_path = _PROMPTS_DIR / f"{prompt_filename}.prompt"
    assert prompt_path.exists(), f"Prompt file not found: {prompt_path}"
    raw = prompt_path.read_text()

    exclude_keys = list(context.keys())
    processed = preprocess(
        raw, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys
    )

    # Un-double braces then substitute context keys (same as orchestrator)
    processed = processed.replace("{{", "{").replace("}}", "}")
    for key, value in context.items():
        processed = processed.replace(f"{{{key}}}", str(value))

    return processed


class TestIssue838StructuralTestBlockingE2E:
    """E2E: Verify rendered Step 8/9 prompts block structural anti-patterns."""

    def test_step8_rendered_prompt_blocks_structural_patterns(self) -> None:
        """The rendered Step 8 prompt sent to the LLM must mention structural
        anti-patterns as blocked, surviving the full preprocess + format pipeline."""
        rendered = _render_prompt("agentic_bug_step8_test_plan_LLM", _STUB_CONTEXT)
        rendered_lower = rendered.lower()

        assert "inspect.signature()" in rendered_lower, (
            "BUG DETECTED (Issue #838): The rendered Step 8 prompt sent to the LLM "
            "does NOT mention 'inspect.signature()' as a blocked anti-pattern. "
            "Without this guidance, the LLM can generate structural test plans that "
            "pass by merely adding parameters to function signatures."
        )
        assert "hasattr()" in rendered_lower or "getattr()" in rendered_lower, (
            "BUG DETECTED (Issue #838): The rendered Step 8 prompt does NOT mention "
            "'hasattr()' or 'getattr()' as blocked anti-patterns."
        )
        assert "sig.parameters" in rendered_lower, (
            "BUG DETECTED (Issue #838): The rendered Step 8 prompt does NOT mention "
            "'sig.parameters' as a blocked pattern."
        )

    def test_step9_rendered_prompt_blocks_structural_patterns(self) -> None:
        """The rendered Step 9 prompt sent to the LLM must mention structural
        anti-patterns as blocked, surviving the full preprocess + format pipeline."""
        rendered = _render_prompt("agentic_bug_step9_generate_LLM", _STUB_CONTEXT)
        rendered_lower = rendered.lower()

        assert "inspect.signature()" in rendered_lower, (
            "BUG DETECTED (Issue #838): The rendered Step 9 prompt sent to the LLM "
            "does NOT mention 'inspect.signature()' as a blocked anti-pattern. "
            "Without this guidance, the LLM generates structural test code like "
            "`assert 'quiet' in sig.parameters` instead of behavioral tests."
        )
        assert "hasattr()" in rendered_lower or "getattr()" in rendered_lower, (
            "BUG DETECTED (Issue #838): The rendered Step 9 prompt does NOT mention "
            "'hasattr()' or 'getattr()' as blocked anti-patterns."
        )
        assert "sig.parameters" in rendered_lower, (
            "BUG DETECTED (Issue #838): The rendered Step 9 prompt does NOT mention "
            "'sig.parameters' as a blocked pattern."
        )

    def test_step9_rendered_prompt_has_bad_good_code_examples(self) -> None:
        """The rendered Step 9 prompt must contain both BAD (structural) and GOOD
        (behavioral) code examples after preprocessing and variable substitution."""
        rendered = _render_prompt("agentic_bug_step9_generate_LLM", _STUB_CONTEXT)
        rendered_lower = rendered.lower()

        has_bad = "bad" in rendered_lower and "inspect.signature" in rendered_lower
        assert has_bad, (
            "BUG DETECTED (Issue #838): The rendered Step 9 prompt does NOT contain "
            "a BAD code example showing the inspect.signature anti-pattern. Without "
            "a concrete negative example, the LLM defaults to structural tests."
        )

        has_good = "good" in rendered_lower and (
            "patch" in rendered_lower or "mock" in rendered_lower
        )
        assert has_good, (
            "BUG DETECTED (Issue #838): The rendered Step 9 prompt does NOT contain "
            "a GOOD code example using mock/patch for behavioral testing."
        )
