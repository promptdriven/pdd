"""
Test Plan for agentic_bug_step7_generate_LLM.prompt

This test file verifies that the Step 7 prompt provides sufficient guidance for
generating tests that detect caller behavior bugs (e.g., using wrong parameter names).

Issue #247: pdd bug generates tests that verify function signature instead of caller behavior

The bug: When a bug involves incorrect function call arguments (e.g., `limit=` vs `k=`),
the current prompt allows the LLM to generate tests that verify the callee rejects wrong
parameters (always passes) rather than tests that verify the caller uses correct parameters
(would actually fail).

These tests FAIL on the current buggy prompt and PASS once the fix is applied.

Test Categories:
1. Unit tests (TestStep7Prompt*): Verify prompt contains required guidance phrases
2. Integration test (TestStep7PromptIntegration): Verify LLM generates correct test code
"""

import os
import re
from pathlib import Path

import pytest


# --- Constants ---

PROMPT_PATH = Path(__file__).parent.parent / "prompts" / "agentic_bug_step7_generate_LLM.prompt"


# --- Fixtures ---


@pytest.fixture
def step7_prompt_content() -> str:
    """Load the Step 7 prompt content."""
    assert PROMPT_PATH.exists(), f"Prompt file not found: {PROMPT_PATH}"
    return PROMPT_PATH.read_text()


# --- Tests ---


class TestStep7PromptCallerMockingGuidance:
    """
    Test that the Step 7 prompt contains guidance for mocking caller behavior.

    When a bug involves incorrect function call arguments, the test should:
    1. Mock the called function
    2. Invoke the caller code path
    3. Assert the caller passed correct parameter names via mock.call_args

    Without this guidance, the LLM takes the easier path of testing that the
    callee rejects wrong parameters (which always passes since the function
    signature was never broken).
    """

    def test_prompt_mentions_mocking_called_function(self, step7_prompt_content: str) -> None:
        """
        Verify the prompt instructs LLMs to mock the called function when testing caller behavior.

        The prompt should mention using mock/patch to wrap the called function so we can
        inspect what arguments the caller passed.
        """
        content_lower = step7_prompt_content.lower()

        # The prompt should mention mocking for caller behavior testing
        has_mock_guidance = any([
            "mock the called function" in content_lower,
            "mock the callee" in content_lower,
            "patch the function being called" in content_lower,
            "@patch" in step7_prompt_content and "caller" in content_lower,
        ])

        assert has_mock_guidance, (
            "Step 7 prompt lacks guidance on mocking called functions for caller behavior tests. "
            "When a bug involves incorrect function call arguments, tests should mock the callee "
            "and verify the caller passes correct parameters."
        )

    def test_prompt_mentions_call_args_inspection(self, step7_prompt_content: str) -> None:
        """
        Verify the prompt instructs LLMs to use call_args to verify parameter names.

        For bugs where the caller uses wrong parameter names (e.g., limit= vs k=),
        the test must inspect mock.call_args.kwargs to verify correctness.
        """
        content_lower = step7_prompt_content.lower()

        # The prompt should mention call_args for inspecting what was passed
        has_call_args_guidance = any([
            "call_args" in content_lower,
            "call_args.kwargs" in content_lower,
            "assert_called_with" in content_lower and "parameter" in content_lower,
        ])

        assert has_call_args_guidance, (
            "Step 7 prompt lacks guidance on using call_args to verify caller behavior. "
            "For parameter mismatch bugs, tests should use mock.call_args.kwargs to verify "
            "the caller passes the correct parameter names."
        )


class TestStep7PromptAntiPatternWarning:
    """
    Test that the Step 7 prompt warns against testing callee signature for caller bugs.

    The anti-pattern: When the bug is "caller uses limit= but callee expects k=",
    generating a test like `search_similar_examples(limit=5)` raises TypeError is WRONG.
    This test always passes because the function signature was never broken.

    The prompt should explicitly warn against this anti-pattern.
    """

    def test_prompt_warns_against_testing_callee_for_caller_bugs(
        self, step7_prompt_content: str
    ) -> None:
        """
        Verify the prompt explicitly warns against the wrong testing approach.

        The prompt should warn: "Do NOT just test that the function rejects wrong parameters"
        or similar guidance to prevent the LLM from taking the easy path.
        """
        content_lower = step7_prompt_content.lower()

        has_anti_pattern_warning = any([
            "do not" in content_lower and "function rejects" in content_lower,
            "don't" in content_lower and "function rejects" in content_lower,
            "do not test that the callee" in content_lower,
            "don't test that the callee" in content_lower,
            "do not just test" in content_lower and "signature" in content_lower,
            "not the callee" in content_lower,
            "caller behavior" in content_lower and "not" in content_lower and "callee" in content_lower,
        ])

        assert has_anti_pattern_warning, (
            "Step 7 prompt lacks warning against testing callee signature for caller bugs. "
            "The prompt should explicitly state: Do NOT just test that the function rejects "
            "wrong parameters when the bug is in the caller's usage."
        )


class TestStep7PromptEnforcesStep6Strategy:
    """
    Test that the Step 7 prompt enforces implementing Step 6's test strategy.

    Step 6 often correctly identifies the test approach (mock, call_args, etc.),
    but Step 7 may ignore this and generate easier tests. The prompt should
    explicitly require implementing what Step 6 planned.
    """

    def test_prompt_requires_implementing_step6_test_strategy(
        self, step7_prompt_content: str
    ) -> None:
        """
        Verify the prompt instructs implementing Step 6's test STRATEGY, not just file path.

        The current prompt only extracts:
        - "Extract the test file path from Step 6"
        - "If Step 6 said (append)/(new)"

        But it should ALSO require:
        - "Implement EXACTLY what Step 6's test plan described"
        - "If Step 6 provided example test code, use that as the template"
        - "Follow Step 6's testing approach (mocking, assertions, etc.)"

        Without this, LLMs ignore Step 6's test strategy and generate easier tests.
        """
        content_lower = step7_prompt_content.lower()

        # The prompt mentions Step 6 for file path extraction, but does it enforce
        # implementing the actual test STRATEGY from Step 6?
        #
        # We need to check for EXPLICIT phrases that indicate strategy enforcement.
        # The current prompt only says "Extract the test file path from Step 6"
        # It does NOT say "Implement Step 6's test strategy" or similar.
        #
        # Key check: The phrases must be EXPLICIT instructions, not just word presence.
        # The current prompt says "planned the test strategy" (descriptive) but does NOT
        # say "implement the strategy" (imperative).
        has_strategy_enforcement = any([
            # Explicit enforcement phrases - these must be exact substrings
            "implement step 6" in content_lower,
            "implement the strategy" in content_lower and "step 6" in content_lower,
            "implement the test strategy" in content_lower,
            "implement exactly what step 6" in content_lower,
            "follow step 6's strategy" in content_lower,
            "follow step 6's test plan" in content_lower,
            "follow the test strategy" in content_lower and "step 6" in content_lower,
            # Template usage - step 6 example as template
            "step 6" in content_lower and "use as template" in content_lower,
            "step 6" in content_lower and "example code" in content_lower and "template" in content_lower,
            # Enforcement keywords in context of Step 6
            "step 6's approach" in content_lower,
            "step 6's test approach" in content_lower,
        ])

        assert has_strategy_enforcement, (
            "Step 7 prompt only extracts file path from Step 6, not the test STRATEGY. "
            "The prompt should require: 'Implement EXACTLY what Step 6's test plan described' "
            "and 'If Step 6 provided example test code, use that as the template'. "
            "Currently it only says 'Extract the test file path from Step 6'."
        )


# --- Integration Test Fixtures and Helpers ---


# Realistic caller-bug scenario: function uses `limit=` but callee expects `k=`
CALLER_BUG_SCENARIO = {
    "issue_url": "https://github.com/example/repo/issues/999",
    "repo_owner": "example",
    "repo_name": "repo",
    "issue_number": "999",
    "worktree_path": "/tmp/test-worktree/example-repo",
    "issue_content": """
## Bug Report

When calling `search_similar_examples()`, the code passes `limit=5` but the function
signature expects `k=5`. This causes a TypeError.

### Steps to Reproduce
1. Call `get_recommendations()` which internally calls `search_similar_examples(limit=5)`
2. Observe TypeError: search_similar_examples() got an unexpected keyword argument 'limit'

### Expected Behavior
The caller should use `k=5` to match the callee's signature.
""",
    "step1_output": "Issue is a valid bug report about parameter name mismatch.",
    "step2_output": "Confirmed bug: caller uses wrong parameter name.",
    "step3_output": "Root cause: get_recommendations() passes limit= but search_similar_examples() expects k=",
    "step4_output": "Located bug in src/recommendations.py:45 - get_recommendations() calls search_similar_examples(limit=count)",
    "step5_output": "Fix: Change line 45 from `search_similar_examples(query, limit=count)` to `search_similar_examples(query, k=count)`",
    "step6_output": """
### Test Location
**File:** tests/test_recommendations.py (new)

### Test Strategy
To verify the caller uses the correct parameter name:
1. **Mock** the `search_similar_examples` function
2. Call `get_recommendations()` which triggers the caller code path
3. Use `mock.call_args.kwargs` to verify the caller passed `k=` (not `limit=`)

### Example Test Code
```python
from unittest.mock import patch

def test_get_recommendations_uses_correct_parameter_name():
    with patch('src.recommendations.search_similar_examples') as mock_search:
        mock_search.return_value = []
        get_recommendations(query="test", count=5)

        # Verify caller used 'k=' not 'limit='
        assert 'k' in mock_search.call_args.kwargs, "Caller should use 'k=' parameter"
        assert 'limit' not in mock_search.call_args.kwargs, "Caller should NOT use 'limit='"
```
""",
}


def has_vertex_credentials() -> bool:
    """Check if Vertex AI credentials are available for integration tests."""
    creds_path = os.environ.get('VERTEX_CREDENTIALS', '')
    if not creds_path:
        return False
    if os.path.isfile(creds_path):
        return True
    return bool(creds_path)


def extract_python_code_blocks(text: str) -> list[str]:
    """
    Extract Python code blocks from markdown-formatted text.

    Handles multiple formats:
    1. Standard ```python blocks
    2. ```py blocks
    3. Bash heredocs (cat <<EOF > file.py ... EOF)
    4. Generic ``` blocks containing Python-like code (imports, def, class)
    """
    results = []

    # 1. Standard ```python blocks (must not be followed by more word chars)
    python_pattern = r'```python\s*\n(.*?)```'
    results.extend(re.findall(python_pattern, text, re.DOTALL))

    # 2. ```py blocks (must be exactly "py", not "python" - use newline after py)
    py_pattern = r'```py\s*\n(.*?)```'
    py_matches = re.findall(py_pattern, text, re.DOTALL)
    # Filter out matches that came from ```python (check original text)
    for match in py_matches:
        # Only include if it's a standalone ```py block, not part of ```python
        if match not in [r for r in results]:
            results.append(match)

    # 3. Bash heredocs: cat <<EOF > *.py ... EOF or cat <<'EOF' > *.py ... EOF
    heredoc_pattern = r"cat\s+<<'?EOF'?\s*>\s*\S+\.py\s*\n(.*?)EOF"
    results.extend(re.findall(heredoc_pattern, text, re.DOTALL))

    # 4. Generic ``` blocks that look like Python (fallback)
    if not results:
        generic_pattern = r'```\s*\n(.*?)```'
        generic_matches = re.findall(generic_pattern, text, re.DOTALL)
        for match in generic_matches:
            # Check if it looks like Python code
            python_indicators = [
                'import ', 'from ', 'def ', 'class ',
                'assert ', 'with ', '@pytest', '@patch'
            ]
            if any(indicator in match for indicator in python_indicators):
                results.append(match)

    # Clean up: strip whitespace from each result
    return [r.strip() for r in results if r.strip()]


class TestExtractPythonCodeBlocks:
    """Unit tests for extract_python_code_blocks function."""

    def test_extracts_standard_python_block(self) -> None:
        """Test extraction of standard ```python blocks."""
        text = "Here is some code:\n```python\ndef foo():\n    pass\n```\nDone."
        result = extract_python_code_blocks(text)
        assert len(result) == 1
        assert "def foo():" in result[0]

    def test_extracts_py_block(self) -> None:
        """Test extraction of ```py blocks."""
        text = "Code:\n```py\nimport os\n```"
        result = extract_python_code_blocks(text)
        assert len(result) == 1
        assert "import os" in result[0]

    def test_extracts_heredoc_python(self) -> None:
        """Test extraction of Python code from bash heredocs."""
        text = '''```bash
mkdir -p tests
cat <<EOF > tests/test_foo.py
from unittest.mock import patch

def test_example():
    assert True
EOF
```'''
        result = extract_python_code_blocks(text)
        assert len(result) == 1
        assert "from unittest.mock import patch" in result[0]
        assert "def test_example():" in result[0]

    def test_extracts_heredoc_with_quoted_eof(self) -> None:
        """Test extraction handles cat <<'EOF' variant."""
        text = '''```bash
cat <<'EOF' > src/module.py
class MyClass:
    pass
EOF
```'''
        result = extract_python_code_blocks(text)
        assert len(result) == 1
        assert "class MyClass:" in result[0]

    def test_fallback_extracts_python_from_generic_block(self) -> None:
        """Test fallback extraction from generic ``` blocks with Python indicators."""
        text = "```\nfrom typing import List\n\ndef process(items: List[str]):\n    pass\n```"
        result = extract_python_code_blocks(text)
        assert len(result) == 1
        assert "from typing import List" in result[0]

    def test_ignores_non_python_generic_blocks(self) -> None:
        """Test that generic blocks without Python indicators are ignored."""
        text = "```\necho hello\nls -la\n```"
        result = extract_python_code_blocks(text)
        assert len(result) == 0

    def test_extracts_multiple_blocks(self) -> None:
        """Test extraction of multiple Python blocks."""
        text = '''```python
def foo():
    pass
```

```python
def bar():
    pass
```'''
        result = extract_python_code_blocks(text)
        assert len(result) == 2

    def test_real_world_llm_output_with_bash_heredoc(self) -> None:
        """Test with realistic LLM output that wraps Python in bash."""
        # This is the exact pattern that caused the original test failure
        text = '''```bash
# 1. Setup worktree environment
ls -a ..

# 2. Create the test file
mkdir -p tests
cat <<EOF > tests/test_recommendations.py
from unittest.mock import patch
from src.recommendations import get_recommendations

def test_get_recommendations_uses_correct_parameter_name():
    with patch('src.recommendations.search_similar_examples') as mock_search:
        mock_search.return_value = []
        get_recommendations(query="test", count=5)
        assert 'k' in mock_search.call_args.kwargs
EOF

# 3. Run the test
pytest tests/test_recommendations.py -v
```'''
        result = extract_python_code_blocks(text)
        assert len(result) == 1
        assert "from unittest.mock import patch" in result[0]
        assert "def test_get_recommendations_uses_correct_parameter_name():" in result[0]
        assert "mock_search.call_args.kwargs" in result[0]


def analyze_test_code_for_mocking_patterns(code: str) -> dict:
    """
    Analyze generated test code for correct mocking patterns.

    Returns a dict with boolean flags for each pattern found.
    """
    code_lower = code.lower()

    return {
        # Does it import/use mock?
        "uses_mock": any([
            "from unittest.mock import" in code,
            "from unittest import mock" in code,
            "import mock" in code,
            "@patch" in code,
            "with patch" in code_lower,
            "mock." in code_lower,
        ]),
        # Does it mock the called function (search_similar_examples)?
        "mocks_callee": any([
            "search_similar_examples" in code and "patch" in code_lower,
            "mock_search" in code_lower,
        ]),
        # Does it use call_args to inspect parameters?
        "uses_call_args": any([
            "call_args" in code_lower,
            "assert_called_with" in code_lower,
            "assert_called_once_with" in code_lower,
        ]),
        # Does it verify the correct parameter name 'k'?
        "verifies_k_parameter": any([
            "'k'" in code and "call_args" in code_lower,
            '"k"' in code and "call_args" in code_lower,
            "k=" in code and "assert" in code_lower,
        ]),
        # ANTI-PATTERN: Does it just test the callee rejects wrong params?
        # This is the WRONG approach that always passes
        "anti_pattern_tests_callee_signature": any([
            "typeerror" in code_lower and "search_similar_examples(" in code_lower
            and "limit=" in code_lower and "patch" not in code_lower,
            "pytest.raises" in code_lower and "search_similar_examples(limit" in code,
        ]),
    }


# --- Integration Tests ---


class TestStep7PromptIntegration:
    """
    Integration tests that verify the Step 7 prompt produces correct LLM output.

    These tests make REAL LLM API calls and validate that the generated test code
    uses proper mocking patterns for caller-bug scenarios.

    Skip criteria: VERTEX_CREDENTIALS not set
    """

    @pytest.fixture
    def formatted_prompt(self, step7_prompt_content: str) -> str:
        """Format the Step 7 prompt with the caller-bug scenario."""
        return step7_prompt_content.format(**CALLER_BUG_SCENARIO)

    @pytest.mark.integration
    @pytest.mark.skipif(
        not has_vertex_credentials(),
        reason="VERTEX_CREDENTIALS not set - skipping integration test"
    )
    def test_llm_generates_test_with_mocking_for_caller_bug(
        self, formatted_prompt: str
    ) -> None:
        """
        Integration test: Verify LLM generates a test that mocks the callee.

        Given a caller-bug scenario where Step 6 explicitly recommends mocking,
        verify that Step 7's LLM output actually uses mocking to test caller behavior.

        This test FAILS if the LLM takes the easy path of testing callee signature.
        """
        from pdd.llm_invoke import llm_invoke

        # The formatted prompt may contain {placeholders} from the output template
        # (e.g., {{test_file_path}} becomes {test_file_path} after first format).
        # Use messages parameter to bypass llm_invoke's formatting.
        messages = [{"role": "user", "content": formatted_prompt}]

        # Call the LLM with pre-formatted messages
        response = llm_invoke(
            prompt="",  # Not used when messages is provided
            input_json={},
            messages=messages,
            strength=0.7,  # Use a capable model
            temperature=0.1,  # Low temperature for consistency
            verbose=True,
        )

        # Extract the generated output
        output = response.get('result', '')
        if hasattr(output, 'content'):
            output = output.content
        output = str(output)

        # Extract Python code blocks from the output
        code_blocks = extract_python_code_blocks(output)
        assert code_blocks, (
            f"LLM output should contain Python code blocks. Got:\n{output[:500]}..."
        )

        # Analyze the generated test code
        all_code = "\n".join(code_blocks)
        analysis = analyze_test_code_for_mocking_patterns(all_code)

        # Verify the test uses mocking (not just testing callee signature)
        assert analysis["uses_mock"], (
            "Generated test should use unittest.mock or @patch. "
            f"Got code:\n{all_code[:500]}..."
        )

        assert analysis["mocks_callee"], (
            "Generated test should mock search_similar_examples (the callee). "
            f"Got code:\n{all_code[:500]}..."
        )

        assert analysis["uses_call_args"], (
            "Generated test should use call_args to verify parameter names. "
            f"Got code:\n{all_code[:500]}..."
        )

        # Verify it's NOT using the anti-pattern
        assert not analysis["anti_pattern_tests_callee_signature"], (
            "Generated test uses ANTI-PATTERN: testing that callee rejects wrong params. "
            "This test would always pass! Should mock callee and verify caller behavior. "
            f"Got code:\n{all_code[:500]}..."
        )

    def test_formatted_prompt_includes_step6_mocking_guidance(
        self, formatted_prompt: str
    ) -> None:
        """
        Unit test: Verify the formatted prompt includes Step 6's mocking guidance.

        This is a sanity check that the test scenario is properly injected.
        The formatted prompt should contain Step 6's explicit mocking instructions.
        """
        # The formatted prompt should contain Step 6's mocking guidance
        assert "mock" in formatted_prompt.lower(), (
            "Formatted prompt should contain Step 6's mocking guidance"
        )
        assert "call_args" in formatted_prompt.lower(), (
            "Formatted prompt should contain Step 6's call_args guidance"
        )
        assert "search_similar_examples" in formatted_prompt, (
            "Formatted prompt should reference the callee function"
        )
