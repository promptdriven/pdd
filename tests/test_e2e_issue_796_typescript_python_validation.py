"""
E2E Test for Issue #796: TypeScript code validated as Python syntax, causing extraction failure

This test exercises the full fix_errors_from_unit_tests() pipeline with TypeScript code
to verify that the `language` parameter is properly forwarded to llm_invoke(), preventing
incorrect Python validation of TypeScript code.

The bug: fix_errors_from_unit_tests() never passes a `language` parameter to llm_invoke(),
so `language` defaults to None. The guard at llm_invoke.py:2847 treats None as Python,
causing _has_invalid_python_code() to run ast.parse() on TypeScript code, which fails
and triggers a costly cache-bypass retry.

The E2E test mocks at the llm_invoke boundary (the LLM edge) while exercising the
full fix_errors_from_unit_tests() pipeline logic, including the buggy llm_invoke() calls
that omit the `language` parameter.

The test should FAIL on buggy code and PASS once the fix is applied.
"""

import inspect
import os
import pytest
import tempfile
from pathlib import Path
from unittest.mock import patch

from pdd.fix_errors_from_unit_tests import fix_errors_from_unit_tests, CodeFix
from pdd.llm_invoke import _looks_like_python_code, _has_invalid_python_code


# Sample TypeScript/React component that is valid TypeScript but invalid Python
TYPESCRIPT_COMPONENT = '''import React from 'react';

interface WaitlistPendingProps {
  email: string;
  position: number;
}

export const WaitlistPending: React.FC<WaitlistPendingProps> = ({ email, position }) => {
  return (
    <div className="waitlist-pending">
      <h2>You're on the waitlist!</h2>
      <p>Email: {email}</p>
      <p>Position: #{position}</p>
    </div>
  );
};

export default WaitlistPending;
'''

# Sample TypeScript unit test
TYPESCRIPT_UNIT_TEST = '''import { render, screen } from '@testing-library/react';
import WaitlistPending from './WaitlistPending';

describe('WaitlistPending', () => {
  it('renders email and position', () => {
    render(<WaitlistPending email="test@example.com" position={42} />);
    expect(screen.getByText('test@example.com')).toBeInTheDocument();
    expect(screen.getByText('#42')).toBeInTheDocument();
  });
});
'''


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory."""
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("OPENAI_API_KEY", "fake-key-for-testing")


class TestIssue796TypeScriptValidationE2E:
    """
    E2E tests verifying that fix_errors_from_unit_tests() does not incorrectly
    validate TypeScript code with Python's ast.parse().
    """

    def test_typescript_triggers_python_validation_heuristic(self):
        """
        Precondition: _looks_like_python_code() matches TypeScript keywords.

        This proves the heuristic triggers on TypeScript, which is the root cause
        of the false positive when language is not passed through.
        """
        assert _looks_like_python_code(TYPESCRIPT_COMPONENT), (
            "Expected TypeScript to trigger _looks_like_python_code() heuristic "
            "(matches 'import', 'return', 'class' keywords)"
        )

    def test_typescript_codefix_flagged_as_invalid_python(self):
        """
        Precondition: _has_invalid_python_code() flags TypeScript in CodeFix as invalid.

        When TypeScript code is in a CodeFix Pydantic model field, _has_invalid_python_code()
        will try ast.parse() on it, which fails because TypeScript is not Python.
        """
        code_fix = CodeFix(
            update_unit_test=True,
            update_code=True,
            fixed_unit_test=TYPESCRIPT_UNIT_TEST,
            fixed_code=TYPESCRIPT_COMPONENT,
        )
        assert _has_invalid_python_code(code_fix), (
            "Expected _has_invalid_python_code() to flag TypeScript as invalid Python. "
            "This is the false positive that triggers the cache-bypass retry."
        )

    def test_fix_errors_pipeline_forwards_language_to_llm_invoke(self):
        """
        E2E Test: Full fix_errors_from_unit_tests() pipeline with TypeScript code.

        This exercises the real pipeline: fix_errors_from_unit_tests() calls llm_invoke()
        twice (analysis + extraction). We mock llm_invoke at the fix_errors_from_unit_tests
        module boundary and verify that `language` is passed through.

        Bug behavior (current):
        - fix_errors_from_unit_tests() calls llm_invoke() without language parameter
        - language defaults to None in both calls
        - This causes _has_invalid_python_code() to validate TypeScript as Python

        Expected behavior (after fix):
        - fix_errors_from_unit_tests() passes language="typescript" to llm_invoke()
        - The guard `language in (None, "python")` skips validation for TypeScript
        """
        with tempfile.NamedTemporaryFile(mode='w', suffix='.log', delete=False) as f:
            error_file = f.name

        try:
            # Mock llm_invoke at the fix_errors_from_unit_tests module level
            # This is the LLM boundary — we control what llm_invoke returns
            # while letting fix_errors_from_unit_tests() pipeline logic run
            call_kwargs_list = []

            def mock_llm_invoke(*args, **kwargs):
                """Capture llm_invoke calls and return appropriate responses."""
                call_kwargs_list.append(kwargs)

                if len(call_kwargs_list) == 1:
                    # First call: analysis step — returns prose
                    return {
                        'result': (
                            "The TypeScript component has a rendering issue. "
                            "The fix is to update the component props."
                        ),
                        'cost': 0.001,
                        'model_name': 'gpt-5-nano',
                    }
                else:
                    # Second call: extraction step — returns CodeFix
                    return {
                        'result': CodeFix(
                            update_unit_test=True,
                            update_code=True,
                            fixed_unit_test=TYPESCRIPT_UNIT_TEST,
                            fixed_code=TYPESCRIPT_COMPONENT,
                        ),
                        'cost': 0.002,
                        'model_name': 'gpt-5-nano',
                    }

            with patch('pdd.fix_errors_from_unit_tests.llm_invoke', side_effect=mock_llm_invoke):
                result = fix_errors_from_unit_tests(
                    unit_test=TYPESCRIPT_UNIT_TEST,
                    code=TYPESCRIPT_COMPONENT,
                    prompt="Fix the WaitlistPending TypeScript React component",
                    error="TypeError: Cannot read properties of undefined (reading 'position')",
                    error_file=error_file,
                    strength=0.5,
                    temperature=0.0,
                    language="typescript",
                )

            # Verify llm_invoke was called twice (analysis + extraction)
            assert len(call_kwargs_list) == 2, (
                f"Expected 2 llm_invoke calls, got {len(call_kwargs_list)}"
            )

            # THE BUG CHECK: Both llm_invoke calls should pass language parameter.
            # With the bug, language is never passed (defaults to None in llm_invoke).
            # After the fix, language="typescript" should be explicitly passed.
            for i, kwargs in enumerate(call_kwargs_list):
                call_label = "analysis" if i == 0 else "extraction"
                assert 'language' in kwargs, (
                    f"BUG DETECTED (Issue #796): llm_invoke() call #{i+1} ({call_label}) "
                    f"does not pass 'language' parameter. Without language='typescript', "
                    f"llm_invoke() defaults to None, causing Python validation to run "
                    f"on TypeScript code via _has_invalid_python_code().\n"
                    f"Call kwargs: {list(kwargs.keys())}"
                )
                assert kwargs['language'] == 'typescript', (
                    f"BUG DETECTED (Issue #796): llm_invoke() call #{i+1} ({call_label}) "
                    f"passes language='{kwargs.get('language')}' instead of 'typescript'."
                )

        finally:
            os.unlink(error_file)

    def test_fix_errors_accepts_language_parameter(self):
        """
        E2E Test: Verify fix_errors_from_unit_tests() accepts a `language` parameter.

        This directly demonstrates the bug: the function has no way to receive
        or forward a language parameter. After the fix, it should accept `language`
        and forward it to llm_invoke().

        This test FAILS on buggy code (language not in signature) and PASSES after fix.
        """
        sig = inspect.signature(fix_errors_from_unit_tests)
        params = list(sig.parameters.keys())

        assert "language" in params, (
            f"BUG DETECTED (Issue #796): fix_errors_from_unit_tests() does not accept "
            f"a 'language' parameter. Without it, the function cannot forward the target "
            f"language to llm_invoke(), causing Python validation on all code.\n"
            f"Current parameters: {params}"
        )
