"""
Failing tests for Issue #1254: pdd sync fails with ANTHROPIC_API_KEY error
despite switching to pdd-gemini-flash label.

Bug Root Cause (pdd/llm_invoke.py ~line 2480):
-----------------------------------------------
When `_select_model_candidates()` cannot find the configured model (e.g.,
"gemini-flash") by exact CSV lookup OR by provider-aware prefix alternatives,
it silently falls back to `available_df.iloc[0]` — typically the first row
in the CSV, which is an Anthropic model.

This silent cross-provider fallback then triggers ANTHROPIC_API_KEY validation
even though the user configured a Gemini provider, causing the error:
    ERROR - API key 'ANTHROPIC_API_KEY' not set. In --force mode, skipping interactive prompt.

Fix Required:
-------------
Instead of silently falling back to `available_df.iloc[0]`, raise a ValueError
with a clear message when no provider match is found. Per the prompt spec
(prompts/llm_invoke_python.prompt line 116):
    "If no model from the same provider is available, raise a ValueError with
    a clear message — do NOT silently fall back to a model from a different
    provider."

All five tests below FAIL on the current buggy code and PASS after the fix.
"""

import pytest
import pandas as pd
from pathlib import Path


@pytest.fixture()
def llm_mod():
    """Import pdd.llm_invoke for testing."""
    from pdd import llm_invoke as mod
    return mod


def _make_df_anthropic_first(llm_mod, tmp_path):
    """CSV mirroring the production layout: Anthropic as first row (iloc[0]),
    Gemini models present but NOT including bare 'gemini-flash'.

    This is the trigger for the bug: when PDD_MODEL_DEFAULT='gemini-flash',
    the lookup fails and silently falls back to the first row (Anthropic),
    causing ANTHROPIC_API_KEY validation to run.
    """
    content = (
        "provider,model,input,output,coding_arena_elo,api_key,"
        "structured_output,reasoning_type,max_tokens,max_completion_tokens,"
        "max_reasoning_tokens\n"
        # First row is the surrogate-base trap (the bug returns this when lookup fails)
        "Anthropic,claude-sonnet-4-6,3.0,15.0,1525,ANTHROPIC_API_KEY,"
        "True,effort,200000,8192,16000\n"
        # Gemini pro is present, but NOT gemini-flash — simulating a user who
        # added the pdd-gemini-flash label but the exact model name differs
        "Google Gemini,gemini/gemini-3.1-pro-preview,2.0,12.0,1456,GEMINI_API_KEY,"
        "True,effort,1000000,8192,0\n"
    )
    csv_path = tmp_path / "anthropic_first_no_gemini_flash.csv"
    csv_path.write_text(content)
    return llm_mod._load_model_data(csv_path)


class TestIssue1254GeminiFlashProviderFallback:
    """Issue #1254: _select_model_candidates must raise ValueError instead of
    silently falling back to an Anthropic model when a Gemini model is configured
    but cannot be found in the CSV."""

    def test_bare_gemini_flash_not_in_csv_raises_value_error(self, llm_mod, tmp_path):
        """Bug #1254: PDD_MODEL_DEFAULT='gemini-flash' (bare, no prefix) not in CSV
        must raise ValueError, NOT silently return Anthropic as the first candidate.

        Current (buggy) behavior: silently returns candidates starting with
        Anthropic (available_df.iloc[0]) → ANTHROPIC_API_KEY validation fires.
        Expected (fixed) behavior: raises ValueError — no cross-provider fallback.
        """
        df = _make_df_anthropic_first(llm_mod, tmp_path)
        with pytest.raises(ValueError):
            llm_mod._select_model_candidates(0.5, "gemini-flash", df)

    def test_gemini_prefix_nonexistent_model_raises_value_error(self, llm_mod, tmp_path):
        """Bug #1254: 'gemini/gemini-flash' (known gemini/ prefix but model absent
        from CSV) must raise ValueError, not silently fall back to Anthropic.

        The prefix 'gemini/' maps to provider 'Google Gemini'. When 'gemini-flash'
        (stripped name) has no row under 'Google Gemini', the surrogate-base path
        currently fires and returns an Anthropic candidate, triggering API key errors.
        """
        df = _make_df_anthropic_first(llm_mod, tmp_path)
        with pytest.raises(ValueError):
            llm_mod._select_model_candidates(0.5, "gemini/gemini-flash", df)

    def test_unresolved_base_does_not_silently_return_anthropic_candidates(self, llm_mod, tmp_path):
        """Bug #1254 regression: the surrogate fallback silently returns Anthropic
        as the first candidate when a Gemini model was configured but not found.

        This test documents the exact failure mode: _select_model_candidates returns
        candidates[0] from the Anthropic provider, which then triggers
        ANTHROPIC_API_KEY validation in --force mode.

        After fix: ValueError is raised instead — no candidates are returned at all.
        """
        df = _make_df_anthropic_first(llm_mod, tmp_path)
        try:
            candidates = llm_mod._select_model_candidates(0.5, "gemini-flash", df)
            # Reached here → bug is still present (no ValueError raised).
            # Record the actual buggy behavior in the failure message.
            first_provider = candidates[0]["provider"] if candidates else "(empty list)"
            first_model = candidates[0]["model"] if candidates else "(none)"
            assert False, (
                f"BUG #1254: _select_model_candidates returned candidates without raising "
                f"ValueError when 'gemini-flash' was not found in CSV. "
                f"First candidate: provider='{first_provider}', model='{first_model}'. "
                f"This causes ANTHROPIC_API_KEY validation to run even though a Gemini "
                f"provider was configured."
            )
        except ValueError:
            pass  # Correct: fix raises ValueError instead of silently returning Anthropic

    def test_vertex_prefix_nonexistent_gemini_model_raises_value_error(self, llm_mod, tmp_path):
        """Bug #1254: 'vertex_ai/gemini-flash' (known vertex_ai/ prefix, model not in CSV)
        must raise ValueError — not silently fall back to Anthropic.

        Vertex AI prefix → provider 'Google Vertex AI'. When the stripped name
        'gemini-flash' has no matching row under 'Google Vertex AI', the current
        code falls through to surrogate-base (Anthropic first row).
        """
        df = _make_df_anthropic_first(llm_mod, tmp_path)
        with pytest.raises(ValueError):
            llm_mod._select_model_candidates(0.5, "vertex_ai/gemini-flash", df)

    def test_fallback_error_message_identifies_configured_model(self, llm_mod, tmp_path):
        """Bug #1254: when the configured model cannot be found, the ValueError
        raised must identify the model name so users can diagnose the problem.

        A silent fallback gives no diagnostic information. The error message should
        name the model that was configured so the user knows what to fix.
        """
        df = _make_df_anthropic_first(llm_mod, tmp_path)
        with pytest.raises(ValueError, match="gemini-flash"):
            llm_mod._select_model_candidates(0.5, "gemini-flash", df)
