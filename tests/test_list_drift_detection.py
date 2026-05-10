"""Tests for AST-based hardcoded-list-vs-canonical-source drift detection.

Issue #1405 (pdd_cloud) Fix B: ``pdd checkup --review-loop`` was missing
the test-isolation drift class that surfaced as 3 of the 7 bugs in
``promptdriven/pdd#858`` (OpenCode CLI backend autonomous solve).

The structural pattern:

* Module ``M`` defines a canonical source — a function or constant that
  returns/holds the authoritative list of N domain string literals
  (provider env vars, file markers, supported languages, etc.).
* Another module in the same package (or the same module) defines a
  hardcoded list/tuple ``S`` of the same domain-literal type with
  ``set(S) ⊂ set(canonical())`` and ``|S| < N``.
* Tests/code that consume ``S`` instead of the canonical source
  silently drift whenever ``M`` grows. The drift surfaces only when
  the runtime environment carries one of the new entries (e.g., a
  developer machine with ``XAI_API_KEY`` set), which the worker
  container that runs ``pdd checkup`` does not provide.

This test file exercises ``pdd.list_drift_detection`` against synthetic
fixtures that mirror the ``test_opencode_provider.py`` pattern and the
``tests/test_pddrc_initializer.py`` pattern catalogued in issue #1405.
"""
from __future__ import annotations

import textwrap
from pathlib import Path

import pytest

from pdd.list_drift_detection import (
    StaticListDriftFinding,
    detect_static_list_drift,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _write(root: Path, relpath: str, body: str) -> Path:
    """Write ``body`` to ``root/relpath``, creating parents."""
    p = root / relpath
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(textwrap.dedent(body).lstrip("\n"), encoding="utf-8")
    return p


# ---------------------------------------------------------------------------
# Synthetic minimal-reproduction scenarios
# ---------------------------------------------------------------------------


def test_drift_between_static_list_and_canonical_function_in_same_file(tmp_path):
    """Bare repro: hardcoded list of 3 vs canonical function returning 5."""
    target = _write(
        tmp_path,
        "pkg/sample.py",
        '''
        ENV_KEYS = ["FOO", "BAR", "BAZ"]  # static list of 3

        def _canonical_env_keys():
            return ["FOO", "BAR", "BAZ", "QUX", "QUUX"]  # canonical source returns 5
        ''',
    )

    findings = detect_static_list_drift([target])

    assert findings, "expected at least one drift finding"
    primary = findings[0]
    assert isinstance(primary, StaticListDriftFinding)
    assert primary.static_list_name == "ENV_KEYS"
    assert primary.canonical_source_name == "_canonical_env_keys"
    assert primary.static_size == 3
    assert primary.canonical_size == 5
    assert primary.static_path == target
    assert primary.canonical_path == target
    # Concrete file:line evidence is what makes this finding actionable.
    assert primary.static_line >= 1
    assert primary.canonical_line >= 1


def test_no_drift_when_lists_agree(tmp_path):
    """Static list equals canonical: no finding."""
    target = _write(
        tmp_path,
        "pkg/aligned.py",
        '''
        ENV_KEYS = ("FOO", "BAR", "BAZ")

        def _canonical_env_keys():
            return ("FOO", "BAR", "BAZ")
        ''',
    )

    findings = detect_static_list_drift([target])
    assert findings == []


def test_no_drift_when_static_list_is_superset(tmp_path):
    """Static list contains MORE than canonical: not the drift class we care about.

    This is rare but legitimate (e.g., a test wants to clear extra keys for
    paranoia). We only flag *under-coverage* of the canonical source.
    """
    target = _write(
        tmp_path,
        "pkg/superset.py",
        '''
        ENV_KEYS = ["FOO", "BAR", "BAZ", "QUX"]

        def _canonical_env_keys():
            return ["FOO", "BAR"]
        ''',
    )

    findings = detect_static_list_drift([target])
    assert findings == []


def test_drift_across_files_in_same_package(tmp_path):
    """Canonical lives in pdd/agentic_common.py; hardcoded subset lives in tests/test_x.py."""
    canonical = _write(
        tmp_path,
        "pdd/agentic_common.py",
        '''
        from typing import Tuple

        _OPENCODE_PROVIDER_ENV_KEYS_FALLBACK: Tuple[str, ...] = (
            "ANTHROPIC_API_KEY",
            "OPENAI_API_KEY",
            "GEMINI_API_KEY",
            "GOOGLE_API_KEY",
            "OPENROUTER_API_KEY",
            "GITHUB_TOKEN",
            "XAI_API_KEY",
            "DEEPSEEK_API_KEY",
            "MISTRAL_API_KEY",
            "COHERE_API_KEY",
            "MOONSHOT_API_KEY",
            "AZURE_API_KEY",
            "AZURE_AI_API_KEY",
            "AWS_ACCESS_KEY_ID",
            "GROQ_API_KEY",
        )
        ''',
    )

    bad_test = _write(
        tmp_path,
        "tests/test_x.py",
        '''
        # Hardcoded 5-key list drifts from the 15-key canonical source.
        _ENV_VARS_TO_CLEAN = [
            "ANTHROPIC_API_KEY",
            "OPENAI_API_KEY",
            "GEMINI_API_KEY",
            "GOOGLE_API_KEY",
            "GITHUB_TOKEN",
        ]
        ''',
    )

    findings = detect_static_list_drift([canonical, bad_test])

    assert findings, "expected drift between hardcoded test list and canonical source"
    matched = [f for f in findings if f.static_list_name == "_ENV_VARS_TO_CLEAN"]
    assert matched, "should pair _ENV_VARS_TO_CLEAN with the canonical fallback tuple"
    primary = matched[0]
    assert primary.static_size == 5
    assert primary.canonical_size == 15
    assert primary.static_path == bad_test
    assert primary.canonical_path == canonical
    assert primary.canonical_source_name == "_OPENCODE_PROVIDER_ENV_KEYS_FALLBACK"


def test_regression_opencode_provider_env_keys_pattern(tmp_path):
    """Mimics the test_opencode_provider.py 26-vs-45 pattern that motivated #1405.

    The test in #858 hard-coded 26 env-var names while the canonical helper
    ``_opencode_provider_env_keys()`` returned 45. This regression fixture
    keeps that exact asymmetry.
    """
    canonical_keys_45 = [
        "ANTHROPIC_API_KEY",
        "OPENAI_API_KEY",
        "GEMINI_API_KEY",
        "GOOGLE_API_KEY",
        "OPENROUTER_API_KEY",
        "GITHUB_TOKEN",
        "XAI_API_KEY",
        "DEEPSEEK_API_KEY",
        "MISTRAL_API_KEY",
        "COHERE_API_KEY",
        "MOONSHOT_API_KEY",
        "AZURE_API_KEY",
        "AZURE_AI_API_KEY",
        "AWS_ACCESS_KEY_ID",
        "AWS_SECRET_ACCESS_KEY",
        "AWS_REGION_NAME",
        "GROQ_API_KEY",
        "TOGETHERAI_API_KEY",
        "FIREWORKS_AI_API_KEY",
        "FIREWORKS_API_KEY",
        "PERPLEXITYAI_API_KEY",
        "REPLICATE_API_KEY",
        "DEEPINFRA_API_KEY",
        "ZAI_API_KEY",
        "DASHSCOPE_API_KEY",
        "MINIMAX_API_KEY",
        "OLLAMA_HOST",
        "LMSTUDIO_HOST",
        "GMI_API_KEY",
        "SNOWFLAKE_API_KEY",
        "VERTEXAI_PROJECT",
        "VERTEXAI_LOCATION",
        "GOOGLE_APPLICATION_CREDENTIALS",
        "AZURE_API_BASE",
        "AZURE_API_VERSION",
        "BEDROCK_ACCESS_KEY_ID",
        "WATSONX_API_KEY",
        "DATABRICKS_TOKEN",
        "BASETEN_API_KEY",
        "PUBLICAI_API_KEY",
        "WANDB_API_KEY",
        "OVHCLOUD_API_KEY",
        "GRADIENT_AI_API_KEY",
        "HEROKU_API_KEY",
        "OCI_API_KEY",
    ]
    hardcoded_keys_26 = canonical_keys_45[:26]

    canonical = _write(
        tmp_path,
        "pdd/agentic_common.py",
        f"""
        _OPENCODE_PROVIDER_ENV_KEYS_FALLBACK = (
            {", ".join(repr(k) for k in canonical_keys_45)},
        )
        """,
    )
    test_file = _write(
        tmp_path,
        "tests/test_opencode_provider.py",
        f"""
        _OPENCODE_PROVIDER_KEYS_HARDCODED = [
            {", ".join(repr(k) for k in hardcoded_keys_26)},
        ]
        """,
    )

    findings = detect_static_list_drift([canonical, test_file])

    matched = [
        f
        for f in findings
        if f.static_list_name == "_OPENCODE_PROVIDER_KEYS_HARDCODED"
    ]
    assert matched, "should detect 26-vs-45 drift across files"
    primary = matched[0]
    assert primary.static_size == 26
    assert primary.canonical_size == 45
    # The missing keys should be reported so the reviewer prompt can quote them.
    assert "XAI_API_KEY" in canonical_keys_45[26:]
    missing_set = set(canonical_keys_45) - set(hardcoded_keys_26)
    assert set(primary.missing_items) == missing_set


def test_drift_with_constant_canonical_source(tmp_path):
    """Canonical can be a module-level constant, not just a function."""
    target = _write(
        tmp_path,
        "pkg/constant_canonical.py",
        '''
        CANONICAL_KEYS = ("FOO", "BAR", "BAZ", "QUX", "QUUX", "CORGE")

        # 4-item static list drifts from the 6-item canonical constant.
        SUBSET_KEYS = ["FOO", "BAR", "BAZ", "QUX"]
        ''',
    )

    findings = detect_static_list_drift([target])
    matched = [f for f in findings if f.static_list_name == "SUBSET_KEYS"]
    assert matched
    primary = matched[0]
    assert primary.canonical_source_name == "CANONICAL_KEYS"
    assert primary.static_size == 4
    assert primary.canonical_size == 6


def test_ignores_lists_with_non_literal_elements(tmp_path):
    """Lists that build values dynamically are not the static-literal class.

    e.g., ``MY_LIST = [some_var, "FOO"]`` is not a "static list" because we
    cannot AST-compare its elements without runtime evaluation.
    """
    target = _write(
        tmp_path,
        "pkg/dynamic.py",
        '''
        SOME_FALLBACK = "BAR"

        # Half-literal, half-Name - not a pure static list.
        MIXED = [SOME_FALLBACK, "FOO"]

        def _canonical():
            return ["FOO", "BAR", "BAZ"]
        ''',
    )

    findings = detect_static_list_drift([target])
    # MIXED is non-static; we should not pair it with _canonical.
    matched = [f for f in findings if f.static_list_name == "MIXED"]
    assert matched == []


def test_ignores_canonical_with_non_literal_returns(tmp_path):
    """If the canonical function builds its return value with calls/comprehensions,
    we do not extract a literal set from it (yet).
    """
    target = _write(
        tmp_path,
        "pkg/dynamic_canonical.py",
        '''
        ENV_KEYS = ["FOO", "BAR"]

        def _build_keys():
            return list(("FOO", "BAR", "BAZ", "QUX"))  # not a pure literal return
        ''',
    )

    findings = detect_static_list_drift([target])
    # We cannot statically resolve the canonical return -> skip silently.
    assert findings == []


def test_ignores_singleton_lists(tmp_path):
    """A 1-element static list is too small to be a drift signal worth flagging.

    Most spurious matches in the wild are 1-element lists like ``ALLOWED = ["python"]``.
    """
    target = _write(
        tmp_path,
        "pkg/singleton.py",
        '''
        SUPPORTED = ["python"]

        def _all_languages():
            return ["python", "typescript", "go", "rust"]
        ''',
    )

    findings = detect_static_list_drift([target])
    matched = [f for f in findings if f.static_list_name == "SUPPORTED"]
    assert matched == []


def test_static_list_must_be_strict_subset(tmp_path):
    """Disjoint static list (no overlap with canonical) is not drift -- it is a
    different vocabulary that happens to share the same shape.
    """
    target = _write(
        tmp_path,
        "pkg/disjoint.py",
        '''
        UNRELATED = ["alpha", "beta"]

        def _api_keys():
            return ["FOO", "BAR", "BAZ"]
        ''',
    )

    findings = detect_static_list_drift([target])
    matched = [f for f in findings if f.static_list_name == "UNRELATED"]
    assert matched == []


def test_handles_unparseable_python_files_gracefully(tmp_path):
    """Syntax errors should not raise -- the scanner should skip the file."""
    bad = _write(tmp_path, "pkg/bad.py", "def broken(:\n  return 1\n")
    good = _write(
        tmp_path,
        "pkg/good.py",
        '''
        SUBSET = ["FOO", "BAR"]

        def _canonical():
            return ["FOO", "BAR", "BAZ", "QUX"]
        ''',
    )

    # The bad file should be skipped, not raise; the good file should still
    # produce a finding.
    findings = detect_static_list_drift([bad, good])
    assert any(f.static_list_name == "SUBSET" for f in findings)


def test_handles_missing_files_gracefully(tmp_path):
    """Nonexistent paths should be skipped, not raise."""
    findings = detect_static_list_drift([tmp_path / "does_not_exist.py"])
    assert findings == []


def test_finding_has_human_readable_summary(tmp_path):
    """Each finding should expose a one-line summary the reviewer prompt can quote."""
    target = _write(
        tmp_path,
        "pkg/with_summary.py",
        '''
        SUBSET = ["FOO", "BAR"]

        def _canonical():
            return ["FOO", "BAR", "BAZ", "QUX"]
        ''',
    )

    findings = detect_static_list_drift([target])
    assert findings
    summary = findings[0].summary
    assert "SUBSET" in summary
    assert "_canonical" in summary
    assert "2" in summary  # static size
    assert "4" in summary  # canonical size


# ---------------------------------------------------------------------------
# Integration: drift findings flow into the reviewer prompt
# ---------------------------------------------------------------------------


def test_review_prompt_embeds_drift_candidate_findings(tmp_path):
    """The reviewer prompt MUST include detected drift candidates so the LLM
    can surface them as findings (or reject them as intentional).
    """
    from pdd.checkup_review_loop import (
        ReviewLoopConfig,
        ReviewLoopContext,
        ReviewLoopState,
        _review_prompt,
    )

    # Build a tiny fake worktree containing a drift instance and point the
    # context at it. The prompt must mention the drift.
    sample = _write(
        tmp_path,
        "pkg/sample.py",
        '''
        ENV_KEYS = ["FOO", "BAR", "BAZ"]

        def _canonical_env_keys():
            return ["FOO", "BAR", "BAZ", "QUX", "QUUX"]
        ''',
    )

    context = ReviewLoopContext(
        issue_url="https://github.com/o/r/issues/1",
        issue_content="Body",
        repo_owner="o",
        repo_name="r",
        issue_number=1,
        issue_title="t",
        architecture_json="{}",
        pddrc_content="None.",
        pr_url="https://github.com/o/r/pull/2",
        pr_owner="o",
        pr_repo="r",
        pr_number=2,
        project_root=tmp_path,
        pr_content="PR body",
    )
    config = ReviewLoopConfig()
    state = ReviewLoopState()

    prompt = _review_prompt(
        reviewer="codex",
        context=context,
        round_number=1,
        state=state,
        config=config,
        mode="review",
        findings_to_verify=[],
        candidate_findings=[
            {
                "summary": "ENV_KEYS (3 items) drifts from _canonical_env_keys (5 items)",
                "location": f"{sample}:1",
                "missing": ["QUX", "QUUX"],
            }
        ],
    )

    assert "Static-Analysis Candidate Findings" in prompt
    assert "ENV_KEYS" in prompt
    assert "_canonical_env_keys" in prompt
    assert "QUX" in prompt and "QUUX" in prompt


def test_review_prompt_omits_static_section_when_no_candidates(tmp_path):
    """When the AST scan produces no drift candidates, the prompt MUST omit
    the section entirely so it does not push noise at the LLM.
    """
    from pdd.checkup_review_loop import (
        ReviewLoopConfig,
        ReviewLoopContext,
        ReviewLoopState,
        _review_prompt,
    )

    context = ReviewLoopContext(
        issue_url="x",
        issue_content="y",
        repo_owner="o",
        repo_name="r",
        issue_number=1,
        issue_title="t",
        architecture_json="{}",
        pddrc_content="None.",
        pr_url="z",
        pr_owner="o",
        pr_repo="r",
        pr_number=2,
        project_root=tmp_path,
        pr_content="",
    )
    config = ReviewLoopConfig()
    state = ReviewLoopState()

    prompt = _review_prompt(
        reviewer="codex",
        context=context,
        round_number=1,
        state=state,
        config=config,
        mode="review",
        findings_to_verify=[],
        candidate_findings=[],
    )

    assert "Static-Analysis Candidate Findings" not in prompt
