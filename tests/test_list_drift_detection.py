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
    """Mimics the *real* test_opencode_provider.py shape that motivated #1405.

    The bug in #858 used an inline tuple inside a ``for k in (...)`` loop
    in a test function body (NOT a module-level constant). The scanner
    must recurse into function bodies and pick up the literal tuple to
    pair it with the canonical fallback in agentic_common.py.

    This is the exact shape the original PR #899 claimed to catch but did
    not (review-blocker #2). It also exercises cross-file pairing.
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
    # *** Real shape ***: inline tuple inside a ``for k in (...)`` loop
    # inside a test function body.  This mirrors the actual #858 bug
    # at tests/test_opencode_provider.py:195-200 in the production repo.
    inline_keys = ", ".join(repr(k) for k in hardcoded_keys_26)
    test_file = _write(
        tmp_path,
        "tests/test_opencode_provider.py",
        f"""
        def test_has_opencode_credentials_anthropic_signal(monkeypatch, tmp_path):
            monkeypatch.delenv("OPENCODE_CONFIG", raising=False)
            for k in (
                {inline_keys},
            ):
                monkeypatch.delenv(k, raising=False)
            monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-ant-test")
        """,
    )

    findings = detect_static_list_drift([canonical, test_file])

    # The detector pairs the inline 26-element tuple in the test file
    # against the 45-element fallback in agentic_common.py.
    matched = [
        f
        for f in findings
        if f.static_path == test_file and f.static_size == 26
    ]
    assert matched, (
        "should detect 26-vs-45 drift across files with the REAL inline "
        "for-loop shape (not the synthetic module-level constant shape)"
    )
    primary = matched[0]
    assert primary.static_size == 26
    assert primary.canonical_size == 45
    # The missing keys should be reported so the reviewer prompt can quote
    # them as concrete evidence.
    missing_set = set(canonical_keys_45) - set(hardcoded_keys_26)
    assert set(primary.missing_items) == missing_set
    assert len(missing_set) == 19, "26-vs-45 must yield exactly 19 missing entries"


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


# ---------------------------------------------------------------------------
# Regression: real-shape scanning (function bodies / for-loops / frozensets)
# ---------------------------------------------------------------------------


def test_regression_real_opencode_provider_for_loop_shape(tmp_path):
    """The real #858 bug used an inline tuple in a ``for k in (...)`` loop
    inside a test function body, NOT a module-level constant.

    Reproduces the exact shape from ``tests/test_opencode_provider.py``
    (the 12-vs-45 case the original PR claimed to catch but did not).
    """
    canonical_keys_45 = [
        "ANTHROPIC_API_KEY", "OPENAI_API_KEY", "GEMINI_API_KEY",
        "GOOGLE_API_KEY", "OPENROUTER_API_KEY", "GITHUB_TOKEN",
        "XAI_API_KEY", "DEEPSEEK_API_KEY", "MISTRAL_API_KEY",
        "COHERE_API_KEY", "MOONSHOT_API_KEY", "AZURE_API_KEY",
        "AZURE_AI_API_KEY", "AWS_ACCESS_KEY_ID", "AWS_SECRET_ACCESS_KEY",
        "AWS_REGION_NAME", "GROQ_API_KEY", "TOGETHERAI_API_KEY",
        "FIREWORKS_AI_API_KEY", "FIREWORKS_API_KEY", "PERPLEXITYAI_API_KEY",
        "REPLICATE_API_KEY", "DEEPINFRA_API_KEY", "ZAI_API_KEY",
        "DASHSCOPE_API_KEY", "MINIMAX_API_KEY", "OLLAMA_HOST",
        "LMSTUDIO_HOST", "GMI_API_KEY", "SNOWFLAKE_API_KEY",
        "VERTEXAI_PROJECT", "VERTEXAI_LOCATION", "GOOGLE_APPLICATION_CREDENTIALS",
        "AZURE_API_BASE", "AZURE_API_VERSION", "BEDROCK_ACCESS_KEY_ID",
        "WATSONX_API_KEY", "DATABRICKS_TOKEN", "BASETEN_API_KEY",
        "PUBLICAI_API_KEY", "WANDB_API_KEY", "OVHCLOUD_API_KEY",
        "GRADIENT_AI_API_KEY", "HEROKU_API_KEY", "OCI_API_KEY",
    ]
    hardcoded_12 = canonical_keys_45[:12]

    canonical_file = _write(
        tmp_path,
        "pdd/agentic_common.py",
        f"""
        _OPENCODE_PROVIDER_ENV_KEYS_FALLBACK = (
            {", ".join(repr(k) for k in canonical_keys_45)},
        )
        """,
    )

    # The real shape: inline tuple inside a ``for k in (...)`` loop in a
    # test function body.  Mirrors tests/test_opencode_provider.py:195-200
    # of the production repo as of the PR-899 review.
    real_shape_keys = ", ".join(repr(k) for k in hardcoded_12)
    test_file = _write(
        tmp_path,
        "tests/test_opencode_provider.py",
        f"""
        def test_has_opencode_credentials_anthropic_signal(monkeypatch, tmp_path):
            monkeypatch.delenv("OPENCODE_CONFIG", raising=False)
            # Clear all backing-provider env vars to a known state, then set one.
            for k in (
                {real_shape_keys},
            ):
                monkeypatch.delenv(k, raising=False)
            monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-ant-test")
        """,
    )

    findings = detect_static_list_drift([canonical_file, test_file])
    # Drift should fire: 12 inline-loop keys vs 45 canonical-fallback keys.
    matched = [f for f in findings if f.static_path == test_file]
    assert matched, (
        "must detect inline tuple in for-loop drift; the real #858 shape "
        "is an inline tuple in a function body, not a module-level constant"
    )
    primary = matched[0]
    assert primary.static_size == 12
    assert primary.canonical_size == 45


def test_regression_inline_list_in_function_body(tmp_path):
    """Hardcoded list inside a function body assignment must be scanned."""
    target = _write(
        tmp_path,
        "tests/test_inline_assign.py",
        '''
        CANONICAL_KEYS = ("FOO", "BAR", "BAZ", "QUX", "QUUX")

        def test_cleans_env(monkeypatch):
            # Function-body assignment to a literal list.  The original
            # AST scan only walked ``tree.body`` so this was ignored.
            keys_to_clean = ["FOO", "BAR", "BAZ"]
            for key in keys_to_clean:
                monkeypatch.delenv(key, raising=False)
        ''',
    )

    findings = detect_static_list_drift([target])
    matched = [f for f in findings if f.static_list_name == "keys_to_clean"]
    assert matched, (
        "function-body assignments to literal lists must be picked up "
        "by the AST walk"
    )


def test_canonical_frozenset_is_recognized(tmp_path):
    """``CANONICAL = frozenset({"a", "b", "c"})`` must be recognized as a
    canonical source.  The production codebase uses this pattern at
    ``pdd/agentic_common.py:1053`` for ``_OPENCODE_PROVIDER_CREDENTIAL_FIELDS``.
    """
    target = _write(
        tmp_path,
        "pkg/frozen_canonical.py",
        '''
        # Mirrors the agentic_common.py:1053 pattern.
        CANONICAL_FIELDS = frozenset(
            {"apikey", "key", "token", "bearer", "bearertoken", "accesstoken", "secret"}
        )

        SUBSET_FIELDS = ["apikey", "key", "token"]
        ''',
    )

    findings = detect_static_list_drift([target])
    matched = [f for f in findings if f.static_list_name == "SUBSET_FIELDS"]
    assert matched, (
        "frozenset(...)-defined canonical sources must be paired against "
        "hardcoded subset lists"
    )
    primary = matched[0]
    assert primary.canonical_source_name == "CANONICAL_FIELDS"
    assert primary.static_size == 3
    assert primary.canonical_size == 7


def test_canonical_set_call_with_list_literal_is_recognized(tmp_path):
    """``CANONICAL = set([...])`` must also be recognized."""
    target = _write(
        tmp_path,
        "pkg/set_canonical.py",
        '''
        CANONICAL_KEYS = set(["FOO", "BAR", "BAZ", "QUX", "QUUX"])

        SUBSET = ("FOO", "BAR")
        ''',
    )

    findings = detect_static_list_drift([target])
    matched = [f for f in findings if f.static_list_name == "SUBSET"]
    assert matched, "set([literal,...]) canonicals must be recognized"


def test_set_literal_canonical_is_recognized(tmp_path):
    """Bare ``CANONICAL = {"a", "b", "c"}`` set literal must be a canonical."""
    target = _write(
        tmp_path,
        "pkg/set_literal_canonical.py",
        '''
        CANONICAL = {"FOO", "BAR", "BAZ", "QUX"}

        SUBSET = ["FOO", "BAR"]
        ''',
    )

    findings = detect_static_list_drift([target])
    matched = [f for f in findings if f.static_list_name == "SUBSET"]
    assert matched, "set-literal canonicals must be recognized"


def test_function_body_literals_are_static_only_not_canonical(tmp_path):
    """Function-body local assignments to literals are recorded as
    *static lists* (so a subset-in-function-body finding fires when the
    canonical lives at module level), but they are NOT treated as
    canonical sources.

    Reasoning: function-local names like ``candidates``, ``lines``,
    ``operation_history`` are routinely reused across unrelated tests
    with different domains, and pairing them as canonicals would produce
    massive cross-test false positives.  A canonical source must be
    deliberate: a module-level constant or a top-level function
    returning a literal.
    """
    target = _write(
        tmp_path,
        "tests/test_helper.py",
        '''
        # SUBSET is at module level -> can be static or canonical.
        SUBSET = ["FOO", "BAR"]

        def _make_fixture():
            # full_set is function-local: static-only, not a canonical.
            full_set = ("FOO", "BAR", "BAZ", "QUX", "QUUX")
            return full_set
        ''',
    )

    findings = detect_static_list_drift([target])
    # The function-local ``full_set`` must NOT be paired as a canonical
    # source against ``SUBSET`` (would generate noise across the repo).
    assert findings == [], (
        "function-body literals must be static-only; pairing them as "
        "canonical sources is a documented false-positive generator"
    )
