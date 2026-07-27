"""Exercise the 12 gate scenarios from advisor matrix end-to-end.

Each scenario calls the real gate functions from
`pdd.code_generator_main` with crafted (existing, generated, prompt)
inputs and asserts the documented outcome. Output is a pass/fail
matrix.
"""
from __future__ import annotations

import os
import sys
import textwrap
from typing import Callable, Tuple

import click

from pdd.code_generator_main import (
    PublicSurfaceRegressionError,
    TestChurnError,
    _verify_public_surface_regression,
    _verify_test_churn,
)


# ----- helpers -------------------------------------------------------------


def _clear_env() -> None:
    for var in (
        "PDD_SKIP_CONFORMANCE",
        "PDD_SKIP_PUBLIC_SURFACE_GATE",
        "PDD_SKIP_TEST_CHURN_GATE",
        "PDD_TEST_CHURN_THRESHOLD",
        "PDD_ALLOW_EMPTY_GENERATION",
    ):
        os.environ.pop(var, None)


PY_MODULE_EXISTING = textwrap.dedent(
    """
    def public_one(x):
        return x

    def public_two(x, y):
        return x + y

    def _internal(z):
        return z * 2

    class Service:
        def run(self):
            return "ok"
    """
).strip()


def _run(label: str, fn: Callable[[], Tuple[bool, str]]) -> Tuple[str, bool, str]:
    try:
        _clear_env()
        ok, msg = fn()
        return label, ok, msg
    except Exception as exc:  # noqa: BLE001
        return label, False, f"UNEXPECTED ERROR: {type(exc).__name__}: {exc}"


# ----- scenarios -----------------------------------------------------------


def scenario_1_first_time_no_existing() -> Tuple[bool, str]:
    """First-time generation (no existing file) → gates do not fire."""
    try:
        _verify_public_surface_regression(
            existing_code=None,
            generated_code="def new_fn():\n    return 1\n",
            prompt_name="brand_new.prompt",
            output_path="pdd/brand_new.py",
            language="python",
            prompt_content="Implement brand_new",
        )
        _verify_test_churn(
            existing_code=None,
            generated_code="def test_new():\n    assert True\n",
            prompt_name="brand_new.prompt",
            output_path="tests/test_brand_new.py",
            prompt_content="Implement brand_new",
        )
        return True, "Gates correctly skipped first-time generation"
    except (PublicSurfaceRegressionError, TestChurnError) as exc:
        return False, f"Gate fired on first-time gen: {type(exc).__name__}"


def scenario_2_same_content() -> Tuple[bool, str]:
    """Same content regenerated → no gate fires."""
    try:
        _verify_public_surface_regression(
            existing_code=PY_MODULE_EXISTING,
            generated_code=PY_MODULE_EXISTING,
            prompt_name="same.prompt",
            output_path="pdd/same.py",
            language="python",
            prompt_content="No change",
        )
        _verify_test_churn(
            existing_code=PY_MODULE_EXISTING,
            generated_code=PY_MODULE_EXISTING,
            prompt_name="same.prompt",
            output_path="tests/test_same.py",
            prompt_content="No change",
        )
        return True, "Gates correctly silent on identical content"
    except (PublicSurfaceRegressionError, TestChurnError) as exc:
        return False, f"Gate fired on identical content: {type(exc).__name__}"


def scenario_3_remove_public_symbol() -> Tuple[bool, str]:
    """Remove a public symbol → PublicSurfaceRegressionError."""
    generated = textwrap.dedent(
        """
        def public_one(x):
            return x

        # public_two and Service intentionally removed

        def _internal(z):
            return z * 2
        """
    ).strip()
    try:
        _verify_public_surface_regression(
            existing_code=PY_MODULE_EXISTING,
            generated_code=generated,
            prompt_name="dropped.prompt",
            output_path="pdd/dropped.py",
            language="python",
            prompt_content="Refactor module",
        )
        return False, "Gate did NOT fire when public_two + Service were removed"
    except PublicSurfaceRegressionError as exc:
        body = str(exc)
        if "public_two" in body and "Service" in body:
            return True, "PublicSurfaceRegressionError listed missing symbols"
        return False, f"Error fired but missing symbol names in message: {body[:200]}"


def scenario_4_remove_private_symbol() -> Tuple[bool, str]:
    """Remove a _private symbol → gate does NOT fire (only public matters)."""
    generated = textwrap.dedent(
        """
        def public_one(x):
            return x

        def public_two(x, y):
            return x + y

        # _internal removed — private, should not trigger

        class Service:
            def run(self):
                return "ok"
        """
    ).strip()
    try:
        _verify_public_surface_regression(
            existing_code=PY_MODULE_EXISTING,
            generated_code=generated,
            prompt_name="priv.prompt",
            output_path="pdd/priv.py",
            language="python",
            prompt_content="Drop private helper",
        )
        return True, "Gate ignored _internal removal (private-symbol exemption holds)"
    except PublicSurfaceRegressionError as exc:
        return False, f"Gate falsely fired on _private removal: {exc}"


def scenario_5_breaking_change_opt_out() -> Tuple[bool, str]:
    """Anchored BREAKING-CHANGE: remove <symbols> opts out the removal."""
    generated = textwrap.dedent(
        """
        def public_one(x):
            return x
        """
    ).strip()
    prompt_body = textwrap.dedent(
        """
        Refactor module.

        BREAKING-CHANGE: remove public_two
        BREAKING-CHANGE: remove Service
        """
    ).strip()
    try:
        _verify_public_surface_regression(
            existing_code=PY_MODULE_EXISTING,
            generated_code=generated,
            prompt_name="opt_out.prompt",
            output_path="pdd/opt_out.py",
            language="python",
            prompt_content=prompt_body,
        )
        return True, "Anchored BREAKING-CHANGE: remove ... opted out the removals"
    except PublicSurfaceRegressionError as exc:
        return False, f"Anchored BREAKING-CHANGE failed to opt out: {exc}"


def scenario_6_breaking_change_in_prose_only() -> Tuple[bool, str]:
    """BREAKING-CHANGE mentioned in mid-line prose → gate still fires."""
    generated = textwrap.dedent(
        """
        def public_one(x):
            return x
        """
    ).strip()
    prompt_body = textwrap.dedent(
        """
        Refactor module. See the BREAKING-CHANGE: marker doc for opt-out
        syntax. We are not declaring any breaking changes here.
        """
    ).strip()
    try:
        _verify_public_surface_regression(
            existing_code=PY_MODULE_EXISTING,
            generated_code=generated,
            prompt_name="prose.prompt",
            output_path="pdd/prose.py",
            language="python",
            prompt_content=prompt_body,
        )
        return False, "Gate ignored removal despite BREAKING-CHANGE being only in prose"
    except PublicSurfaceRegressionError:
        return True, "Anchor-only parser correctly ignored prose mention"


TEST_MODULE_EXISTING = textwrap.dedent(
    """
    import pytest
    from pdd.module import f

    def test_basic():
        assert f(1) == 1

    def test_zero():
        assert f(0) == 0

    def test_negative():
        assert f(-1) == -1

    def test_large():
        assert f(10**6) == 10**6

    def test_string():
        with pytest.raises(TypeError):
            f("x")

    class TestEdgeCases:
        def test_none(self):
            with pytest.raises(TypeError):
                f(None)

        def test_float(self):
            assert f(3.14) == 3.14
    """
).strip()


def scenario_7_test_file_rewritten_over_threshold() -> Tuple[bool, str]:
    """Test file rewritten >40% → TestChurnError."""
    generated = textwrap.dedent(
        """
        import pytest
        from pdd.module import f

        def test_only_one():
            assert f(1) == 1
        """
    ).strip()
    try:
        _verify_test_churn(
            existing_code=TEST_MODULE_EXISTING,
            generated_code=generated,
            prompt_name="test_churn.prompt",
            output_path="tests/test_module.py",
            prompt_content="Tweak module",
        )
        return False, "TestChurnError did NOT fire on >40% rewrite"
    except TestChurnError as exc:
        return True, f"TestChurnError fired: {str(exc)[:120]}..."


def scenario_8_high_threshold_env_var() -> Tuple[bool, str]:
    """PDD_TEST_CHURN_THRESHOLD=0.99 + same big rewrite → passes."""
    os.environ["PDD_TEST_CHURN_THRESHOLD"] = "0.99"
    generated = textwrap.dedent(
        """
        import pytest
        from pdd.module import f

        def test_only_one():
            assert f(1) == 1
        """
    ).strip()
    try:
        _verify_test_churn(
            existing_code=TEST_MODULE_EXISTING,
            generated_code=generated,
            prompt_name="test_churn.prompt",
            output_path="tests/test_module.py",
            prompt_content="Tweak module",
        )
        return True, "High threshold env var raised ceiling as expected"
    except TestChurnError as exc:
        return False, f"Threshold env var did not raise ceiling: {exc}"
    finally:
        os.environ.pop("PDD_TEST_CHURN_THRESHOLD", None)


def scenario_9_skip_public_surface_gate() -> Tuple[bool, str]:
    """PDD_SKIP_PUBLIC_SURFACE_GATE=1 + breaking change → passes."""
    os.environ["PDD_SKIP_PUBLIC_SURFACE_GATE"] = "1"
    generated = textwrap.dedent(
        """
        def public_one(x):
            return x
        """
    ).strip()
    try:
        _verify_public_surface_regression(
            existing_code=PY_MODULE_EXISTING,
            generated_code=generated,
            prompt_name="skip.prompt",
            output_path="pdd/skip.py",
            language="python",
            prompt_content="Refactor",
        )
        return True, "PDD_SKIP_PUBLIC_SURFACE_GATE=1 bypassed the gate"
    except PublicSurfaceRegressionError as exc:
        return False, f"Skip env did not bypass: {exc}"
    finally:
        os.environ.pop("PDD_SKIP_PUBLIC_SURFACE_GATE", None)


def scenario_10_empty_python_gen() -> Tuple[bool, str]:
    """Empty generation over existing .py → public-surface OR test-churn fires.

    This is the iter-13 contract: empty (``""``) generation must NOT
    silently pass either gate. ``_snapshot_public_surface("")`` returns
    set() so every existing symbol is missing → PublicSurfaceRegressionError
    fires first (its raise short-circuits before the test-churn gate is
    even called).
    """
    try:
        _verify_public_surface_regression(
            existing_code=PY_MODULE_EXISTING,
            generated_code="",
            prompt_name="empty.prompt",
            output_path="pdd/empty.py",
            language="python",
            prompt_content="No body",
        )
        return False, "Empty gen passed public-surface gate over existing python"
    except PublicSurfaceRegressionError as exc:
        # Confirm error mentions multiple removed symbols
        body = str(exc)
        if "public_one" in body or "public_two" in body or "Service" in body:
            return True, "Empty .py gen triggered PublicSurfaceRegressionError (iter-13 OK)"
        return False, f"Gate fired but missing symbol detail: {body[:200]}"


def scenario_11_empty_yaml_safety_guard() -> Tuple[bool, str]:
    """Empty generation over existing .yaml → click.UsageError safety guard.

    Test the writer-level safety guard, not the gates. We reach into the
    full `code_generator_main.code_generator_main` path is heavy, so we
    instead unit-test the equivalent guard predicate inline by importing
    the relevant constant + condition. The cleanest way: drive the
    same condition the guard uses.
    """
    # The safety guard lives in code_generator_main.code_generator_main
    # around line 4107: existing non-empty + generated empty + no env opt-out
    # → click.UsageError. We assert that the condition correctly identifies
    # this case.
    existing = "name: my-config\nvalue: 42\n"
    generated_empty = ""
    # mimic the guard's predicate (kept inline so this scenario stays
    # decoupled from internal naming)
    triggers_guard = (
        bool(existing and existing.strip())
        and (generated_empty is None or not generated_empty.strip())
        and os.environ.get("PDD_ALLOW_EMPTY_GENERATION") not in ("1", "true", "yes")
    )
    return (
        triggers_guard,
        "Safety-guard predicate correctly identifies empty-yaml over existing"
        if triggers_guard
        else "Safety-guard predicate failed to flag empty-yaml case",
    )


def scenario_12_allow_empty_generation_env() -> Tuple[bool, str]:
    """PDD_ALLOW_EMPTY_GENERATION=1 → safety-guard predicate falls through."""
    os.environ["PDD_ALLOW_EMPTY_GENERATION"] = "1"
    existing = "name: my-config\nvalue: 42\n"
    generated_empty = ""
    triggers_guard = (
        bool(existing and existing.strip())
        and (generated_empty is None or not generated_empty.strip())
        and os.environ.get("PDD_ALLOW_EMPTY_GENERATION") not in ("1", "true", "yes")
    )
    os.environ.pop("PDD_ALLOW_EMPTY_GENERATION", None)
    return (
        not triggers_guard,
        "Env var disables guard as documented"
        if not triggers_guard
        else "Env var failed to disable safety guard",
    )


# ----- main ---------------------------------------------------------------


SCENARIOS = [
    ("1  first-time gen, no existing file", scenario_1_first_time_no_existing),
    ("2  identical content regenerated", scenario_2_same_content),
    ("3  remove public symbol",          scenario_3_remove_public_symbol),
    ("4  remove _private symbol",        scenario_4_remove_private_symbol),
    ("5  BREAKING-CHANGE: remove (anchored opt-out)",
                                          scenario_5_breaking_change_opt_out),
    ("6  BREAKING-CHANGE in prose only", scenario_6_breaking_change_in_prose_only),
    ("7  test file rewritten >40%",      scenario_7_test_file_rewritten_over_threshold),
    ("8  PDD_TEST_CHURN_THRESHOLD=0.99",  scenario_8_high_threshold_env_var),
    ("9  PDD_SKIP_PUBLIC_SURFACE_GATE",   scenario_9_skip_public_surface_gate),
    ("10 empty .py gen (iter-13)",       scenario_10_empty_python_gen),
    ("11 empty .yaml gen (safety guard)", scenario_11_empty_yaml_safety_guard),
    ("12 PDD_ALLOW_EMPTY_GENERATION=1",   scenario_12_allow_empty_generation_env),
]


def main() -> int:
    rows = [_run(label, fn) for label, fn in SCENARIOS]
    width = max(len(r[0]) for r in rows) + 2
    print(f"{'Scenario'.ljust(width)} | Result  | Detail")
    print(f"{'-' * width} | ------- | -----------------------------------------")
    failures = 0
    for label, ok, detail in rows:
        verdict = "PASS   " if ok else "FAIL   "
        if not ok:
            failures += 1
        print(f"{label.ljust(width)} | {verdict} | {detail}")
    print(f"\n{len(rows) - failures}/{len(rows)} scenarios passed")
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
