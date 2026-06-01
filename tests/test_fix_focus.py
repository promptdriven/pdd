"""Tests for pdd.fix_focus public helpers."""
import json
import textwrap
from pathlib import Path

import pytest

from pdd.fix_focus import (
    FunctionSlice,
    _diagnose_broken_functions,
    _extract_test_slices,
    _format_slice_for_llm,
    _get_all_functions,
    _match_slices_to_traceback,
    build_skeleton,
    extract_function_names_from_traceback,
    is_large,
    prepare_focused_inputs,
    reconstruct_code,
)


# ---------------------------------------------------------------------------
# is_large
# ---------------------------------------------------------------------------

def test_is_large_false_for_small_files():
    assert not is_large("x = 1\n", "y = 2\n")


def test_is_large_true_for_large_code():
    big_code = "x = 1\n" * 600
    assert is_large(big_code, "y = 2\n")


def test_is_large_true_for_large_test():
    big_test = "x = 1\n" * 1100
    assert is_large("y = 2\n", big_test)


# ---------------------------------------------------------------------------
# build_skeleton
# ---------------------------------------------------------------------------

def test_build_skeleton_replaces_bodies():
    src = textwrap.dedent("""\
        def add(a, b):
            return a + b

        def multiply(a, b):
            x = a * b
            return x
    """)
    result = build_skeleton(src)
    assert "def add(a, b):" in result
    assert "return a + b" not in result
    assert "..." in result


def test_build_skeleton_preserves_docstring():
    src = textwrap.dedent("""\
        def greet(name):
            \"\"\"Say hello.\"\"\"
            return f"hello {name}"
    """)
    result = build_skeleton(src)
    assert '"""Say hello."""' in result
    assert "return" not in result


def test_build_skeleton_invalid_syntax_returns_unchanged():
    src = "def foo(:\n    pass\n"
    assert build_skeleton(src) == src


def test_build_skeleton_single_docstring_body_untouched():
    src = textwrap.dedent("""\
        def doc_only():
            \"\"\"Only a docstring.\"\"\"
    """)
    result = build_skeleton(src)
    assert '"""Only a docstring."""' in result


# ---------------------------------------------------------------------------
# extract_function_names_from_traceback
# ---------------------------------------------------------------------------

def test_extract_names_from_traceback_single():
    tb = textwrap.dedent("""\
        Traceback (most recent call last):
          File "test_foo.py", line 10, in test_run
          File "foo.py", line 5, in run
        AssertionError: expected 1 got 0
    """)
    names = extract_function_names_from_traceback(tb)
    assert "run" in names or "test_run" in names


def test_extract_names_empty_on_no_traceback():
    assert extract_function_names_from_traceback("no traceback here") == []


def test_extract_names_empty_on_too_many():
    tb = "\n".join(
        f'  File "x.py", line {i}, in func{i}' for i in range(10)
    )
    assert extract_function_names_from_traceback(tb) == []


def test_extract_names_excludes_module():
    tb = '  File "x.py", line 1, in <module>'
    assert extract_function_names_from_traceback(tb) == []


# ---------------------------------------------------------------------------
# _get_all_functions
# ---------------------------------------------------------------------------

def test_get_all_functions_top_level():
    src = textwrap.dedent("""\
        def foo():
            return 1

        def bar(x):
            return x + 1
    """)
    slices = _get_all_functions(src)
    names = [s.name for s in slices]
    assert "foo" in names
    assert "bar" in names


def test_get_all_functions_qualname_for_method():
    src = textwrap.dedent("""\
        class MyClass:
            def run(self):
                return 42
    """)
    slices = _get_all_functions(src)
    assert len(slices) == 1
    assert slices[0].qualname == "MyClass.run"
    assert slices[0].name == "run"


def test_get_all_functions_dedents_method():
    src = textwrap.dedent("""\
        class MyClass:
            def run(self):
                return 42
    """)
    slices = _get_all_functions(src)
    assert slices[0].indent == 4
    assert slices[0].source.startswith("def run")


def test_get_all_functions_invalid_syntax_returns_empty():
    assert _get_all_functions("def foo(:\n    pass\n") == []


# ---------------------------------------------------------------------------
# _format_slice_for_llm
# ---------------------------------------------------------------------------

def test_format_top_level_function_unchanged():
    slc = FunctionSlice(
        name="foo", qualname="foo", start_line=1, end_line=2,
        source="def foo():\n    return 1\n", indent=0,
    )
    result = _format_slice_for_llm(slc)
    assert result == "def foo():\n    return 1\n"


def test_format_method_wrapped_in_class_stub():
    slc = FunctionSlice(
        name="run", qualname="MyClass.run", start_line=2, end_line=3,
        source="def run(self):\n    return 42\n", indent=4,
    )
    result = _format_slice_for_llm(slc)
    assert result.startswith("class MyClass:")
    assert "def run(self):" in result


# ---------------------------------------------------------------------------
# _extract_test_slices
# ---------------------------------------------------------------------------

_PYTEST_ERROR_LOG = textwrap.dedent("""\
    FAILED tests/test_math.py::TestCalc::test_add - AssertionError
    FAILED tests/test_math.py::test_multiply - AssertionError
""")

_TEST_FILE = textwrap.dedent("""\
    import pytest
    from mymodule import add, multiply

    @pytest.fixture
    def calc():
        return {}

    class TestCalc:
        def test_add(self):
            assert add(1, 2) == 3

        def test_sub(self):
            assert True

    def test_multiply():
        assert multiply(2, 3) == 6

    def test_divide():
        assert True
""")


def test_extract_test_slices_includes_targets():
    result = _extract_test_slices(_PYTEST_ERROR_LOG, _TEST_FILE)
    assert "class TestCalc:" in result
    assert "test_multiply" in result


def test_extract_test_slices_excludes_passing_tests():
    result = _extract_test_slices(_PYTEST_ERROR_LOG, _TEST_FILE)
    assert "test_divide" not in result


def test_extract_test_slices_preserves_imports():
    result = _extract_test_slices(_PYTEST_ERROR_LOG, _TEST_FILE)
    assert "import pytest" in result


def test_extract_test_slices_fallback_on_no_targets():
    result = _extract_test_slices("no FAILED lines here", _TEST_FILE)
    assert result == _TEST_FILE


def test_extract_test_slices_fallback_on_syntax_error():
    result = _extract_test_slices(_PYTEST_ERROR_LOG, "def (broken:")
    assert result == "def (broken:"


def test_extract_test_slices_result_smaller_than_original():
    # The extracted subset should be meaningfully smaller than the original.
    result = _extract_test_slices(_PYTEST_ERROR_LOG, _TEST_FILE)
    assert len(result) < len(_TEST_FILE)


def test_extract_test_slices_preserves_fixture_no_parens():
    # @pytest.fixture (no parentheses) should be included in the preamble.
    result = _extract_test_slices(_PYTEST_ERROR_LOG, _TEST_FILE)
    assert "def calc(" in result


def test_extract_test_slices_preserves_fixture_with_parens():
    # @pytest.fixture() (with call parentheses, ast.Call) should also be preserved.
    test_file_with_call_fixture = textwrap.dedent("""\
        import pytest
        from mymodule import add

        @pytest.fixture()
        def calc():
            return {}

        def test_add():
            assert add(1, 2) == 3

        def test_noop():
            assert True
    """)
    error_log = "FAILED tests/test_math.py::test_add - AssertionError\n"
    result = _extract_test_slices(error_log, test_file_with_call_fixture)
    assert "def calc(" in result
    assert "test_add" in result
    assert "test_noop" not in result


def test_extract_test_slices_class_method_keeps_context_without_unrelated_tests():
    """Regression: method-level node ids should not include an entire large class."""
    test_file = textwrap.dedent("""\
        import pytest

        CASES = [1, 2, 3]

        def helper(value):
            return value + 1

        class Params:
            base = 10

        class TestBig:
            scale = 2

            def setUp(self):
                self.params = Params()

            def helper_method(self, value):
                return helper(value) * self.scale

            def test_failing(self):
                assert self.helper_method(CASES[0]) == 4

            def test_passing_one(self):
                assert True

            def test_passing_two(self):
                assert True
    """)
    error_log = "FAILED tests/test_big.py::TestBig::test_failing - AssertionError\n"

    result = _extract_test_slices(error_log, test_file)

    assert "CASES = [1, 2, 3]" in result
    assert "def helper(" in result
    assert "class Params:" in result
    assert "class TestBig:" in result
    assert "def setUp(" in result
    assert "def helper_method(" in result
    assert "def test_failing(" in result
    assert "test_passing_one" not in result
    assert "test_passing_two" not in result


def test_extract_test_slices_includes_referenced_test_base_context():
    """Regression: sliced classes must keep referenced helper/base classes."""
    test_file = textwrap.dedent("""\
        import pytest

        class TestBase:
            __test__ = False

            def assert_ok(self, value):
                assert value == "ok"

        class TestFeature(TestBase):
            def test_failing(self):
                self.assert_ok("bad")

            def test_passing(self):
                assert True
    """)
    error_log = "FAILED tests/test_feature.py::TestFeature::test_failing - AssertionError\n"

    result = _extract_test_slices(error_log, test_file)

    assert "class TestBase:" in result
    assert "__test__ = False" in result
    assert "def assert_ok(" in result
    assert "class TestFeature(TestBase):" in result
    assert "def test_failing(" in result
    assert "def test_passing(" not in result


def test_extract_test_slices_falls_back_when_support_context_too_large():
    """Avoid returning an incomplete-looking tiny slice when context dominates."""
    helper_methods = "\n".join(
        f"    def helper_{idx}(self):\n        return {idx}"
        for idx in range(20)
    )
    test_file = textwrap.dedent(f"""\
        class TestBase:
            __test__ = False
{helper_methods}

        class TestFeature(TestBase):
            def test_failing(self):
                assert self.helper_19() == 0
    """)
    error_log = "FAILED tests/test_feature.py::TestFeature::test_failing - AssertionError\n"

    result = _extract_test_slices(error_log, test_file)

    assert result == test_file


# ---------------------------------------------------------------------------
# reconstruct_code – top-level function
# ---------------------------------------------------------------------------

def test_reconstruct_top_level_function():
    original = textwrap.dedent("""\
        def foo():
            return 1

        def bar():
            return 2
    """)
    fixed_code = textwrap.dedent("""\
        def foo():
            return 99
    """)
    src = textwrap.dedent("""\
        def foo():
            return 1
    """)
    slices = _get_all_functions(original)
    foo_slice = next(s for s in slices if s.name == "foo")
    result = reconstruct_code(original, fixed_code, [foo_slice])
    assert "return 99" in result
    assert "return 2" in result   # bar unchanged


# ---------------------------------------------------------------------------
# reconstruct_code – class method (critical regression test)
# ---------------------------------------------------------------------------

def test_reconstruct_class_method():
    original = textwrap.dedent("""\
        class MyClass:
            def run(self):
                return 1

            def other(self):
                return 2
    """)
    slices = _get_all_functions(original)
    run_slice = next(s for s in slices if s.name == "run")

    # Simulate what the LLM returns: a class stub with the fixed method.
    fixed_focused = textwrap.dedent("""\
        class MyClass:
            def run(self):
                return 99
    """)
    result = reconstruct_code(original, fixed_focused, [run_slice])

    assert "return 99" in result
    assert "return 2" in result        # other() unchanged
    # The result must still be valid Python (indentation preserved).
    import ast as _ast
    try:
        _ast.parse(result)
    except SyntaxError as e:
        pytest.fail(f"reconstruct_code produced invalid syntax: {e}\n{result}")


def test_reconstruct_method_no_collision_between_classes():
    """Two classes with a method of the same name: only the targeted one changes."""
    original = textwrap.dedent("""\
        class A:
            def run(self):
                return 1

        class B:
            def run(self):
                return 2
    """)
    slices = _get_all_functions(original)
    a_run = next(s for s in slices if s.qualname == "A.run")

    fixed_focused = textwrap.dedent("""\
        class A:
            def run(self):
                return 99
    """)
    result = reconstruct_code(original, fixed_focused, [a_run])
    lines = result.splitlines()
    # A.run changed
    assert any("return 99" in l for l in lines)
    # B.run unchanged
    assert any("return 2" in l for l in lines)


def test_reconstruct_returns_original_on_empty_fixed():
    original = "def foo():\n    return 1\n"
    slices = _get_all_functions(original)
    result = reconstruct_code(original, "", slices)
    assert result == original


def test_reconstruct_returns_original_on_syntax_error_in_fixed():
    original = "def foo():\n    return 1\n"
    slices = _get_all_functions(original)
    result = reconstruct_code(original, "def foo(:\n    bad\n", slices)
    assert result == original


# ---------------------------------------------------------------------------
# reconstruct_code – no cross-class splicing when both slices are selected
# ---------------------------------------------------------------------------

def test_reconstruct_no_cross_class_splice_when_both_selected():
    """
    Regression test: when A.run and B.run are both in slices but the LLM only
    returns a fix for A.run, B.run must NOT be overwritten with A.run's body.
    Previously the simple-name fallback in reconstruct_code caused this bug.
    """
    original = textwrap.dedent("""\
        class A:
            def run(self):
                return 1

        class B:
            def run(self):
                return 2
    """)
    slices = _get_all_functions(original)
    # Both A.run and B.run are in slices (simulates the fast-path selecting all
    # slices whose .name matches the traceback name "run").
    assert len(slices) == 2

    # LLM only returns a fix for A.run (one class stub).
    fixed_focused = textwrap.dedent("""\
        class A:
            def run(self):
                return 99
    """)
    result = reconstruct_code(original, fixed_focused, slices)

    lines = result.splitlines()
    # A.run updated
    assert any("return 99" in l for l in lines), "A.run fix not applied"
    # B.run must NOT be overwritten
    assert any("return 2" in l for l in lines), "B.run was incorrectly overwritten"


# ---------------------------------------------------------------------------
# _match_slices_to_traceback – line-based disambiguation
# ---------------------------------------------------------------------------

def test_match_slices_disambiguates_by_line():
    """
    When A.run is at lines 2-3 and B.run is at lines 6-7, a traceback
    pointing to line 3 (inside A.run) should select only A.run.
    """
    src = textwrap.dedent("""\
        class A:
            def run(self):
                return 1

        class B:
            def run(self):
                return 2
    """)
    all_slices = _get_all_functions(src)
    # Traceback line 3 falls inside A.run; line 3 is "return 1" inside A.
    traceback = '  File "foo.py", line 3, in run\nAssertionError'
    matched = _match_slices_to_traceback(all_slices, traceback, ["run"])
    assert len(matched) == 1
    assert matched[0].qualname == "A.run"


def test_match_slices_falls_back_to_all_when_no_line_info():
    """Without line numbers in the traceback, all candidates are returned."""
    src = textwrap.dedent("""\
        class A:
            def run(self):
                return 1

        class B:
            def run(self):
                return 2
    """)
    all_slices = _get_all_functions(src)
    # Traceback has no line number format (e.g. from Phase-1 LLM diagnosis)
    traceback = "run failed somehow"
    matched = _match_slices_to_traceback(all_slices, traceback, ["run"])
    qualnames = {s.qualname for s in matched}
    assert "A.run" in qualnames
    assert "B.run" in qualnames


def test_match_slices_by_qualname():
    """When LLM returns a qualified name like 'A.run', the slice is matched directly."""
    src = textwrap.dedent("""\
        class A:
            def run(self):
                return 1

        class B:
            def run(self):
                return 2
    """)
    all_slices = _get_all_functions(src)
    # Phase-1 LLM diagnosis returned the qualified name "A.run"
    matched = _match_slices_to_traceback(all_slices, "", ["A.run"])
    assert len(matched) == 1
    assert matched[0].qualname == "A.run"


def test_prepare_focused_inputs_runs_phase1_when_traceback_only_names_test(monkeypatch):
    """
    Regression: assertion failures often put only the failing test function in
    the traceback. If that fast-path name is not in product code, Phase 1 must
    run instead of abandoning focused repair.
    """
    code = textwrap.dedent("""\
        def target():
            return 0
    """) + ("\n# filler\n" * 501)
    unit_test = textwrap.dedent("""\
        from module import target

        def test_target():
            assert target() == 1
    """)
    error = textwrap.dedent("""\
        FAILED tests/test_module.py::test_target - AssertionError
        Traceback (most recent call last):
          File "tests/test_module.py", line 4, in test_target
            assert target() == 1
        AssertionError
    """)
    calls = []

    def fake_diagnose(**kwargs):
        calls.append(kwargs)
        return ["target"]

    monkeypatch.setattr("pdd.fix_focus._diagnose_broken_functions", fake_diagnose)

    focused = prepare_focused_inputs(
        code,
        unit_test,
        error,
        strength=0.6,
        temperature=0.2,
        time=0.7,
        verbose=True,
        language="python",
    )

    assert calls, "Phase 1 diagnosis should run when fast-path names only match tests"
    assert focused is not None
    assert "def target()" in focused.focused_code
    assert focused.slices[0].name == "target"


def test_diagnose_broken_functions_skips_llm_when_code_has_syntax_error(monkeypatch):
    """
    Syntax-broken large files cannot be skeletonized safely; Phase 1 should
    fall back without sending the unchanged full file to the LLM.
    """
    calls = []

    def fake_llm_invoke(**kwargs):
        calls.append(kwargs)
        return {"result": None}

    monkeypatch.setattr("pdd.llm_invoke.llm_invoke", fake_llm_invoke)

    result = _diagnose_broken_functions(
        code="def broken(:\n    pass\n",
        error="SyntaxError: invalid syntax",
        strength=0.6,
        temperature=0.0,
        time=0.5,
    )

    assert result == []
    assert calls == []


def test_fix_focus_prompt_and_architecture_require_phase1_when_fast_path_misses_product_code():
    """
    Regression: PDD regenerates source from prompt and architecture metadata.
    Both must preserve the Phase 1 fallback when traceback names do not match
    product-code slices, otherwise assertion-only failures can lose focused repair.
    """
    repo_root = Path(__file__).resolve().parents[1]
    prompt_text = (repo_root / "pdd/prompts/fix_focus_python.prompt").read_text(encoding="utf-8")
    architecture = json.loads((repo_root / "architecture.json").read_text(encoding="utf-8"))
    fix_focus_entry = next(
        entry for entry in architecture if entry.get("filename") == "fix_focus_python.prompt"
    )

    required_prompt_phrases = [
        "fast-path targets do not match product-code slices",
        "fast-path names are found but do not match any product-code slices",
        "it must run Phase 1 once before returning `None`",
    ]
    for phrase in required_prompt_phrases:
        assert phrase in prompt_text

    architecture_contract = (
        fix_focus_entry.get("reason", "") + "\n" + fix_focus_entry.get("description", "")
    )
    assert "fast-path targets do not match product-code slices" in architecture_contract
    assert "fast-path names match no product-code slices" in architecture_contract
