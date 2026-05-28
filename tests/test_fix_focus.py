"""Tests for pdd.fix_focus public helpers."""
import textwrap

import pytest

from pdd.fix_focus import (
    FunctionSlice,
    _extract_test_slices,
    _format_slice_for_llm,
    _get_all_functions,
    build_skeleton,
    extract_function_names_from_traceback,
    is_large,
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
