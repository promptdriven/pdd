import os
import textwrap
import pytest
from pdd.content_selector import ContentSelector
from pdd.preprocess import preprocess
from pdd.code_generator_main import _verify_public_surface_regression, PublicSurfaceRegressionError


def test_content_selector_dependency_expansion():
    """Verify ContentSelector recursively expands local dependencies."""
    code = textwrap.dedent("""
        import os

        BASE = 10

        def helper(x):
            return x + BASE

        def entry(y):
            return helper(y)

        def unrelated():
            pass
    """)

    result = ContentSelector.select(
        code, ["def:entry"], file_path="test.py", expand_dependencies=True
    )

    assert "def entry(y):" in result
    assert "def helper(x):" in result
    assert "BASE = 10" in result
    assert "import os" in result
    assert "def unrelated():" not in result


def test_preprocess_expand_attribute():
    """Verify the preprocessor respects the expand="true" attribute."""
    with open("dep_test.py", "w", encoding="utf-8") as handle:
        handle.write(textwrap.dedent("""
            CONST = 42
            def func():
                return CONST
        """))

    try:
        prompt = '<include path="dep_test.py" select="def:func" expand="true" />'
        result = preprocess(prompt)

        assert "def func():" in result
        assert "CONST = 42" in result
    finally:
        if os.path.exists("dep_test.py"):
            os.remove("dep_test.py")


def test_patch_target_protection(tmp_path):
    """Verify _verify_public_surface_regression protects symbols referenced in tests."""
    project_dir = tmp_path / "my_project"
    project_dir.mkdir()
    (project_dir / "__init__.py").touch()

    code_file = project_dir / "logic.py"
    code_file.write_text(textwrap.dedent("""
        def _private_but_patched():
            return "secret"

        def public_func():
            return _private_but_patched()
    """), encoding="utf-8")

    test_dir = project_dir / "tests"
    test_dir.mkdir()
    test_file = test_dir / "test_logic.py"
    test_file.write_text(textwrap.dedent("""
        from unittest.mock import patch
        @patch("my_project.logic._private_but_patched")
        def test_logic(mock_private):
            pass
    """), encoding="utf-8")

    existing_code = code_file.read_text(encoding="utf-8")
    generated_code = textwrap.dedent("""
        def public_func():
            return "refactored"
    """)

    with pytest.raises(PublicSurfaceRegressionError, match="_private_but_patched"):
        _verify_public_surface_regression(
            existing_code=existing_code,
            generated_code=generated_code,
            prompt_name="logic_python",
            output_path=str(code_file),
            language="python",
            prompt_content="% Goal: Refactor logic.py",
        )


if __name__ == "__main__":
    pytest.main([__file__])
