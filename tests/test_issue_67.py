import os
import textwrap
import pytest
from pdd.content_selector import ContentSelector
from pdd.preprocess import preprocess
from pdd.code_generator_main import _snapshot_public_surface, _collect_patch_targets


def test_content_selector_expand_patch_targets(tmp_path):
    module_path = tmp_path / "module.py"
    test_path = tmp_path / "test_module.py"

    content = textwrap.dedent("""
        def public_func():
            return 1

        def _private_helper():
            return 42
    """)

    test_content = textwrap.dedent("""
        from unittest.mock import patch
        @patch("module._private_helper")
        def test_func(mock_helper):
            pass
    """)

    module_path.write_text(content)
    test_path.write_text(test_content)

    selected = ContentSelector.select(
        content,
        "def:public_func",
        file_path=str(module_path),
        expand_dependencies=True,
    )

    assert "_private_helper" in selected
    assert "def _private_helper():" in selected


def test_preprocess_expand_true(tmp_path):
    module_path = tmp_path / "module.py"
    test_path = tmp_path / "test_module.py"

    content = textwrap.dedent("""
        def public_func():
            return 1

        def _private_helper():
            return 42
    """)

    test_content = textwrap.dedent("""
        from unittest.mock import patch
        @patch("module._private_helper")
        def test_func(mock_helper):
            pass
    """)

    module_path.write_text(content)
    test_path.write_text(test_content)

    old_cwd = os.getcwd()
    os.chdir(tmp_path)
    try:
        prompt = '<include path="module.py" select="def:public_func" expand="true" />'
        processed = preprocess(prompt, recursive=False)
        assert "_private_helper" in processed
    finally:
        os.chdir(old_cwd)


def test_preprocess_expand_bare(tmp_path):
    module_path = tmp_path / "module.py"
    test_path = tmp_path / "test_module.py"

    content = textwrap.dedent("""
        def public_func():
            return 1

        def _private_helper():
            return 42
    """)

    test_content = textwrap.dedent("""
        from unittest.mock import patch
        @patch("module._private_helper")
        def test_func(mock_helper):
            pass
    """)

    module_path.write_text(content)
    test_path.write_text(test_content)

    old_cwd = os.getcwd()
    os.chdir(tmp_path)
    try:
        prompt = '<include path="module.py" select="def:public_func" expand />'
        processed = preprocess(prompt, recursive=False)
        assert "_private_helper" in processed
    finally:
        os.chdir(old_cwd)


def test_code_generator_public_surface_patch_targets():
    content = textwrap.dedent("""
        def public_func(): pass
        def _private_helper(): pass
    """)

    surface = _snapshot_public_surface(content, "python")
    assert "public_func" in surface
    assert "_private_helper" not in surface

    surface = _snapshot_public_surface(content, "python", patch_targets={"_private_helper"})
    assert "public_func" in surface
    assert "_private_helper" in surface


def test_code_generator_deep_recursion():
    content = textwrap.dedent("""
        class Outer:
            class Inner:
                def method(self): pass
                def _private(self): pass
    """)

    surface = _snapshot_public_surface(content, "python")
    assert "Outer" in surface
    assert "Outer.Inner" in surface
    assert "Outer.Inner.method" in surface
    assert "Outer.Inner._private" not in surface

    surface = _snapshot_public_surface(content, "python", patch_targets={"Outer.Inner._private"})
    assert "Outer.Inner._private" in surface
