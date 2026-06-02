import os
import pathlib
import textwrap
import pytest
from pdd.content_selector import ContentSelector
from pdd.preprocess import preprocess
from pdd.code_generator_main import _snapshot_public_surface, _collect_patch_targets

def test_content_selector_expand_patch_targets(tmp_path):
    # Setup: a file with a private helper and a sibling test that patches it
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
    
    # Select public_func with expand_dependencies=True
    # If patch target preservation works, _private_helper SHOULD be included
    selected = ContentSelector.select(
        content, 
        "def:public_func", 
        file_path=str(module_path), 
        expand_dependencies=True
    )
    
    assert "_private_helper" in selected
    assert "def _private_helper():" in selected

def test_preprocess_expand_true(tmp_path):
    # Setup: a prompt that includes a file with expand="true"
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
    
    # We need to change CWD or use absolute path for include to work easily in tests
    # Preprocess uses PathResolver which usually checks CWD.
    old_cwd = os.getcwd()
    os.chdir(tmp_path)
    try:
        prompt = '<include path="module.py" select="def:public_func" expand="true" />'
        processed = preprocess(prompt, recursive=False)
        assert "_private_helper" in processed
    finally:
        os.chdir(old_cwd)

def test_preprocess_expand_bare(tmp_path):
    # Setup: a prompt that includes a file with bare expand attribute
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
    # Verify that _snapshot_public_surface ignores private symbols unless they are patch targets
    content = textwrap.dedent("""
        def public_func(): pass
        def _private_helper(): pass
    """)
    
    # Without patch targets
    surface = _snapshot_public_surface(content, "python")
    assert "public_func" in surface
    assert "_private_helper" not in surface
    
    # With patch targets
    surface = _snapshot_public_surface(content, "python", patch_targets={"_private_helper"})
    assert "public_func" in surface
    assert "_private_helper" in surface

def test_code_generator_deep_recursion():
    # Verify deep recursion in public surface
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
    
    # With patch target at depth
    surface = _snapshot_public_surface(content, "python", patch_targets={"Outer.Inner._private"})
    assert "Outer.Inner._private" in surface
