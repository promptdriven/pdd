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
            os.getcwd()
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
    assert "import os" in result  # referenced by entry(), not unrelated imports
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


def test_import_drift_prevention_excludes_unused_imports():
    """Expanded slices include only imports referenced by preserved symbols."""
    code = textwrap.dedent("""
        import os
        import json

        def entry():
            return os.getcwd()

        def other():
            return json.loads("{}")
    """)

    result = ContentSelector.select(
        code, ["def:entry"], file_path="module.py", expand_dependencies=True
    )

    assert "import os" in result
    assert "import json" not in result
    assert "def other():" not in result


def test_patch_target_no_false_positive_when_private_symbol_remains(tmp_path):
    """Patched private helpers still present in generated code must not trip the gate."""
    project_dir = tmp_path / "pkg"
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
    (test_dir / "test_logic.py").write_text(textwrap.dedent("""
        from unittest.mock import patch
        @patch("pkg.logic._private_but_patched")
        def test_logic(mock_private):
            pass
    """), encoding="utf-8")

    existing_code = code_file.read_text(encoding="utf-8")
    generated_code = textwrap.dedent("""
        def _private_but_patched():
            return "still here"

        def public_func():
            return _private_but_patched()
    """)

    _verify_public_surface_regression(
        existing_code=existing_code,
        generated_code=generated_code,
        prompt_name="logic_python",
        output_path=str(code_file),
        language="python",
        prompt_content="% Goal: Refactor logic.py",
    )


def test_monkeypatch_setattr_expands_patch_target(tmp_path):
    """monkeypatch.setattr targets are preserved during dependency expansion."""
    module_path = tmp_path / "service.py"
    test_path = tmp_path / "tests" / "test_service.py"
    test_path.parent.mkdir()
    module_path.write_text(textwrap.dedent("""
        def public_api():
            return _internal()

        def _internal():
            return 1
    """), encoding="utf-8")
    test_path.write_text(textwrap.dedent("""
        def test_api(monkeypatch):
            monkeypatch.setattr("service._internal", lambda: 99)
    """), encoding="utf-8")

    selected = ContentSelector.select(
        module_path.read_text(encoding="utf-8"),
        "def:public_api",
        file_path=str(module_path),
        expand_dependencies=True,
    )
    assert "def _internal():" in selected


def test_patch_target_signature_drift_raises(tmp_path):
    """Patched private helpers must not change callable signatures without opt-out."""
    project_dir = tmp_path / "pkg"
    project_dir.mkdir()
    (project_dir / "__init__.py").touch()

    code_file = project_dir / "logic.py"
    code_file.write_text(textwrap.dedent("""
        def _private_but_patched(x):
            return x

        def public_func():
            return _private_but_patched(1)
    """), encoding="utf-8")

    test_dir = project_dir / "tests"
    test_dir.mkdir()
    (test_dir / "test_logic.py").write_text(textwrap.dedent("""
        from unittest.mock import patch
        @patch("pkg.logic._private_but_patched")
        def test_logic(mock_private):
            pass
    """), encoding="utf-8")

    existing_code = code_file.read_text(encoding="utf-8")
    generated_code = textwrap.dedent("""
        def _private_but_patched(x, y):
            return x + y

        def public_func():
            return _private_but_patched(1, 2)
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


def test_patch_object_target_expands_and_collects(tmp_path):
    """patch.object(module, \"attr\") forms are discovered and expanded."""
    from pdd.split_validation import collect_patch_symbols_for_module

    module_path = tmp_path / "service.py"
    test_path = tmp_path / "tests" / "test_service.py"
    test_path.parent.mkdir()
    module_path.write_text(textwrap.dedent("""
        import service

        def public_api():
            return service._internal()

        def _internal():
            return 1
    """), encoding="utf-8")
    test_path.write_text(textwrap.dedent("""
        import service
        from unittest.mock import patch
        @patch.object(service, "_internal")
        def test_api(mock_internal):
            pass
    """), encoding="utf-8")

    symbols = collect_patch_symbols_for_module(module_path)
    assert "_internal" in symbols

    selected = ContentSelector.select(
        module_path.read_text(encoding="utf-8"),
        "def:public_api",
        file_path=str(module_path),
        expand_dependencies=True,
    )
    assert "def _internal():" in selected


def test_patch_object_imported_class_target_collects_and_protects(tmp_path):
    """patch.object(Service, \"_private\") must preserve the patched class method."""
    from pdd.split_validation import collect_patch_symbols_for_module

    module_path = tmp_path / "service.py"
    test_path = tmp_path / "test_service.py"
    module_path.write_text(
        textwrap.dedent(
            """
            class Service:
                def _private(self):
                    return "secret"

                def public_api(self):
                    return self._private()
            """
        ),
        encoding="utf-8",
    )
    test_path.write_text(
        textwrap.dedent(
            """
            from unittest.mock import patch
            from service import Service

            @patch.object(Service, "_private")
            def test_service(mock_private):
                pass
            """
        ),
        encoding="utf-8",
    )

    symbols = collect_patch_symbols_for_module(module_path)
    assert "Service._private" in symbols

    existing_code = module_path.read_text(encoding="utf-8")
    generated_code = textwrap.dedent(
        """
        class Service:
            def public_api(self):
                return "ok"
        """
    )

    with pytest.raises(PublicSurfaceRegressionError, match="Service._private"):
        _verify_public_surface_regression(
            existing_code=existing_code,
            generated_code=generated_code,
            prompt_name="service_python",
            output_path=str(module_path),
            language="python",
            prompt_content="% Goal: Refactor service.py",
        )

    selected = ContentSelector.select(
        existing_code,
        "def:public_api",
        file_path=str(module_path),
        expand_dependencies=True,
    )
    assert "def _private(self):" in selected


def test_patch_object_class_signature_drift_raises(tmp_path):
    """patch.object(Service, \"_private\") must block signature drift on class methods."""
    module_path = tmp_path / "service.py"
    test_path = tmp_path / "test_service.py"
    module_path.write_text(
        textwrap.dedent(
            """
            class Service:
                def _private(self, x):
                    return x

                def public_api(self):
                    return self._private(1)
            """
        ),
        encoding="utf-8",
    )
    test_path.write_text(
        textwrap.dedent(
            """
            from unittest.mock import patch
            from service import Service

            @patch.object(Service, "_private")
            def test_service(mock_private):
                pass
            """
        ),
        encoding="utf-8",
    )

    existing_code = module_path.read_text(encoding="utf-8")
    generated_code = textwrap.dedent(
        """
        class Service:
            def _private(self, x, y):
                return x + y

            def public_api(self):
                return self._private(1, 2)
        """
    )

    with pytest.raises(PublicSurfaceRegressionError, match="Service._private"):
        _verify_public_surface_regression(
            existing_code=existing_code,
            generated_code=generated_code,
            prompt_name="service_python",
            output_path=str(module_path),
            language="python",
            prompt_content="% Goal: Refactor service.py",
        )


def test_patch_object_keyword_attribute_collects(tmp_path):
    """patch.object(Service, attribute=\"_private\") resolves like the positional form."""
    from pdd.split_validation import collect_patch_symbols_for_module

    module_path = tmp_path / "service.py"
    test_path = tmp_path / "test_service.py"
    module_path.write_text(
        textwrap.dedent(
            """
            class Service:
                def _private(self):
                    return 1
            """
        ),
        encoding="utf-8",
    )
    test_path.write_text(
        textwrap.dedent(
            """
            from unittest.mock import patch
            from service import Service

            @patch.object(Service, attribute="_private")
            def test_service(mock_private):
                pass
            """
        ),
        encoding="utf-8",
    )

    symbols = collect_patch_symbols_for_module(module_path)
    assert "Service._private" in symbols


def test_unittest_mock_patch_object_collects(tmp_path):
    """unittest.mock.patch.object(Service, \"_private\") resolves via import map."""
    from pdd.split_validation import collect_patch_symbols_for_module

    module_path = tmp_path / "service.py"
    test_path = tmp_path / "test_service.py"
    module_path.write_text(
        textwrap.dedent(
            """
            class Service:
                def _private(self):
                    return 1
            """
        ),
        encoding="utf-8",
    )
    test_path.write_text(
        textwrap.dedent(
            """
            import unittest.mock
            from service import Service

            @unittest.mock.patch.object(Service, "_private")
            def test_service(mock_private):
                pass
            """
        ),
        encoding="utf-8",
    )

    symbols = collect_patch_symbols_for_module(module_path)
    assert "Service._private" in symbols


def test_patch_object_ignores_test_local_class_without_import(tmp_path):
    """A Service class defined only in the test file must not map to the module."""
    from pdd.split_validation import collect_patch_symbols_for_module

    module_path = tmp_path / "service.py"
    test_path = tmp_path / "test_service.py"
    module_path.write_text(
        textwrap.dedent(
            """
            class Service:
                def _private(self):
                    return 1
            """
        ),
        encoding="utf-8",
    )
    test_path.write_text(
        textwrap.dedent(
            """
            from unittest.mock import patch

            class Service:
                def _private(self):
                    pass

            @patch.object(Service, "_private")
            def test_service(mock_private):
                pass
            """
        ),
        encoding="utf-8",
    )

    symbols = collect_patch_symbols_for_module(module_path)
    assert "Service._private" not in symbols


def test_preprocess_compress_expand_includes_dependencies(tmp_path):
    """compress=True must honor expand=\"true\" on selective includes."""
    module_path = tmp_path / "module.py"
    module_path.write_text(
        textwrap.dedent(
            """
            CONST = 42

            def helper():
                return CONST

            def entry():
                return helper()
            """
        ),
        encoding="utf-8",
    )

    old_cwd = os.getcwd()
    os.chdir(tmp_path)
    try:
        prompt = '<include path="module.py" select="def:entry" expand="true" />'
        result = preprocess(prompt, recursive=False, compress=True)
        assert "def entry():" in result
        assert "def helper():" in result
        assert "CONST = 42" in result
    finally:
        os.chdir(old_cwd)


def test_preprocess_mode_compressed_expand_includes_dependencies(tmp_path):
    """Explicit mode=\"compressed\" must honor expand=\"true\"."""
    module_path = tmp_path / "module.py"
    module_path.write_text(
        textwrap.dedent(
            """
            CONST = 42

            def helper():
                return CONST

            def entry():
                return helper()
            """
        ),
        encoding="utf-8",
    )

    old_cwd = os.getcwd()
    os.chdir(tmp_path)
    try:
        prompt = (
            '<include path="module.py" select="def:entry" '
            'mode="compressed" expand="true" />'
        )
        result = preprocess(prompt, recursive=False)
        assert "def entry():" in result
        assert "def helper():" in result
        assert "CONST = 42" in result
    finally:
        os.chdir(old_cwd)


def test_patch_target_typed_constant_protection(tmp_path):
    """Patched typed constants (_SECRET: int = 1) are protected by the gate."""
    project_dir = tmp_path / "pkg"
    project_dir.mkdir()
    (project_dir / "__init__.py").touch()

    code_file = project_dir / "logic.py"
    code_file.write_text(
        textwrap.dedent(
            """
            _SECRET: int = 1

            def public_func():
                return _SECRET
            """
        ),
        encoding="utf-8",
    )

    test_dir = project_dir / "tests"
    test_dir.mkdir()
    (test_dir / "test_logic.py").write_text(
        textwrap.dedent(
            """
            def test_logic(monkeypatch):
                monkeypatch.setattr("pkg.logic._SECRET", 2)
            """
        ),
        encoding="utf-8",
    )

    existing_code = code_file.read_text(encoding="utf-8")
    generated_code = textwrap.dedent(
        """
        def public_func():
            return 1
        """
    )

    with pytest.raises(PublicSurfaceRegressionError, match="_SECRET"):
        _verify_public_surface_regression(
            existing_code=existing_code,
            generated_code=generated_code,
            prompt_name="logic_python",
            output_path=str(code_file),
            language="python",
            prompt_content="% Goal: Refactor logic.py",
        )


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
