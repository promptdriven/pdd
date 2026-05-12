"""Tests for scripts/ci_detect_changed_modules.py."""

from __future__ import annotations

import importlib.util
from pathlib import Path


def _load_module():
    script_path = (
        Path(__file__).resolve().parents[1] / "scripts" / "ci_detect_changed_modules.py"
    )
    spec = importlib.util.spec_from_file_location(
        "ci_detect_changed_modules", script_path
    )
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def test_basename_from_nested_code_paths():
    module = _load_module()

    assert module._basename_from_path("pdd/commands/checkup.py") == "commands/checkup"
    assert module._basename_from_path("pdd/core/cloud.py") == "core/cloud"
    assert (
        module._basename_from_path("pdd/server/routes/auth.py")
        == "server/routes/auth"
    )


def test_basename_excludes_package_main_shim():
    module = _load_module()

    assert module._basename_from_path("pdd/__main__.py") is None
    assert module._basename_from_path("pdd/prompts/__main___python.prompt") is None
    assert module._basename_from_path("context/__main___example.py") is None
    assert module._basename_from_path("tests/test___main__.py") is None


def test_basename_excludes_ci_helper_script_tests():
    module = _load_module()

    assert module._basename_from_path("tests/test_ci_detect_changed_modules.py") is None
    assert module._basename_from_path("tests/test_copy_package_data_to_public.py") is None


def test_basename_excludes_agent_reviewed_model_catalog():
    module = _load_module()

    assert module._basename_from_path("pdd/generate_model_catalog.py") is None
    assert (
        module._basename_from_path("pdd/prompts/generate_model_catalog_python.prompt")
        is None
    )
    assert module._basename_from_path("context/generate_model_catalog_example.py") is None
    assert module._basename_from_path("tests/test_generate_model_catalog.py") is None


def test_basename_from_nested_context_and_tests():
    module = _load_module()

    assert (
        module._basename_from_path("context/core/errors_example.py")
        == "core/errors"
    )
    assert module._basename_from_path("tests/core/test_cloud.py") == "core/cloud"
    assert (
        module._basename_from_path("tests/server/test_security.py")
        == "server/security"
    )


def test_reverse_dep_detects_recursive_nested_include(monkeypatch):
    module = _load_module()
    monkeypatch.chdir(_repo_root())

    result = module._reverse_dep_basenames(["context/core/errors_example.py"])

    assert "core/cloud" in result


def test_reverse_dep_respects_selected_function_changes(tmp_path, monkeypatch):
    module = _load_module()
    monkeypatch.chdir(tmp_path)

    prompt_dir = tmp_path / "prompts"
    context_dir = tmp_path / "context"
    prompt_dir.mkdir()
    context_dir.mkdir()

    (prompt_dir / "old_consumer_python.prompt").write_text(
        '<include select="def:old_func">context/shared_example.py</include>',
        encoding="utf-8",
    )
    (prompt_dir / "new_consumer_python.prompt").write_text(
        '<include select="def:new_func">context/shared_example.py</include>',
        encoding="utf-8",
    )
    (context_dir / "shared_example.py").write_text(
        "def old_func():\n    return 'old'\n\n"
        "def new_func():\n    return 'new'\n",
        encoding="utf-8",
    )

    monkeypatch.setattr(
        module,
        "_changed_python_defs",
        lambda path, diff_base: {"new_func"}
        if path == "context/shared_example.py"
        else None,
    )

    result = module._reverse_dep_basenames(
        ["context/shared_example.py"], diff_base="origin/main...HEAD"
    )

    assert "new_consumer" in result
    assert "old_consumer" not in result


def test_reverse_dep_without_diff_base_keeps_conservative_matching(
    tmp_path, monkeypatch
):
    module = _load_module()
    monkeypatch.chdir(tmp_path)

    prompt_dir = tmp_path / "prompts"
    context_dir = tmp_path / "context"
    prompt_dir.mkdir()
    context_dir.mkdir()

    (prompt_dir / "old_consumer_python.prompt").write_text(
        '<include select="def:old_func">context/shared_example.py</include>',
        encoding="utf-8",
    )
    (context_dir / "shared_example.py").write_text(
        "def old_func():\n    return 'old'\n",
        encoding="utf-8",
    )

    result = module._reverse_dep_basenames(["context/shared_example.py"])

    assert "old_consumer" in result


def test_reverse_dep_detects_include_many(monkeypatch):
    module = _load_module()
    monkeypatch.chdir(_repo_root())

    result = module._reverse_dep_basenames(["context/auto_update_example.py"])

    assert "core/cli" in result


def test_extract_include_refs_splits_on_newlines():
    """<include-many> bodies often list one entry per line — both commas and
    newlines must be honored. The preprocessor and sync-order code both accept
    newline-delimited entries (see frontend/components/...GenerationProgressModal
    for a real example), so the reverse-dep scan needs to as well."""
    module = _load_module()

    body = "<include-many>\na.py\nb.py\n</include-many>"
    refs = module._extract_include_refs(body)
    assert refs == [("a.py", None), ("b.py", None)]

    indented = (
        "<include-many>\n"
        "    ./Icon/CheckIcon.tsx\n"
        "    ./Icon/SpinnerIcon.tsx\n"
        "</include-many>"
    )
    refs = module._extract_include_refs(indented)
    assert refs == [
        ("Icon/CheckIcon.tsx", None),
        ("Icon/SpinnerIcon.tsx", None),
    ]


def test_reverse_dep_detects_newline_delimited_include_many(tmp_path, monkeypatch):
    """A real prompt with newline-only include-many entries must still pull its
    consumer into auto-heal when one of those entries changes."""
    module = _load_module()
    monkeypatch.chdir(tmp_path)

    prompt_dir = tmp_path / "pdd" / "prompts" / "frontend" / "components"
    prompt_dir.mkdir(parents=True)
    (prompt_dir / "Modal_typescriptreact.prompt").write_text(
        "<include-many>\n"
        "    ./Icon/CheckIcon.tsx\n"
        "    ./Icon/SpinnerIcon.tsx\n"
        "</include-many>\n"
    )

    result = module._reverse_dep_basenames(
        ["pdd/prompts/frontend/components/Icon/CheckIcon.tsx"]
    )

    assert "frontend/components/Modal" in result


def test_detect_combines_nested_direct_and_reverse_dependencies(monkeypatch):
    module = _load_module()
    monkeypatch.chdir(_repo_root())
    monkeypatch.setattr(
        module,
        "_git_changed_files",
        lambda diff_base: [
            "pdd/server/routes/auth.py",
            "context/auto_update_example.py",
        ],
    )

    result = module.detect("origin/main...HEAD")

    assert "server/routes/auth" in result
    assert "core/cli" in result


def test_detect_excludes_package_main_shim(monkeypatch):
    module = _load_module()
    monkeypatch.chdir(_repo_root())
    monkeypatch.setattr(
        module,
        "_git_changed_files",
        lambda diff_base: [
            "pdd/__main__.py",
            "pdd/prompts/__main___python.prompt",
            "context/__main___example.py",
            "tests/test___main__.py",
        ],
    )

    assert module.detect("origin/main...HEAD") == []
