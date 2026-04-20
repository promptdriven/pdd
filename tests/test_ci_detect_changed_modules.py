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


def test_reverse_dep_detects_include_many(monkeypatch):
    module = _load_module()
    monkeypatch.chdir(_repo_root())

    result = module._reverse_dep_basenames(["context/auto_update_example.py"])

    assert "core/cli" in result


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
