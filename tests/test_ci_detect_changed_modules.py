"""Tests for scripts/ci_detect_changed_modules.py."""

from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest


def _load_module():
    script_path = (
        Path(__file__).resolve().parents[1] / "scripts" / "ci_detect_changed_modules.py"
    )
    return _load_module_from_path("ci_detect_changed_modules", script_path)


def _load_packaged_module():
    script_path = Path(__file__).resolve().parents[1] / "pdd" / "ci_detect_changed_modules.py"
    return _load_module_from_path("pdd_ci_detect_changed_modules", script_path)


def _load_module_from_path(name: str, script_path: Path):
    spec = importlib.util.spec_from_file_location(
        name, script_path
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


def test_basename_excludes_ci_detect_prompt_and_module():
    """The detector's own prompt and packaged copy must never be flagged for
    auto-heal. The bare-basename form covers the canonical path
    (pdd/prompts/ci_detect_changed_modules_python.prompt + the packaged
    module); the path-qualified form is kept as defensive coverage in case
    the prompt is ever relocated back under a subdirectory, since that
    placement would otherwise re-introduce the auto-heal failure mode where
    a bogus pdd/scripts/ci_detect_changed_modules.py path gets fed to
    ``pdd example``."""
    module = _load_module()

    assert (
        module._basename_from_path(
            "pdd/prompts/ci_detect_changed_modules_python.prompt"
        )
        is None
    )
    assert module._basename_from_path("pdd/ci_detect_changed_modules.py") is None
    assert (
        module._basename_from_path(
            "pdd/prompts/scripts/ci_detect_changed_modules_python.prompt"
        )
        is None
    )


def test_basename_excludes_agent_reviewed_model_catalog():
    module = _load_module()

    assert module._basename_from_path("pdd/generate_model_catalog.py") is None
    assert (
        module._basename_from_path("pdd/prompts/generate_model_catalog_python.prompt")
        is None
    )
    assert module._basename_from_path("context/generate_model_catalog_example.py") is None
    assert module._basename_from_path("tests/test_generate_model_catalog.py") is None


def test_basename_excludes_external_canonical_pdd_cloud_prompts():
    """Packaged canonical GitHub App prompts have no local PDD code files.

    They must not trigger headless auto-heal against bogus paths such as
    pdd/src/clients/github_client.py.
    """
    for module in (_load_module(), _load_packaged_module()):
        assert (
            module._basename_from_path(
                "pdd/prompts/src/clients/github_client_Python.prompt"
            )
            is None
        )
        assert (
            module._basename_from_path(
                "pdd/prompts/src/pdd_issue_runner_job_Python.prompt"
            )
            is None
        )
        assert (
            module._basename_from_path(
                "pdd/prompts/src/services/pdd_issue_completion_evidence_Python.prompt"
            )
            is None
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


def test_reverse_dep_matches_exact_repo_and_prompt_relative_paths(tmp_path, monkeypatch):
    """Repository and prompt-relative includes must resolve without basename matching."""
    module = _load_module()
    monkeypatch.chdir(tmp_path)

    prompt_dir = tmp_path / "pdd" / "prompts" / "nested"
    prompt_dir.mkdir(parents=True)
    (tmp_path / "pdd" / "shared.py").write_text(
        "def root_change():\n    return 'root'\n", encoding="utf-8"
    )
    relative_target = prompt_dir / "parts" / "shared.py"
    relative_target.parent.mkdir()
    relative_target.write_text(
        "def relative_change():\n    return 'relative'\n", encoding="utf-8"
    )
    (prompt_dir / "repo_consumer_python.prompt").write_text(
        "<include>pdd/shared.py</include>", encoding="utf-8"
    )
    (prompt_dir / "relative_consumer_python.prompt").write_text(
        '<include select="def:relative_change">./parts/shared.py</include>',
        encoding="utf-8",
    )

    monkeypatch.setattr(
        module,
        "_changed_python_defs",
        lambda path, diff_base: {"relative_change"}
        if path == "pdd/prompts/nested/parts/shared.py"
        else None,
    )

    result = module._reverse_dep_basenames(
        ["pdd/shared.py", "pdd/prompts/nested/parts/shared.py"],
        diff_base="origin/main...HEAD",
    )

    assert "nested/repo_consumer" in result
    assert "nested/relative_consumer" in result


def test_reverse_dep_projects_packaged_prompt_to_source_tree(monkeypatch):
    """Packaged prompt-relative includes resolve against the canonical source tree."""
    monkeypatch.chdir(_repo_root())

    for module in (_load_module(), _load_packaged_module()):
        result = module._reverse_dep_basenames(
            ["pdd/frontend/components/CreatePromptModal.tsx"]
        )

        assert "frontend/components/PromptSelector" in result


def test_reverse_dep_ignores_cross_directory_basename_collisions(
    tmp_path, monkeypatch
):
    """An include must not pull in a similarly named module from another directory."""
    module = _load_module()
    monkeypatch.chdir(tmp_path)

    prompt_dir = tmp_path / "prompts"
    prompt_dir.mkdir()
    (tmp_path / "pdd").mkdir()
    (tmp_path / "pdd" / "evidence_store.py").write_text(
        "def target():\n    return 'target'\n", encoding="utf-8"
    )
    (tmp_path / "pdd" / "agentic_sync_runner.py").write_text(
        "def target():\n    return 'target'\n", encoding="utf-8"
    )
    (prompt_dir / "evidence_consumer_python.prompt").write_text(
        "<include>pdd/evidence_store.py</include>", encoding="utf-8"
    )
    (prompt_dir / "runner_consumer_python.prompt").write_text(
        "<include>pdd/agentic_sync_runner.py</include>", encoding="utf-8"
    )

    result = module._reverse_dep_basenames(
        ["pdd/sync_core/evidence_store.py", "pdd/sync_core/runner.py"]
    )

    assert "evidence_consumer" not in result
    assert "runner_consumer" not in result


def test_extract_include_refs_honors_path_attribute_precedence():
    module = _load_module()

    refs = module._extract_include_refs(
        '<include path="pdd/right.py">pdd/wrong.py</include>\n'
        '<include select="def:chosen" path="pdd/right.py" />'
    )

    assert refs == [("pdd/right.py", None), ("pdd/right.py", {"chosen"})]


def test_reverse_dep_path_attribute_tracks_target_not_body(tmp_path, monkeypatch):
    module = _load_module()
    monkeypatch.chdir(tmp_path)

    prompt_dir = tmp_path / "prompts"
    source_dir = tmp_path / "pdd"
    prompt_dir.mkdir()
    source_dir.mkdir()
    (source_dir / "right.py").write_text("right = True\n", encoding="utf-8")
    (source_dir / "wrong.py").write_text("wrong = True\n", encoding="utf-8")
    (prompt_dir / "consumer_python.prompt").write_text(
        '<include path="pdd/right.py">pdd/wrong.py</include>', encoding="utf-8"
    )

    assert "consumer" in module._reverse_dep_basenames(["pdd/right.py"])
    assert "consumer" not in module._reverse_dep_basenames(["pdd/wrong.py"])


def test_reverse_dep_traverses_complete_include_closure(tmp_path, monkeypatch):
    module = _load_module()
    monkeypatch.chdir(tmp_path)

    prompt_dir = tmp_path / "prompts" / "nested"
    source_dir = tmp_path / "pdd"
    prompt_dir.mkdir(parents=True)
    source_dir.mkdir()
    (source_dir / "leaf.py").write_text("leaf = True\n", encoding="utf-8")
    (prompt_dir / "inner_python.prompt").write_text(
        "<include>pdd/leaf.py</include>", encoding="utf-8"
    )
    (prompt_dir / "outer_python.prompt").write_text(
        "<include>./inner_python.prompt</include>", encoding="utf-8"
    )

    result = module._reverse_dep_basenames(["pdd/leaf.py"])

    assert result >= {"nested/inner", "nested/outer"}


def test_reverse_dep_closure_traverses_included_artifacts(tmp_path, monkeypatch):
    module = _load_module()
    monkeypatch.chdir(tmp_path)

    prompt_dir = tmp_path / "prompts"
    docs_dir = tmp_path / "docs"
    source_dir = tmp_path / "pdd"
    prompt_dir.mkdir()
    docs_dir.mkdir()
    source_dir.mkdir()
    (source_dir / "leaf.py").write_text("leaf = True\n", encoding="utf-8")
    (docs_dir / "inner.md").write_text(
        "<include>pdd/leaf.py</include>", encoding="utf-8"
    )
    (prompt_dir / "outer_python.prompt").write_text(
        "<include>docs/inner.md</include>", encoding="utf-8"
    )

    assert "outer" in module._reverse_dep_basenames(["pdd/leaf.py"])


@pytest.mark.timeout(1)
def test_reverse_dep_include_cycle_terminates_deterministically(tmp_path, monkeypatch):
    module = _load_module()
    monkeypatch.chdir(tmp_path)

    prompt_dir = tmp_path / "prompts"
    source_dir = tmp_path / "pdd"
    prompt_dir.mkdir()
    source_dir.mkdir()
    (source_dir / "leaf.py").write_text("leaf = True\n", encoding="utf-8")
    (prompt_dir / "a_python.prompt").write_text(
        "<include>pdd/leaf.py</include><include>./b_python.prompt</include>",
        encoding="utf-8",
    )
    (prompt_dir / "b_python.prompt").write_text(
        "<include>./a_python.prompt</include>", encoding="utf-8"
    )

    result = module._reverse_dep_basenames(["pdd/leaf.py"])

    assert result == {"a", "b"}


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


def test_prompt_contract_requires_exact_transitive_include_matching():
    prompt = (
        _repo_root() / "pdd" / "prompts" / "ci_detect_changed_modules_python.prompt"
    ).read_text(encoding="utf-8")

    assert "Never use suffix or bare-basename matching" in prompt
    assert "complete transitive reverse-dependency closure" in prompt
    assert "`path=` overrides the include body" in prompt
