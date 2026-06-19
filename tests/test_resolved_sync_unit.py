"""Tests for pdd.resolved_sync_unit (issue #1675 full ResolvedSyncUnit)."""
from __future__ import annotations

from pathlib import Path

from pdd.resolved_sync_unit import ResolvedSyncUnit, resolve_sync_unit

_ROOT = (
    'version: "1.0"\n'
    "contexts:\n"
    "  extensions-github_pdd_app:\n"
    '    paths: ["extensions/github_pdd_app/**"]\n'
    "    defaults:\n"
    '      prompts_dir: "prompts"\n'
    "  default:\n"
    '    paths: ["**"]\n'
    "    defaults:\n"
    '      prompts_dir: "prompts"\n'
)

_NESTED_SPECIFIC = (
    'version: "1.0"\n'
    "contexts:\n"
    "  pdd_executor_pkg:\n"
    '    paths: ["pdd_codex*", "src/**"]\n'
    "    defaults:\n"
    '      prompts_dir: "prompts"\n'
    '      generate_output_path: "pdd/"\n'
    '      test_output_path: "tests/"\n'
    "  default:\n"
    '    paths: ["**"]\n'
    "    defaults:\n"
    '      prompts_dir: "prompts"\n'
)

_DEFAULT_ONLY = (
    'version: "1.0"\n'
    "contexts:\n"
    "  default:\n"
    '    paths: ["**"]\n'
    "    defaults:\n"
    '      prompts_dir: "prompts"\n'
)


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def test_requested_context_valid_is_forwarded(tmp_path):
    _write(tmp_path / ".pddrc", _ROOT)
    unit = resolve_sync_unit(
        "extensions/github_pdd_app/foo",
        "extensions/github_pdd_app/foo",
        tmp_path,
        requested_context="extensions-github_pdd_app",
    )
    assert unit.context == "extensions-github_pdd_app"
    assert unit.pddrc_path == tmp_path / ".pddrc"


def test_root_context_substituted_by_nested_specific(tmp_path):
    _write(tmp_path / ".pddrc", _ROOT)
    nested = tmp_path / "extensions" / "github_pdd_app"
    _write(nested / ".pddrc", _NESTED_SPECIFIC)
    unit = resolve_sync_unit(
        "pdd_codex", "pdd_codex", nested,
        requested_context="extensions-github_pdd_app",
    )
    # Root context is invalid for the nested cwd -> substitute the nested one.
    assert unit.context == "pdd_executor_pkg"
    assert unit.generate_output_path == nested / "pdd"
    assert unit.test_output_path == nested / "tests"


def test_default_only_nested_omits_invalid_parent_context(tmp_path):
    # Req 3: a nested project with only a default context must OMIT --context
    # when the parent context is invalid there, not fail.
    _write(tmp_path / ".pddrc", _ROOT)
    nested = tmp_path / "apps" / "foo" / "service"
    _write(nested / ".pddrc", _DEFAULT_ONLY)
    unit = resolve_sync_unit(
        "widget", "widget", nested,
        requested_context="extensions-github_pdd_app",
    )
    assert unit.context is None
    assert unit.pddrc_path == nested / ".pddrc"


def test_no_requested_context_resolves_specific(tmp_path):
    nested = tmp_path / "extensions" / "github_pdd_app"
    _write(nested / ".pddrc", _NESTED_SPECIFIC)
    unit = resolve_sync_unit("pdd_codex", "pdd_codex", nested)
    assert unit.context == "pdd_executor_pkg"


def test_no_pddrc_yields_no_context(tmp_path):
    sub = tmp_path / "proj"
    sub.mkdir()
    unit = resolve_sync_unit("mod", "mod", sub, requested_context="whatever")
    assert unit.context is None
    assert unit.prompts_dir == sub / "prompts"
    assert unit.pddrc_path is None


def test_with_cwd_rebases_paths_preserves_context(tmp_path):
    nested = tmp_path / "extensions" / "github_pdd_app"
    _write(nested / ".pddrc", _NESTED_SPECIFIC)
    unit = resolve_sync_unit("pdd_codex", "pdd_codex", nested)
    worktree = tmp_path / "wt" / "extensions" / "github_pdd_app"
    remapped = unit.with_cwd(worktree)
    assert remapped.cwd == worktree
    assert remapped.context == "pdd_executor_pkg"
    assert remapped.pddrc_path == worktree / ".pddrc"
    assert remapped.generate_output_path == worktree / "pdd"
    assert isinstance(remapped, ResolvedSyncUnit)
