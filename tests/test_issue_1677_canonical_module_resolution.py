"""Regression tests for issue #1677.

`pdd sync` must resolve modules by canonical path, not ambiguous short
basenames. When a bare basename (e.g. Next.js ``page``) maps to more than one
architecture.json module, PDD must fail fast and list the choices instead of
silently generating to the wrong path (e.g. ``frontend/src/page.tsx``).

These tests are intentionally written before the fix (TDD) and cover the
acceptance criteria in the issue.
"""
import json
from pathlib import Path

import pytest

from pdd.sync_determine_operation import (
    AmbiguousModuleError,
    get_pdd_file_paths,
    sync_determine_operation,
    _architecture_module_choices,
    _safe_basename,
)
from pdd.agentic_sync import _drop_ambiguous_basenames


# --------------------------------------------------------------------------- #
# Fixtures
# --------------------------------------------------------------------------- #
def _write_pddrc(root: Path, generate_output_path: str = "src/") -> None:
    (root / ".pddrc").write_text(
        "contexts:\n"
        "  default:\n"
        "    paths: ['**']\n"
        "    defaults:\n"
        "      prompts_dir: 'prompts'\n"
        f"      generate_output_path: '{generate_output_path}'\n"
    )


def _make_two_page_project(root: Path) -> None:
    """Two distinct `page` modules sharing the leaf basename `page`."""
    _write_pddrc(root)
    arch = [
        {"filename": "page_TypeScriptReact.prompt", "filepath": "src/app/login/page.tsx"},
        {"filename": "page_TypeScriptReact.prompt", "filepath": "src/app/settings/page.tsx"},
        {"filename": "dashboard_TypeScriptReact.prompt", "filepath": "src/app/dashboard/dashboard.tsx"},
    ]
    (root / "architecture.json").write_text(json.dumps(arch, indent=2))
    for sub in ("login", "settings"):
        d = root / "prompts" / "app" / sub
        d.mkdir(parents=True)
        (d / "page_TypeScriptReact.prompt").write_text(f"{sub} page")
    dd = root / "prompts" / "app" / "dashboard"
    dd.mkdir(parents=True)
    (dd / "dashboard_TypeScriptReact.prompt").write_text("dashboard")


# --------------------------------------------------------------------------- #
# CLI / core resolver layer
# --------------------------------------------------------------------------- #
def test_bare_ambiguous_basename_raises(tmp_path, monkeypatch):
    """`pdd sync page` must fail when two `page` modules exist."""
    _make_two_page_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    with pytest.raises(AmbiguousModuleError) as exc:
        get_pdd_file_paths("page", "TypeScriptReact", prompts_dir="prompts")
    msg = str(exc.value)
    # The error lists the conflicting canonical targets.
    assert "page" in msg
    assert "login" in msg and "settings" in msg


def test_ambiguity_choices_helper_lists_distinct_targets(tmp_path, monkeypatch):
    _make_two_page_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    choices = _architecture_module_choices(
        tmp_path / "architecture.json", "page", "TypeScriptReact"
    )
    assert len(choices) == 2
    joined = " ".join(choices)
    assert "login" in joined and "settings" in joined


def test_unique_bare_basename_still_resolves(tmp_path, monkeypatch):
    """Backward compat: a unique short name must NOT be broken."""
    _make_two_page_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    # `dashboard` is unique -> resolves, no raise.
    paths = get_pdd_file_paths("dashboard", "TypeScriptReact", prompts_dir="prompts")
    assert Path(paths["code"]).as_posix().endswith("src/app/dashboard/dashboard.tsx")


def test_ambiguous_leaf_gets_distinct_example_test_paths(tmp_path, monkeypatch):
    """Two path-qualified modules sharing an ambiguous leaf (`page`) must NOT collide
    on `examples/page_example.tsx` / `tests/test_page.tsx` — the example/test stems are
    derived from the canonical code path so they stay distinct."""
    _make_two_page_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    login = get_pdd_file_paths("app/login/page", "TypeScriptReact", prompts_dir="prompts")
    settings = get_pdd_file_paths("app/settings/page", "TypeScriptReact", prompts_dir="prompts")
    # Source files already resolve correctly.
    assert Path(login["code"]).as_posix().endswith("src/app/login/page.tsx")
    assert Path(settings["code"]).as_posix().endswith("src/app/settings/page.tsx")
    # Example/test artifacts must be distinct (the collision the issue flagged).
    assert Path(login["example"]) != Path(settings["example"])
    assert Path(login["test"]) != Path(settings["test"])
    assert "page_example" != Path(login["example"]).name  # not the bare collision name


def test_unique_leaf_keeps_flat_example_test_paths(tmp_path, monkeypatch):
    """Backward compat: a unique leaf keeps the flat `examples/<stem>_example` path."""
    _make_two_page_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    paths = get_pdd_file_paths("dashboard", "TypeScriptReact", prompts_dir="prompts")
    assert Path(paths["example"]).name == "dashboard_example.tsx"
    assert Path(paths["test"]).name == "test_dashboard.tsx"


def test_path_qualified_basename_resolves_correct_module(tmp_path, monkeypatch):
    """`pdd sync app/login/page` resolves to the login page, not settings."""
    _make_two_page_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    paths = get_pdd_file_paths("app/login/page", "TypeScriptReact", prompts_dir="prompts")
    assert Path(paths["code"]).as_posix().endswith("src/app/login/page.tsx")


def test_wrong_path_qualified_name_does_not_resolve_to_leaf(tmp_path, monkeypatch):
    """A wrong/foreign path-qualified name (`foo/page`, no such directory) must NOT
    silently resolve to a same-leaf module in a different directory
    (`app/login/page`). It is treated as not-found, not the wrong module."""
    _make_two_page_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    paths = get_pdd_file_paths("foo/page", "TypeScriptReact", prompts_dir="prompts")
    code = Path(paths["code"]).as_posix()
    prompt = Path(paths["prompt"]).as_posix()
    # Must not have resolved to the login (or settings) module.
    assert not code.endswith("src/app/login/page.tsx")
    assert not code.endswith("src/app/settings/page.tsx")
    assert "app/login/page_TypeScriptReact.prompt" not in prompt
    assert "app/settings/page_TypeScriptReact.prompt" not in prompt


def test_correct_path_qualified_name_still_resolves(tmp_path, monkeypatch):
    """The strict directory check must NOT break a correct path-qualified name."""
    _make_two_page_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    paths = get_pdd_file_paths("app/settings/page", "TypeScriptReact", prompts_dir="prompts")
    assert Path(paths["code"]).as_posix().endswith("src/app/settings/page.tsx")


def test_wrong_prefix_multipart_qualified_name_does_not_resolve(tmp_path, monkeypatch):
    """`foo/login/page` (wrong top directory) must NOT resolve to `app/login/page`
    just because the last two path parts match — the full path-qualified basename must
    be a suffix of the module filepath."""
    _make_two_page_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    paths = get_pdd_file_paths("foo/login/page", "TypeScriptReact", prompts_dir="prompts")
    assert not Path(paths["code"]).as_posix().endswith("src/app/login/page.tsx")


def test_shorter_qualified_form_still_resolves(tmp_path, monkeypatch):
    """A legitimately shorter qualified form (`login/page`) still resolves to
    `app/login/page` (it is a true path-suffix of the filepath)."""
    _make_two_page_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    paths = get_pdd_file_paths("login/page", "TypeScriptReact", prompts_dir="prompts")
    assert Path(paths["code"]).as_posix().endswith("src/app/login/page.tsx")


def test_qualified_name_does_not_borrow_root_module_architecture(tmp_path, monkeypatch):
    """A wrong qualified name `foo/page` must not borrow a root `page` module's
    architecture entry (filepath/prompt). It is treated as a new, path-qualified
    module instead — its prompt is expected under `prompts/foo/`, not the root one.

    (Note: deriving the *code* path for such an unmatched new module still flows
    through `construct_paths`, which is out of scope here; this test pins the
    resolver behavior — the existing root module is not adopted.)"""
    _write_pddrc(tmp_path)
    (tmp_path / "architecture.json").write_text(json.dumps(
        [{"filename": "page_TypeScriptReact.prompt", "filepath": "src/page.tsx"}]))
    pdir = tmp_path / "prompts"
    pdir.mkdir()
    (pdir / "page_TypeScriptReact.prompt").write_text("root page")
    monkeypatch.chdir(tmp_path)
    paths = get_pdd_file_paths("foo/page", "TypeScriptReact", prompts_dir="prompts")
    # The root module's own prompt file is not adopted for the foreign qualified name.
    assert Path(paths["prompt"]).as_posix().endswith("prompts/foo/page_TypeScriptReact.prompt")


def test_language_variants_not_ambiguous(tmp_path, monkeypatch):
    """A module that exists in two languages (foo.py + foo.ts) is NOT ambiguous
    for a specific language query (codex false-positive guard)."""
    _write_pddrc(tmp_path)
    arch = [
        {"filename": "foo_Python.prompt", "filepath": "src/foo.py"},
        {"filename": "foo_TypeScript.prompt", "filepath": "src/foo.ts"},
    ]
    (tmp_path / "architecture.json").write_text(json.dumps(arch))
    pdir = tmp_path / "prompts"
    pdir.mkdir()
    (pdir / "foo_Python.prompt").write_text("py")
    (pdir / "foo_TypeScript.prompt").write_text("ts")
    monkeypatch.chdir(tmp_path)
    paths = get_pdd_file_paths("foo", "Python", prompts_dir="prompts")
    assert Path(paths["code"]).as_posix().endswith("src/foo.py")


def test_ambiguity_propagates_through_sync_determine_operation(tmp_path, monkeypatch):
    """The ambiguity error must NOT be swallowed by the broad `except Exception`
    in _perform_sync_analysis (which would let sync silently proceed)."""
    _make_two_page_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    with pytest.raises(AmbiguousModuleError):
        sync_determine_operation(
            "page", "TypeScriptReact", target_coverage=80.0, read_only=True
        )


def test_pr1828_fixture_does_not_generate_src_page(tmp_path, monkeypatch):
    """Mirror of pdd_cloud PR #1828: many `page` modules, root-prefixed filepaths.
    Must raise rather than generate the wrong `src/page.tsx`."""
    _write_pddrc(tmp_path, generate_output_path="src/")
    arch = [
        {"filename": "page_TypeScriptReact.prompt", "filepath": "src/app/login/page.tsx"},
        {"filename": "page_TypeScriptReact.prompt", "filepath": "src/app/settings/security/page.tsx"},
        {"filename": "page_TypeScriptReact.prompt", "filepath": "src/app/settings/github/page.tsx"},
    ]
    (tmp_path / "architecture.json").write_text(json.dumps(arch))
    for sub in ("login", "settings/security", "settings/github"):
        d = tmp_path / "prompts" / "app" / sub
        d.mkdir(parents=True)
        (d / "page_TypeScriptReact.prompt").write_text("page")
    monkeypatch.chdir(tmp_path)
    with pytest.raises(AmbiguousModuleError):
        get_pdd_file_paths("page", "TypeScriptReact", prompts_dir="prompts")


# --------------------------------------------------------------------------- #
# Agentic layer — driven from real architecture.json files under project_root
# (the agentic guard resolves each entry's filepath against its OWN arch dir).
# --------------------------------------------------------------------------- #
def _write_arch(root: Path, entries, *, subdir: str = "") -> None:
    arch_dir = root / subdir if subdir else root
    arch_dir.mkdir(parents=True, exist_ok=True)
    (arch_dir / "architecture.json").write_text(json.dumps(entries, indent=2))


def _two_page_project(root: Path) -> None:
    _write_arch(root, [
        {"filename": "page_TypeScriptReact.prompt", "filepath": "src/app/login/page.tsx"},
        {"filename": "page_TypeScriptReact.prompt", "filepath": "src/app/settings/page.tsx"},
        {"filename": "dashboard_TypeScriptReact.prompt", "filepath": "src/app/dashboard/dashboard.tsx"},
    ])


def test_agentic_drops_ambiguous_bare_basename(tmp_path):
    _two_page_project(tmp_path)
    kept, ambiguous = _drop_ambiguous_basenames(["page"], tmp_path)
    assert kept == []
    assert "page" in ambiguous
    assert len(ambiguous["page"]) == 2


def test_agentic_keeps_path_qualified_basename(tmp_path):
    """A path-qualified name from the branch diff already disambiguates."""
    _two_page_project(tmp_path)
    kept, ambiguous = _drop_ambiguous_basenames(["app/login/page"], tmp_path)
    assert kept == ["app/login/page"]
    assert ambiguous == {}


def test_agentic_keeps_unique_bare_basename(tmp_path):
    _two_page_project(tmp_path)
    kept, ambiguous = _drop_ambiguous_basenames(["dashboard"], tmp_path)
    assert kept == ["dashboard"]
    assert ambiguous == {}


def test_agentic_does_not_flag_root_vs_nested_same_module(tmp_path):
    """The SAME file declared in both a root and a nested architecture.json (the
    Sidebar case) resolves to one canonical path and must NOT be flagged ambiguous.
    Root arch lists it frontend-rooted; nested frontend/architecture.json lists it
    relative to frontend/ — both resolve to <root>/frontend/src/.../Sidebar.tsx."""
    _write_arch(tmp_path, [
        {"filename": "Sidebar_TypeScriptReact.prompt",
         "filepath": "frontend/src/components/layout/Sidebar.tsx"},
    ])
    _write_arch(tmp_path, [
        {"filename": "Sidebar_TypeScriptReact.prompt",
         "filepath": "src/components/layout/Sidebar.tsx"},
    ], subdir="frontend")
    kept, ambiguous = _drop_ambiguous_basenames(["Sidebar"], tmp_path)
    assert kept == ["Sidebar"]
    assert ambiguous == {}


def test_agentic_flags_same_name_in_different_subprojects(tmp_path):
    """Two DIFFERENT files in different sub-projects, each spelled `src/page.tsx`
    relative to its own architecture.json, are genuinely ambiguous — the combined
    view must resolve them against their own arch dirs and keep them distinct
    (regression for the combined-architecture false negative)."""
    _write_arch(tmp_path, [
        {"filename": "page_TypeScriptReact.prompt", "filepath": "src/page.tsx"},
    ], subdir="appA")
    _write_arch(tmp_path, [
        {"filename": "page_TypeScriptReact.prompt", "filepath": "src/page.tsx"},
    ], subdir="appB")
    kept, ambiguous = _drop_ambiguous_basenames(["page"], tmp_path)
    assert kept == []
    assert "page" in ambiguous
    assert len(ambiguous["page"]) == 2


def test_agentic_does_not_flag_language_variants(tmp_path):
    """A module that exists in two languages (foo.py + foo.ts) is one module, not
    an ambiguous pair (codex false-positive guard)."""
    _write_arch(tmp_path, [
        {"filename": "foo_Python.prompt", "filepath": "src/foo.py"},
        {"filename": "foo_TypeScript.prompt", "filepath": "src/foo.ts"},
    ])
    kept, ambiguous = _drop_ambiguous_basenames(["foo"], tmp_path)
    assert kept == ["foo"]
    assert ambiguous == {}


# --------------------------------------------------------------------------- #
# Metadata backward-compat (acceptance criteria)
# --------------------------------------------------------------------------- #
def _unregistered_project(root: Path, *, generate="src/", example="examples/", test="tests/") -> None:
    (root / ".pddrc").write_text(
        "contexts:\n  default:\n    paths: ['**']\n    defaults:\n"
        "      prompts_dir: 'prompts'\n"
        f"      generate_output_path: '{generate}'\n"
        f"      example_output_path: '{example}'\n"
        f"      test_output_path: '{test}'\n"
    )
    (root / "architecture.json").write_text("[]")  # nothing registered


def test_unregistered_qualified_module_preserves_directory(tmp_path, monkeypatch):
    """A path-qualified module with NO architecture entry (a new module) must keep its
    directory in code/example/test instead of collapsing to the bare leaf — otherwise
    two `*/page` modules overwrite each other's `src/page.tsx`/`examples/page_example`."""
    _unregistered_project(tmp_path)
    d = tmp_path / "prompts" / "foo"
    d.mkdir(parents=True)
    (d / "page_TypeScriptReact.prompt").write_text("p")
    monkeypatch.chdir(tmp_path)
    paths = get_pdd_file_paths("foo/page", "TypeScriptReact", prompts_dir="prompts")
    assert Path(paths["code"]).as_posix().endswith("src/foo/page.tsx")
    assert Path(paths["example"]).as_posix().endswith("examples/foo/page_example.tsx")
    assert Path(paths["test"]).as_posix().endswith("tests/foo/test_page.tsx")


def test_unregistered_qualified_two_modules_do_not_collide(tmp_path, monkeypatch):
    _unregistered_project(tmp_path)
    for sub in ("foo", "bar"):
        d = tmp_path / "prompts" / sub
        d.mkdir(parents=True)
        (d / "page_TypeScriptReact.prompt").write_text("p")
    monkeypatch.chdir(tmp_path)
    foo = get_pdd_file_paths("foo/page", "TypeScriptReact", prompts_dir="prompts")
    bar = get_pdd_file_paths("bar/page", "TypeScriptReact", prompts_dir="prompts")
    assert Path(foo["code"]) != Path(bar["code"])
    assert Path(foo["example"]) != Path(bar["example"])
    assert Path(foo["test"]) != Path(bar["test"])


def test_unregistered_flat_module_unaffected(tmp_path, monkeypatch):
    _unregistered_project(tmp_path)
    (tmp_path / "prompts").mkdir()
    (tmp_path / "prompts" / "widget_TypeScriptReact.prompt").write_text("p")
    monkeypatch.chdir(tmp_path)
    paths = get_pdd_file_paths("widget", "TypeScriptReact", prompts_dir="prompts")
    assert Path(paths["code"]).as_posix().endswith("src/widget.tsx")
    assert Path(paths["example"]).name == "widget_example.tsx"
    assert Path(paths["test"]).name == "test_widget.tsx"


def test_unregistered_qualified_shared_area_not_duplicated(tmp_path, monkeypatch):
    """When the configured output dir shares an area with the basename's directory
    (`frontend/src/` + `frontend/app/login/page`), the shared segment is recognised and
    the result is `frontend/src/app/login/page.tsx` — not duplicated, not collapsed."""
    _unregistered_project(tmp_path, generate="frontend/src/", example="frontend/src/", test="frontend/src/")
    d = tmp_path / "prompts" / "frontend" / "app" / "login"
    d.mkdir(parents=True)
    (d / "page_TypeScriptReact.prompt").write_text("p")
    monkeypatch.chdir(tmp_path)
    paths = get_pdd_file_paths("frontend/app/login/page", "TypeScriptReact", prompts_dir="prompts")
    assert Path(paths["code"]).as_posix().endswith("frontend/src/app/login/page.tsx")
    assert Path(paths["code"]).as_posix().count("frontend/") == 1


def test_unregistered_qualified_tail_head_overlap(tmp_path, monkeypatch):
    """`app/login/page` under `src/app/` resolves to `src/app/login/page.tsx` (the
    output dir's tail `app` overlaps the basename's head — no `src/app/app/...`)."""
    _unregistered_project(tmp_path, generate="src/app/", example="src/app/", test="src/app/")
    d = tmp_path / "prompts" / "app" / "login"
    d.mkdir(parents=True)
    (d / "page_TypeScriptReact.prompt").write_text("p")
    monkeypatch.chdir(tmp_path)
    paths = get_pdd_file_paths("app/login/page", "TypeScriptReact", prompts_dir="prompts")
    assert Path(paths["code"]).as_posix().endswith("src/app/login/page.tsx")
    assert "app/app" not in Path(paths["code"]).as_posix()


def test_unregistered_qualified_repo_path_contains_prefix(tmp_path, monkeypatch):
    """A repo path component equal to the basename's directory (e.g. the project living
    under a `foo/` directory) must NOT cause the directory to be dropped — overlap is
    measured against the configured output dir, not the absolute repo path."""
    project = tmp_path / "foo"  # repo path contains 'foo'
    (project / "prompts" / "foo").mkdir(parents=True)
    _unregistered_project(project, generate="src/", example="src/", test="src/")
    (project / "prompts" / "foo" / "page_TypeScriptReact.prompt").write_text("p")
    monkeypatch.chdir(project)
    paths = get_pdd_file_paths("foo/page", "TypeScriptReact", prompts_dir="prompts")
    assert Path(paths["code"]).as_posix().endswith("src/foo/page.tsx")


def test_cli_sync_ambiguous_exits_nonzero(tmp_path, monkeypatch):
    """`pdd sync page` on an ambiguous module must EXIT NON-ZERO (not just print) so CI,
    automation, and the agentic child runners (which treat exit 0 as success) detect the
    failure. The choices must be printed even under --quiet (a hard, actionable error)."""
    from click.testing import CliRunner
    import pdd.cli  # noqa: F401 - registers commands (incl. sync) on the core CLI
    from pdd.core.cli import cli as real_cli

    _make_two_page_project(tmp_path)
    monkeypatch.chdir(tmp_path)

    for extra in ([], ["--quiet"]):
        result = CliRunner().invoke(
            real_cli, ["--no-core-dump", *extra, "sync", "page", "--dry-run"]
        )
        assert result.exit_code != 0, f"expected non-zero exit (args={extra}); output:\n{result.output}"
        assert "Ambiguous module 'page'" in result.output, result.output
        # And it must not have generated the wrong default file.
        assert not (tmp_path / "src" / "page.tsx").exists()


def test_cli_ambiguity_choices_with_dynamic_route_segments(tmp_path, monkeypatch):
    """Next.js dynamic routes (`[id]`, `[slug]`) contain Rich-markup metacharacters. The
    listed choices must show them intact, not swallow them into `src/app/users//page.tsx`."""
    from click.testing import CliRunner
    import pdd.cli  # noqa: F401
    from pdd.core.cli import cli as real_cli

    _write_pddrc(tmp_path)
    arch = [
        {"filename": "page_TypeScriptReact.prompt", "filepath": "src/app/users/[id]/page.tsx"},
        {"filename": "page_TypeScriptReact.prompt", "filepath": "src/app/posts/[id]/page.tsx"},
    ]
    (tmp_path / "architecture.json").write_text(json.dumps(arch))
    for sub in ("users/[id]", "posts/[id]"):
        d = tmp_path / "prompts" / "app" / sub
        d.mkdir(parents=True)
        (d / "page_TypeScriptReact.prompt").write_text("p")
    monkeypatch.chdir(tmp_path)

    result = CliRunner().invoke(real_cli, ["--no-core-dump", "sync", "page", "--dry-run"])
    assert result.exit_code != 0, result.output
    assert "src/app/users/[id]/page.tsx" in result.output, result.output
    assert "src/app/posts/[id]/page.tsx" in result.output, result.output


def test_metadata_key_is_path_aware_for_qualified_names():
    """Path-qualified identity already yields a distinct, path-aware metadata key;
    no mass-rename needed. Old unique bare keys remain stable."""
    assert _safe_basename("app/login/page") == "app_login_page"
    assert _safe_basename("app/settings/page") == "app_settings_page"
    assert _safe_basename("dashboard") == "dashboard"


# --------------------------------------------------------------------------- #
# Matching precision (added after adversarial review)
# --------------------------------------------------------------------------- #
def test_unrelated_module_with_same_filepath_stem_is_not_ambiguous(tmp_path, monkeypatch):
    """A DIFFERENT module whose code file merely happens to be named `page.tsx`
    (e.g. a `home` route -> src/home/page.tsx, prompt `home_*.prompt`) must NOT make
    the uniquely-named `page` module ambiguous. Match is by prompt filename, not
    filepath stem."""
    _write_pddrc(tmp_path)
    arch = [
        {"filename": "page_TypeScriptReact.prompt", "filepath": "src/page.tsx"},
        {"filename": "home_TypeScriptReact.prompt", "filepath": "src/home/page.tsx"},
    ]
    (tmp_path / "architecture.json").write_text(json.dumps(arch))
    pdir = tmp_path / "prompts"
    pdir.mkdir()
    (pdir / "page_TypeScriptReact.prompt").write_text("page")
    (pdir / "home_TypeScriptReact.prompt").write_text("home")
    monkeypatch.chdir(tmp_path)
    # Helper reports a single distinct target -> not ambiguous.
    choices = _architecture_module_choices(tmp_path / "architecture.json", "page", "TypeScriptReact")
    assert choices == ["src/page.tsx"]
    # And resolution proceeds without raising.
    paths = get_pdd_file_paths("page", "TypeScriptReact", prompts_dir="prompts")
    assert Path(paths["code"]).as_posix().endswith("src/page.tsx")
    # Agentic guard agrees (architecture.json on disk under tmp_path).
    kept, ambiguous = _drop_ambiguous_basenames(["page"], tmp_path)
    assert kept == ["page"] and ambiguous == {}


def test_two_same_filename_modules_in_one_arch_are_distinct(tmp_path, monkeypatch):
    """Within a single architecture.json, two entries with the same prompt filename
    but different filepaths are genuinely different modules and stay distinct — they
    must NOT be suffix-collapsed (that collapse only applies to the agentic combined
    multi-architecture view)."""
    _write_pddrc(tmp_path)
    arch = [
        {"filename": "page_TypeScriptReact.prompt", "filepath": "src/page.tsx"},
        {"filename": "page_TypeScriptReact.prompt", "filepath": "frontend/src/page.tsx"},
    ]
    (tmp_path / "architecture.json").write_text(json.dumps(arch))
    monkeypatch.chdir(tmp_path)
    choices = _architecture_module_choices(tmp_path / "architecture.json", "page", "TypeScriptReact")
    assert len(choices) == 2
    with pytest.raises(AmbiguousModuleError):
        get_pdd_file_paths("page", "TypeScriptReact", prompts_dir="prompts")


def test_case_insensitive_filename_ambiguity(tmp_path, monkeypatch):
    """Filename matching is case-insensitive (mirrors _get_filepath_from_architecture)."""
    _write_pddrc(tmp_path)
    arch = [
        {"filename": "Page_TypeScriptReact.prompt", "filepath": "src/app/login/page.tsx"},
        {"filename": "page_typescriptreact.prompt", "filepath": "src/app/settings/page.tsx"},
    ]
    (tmp_path / "architecture.json").write_text(json.dumps(arch))
    monkeypatch.chdir(tmp_path)
    choices = _architecture_module_choices(tmp_path / "architecture.json", "page", "TypeScriptReact")
    assert len(choices) == 2


def test_modules_dict_architecture_format(tmp_path, monkeypatch):
    """Ambiguity detection works for the {"modules": [...]} architecture shape too."""
    _write_pddrc(tmp_path)
    arch = {"modules": [
        {"filename": "page_TypeScriptReact.prompt", "filepath": "src/app/login/page.tsx"},
        {"filename": "page_TypeScriptReact.prompt", "filepath": "src/app/settings/page.tsx"},
    ]}
    (tmp_path / "architecture.json").write_text(json.dumps(arch))
    monkeypatch.chdir(tmp_path)
    with pytest.raises(AmbiguousModuleError):
        get_pdd_file_paths("page", "TypeScriptReact", prompts_dir="prompts")


def test_directory_qualified_arch_filenames_are_detected(tmp_path, monkeypatch):
    """Architecture filenames may be directory-qualified (e.g.
    `app/login/page_TypeScriptReact.prompt`, per normalize_architecture_filenames).
    The guard matches on the filename LEAF so these are still detected as ambiguous
    (otherwise the resolver's recursive lookup would silently pick one)."""
    _write_pddrc(tmp_path)
    arch = [
        {"filename": "app/login/page_TypeScriptReact.prompt", "filepath": "src/app/login/page.tsx"},
        {"filename": "app/settings/page_TypeScriptReact.prompt", "filepath": "src/app/settings/page.tsx"},
    ]
    (tmp_path / "architecture.json").write_text(json.dumps(arch))
    monkeypatch.chdir(tmp_path)
    choices = _architecture_module_choices(tmp_path / "architecture.json", "page", "TypeScriptReact")
    assert len(choices) == 2
    with pytest.raises(AmbiguousModuleError):
        get_pdd_file_paths("page", "TypeScriptReact", prompts_dir="prompts")


def test_non_prompt_filename_collision_is_ambiguous(tmp_path, monkeypatch):
    """Architecture entries can use non-prompt source filenames (e.g.
    `GitHubAppCTA.tsx` in a frontend architecture.json). When two such entries share a
    filepath stem (`.../page.tsx`), bare `page` is ambiguous and must be caught — by
    both the CLI guard (filepath-stem matched, language-gated) and the agentic guard."""
    _write_pddrc(tmp_path)
    arch = [
        {"filename": "DashboardPage.tsx", "filepath": "src/dashboard/page.tsx"},
        {"filename": "SettingsPage.tsx", "filepath": "src/settings/page.tsx"},
    ]
    (tmp_path / "architecture.json").write_text(json.dumps(arch))
    monkeypatch.chdir(tmp_path)
    choices = _architecture_module_choices(tmp_path / "architecture.json", "page", "TypeScriptReact")
    assert len(choices) == 2
    with pytest.raises(AmbiguousModuleError):
        get_pdd_file_paths("page", "TypeScriptReact", prompts_dir="prompts")
    kept, ambiguous = _drop_ambiguous_basenames(["page"], tmp_path)
    assert kept == []
    assert "page" in ambiguous and len(ambiguous["page"]) == 2


def test_prompt_named_module_not_aliased_by_incidental_filepath_stem(tmp_path, monkeypatch):
    """A module with a real prompt filename (`home_*.prompt`) whose code file is
    incidentally `.../page.tsx` is identified as `home`, NOT `page`. So a single real
    `page` module is not made ambiguous by it (the filepath-stem alias only applies to
    non-prompt filenames)."""
    _write_pddrc(tmp_path)
    arch = [
        {"filename": "page_TypeScriptReact.prompt", "filepath": "src/page.tsx"},
        {"filename": "home_TypeScriptReact.prompt", "filepath": "src/home/page.tsx"},
    ]
    (tmp_path / "architecture.json").write_text(json.dumps(arch))
    monkeypatch.chdir(tmp_path)
    assert _architecture_module_choices(tmp_path / "architecture.json", "page", "TypeScriptReact") == ["src/page.tsx"]
    kept, ambiguous = _drop_ambiguous_basenames(["page"], tmp_path)
    assert kept == ["page"] and ambiguous == {}


def test_ambiguity_propagates_through_orchestration_non_dry_run(tmp_path, monkeypatch):
    """Non-dry-run `pdd sync` must propagate ambiguity (not bury it in a generic
    'Failed to construct paths' result) so the CLI surfaces it via handle_error."""
    from pdd.sync_orchestration import sync_orchestration
    _make_two_page_project(tmp_path)
    monkeypatch.chdir(tmp_path)
    with pytest.raises(AmbiguousModuleError):
        sync_orchestration(
            basename="page",
            language="TypeScriptReact",
            prompts_dir="prompts",
            dry_run=False,
            quiet=True,
        )
