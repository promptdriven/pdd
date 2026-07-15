"""Tests for architecture.json vs prompt <include> cross-validation."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd import cli
from pdd.architecture_include_validation import (
    collect_architecture_include_validation_warnings,
    cross_validate_architecture_with_prompt_includes,
    resolve_architecture_prompt_path,
)


def _write_pair(
    root: Path,
    filename: str,
    body: str,
    *,
    subdir: str = "",
) -> None:
    rel = Path(filename)
    base = root / "prompts"
    if subdir:
        base = base / subdir
    base.mkdir(parents=True, exist_ok=True)
    (base / rel.name).write_text(body, encoding="utf-8")


def test_no_mismatch_when_arch_matches_includes(tmp_path: Path) -> None:
    """Aligned architecture dependencies and module <include>s produce no warnings."""
    root = tmp_path / "proj"
    root.mkdir()
    prompts = root / "prompts"
    prompts.mkdir()

    _write_pair(
        root,
        "child_Python.prompt",
        "% Reason\n<include>parent_python.prompt</include>\n",
    )
    _write_pair(root, "parent_Python.prompt", "% Reason\n")

    arch = [
        {"filename": "child_Python.prompt", "dependencies": ["parent_Python.prompt"]},
        {"filename": "parent_Python.prompt", "dependencies": []},
    ]
    (root / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert warnings == []


def test_ignores_example_py_includes_for_arch_edges(tmp_path: Path) -> None:
    """Example *.py includes do not count as module edges (no false extra-include warnings)."""
    root = tmp_path / "proj"
    root.mkdir()
    prompts = root / "prompts"
    prompts.mkdir()

    _write_pair(
        root,
        "api_Python.prompt",
        "%\n<include>context/models_example.py</include>\n",
    )
    _write_pair(root, "models_Python.prompt", "% Models\n")

    arch = [
        {"filename": "api_Python.prompt", "dependencies": []},
        {"filename": "models_Python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert warnings == []


def test_warns_when_arch_dep_not_included(tmp_path: Path) -> None:
    """Architecture lists a dependency the prompt does not <include> as a module."""
    root = tmp_path / "proj"
    root.mkdir()
    prompts = root / "prompts"
    prompts.mkdir()

    _write_pair(
        root,
        "api_Python.prompt",
        "% Only doc context\n<include>context/readme.md</include>\n",
    )
    _write_pair(root, "models_Python.prompt", "% Models\n")

    arch = [
        {"filename": "api_Python.prompt", "dependencies": ["models_Python.prompt"]},
        {"filename": "models_Python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert len(warnings) == 1
    assert "api_Python.prompt" in warnings[0]
    assert "models" in warnings[0].lower() or "models_Python.prompt" in warnings[0]
    assert "include" in warnings[0].lower()


def test_warns_when_include_module_missing_from_arch_deps(tmp_path: Path) -> None:
    """Prompt <include>s another module prompt but architecture dependencies omit it."""
    root = tmp_path / "proj"
    root.mkdir()
    prompts = root / "prompts"
    prompts.mkdir()

    _write_pair(
        root,
        "frontend_Python.prompt",
        "% UI\n<include>shared_python.prompt</include>\n",
    )
    _write_pair(root, "shared_Python.prompt", "% Shared\n")

    arch = [
        {"filename": "frontend_Python.prompt", "dependencies": []},
        {"filename": "shared_Python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert len(warnings) == 1
    assert "frontend_Python.prompt" in warnings[0]
    assert "shared" in warnings[0].lower()
    assert "architecture" in warnings[0].lower() or "dependencies" in warnings[0].lower()


def test_ignores_non_module_includes(tmp_path: Path) -> None:
    """Context paths and non-module includes do not trigger missing-arch-dep warnings."""
    root = tmp_path / "proj"
    root.mkdir()
    (root / "prompts").mkdir()
    (root / "context").mkdir()
    (root / "context" / "preamble.prompt").write_text("x", encoding="utf-8")

    _write_pair(
        root,
        "solo_Python.prompt",
        "%\n<include>context/preamble.prompt</include>\n",
    )

    arch = [{"filename": "solo_Python.prompt", "dependencies": []}]

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert warnings == []


def test_skips_entry_when_prompt_file_missing(tmp_path: Path) -> None:
    """Missing prompt on disk yields a single skip warning, not a crash."""
    arch = [
        {"filename": "ghost_Python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, tmp_path)
    assert len(warnings) == 1
    assert "ghost" in warnings[0].lower()
    assert "not found" in warnings[0].lower() or "missing" in warnings[0].lower()


def test_both_mismatches_report_two_warnings(tmp_path: Path) -> None:
    """Extra arch dep and extra include each produce a warning."""
    root = tmp_path / "proj"
    root.mkdir()
    (root / "prompts").mkdir()

    _write_pair(
        root,
        "a_Python.prompt",
        "%\n<include>c_python.prompt</include>\n",
    )
    _write_pair(root, "b_Python.prompt", "%\n")
    _write_pair(root, "c_Python.prompt", "%\n")

    arch = [
        {"filename": "a_Python.prompt", "dependencies": ["b_Python.prompt"]},
        {"filename": "b_Python.prompt", "dependencies": []},
        {"filename": "c_Python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert len(warnings) == 2
    kinds = " ".join(warnings).lower()
    assert "b_python" in kinds or "b" in kinds
    assert "c_python" in kinds or "c" in kinds


def test_collect_resolves_prompts_relative_to_arch_parent(tmp_path: Path) -> None:
    """Each architecture.json is validated using its parent as the prompt root."""
    (tmp_path / ".git").mkdir()
    svc = tmp_path / "svc"
    prompts = svc / "prompts"
    prompts.mkdir(parents=True)
    (prompts / "child_Python.prompt").write_text(
        "%\n<include>parent_python.prompt</include>\n", encoding="utf-8"
    )
    (prompts / "parent_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [
        {"filename": "child_Python.prompt", "dependencies": ["parent_Python.prompt"]},
        {"filename": "parent_Python.prompt", "dependencies": []},
    ]
    (svc / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    warnings = collect_architecture_include_validation_warnings(tmp_path)
    assert warnings == []


def test_collect_skips_examples_tree_when_configured(tmp_path: Path) -> None:
    """Bundled sample trees are skipped unless strict validation is requested."""
    (tmp_path / ".git").mkdir()
    ex = tmp_path / "examples" / "demo"
    prompts = ex / "prompts"
    prompts.mkdir(parents=True)
    (prompts / "a_Python.prompt").write_text(
        "%\n<include>b_python.prompt</include>\n", encoding="utf-8"
    )
    (prompts / "b_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [{"filename": "a_Python.prompt", "dependencies": []}]
    (ex / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    assert collect_architecture_include_validation_warnings(
        tmp_path, skip_bundled_sample_arch=True
    ) == []
    strict = collect_architecture_include_validation_warnings(
        tmp_path, skip_bundled_sample_arch=False
    )
    assert len(strict) == 1


def test_pdd_dependency_tag_satisfies_arch_dep(tmp_path: Path) -> None:
    """<pdd-dependency> alone must satisfy an arch.json dep — no <include> of the .prompt needed.

    Per docs/prompting_guide.md, <pdd-dependency> is the authoritative architectural
    declaration; <include> is purely for LLM context ("does NOT affect architecture").
    The forward check must honor <pdd-dependency> as proof of a declared dep so that
    prompts using the tag aren't flagged as drift.
    """
    root = tmp_path / "proj"
    (root / "prompts").mkdir(parents=True)

    _write_pair(
        root,
        "orchestrator_Python.prompt",
        "<pdd-dependency>helper_python.prompt</pdd-dependency>\n"
        "<include>context/helper_example.py</include>\n"
        "% Body\n",
    )
    _write_pair(root, "helper_Python.prompt", "% Helper\n")

    arch = [
        {
            "filename": "orchestrator_Python.prompt",
            "dependencies": ["helper_Python.prompt"],
        },
        {"filename": "helper_Python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert warnings == [], f"Expected no warnings; got: {warnings}"


def test_pdd_dependency_tag_after_erb_comment_satisfies_arch_dep(tmp_path: Path) -> None:
    """ERB-style prompt comments before metadata must not hide pdd-dependency tags."""
    root = tmp_path / "proj"
    (root / "prompts").mkdir(parents=True)

    _write_pair(
        root,
        "orchestrator_Python.prompt",
        "<%-- NOTE: multi-line prompt comment\n"
        "     before metadata tags. --%>\n"
        "<pdd-dependency>helper_python.prompt</pdd-dependency>\n"
        "% Body\n",
    )
    _write_pair(root, "helper_Python.prompt", "% Helper\n")

    arch = [
        {
            "filename": "orchestrator_Python.prompt",
            "dependencies": ["helper_Python.prompt"],
        },
        {"filename": "helper_Python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert warnings == [], f"Expected no warnings; got: {warnings}"


def test_pdd_dependency_and_include_mixed(tmp_path: Path) -> None:
    """A prompt may satisfy different arch deps via <pdd-dependency> and <include>."""
    root = tmp_path / "proj"
    (root / "prompts").mkdir(parents=True)

    _write_pair(
        root,
        "orchestrator_Python.prompt",
        "<pdd-dependency>helper_python.prompt</pdd-dependency>\n"
        "% Body\n"
        "<include>other_python.prompt</include>\n",
    )
    _write_pair(root, "helper_Python.prompt", "% Helper\n")
    _write_pair(root, "other_Python.prompt", "% Other\n")

    arch = [
        {
            "filename": "orchestrator_Python.prompt",
            "dependencies": ["helper_Python.prompt", "other_Python.prompt"],
        },
        {"filename": "helper_Python.prompt", "dependencies": []},
        {"filename": "other_Python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert warnings == [], f"Expected no warnings; got: {warnings}"


def test_ci_drift_heal_prompt_declares_architecture_dependencies() -> None:
    """ci_drift_heal's prompt metadata must match its architecture dependencies."""
    repo_root = Path(__file__).resolve().parents[1]
    arch = json.loads((repo_root / "architecture.json").read_text(encoding="utf-8"))

    warnings = cross_validate_architecture_with_prompt_includes(arch, repo_root)
    ci_drift_warnings = [
        warning
        for warning in warnings
        if "ci_drift_heal_python.prompt" in warning
    ]

    assert not ci_drift_warnings


@patch("pdd.core.cli.auto_update")
def test_validate_arch_includes_cli_ok(mock_auto_update, tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    runner = CliRunner()
    result = runner.invoke(
        cli.cli,
        ["checkup", "--validate-arch-includes", "--project-root", str(tmp_path)],
    )
    assert result.exit_code == 0
    assert "No architecture" in result.output or "mismatches" in result.output


@patch("pdd.core.cli.auto_update")
def test_validate_arch_includes_cli_fails_on_mismatch(mock_auto_update, tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "a_Python.prompt").write_text(
        "%\n<include>b_python.prompt</include>\n", encoding="utf-8"
    )
    (prompts / "b_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [{"filename": "a_Python.prompt", "dependencies": []}]
    (tmp_path / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    runner = CliRunner()
    result = runner.invoke(
        cli.cli,
        ["checkup", "--validate-arch-includes", "--project-root", str(tmp_path)],
    )
    assert result.exit_code == 1
    assert "mismatch" in result.output.lower()


# --- Issue #1256: Dict-format architecture tolerance ---


def test_dict_format_architecture_validates_includes(tmp_path: Path) -> None:
    """collect_architecture_include_validation_warnings processes dict-format architecture (Test 11).

    Bug: isinstance(data, list) at architecture_include_validation.py:76 returns
    False for dict-format {"modules": [...]}, so the file is silently skipped and
    no warnings about include mismatches are produced.
    """
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    # Prompt a includes b, but architecture says a has no deps -> mismatch
    (prompts / "a_Python.prompt").write_text(
        "%\n<include>b_python.prompt</include>\n", encoding="utf-8"
    )
    (prompts / "b_Python.prompt").write_text("%\n", encoding="utf-8")
    # Dict-format architecture with a having no declared deps
    arch = {"modules": [
        {"filename": "a_Python.prompt", "dependencies": []},
        {"filename": "b_Python.prompt", "dependencies": []},
    ]}
    (tmp_path / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    warnings = collect_architecture_include_validation_warnings(
        tmp_path, skip_bundled_sample_arch=False
    )
    assert len(warnings) > 0, (
        "Dict-format architecture should be validated for include mismatches, "
        "but isinstance(data, list) at architecture_include_validation.py:76 silently skips it"
    )


def test_resolve_packaged_prompt_under_pdd_prompts(tmp_path: Path) -> None:
    """Prompts for pdd/* modules live under pdd/prompts/, not only prompts/ symlink."""
    root = tmp_path / "repo"
    prompt = root / "pdd" / "prompts" / "evidence_manifest_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("% Reason\n", encoding="utf-8")

    resolved = resolve_architecture_prompt_path("pdd/evidence_manifest_python.prompt", root)
    assert resolved == prompt.resolve()

    arch = [
        {
            "filename": "pdd/evidence_manifest_python.prompt",
            "filepath": "pdd/evidence_manifest.py",
            "dependencies": [],
        }
    ]
    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert not any("prompt file not found" in w for w in warnings)


# ============================================================================
# Issue #2081: Bug 1 — False-clean signal from --validate-arch-includes
#
# collect_architecture_include_validation_warnings only calls
# cross_validate_architecture_with_prompt_includes, which checks <include>/dep
# alignment but does NOT call validate_architecture_modules.  Structural errors
# (cycles, missing registry targets, empty metadata) are therefore invisible to
# the checkup path, giving a false-clean exit-0 while sync-architecture --dry-run
# surfaces them.
#
# Tests 1–5 assert the EXPECTED (fixed) behavior.  They FAIL on current code and
# should PASS after the fix.
# Reproduction tests (classes below) preserve Step 5 assertions and are marked
# with "# Step 5 reproduction" comments.
# ============================================================================

from pdd.architecture_sync import validate_architecture_modules as _val_arch_mods


# ---------------------------------------------------------------------------
# Shared helpers for Issue #2081 tests
# ---------------------------------------------------------------------------


def _arch2081_module(
    filename: str,
    *,
    description: str = "A module",
    dependencies: list | None = None,
    filepath: str | None = None,
) -> dict:
    """Return a minimal architecture module dict."""
    if filepath is None:
        base = filename.replace("_python.prompt", "").replace(".prompt", "")
        filepath = f"pdd/{base}.py"
    return {
        "filename": filename,
        "filepath": filepath,
        "reason": description,
        "description": description,
        "dependencies": dependencies or [],
        "priority": 1,
        "tags": ["module"],
        "interface": {"type": "module", "module": {"functions": []}},
    }


def _write_arch2081(tmp_path: Path, modules: list, prompt_bodies: dict | None = None) -> None:
    """Write architecture.json and prompt files into tmp_path for discovery tests."""
    prompts = tmp_path / "prompts"
    prompts.mkdir(parents=True, exist_ok=True)
    if prompt_bodies:
        for name, body in prompt_bodies.items():
            (prompts / name).write_text(body, encoding="utf-8")
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": modules}, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )


# ---------------------------------------------------------------------------
# Step 8 Test 1 — collect_warnings surfaces circular dependency
# ---------------------------------------------------------------------------


def test_collect_warnings_surfaces_circular_dependency(tmp_path: Path) -> None:
    """
    Bug 1a fix: collect_architecture_include_validation_warnings must surface an
    A→B→A cycle.  The prompts include each other so the narrow include/dep alignment
    check reports no mismatch — the cycle is the only structural error.

    FAILS on current code because only cross_validate is called (no cycle detection).
    """
    modules = [
        _arch2081_module("mod_a_python.prompt", description="A", dependencies=["mod_b_python.prompt"]),
        _arch2081_module("mod_b_python.prompt", description="B", dependencies=["mod_a_python.prompt"]),
    ]
    prompt_bodies = {
        "mod_a_python.prompt": "<include>mod_b_python.prompt</include>\n% Module A\n",
        "mod_b_python.prompt": "<include>mod_a_python.prompt</include>\n% Module B\n",
    }
    _write_arch2081(tmp_path, modules, prompt_bodies)

    warnings = collect_architecture_include_validation_warnings(
        tmp_path, skip_bundled_sample_arch=False
    )

    assert warnings, (
        "Bug 1a: collect_architecture_include_validation_warnings returned [] "
        "for a graph with an A→B→A circular dependency.  After the fix it must "
        "surface cycle errors so --validate-arch-includes agrees with "
        "sync-architecture --dry-run."
    )
    combined = " ".join(warnings).lower()
    assert "circular" in combined or "cycle" in combined, (
        f"Expected a cycle/circular warning; got: {warnings}"
    )


# ---------------------------------------------------------------------------
# Step 8 Test 2 — collect_warnings surfaces unregistered dependency target
# ---------------------------------------------------------------------------


def test_collect_warnings_surfaces_unregistered_dep_target(tmp_path: Path) -> None:
    """
    Bug 1c fix: collect_architecture_include_validation_warnings must warn when a
    module declares a dependency on a filename that is not registered in the
    architecture.

    The consumer prompt has NO <include> tags, so the narrow include/dep alignment
    check sees no forward-direction mismatch (ghost is not in filename_to_basename,
    so it is silently skipped from arch_modules).  Only validate_architecture_modules
    catches this as a missing_dependency error.

    FAILS on current code.
    """
    modules = [
        _arch2081_module(
            "consumer_python.prompt",
            description="Consumer",
            dependencies=["ghost_python.prompt"],  # ghost not registered
        ),
    ]
    prompt_bodies = {
        "consumer_python.prompt": "% Consumer — no <include> tags\n",
    }
    _write_arch2081(tmp_path, modules, prompt_bodies)

    warnings = collect_architecture_include_validation_warnings(
        tmp_path, skip_bundled_sample_arch=False
    )

    assert warnings, (
        "Bug 1c: collect_architecture_include_validation_warnings returned [] "
        "when consumer_python.prompt declares a dependency on ghost_python.prompt "
        "which is not in the architecture.  validate_architecture_modules detects "
        "this as missing_dependency; the two validators must agree."
    )
    combined = " ".join(warnings).lower()
    assert "ghost" in combined or "missing" in combined or "non-existent" in combined, (
        f"Expected a missing-dep warning mentioning ghost; got: {warnings}"
    )


# ---------------------------------------------------------------------------
# Step 8 Test 3 — collect_warnings surfaces empty description field
# ---------------------------------------------------------------------------


def test_collect_warnings_surfaces_empty_description_field(tmp_path: Path) -> None:
    """
    Bug 1b fix: collect_architecture_include_validation_warnings must warn when a
    module has an empty 'description' field.  The narrow include/dep alignment check
    does not inspect metadata fields; only validate_architecture_modules flags this
    as an invalid_field error.

    FAILS on current code.
    """
    modules = [
        _arch2081_module("mod_python.prompt", description=""),  # empty — structural error
    ]
    prompt_bodies = {
        "mod_python.prompt": "% module — no includes\n",
    }
    _write_arch2081(tmp_path, modules, prompt_bodies)

    warnings = collect_architecture_include_validation_warnings(
        tmp_path, skip_bundled_sample_arch=False
    )

    assert warnings, (
        "Bug 1b: collect_architecture_include_validation_warnings returned [] for "
        "a module with an empty 'description' field.  validate_architecture_modules "
        "flags this as invalid_field; the two validators must agree."
    )
    combined = " ".join(warnings).lower()
    assert "description" in combined or "invalid" in combined or "empty" in combined, (
        f"Expected an invalid-field warning mentioning description; got: {warnings}"
    )


# ---------------------------------------------------------------------------
# Step 8 Test 4 — CLI exits non-zero on structural cycle
# ---------------------------------------------------------------------------


def test_validate_arch_includes_cli_exits_nonzero_on_structural_cycle(
    tmp_path: Path,
) -> None:
    """
    Bug 1a fix (CLI channel): `checkup --validate-arch-includes` must exit 1 when
    the architecture has a circular dependency — even when <include> tags match arch
    deps (so the narrow validator reports no mismatch).

    FAILS on current code with exit_code=0 and "No architecture / <include>
    mismatches found." because only the narrow include-alignment check runs.
    """
    (tmp_path / ".git").mkdir()
    modules = [
        _arch2081_module("alpha_python.prompt", description="Alpha", dependencies=["beta_python.prompt"]),
        _arch2081_module("beta_python.prompt", description="Beta", dependencies=["alpha_python.prompt"]),
    ]
    prompt_bodies = {
        "alpha_python.prompt": "<include>beta_python.prompt</include>\n% Alpha\n",
        "beta_python.prompt": "<include>alpha_python.prompt</include>\n% Beta\n",
    }
    _write_arch2081(tmp_path, modules, prompt_bodies)

    runner = CliRunner()
    result = runner.invoke(
        cli.cli,
        ["checkup", "--validate-arch-includes", "--project-root", str(tmp_path)],
    )

    assert result.exit_code == 1, (
        f"Bug 1a (CLI): exit_code={result.exit_code!r} — expected 1 because the "
        f"graph has a cycle.  Output: {result.output!r}"
    )


# ---------------------------------------------------------------------------
# Step 8 Test 5 — Regression: clean graph is still empty (no false positives)
# ---------------------------------------------------------------------------


def test_collect_warnings_clean_graph_no_structural_errors_is_empty(
    tmp_path: Path,
) -> None:
    """
    Regression: after the Bug 1 fix, a genuinely clean graph (no cycles, no
    missing deps, valid metadata, includes matching deps) must still produce zero
    warnings from collect_architecture_include_validation_warnings.
    """
    modules = [
        _arch2081_module("leaf_python.prompt", description="Leaf", dependencies=[]),
        _arch2081_module(
            "root_python.prompt",
            description="Root",
            dependencies=["leaf_python.prompt"],
        ),
    ]
    prompt_bodies = {
        "leaf_python.prompt": "% Leaf module\n",
        "root_python.prompt": "<include>leaf_python.prompt</include>\n% Root\n",
    }
    _write_arch2081(tmp_path, modules, prompt_bodies)

    warnings = collect_architecture_include_validation_warnings(
        tmp_path, skip_bundled_sample_arch=False
    )

    assert warnings == [], (
        f"Regression: clean graph produced unexpected warnings: {warnings}"
    )
    # Also sanity-check the full structural validator
    struct = _val_arch_mods(modules)
    assert struct["valid"], f"Clean graph failed structural validation: {struct['errors']}"


# ============================================================================
# Step 5 reproduction tests for Bug 1
# These are preserved from the Step 5 investigation and demonstrate the specific
# cross_validate / validate_architecture_modules divergence.
# ============================================================================


class TestCheckupMissesCircularDependencies2081:
    """
    # Step 5 reproduction
    cross_validate_architecture_with_prompt_includes (used by
    checkup --validate-arch-includes) does not detect cycles in the dependency
    graph.  validate_architecture_modules (used by sync-architecture --dry-run)
    does detect them.

    Expected (fixed) behavior: both must flag the cycle or at minimum
    --validate-arch-includes must not claim "no mismatches" when structural
    errors exist.
    """

    def _make_cyclic_arch(self, tmp_path: Path):
        root, prompts = tmp_path / "proj", tmp_path / "proj" / "prompts"
        prompts.mkdir(parents=True)
        (prompts / "module_a_python.prompt").write_text(
            "<include>module_b_python.prompt</include>\n% module A\n", encoding="utf-8"
        )
        (prompts / "module_b_python.prompt").write_text(
            "<include>module_a_python.prompt</include>\n% module B\n", encoding="utf-8"
        )
        arch_data = [
            _arch2081_module("module_a_python.prompt", description="Module A", dependencies=["module_b_python.prompt"]),
            _arch2081_module("module_b_python.prompt", description="Module B", dependencies=["module_a_python.prompt"]),
        ]
        (root / "architecture.json").write_text(
            json.dumps({"modules": arch_data}, indent=2), encoding="utf-8"
        )
        return arch_data, root

    def test_validate_architecture_modules_detects_cycle(self, tmp_path: Path) -> None:
        """validate_architecture_modules must flag the A→B→A cycle as an error."""
        arch_data, _root = self._make_cyclic_arch(tmp_path)
        result = _val_arch_mods(arch_data)
        cycle_errors = [e for e in result["errors"] if e["type"] == "circular_dependency"]
        assert cycle_errors, (
            f"validate_architecture_modules must detect the A→B→A cycle. "
            f"Errors: {result['errors']}"
        )

    def test_cross_validate_does_not_detect_cycle_but_commands_must_agree(
        self, tmp_path: Path
    ) -> None:
        """
        # Step 5 reproduction — Bug 1a
        EXPECTED (fixed): when the graph has a cycle, the checkup path must NOT
        return zero warnings while the sync path returns cycle errors.
        """
        arch_data, root = self._make_cyclic_arch(tmp_path)
        include_warnings = cross_validate_architecture_with_prompt_includes(arch_data, root)
        struct_result = _val_arch_mods(arch_data)
        struct_has_cycle = any(e["type"] == "circular_dependency" for e in struct_result["errors"])

        if struct_has_cycle:
            assert include_warnings, (
                "Bug 1a: cross_validate_architecture_with_prompt_includes returned "
                "no warnings for a graph with an A→B→A cycle. "
                "validate_architecture_modules detected the cycle. "
                "The two validators must agree."
            )


class TestCheckupMissesInvalidMetadataFields2081:
    """
    # Step 5 reproduction
    cross_validate_architecture_with_prompt_includes does not flag modules with
    empty description or filepath fields.  validate_architecture_modules does.
    """

    def test_validate_architecture_modules_flags_empty_description(
        self, tmp_path: Path
    ) -> None:
        """validate_architecture_modules must report invalid_field for empty description."""
        arch_data = [_arch2081_module("mod_python.prompt", description="")]
        result = _val_arch_mods(arch_data)
        field_errors = [e for e in result["errors"] if e["type"] == "invalid_field"]
        assert field_errors, (
            f"validate_architecture_modules should flag empty 'description' as "
            f"invalid_field. Errors: {result['errors']}"
        )

    def test_cross_validate_does_not_flag_empty_description(
        self, tmp_path: Path
    ) -> None:
        """
        # Step 5 reproduction — Bug 1b
        EXPECTED (fixed): after the fix, list_validate_arch_include_warnings must
        surface empty-description errors, or both commands must converge.
        """
        root, prompts = tmp_path, tmp_path / "prompts"
        prompts.mkdir()
        (prompts / "mod_python.prompt").write_text("% module\n", encoding="utf-8")
        arch_data = [_arch2081_module("mod_python.prompt", description="")]
        (root / "architecture.json").write_text(
            json.dumps({"modules": arch_data}), encoding="utf-8"
        )

        include_warnings = cross_validate_architecture_with_prompt_includes(arch_data, root)
        struct_result = _val_arch_mods(arch_data)
        struct_has_empty_desc = any(e["type"] == "invalid_field" for e in struct_result["errors"])

        if struct_has_empty_desc:
            assert include_warnings, (
                "Bug 1b: cross_validate_architecture_with_prompt_includes returned "
                "no warnings for a module with an empty 'description' field. "
                "validate_architecture_modules flagged it as invalid_field. "
                "The two validators must agree."
            )


class TestCheckupMissesMissingDependencies2081:
    """
    # Step 5 reproduction
    validate_architecture_modules detects when a module's dependency references a
    module not in the architecture.  cross_validate_architecture_with_prompt_includes
    does not (it skips deps not in filename_to_basename).
    """

    def test_validate_architecture_modules_flags_missing_dep(
        self, tmp_path: Path
    ) -> None:
        """validate_architecture_modules must report missing_dependency errors."""
        arch_data = [
            _arch2081_module(
                "consumer_python.prompt",
                description="Consumer",
                dependencies=["ghost_python.prompt"],
            )
        ]
        result = _val_arch_mods(arch_data)
        missing_errors = [e for e in result["errors"] if e["type"] == "missing_dependency"]
        assert missing_errors, (
            f"validate_architecture_modules should flag 'ghost_python.prompt' as "
            f"missing_dependency. Errors: {result['errors']}"
        )

    def test_cross_validate_does_not_flag_unregistered_dependency(
        self, tmp_path: Path
    ) -> None:
        """
        # Step 5 reproduction — Bug 1c
        EXPECTED (fixed): both validators must agree on whether the registry is
        complete and consistent.
        """
        root, prompts = tmp_path, tmp_path / "prompts"
        prompts.mkdir()
        (prompts / "consumer_python.prompt").write_text(
            "% Consumer — no includes\n", encoding="utf-8"
        )
        arch_data = [
            _arch2081_module(
                "consumer_python.prompt",
                description="Consumer",
                dependencies=["ghost_python.prompt"],
            )
        ]
        (root / "architecture.json").write_text(
            json.dumps({"modules": arch_data}), encoding="utf-8"
        )

        include_warnings = cross_validate_architecture_with_prompt_includes(arch_data, root)
        struct_result = _val_arch_mods(arch_data)
        struct_has_missing = any(e["type"] == "missing_dependency" for e in struct_result["errors"])

        if struct_has_missing:
            assert include_warnings, (
                "Bug 1c: cross_validate_architecture_with_prompt_includes returned "
                "no warnings when consumer_python.prompt declares a dependency on "
                "ghost_python.prompt which is not in the architecture. "
                "validate_architecture_modules detected the missing dependency. "
                "The two validators must agree."
            )


class TestCommandVerdictConsistency2081:
    """
    # Step 5 reproduction
    High-level consistency: for any graph, if cross_validate returns no warnings,
    validate_architecture_modules must also return no errors for overlapping claims.
    """

    def test_clean_graph_both_validators_agree(self, tmp_path: Path) -> None:
        """A genuinely clean graph must produce no warnings or errors from either validator."""
        root, prompts = tmp_path, tmp_path / "prompts"
        prompts.mkdir()
        (prompts / "leaf_python.prompt").write_text("% Leaf module\n", encoding="utf-8")
        (prompts / "root_python.prompt").write_text(
            "<include>leaf_python.prompt</include>\n", encoding="utf-8"
        )
        arch_data = [
            _arch2081_module("leaf_python.prompt", description="Leaf"),
            _arch2081_module("root_python.prompt", description="Root", dependencies=["leaf_python.prompt"]),
        ]
        include_warnings = cross_validate_architecture_with_prompt_includes(arch_data, root)
        struct_result = _val_arch_mods(arch_data)
        assert not include_warnings, f"Clean graph produced include-validation warnings: {include_warnings}"
        assert struct_result["valid"], f"Clean graph produced structural errors: {struct_result['errors']}"

    def test_cyclic_graph_both_validators_flag_it(self, tmp_path: Path) -> None:
        """
        # Step 5 reproduction — Bug 1a
        A graph with a cycle must cause BOTH validators to report problems.
        EXPECTED (fixed): cross_validate_architecture_with_prompt_includes must also
        indicate the graph is not clean when a cycle is present.
        """
        root, prompts = tmp_path, tmp_path / "prompts"
        prompts.mkdir()
        (prompts / "alpha_python.prompt").write_text(
            "<include>beta_python.prompt</include>\n% Alpha\n", encoding="utf-8"
        )
        (prompts / "beta_python.prompt").write_text(
            "<include>alpha_python.prompt</include>\n% Beta\n", encoding="utf-8"
        )
        arch_data = [
            _arch2081_module("alpha_python.prompt", description="Alpha", dependencies=["beta_python.prompt"]),
            _arch2081_module("beta_python.prompt", description="Beta", dependencies=["alpha_python.prompt"]),
        ]

        include_warnings = cross_validate_architecture_with_prompt_includes(arch_data, root)
        struct_result = _val_arch_mods(arch_data)
        cycle_errors = [e for e in struct_result["errors"] if e["type"] == "circular_dependency"]
        assert cycle_errors, "validate_architecture_modules must detect the alpha→beta→alpha cycle"

        assert include_warnings, (
            "Bug 1a (consistency): cross_validate_architecture_with_prompt_includes "
            "returned [] for a graph with a circular dependency, while "
            "validate_architecture_modules detected the cycle. "
            "Both validators must agree on the health of the graph."
        )
