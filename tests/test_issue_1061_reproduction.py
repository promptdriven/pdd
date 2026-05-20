"""Regression tests for issue #1061.

PR #1055 produced an architecture/prompt drift: ``architecture.json`` for
``agentic_update_python.prompt`` gained a ``"sync_order_python.prompt"``
dependency even though the prompt only declares
``<pdd-dependency>agentic_update_LLM.prompt</pdd-dependency>``. The prompt
included ``pdd/sync_order.py`` purely as helper/source context with
``mode="interface"`` / ``select="..."``.

Per ``docs/prompting_guide.md`` ``<pdd-dependency>`` is the authoritative
architectural declaration; a plain ``<include>`` can be context without
being an architecture edge. ``pdd sync`` must not write only one side of
that contract, or ``pdd checkup --validate-arch-includes`` fails with::

    architecture.json / <include> mismatch:
      'agentic_update_python.prompt' declares dependency on module
      'sync_order' ('sync_order_python.prompt') but the prompt has no
      <include> or <pdd-dependency> of that module's prompt

These tests encode the acceptance criteria: a selected/interface include
of ``pdd/sync_order.py`` (no matching ``<pdd-dependency>``) must not
cause ``validate-arch-includes`` to flag a mismatch after sync. They
exercise the two production code paths that update architecture
dependencies during ``pdd sync``: the auto-deps merge and the
prompt-driven metadata update.
"""
from __future__ import annotations

import json
from pathlib import Path

from unittest.mock import patch, MagicMock

from pdd.architecture_include_validation import (
    cross_validate_architecture_with_prompt_includes,
)
from pdd.architecture_sync import update_architecture_from_prompt
from pdd.auto_deps_architecture import merge_auto_deps_includes_into_architecture
from pdd.load_prompt_template import load_prompt_template


# Prompt body matching the #1055 shape: interface-mode source-context include
# of ``pdd/sync_order.py`` but no matching ``<pdd-dependency>`` for the
# ``sync_order`` module prompt.
_PROMPT_1055_SHAPE = """<pdd-reason>Coordinates agentic prompt updates.</pdd-reason>

<pdd-dependency>agentic_update_LLM.prompt</pdd-dependency>

<include>context/python_preamble.prompt</include>

% Goal
Write the `pdd/agentic_update.py` module.

% Dependencies
<pdd.sync_order.extract_includes_from_file>
    <include select="def:extract_includes_from_file" mode="interface">pdd/sync_order.py</include>
</pdd.sync_order.extract_includes_from_file>
"""


def _seed_project(tmp_path: Path) -> tuple[Path, Path]:
    """Create a minimal project tree resembling promptdriven/pdd."""
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    pdd_dir = tmp_path / "pdd"
    pdd_dir.mkdir()
    (pdd_dir / "sync_order.py").write_text(
        "def extract_includes_from_file(p):\n    pass\n",
        encoding="utf-8",
    )

    (prompts / "agentic_update_python.prompt").write_text(
        _PROMPT_1055_SHAPE, encoding="utf-8"
    )
    (prompts / "agentic_update_LLM.prompt").write_text("%", encoding="utf-8")
    (prompts / "sync_order_python.prompt").write_text("%", encoding="utf-8")
    return prompts, pdd_dir


def test_auto_deps_does_not_promote_interface_include_of_module_source(
    tmp_path: Path,
) -> None:
    """``merge_auto_deps_includes_into_architecture`` must not turn an
    ``<include select="..." mode="interface">pdd/sync_order.py</include>``
    helper-context include into an architecture dependency on
    ``sync_order_python.prompt``.

    Per the prompting guide, that include is context for the LLM; the
    architecture edge would have to come from a ``<pdd-dependency>`` tag
    instead. Promoting context-only includes is precisely what produces
    the #1055 drift.
    """
    prompts, _ = _seed_project(tmp_path)
    old_prompt = (
        "<pdd-reason>r</pdd-reason>\n\n"
        "<pdd-dependency>agentic_update_LLM.prompt</pdd-dependency>\n\n"
        "% Body\n"
    )
    new_prompt = _PROMPT_1055_SHAPE

    arch = [
        {
            "filename": "agentic_update_python.prompt",
            "dependencies": ["agentic_update_LLM.prompt"],
        },
        {"filename": "agentic_update_LLM.prompt", "dependencies": []},
        {"filename": "sync_order_python.prompt", "dependencies": []},
    ]
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps(arch, indent=2), encoding="utf-8")

    report = merge_auto_deps_includes_into_architecture(
        tmp_path,
        prompts / "agentic_update_python.prompt",
        old_prompt,
        new_prompt,
    )

    # The interface-mode include is context, not an arch edge.
    assert "sync_order_python.prompt" not in report["added_dependencies"], (
        "auto-deps must not promote a `mode=interface` source-file include "
        "into an architecture dependency on the module's prompt"
    )

    final = json.loads(arch_path.read_text(encoding="utf-8"))
    deps = final[0]["dependencies"]
    assert "sync_order_python.prompt" not in deps, (
        f"architecture.json gained an undeclared dependency: {deps!r}"
    )


def test_metadata_sync_trims_architecture_to_prompt_dependencies(
    tmp_path: Path,
) -> None:
    """``update_architecture_from_prompt`` must remove architecture deps
    that the prompt does not declare via ``<pdd-dependency>``.

    Starting from the post-buggy-sync state PR #1055 produced — arch has
    ``sync_order_python.prompt`` but the prompt does not — sync must
    converge the architecture back onto the prompt's authoritative
    declaration so ``validate-arch-includes`` passes.
    """
    prompts, _ = _seed_project(tmp_path)

    # Architecture as PR #1055 left it: extra `sync_order_python.prompt`.
    arch = [
        {
            "filename": "agentic_update_python.prompt",
            "dependencies": [
                "agentic_update_LLM.prompt",
                "sync_order_python.prompt",
            ],
        },
        {"filename": "agentic_update_LLM.prompt", "dependencies": []},
        {"filename": "sync_order_python.prompt", "dependencies": []},
    ]
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps(arch, indent=2), encoding="utf-8")

    result = update_architecture_from_prompt(
        prompt_filename="agentic_update_python.prompt",
        prompts_dir=prompts,
        architecture_path=arch_path,
    )
    assert result["success"], result.get("error")

    final = json.loads(arch_path.read_text(encoding="utf-8"))
    deps = final[0]["dependencies"]
    assert deps == ["agentic_update_LLM.prompt"], (
        "sync should trim architecture deps to match the prompt's "
        f"<pdd-dependency> declarations; got {deps!r}"
    )


def test_validate_arch_includes_passes_for_1055_shape_after_sync(
    tmp_path: Path,
) -> None:
    """End-to-end: starting from a clean state and applying the #1055
    prompt edit, the two sync paths together (auto-deps merge + metadata
    sync) must leave the project in a state where
    ``cross_validate_architecture_with_prompt_includes`` reports no
    mismatches — the acceptance criterion explicitly named in the issue.
    """
    prompts, _ = _seed_project(tmp_path)

    old_prompt = (
        "<pdd-reason>r</pdd-reason>\n\n"
        "<pdd-dependency>agentic_update_LLM.prompt</pdd-dependency>\n\n"
        "% Body\n"
    )
    new_prompt = _PROMPT_1055_SHAPE

    # Start arch in sync with the pre-edit prompt.
    arch = [
        {
            "filename": "agentic_update_python.prompt",
            "dependencies": ["agentic_update_LLM.prompt"],
        },
        {"filename": "agentic_update_LLM.prompt", "dependencies": []},
        {"filename": "sync_order_python.prompt", "dependencies": []},
    ]
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps(arch, indent=2), encoding="utf-8")

    # Simulate the two sync stages that mutate architecture.json deps.
    merge_auto_deps_includes_into_architecture(
        tmp_path,
        prompts / "agentic_update_python.prompt",
        old_prompt,
        new_prompt,
    )
    update_architecture_from_prompt(
        prompt_filename="agentic_update_python.prompt",
        prompts_dir=prompts,
        architecture_path=arch_path,
    )

    final = json.loads(arch_path.read_text(encoding="utf-8"))
    warnings = cross_validate_architecture_with_prompt_includes(final, tmp_path)
    assert warnings == [], (
        "validate-arch-includes must not warn after sync for the #1055 "
        f"shape; got: {warnings!r}"
    )


def test_buggy_post_sync_state_is_detected_by_validation(tmp_path: Path) -> None:
    """Sanity check: the *current* buggy state PR #1055 produced — arch
    listing ``sync_order_python.prompt`` while the prompt does not — IS
    flagged by ``cross_validate_architecture_with_prompt_includes`` with
    the exact warning text quoted in the issue. This guards against
    regressions in the validator itself.
    """
    prompts, _ = _seed_project(tmp_path)

    arch = [
        {
            "filename": "agentic_update_python.prompt",
            "dependencies": [
                "agentic_update_LLM.prompt",
                "sync_order_python.prompt",
            ],
        },
        {"filename": "agentic_update_LLM.prompt", "dependencies": []},
        {"filename": "sync_order_python.prompt", "dependencies": []},
    ]
    warnings = cross_validate_architecture_with_prompt_includes(arch, tmp_path)
    assert any(
        "declares dependency on module 'sync_order'" in w
        and "but the prompt has no <include> or <pdd-dependency>" in w
        for w in warnings
    ), f"expected the #1061 mismatch warning, got: {warnings!r}"


# ---------------------------------------------------------------------------
# Step 9 fix-detection tests.
#
# The fix spans two files (Step 7):
#   * pdd/prompts/agentic_sync_identify_modules_LLM.prompt  (the prompt fix)
#   * pdd/agentic_sync.py                                   (caller of LLM
#                                                            + _apply_architecture_corrections)
#
# Tests 1-2 exercise the *rendered prompt sent to the LLM*: that's the
# contract Step 7 changed. Tests 3-5 exercise the caller/callee boundary
# in agentic_sync.py with a prompt-following mock LLM (Step 4 confirmed
# the suspect modules use no real external APIs, so the only mock point
# is the LLM boundary).
# ---------------------------------------------------------------------------


def _render_identify_modules_prompt(issue_content: str, arch_json: str, issue_number: int) -> str:
    """Mirror exactly how ``run_agentic_sync`` renders the LLM prompt.

    Point the path resolver at the worktree via ``PDD_PATH`` so we read the
    *worktree's* prompt file (which carries the Step 7 fix) rather than any
    installed copy under ``/opt/pdd-repo`` or site-packages.
    """
    import os
    worktree_root = Path(__file__).resolve().parent.parent
    old_pdd_path = os.environ.get("PDD_PATH")
    os.environ["PDD_PATH"] = str(worktree_root)
    try:
        template = load_prompt_template("agentic_sync_identify_modules_LLM")
    finally:
        if old_pdd_path is None:
            os.environ.pop("PDD_PATH", None)
        else:
            os.environ["PDD_PATH"] = old_pdd_path
    assert template is not None, "agentic_sync_identify_modules_LLM template must load"
    safe_arch = arch_json.replace("{", "{{").replace("}", "}}")
    return template.format(
        issue_content=issue_content,
        architecture_json=safe_arch,
        issue_number=issue_number,
    )


def test_identify_modules_prompt_declares_pdd_dependency_authoritative() -> None:
    """The rendered LLM prompt MUST instruct the model that ``<pdd-dependency>``
    is the authoritative source of truth and that ``<include>`` directives
    (in any form, including ``mode="interface"``, ``select="def:..."``) are
    LLM context only and MUST NOT become architectural dependencies.

    Without these rules in the rendered contract, ``_apply_architecture_corrections``
    will faithfully apply whatever the LLM returns — which is exactly how the
    #1055 / #1061 drift got written to ``architecture.json`` in the first place.

    This is the BEHAVIOR test of the Step 7 fix: it asserts on the string
    actually sent to the LLM via the production rendering path, not on Python
    source structure. An empty stub in agentic_sync.py would still cause this
    test to fail because the assertion is on the prompt contents.
    """
    rendered = _render_identify_modules_prompt(
        issue_content="Sync architecture for issue #1061.",
        arch_json='[{"filename": "agentic_update_python.prompt", "dependencies": ["agentic_update_LLM.prompt"]}]',
        issue_number=1061,
    )

    # Authoritative-source rule: <pdd-dependency> is the source of truth.
    assert "<pdd-dependency>" in rendered, (
        "Prompt must reference <pdd-dependency> as the authoritative tag"
    )
    assert "single source of truth" in rendered or "source of truth" in rendered, (
        "Prompt must label <pdd-dependency> as the source of truth for deps"
    )
    # The rule must explicitly bind both directions: a dep belongs iff the
    # prompt declares it, AND must not be added otherwise.
    assert "if and only if" in rendered, (
        "Prompt must state the if-and-only-if binding between <pdd-dependency> "
        "and architecture.json[dependencies]"
    )
    assert "MUST NOT" in rendered, (
        "Prompt must use MUST NOT to express the hard boundary on fabricated deps"
    )

    # Context-only rule: <include> (incl. mode="interface" / select=) is NOT
    # an architectural edge. Accept either literal `<include>` or the
    # entity-escaped `&lt;include&gt;` form (F8: inline doc examples are escaped
    # to keep extract_includes_from_file_ordered from parsing prose as live tags).
    assert "<include>" in rendered or "&lt;include&gt;" in rendered, (
        "Prompt must mention <include> directives (literal or entity-escaped)"
    )
    assert "context only" in rendered or "context-only" in rendered or "LLM context" in rendered, (
        "Prompt must label <include> directives as context-only"
    )
    assert 'mode="interface"' in rendered, (
        "Prompt must explicitly call out mode=\"interface\" as still context-only "
        "(this is the exact #1055 shape)"
    )
    assert "select=" in rendered or 'select="def:' in rendered, (
        "Prompt must call out select=\"def:...\" / select=\"...\" as still context-only"
    )


def test_identify_modules_prompt_includes_1055_worked_example() -> None:
    """The rendered prompt MUST contain a worked example using the exact
    #1055 / #1061 shape — ``pdd/sync_order.py`` pulled in as an interface
    include — so the LLM has a concrete pattern to follow when it sees
    architecture.json contains ``sync_order_python.prompt`` but the prompt
    does not declare it via ``<pdd-dependency>``.

    Step 7 added this worked example specifically because the bug was that
    the LLM's "validate dependencies" task had no concrete example showing
    that an interface-mode include is NOT an architectural edge. Without
    the example, the LLM may default to "if the prompt mentions sync_order,
    treat it as a dep". The example is the corrective signal.
    """
    rendered = _render_identify_modules_prompt(
        issue_content="Validate dependencies",
        arch_json="[]",
        issue_number=1061,
    )

    # The worked example must reference the exact file from the issue.
    assert "pdd/sync_order.py" in rendered, (
        "Prompt's worked example must reference pdd/sync_order.py — the exact "
        "file from PR #1055 that produced the drift"
    )
    assert "sync_order_python.prompt" in rendered, (
        "Worked example must show sync_order_python.prompt as the candidate "
        "fake-dep being discussed"
    )
    # And it must demonstrate the correction = REMOVE the fake dep, not add
    # a fabricated <pdd-dependency> tag.
    assert "agentic_update_LLM.prompt" in rendered, (
        "Worked example must show the surviving authoritative dep "
        "(agentic_update_LLM.prompt) after correction"
    )
    # The example must direct the LLM toward the correction direction:
    # removing the spurious arch entry, not fabricating a <pdd-dependency>.
    lower = rendered.lower()
    assert "do not" in lower or "do not propose adding" in lower or "do not keep" in lower, (
        "Worked example must explicitly tell the LLM not to fabricate or keep "
        "the spurious dependency"
    )


def _arch_entry(name: str, deps: list[str]) -> dict:
    return {"filename": name, "dependencies": list(deps)}


@patch("pdd.agentic_sync.AsyncSyncRunner")
@patch("pdd.agentic_sync._filter_already_synced", side_effect=lambda mods, *a, **kw: mods)
@patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
@patch("pdd.agentic_sync._run_dry_run_validation")
@patch("pdd.agentic_sync.build_dep_graph_from_architecture_data")
@patch("pdd.agentic_sync.run_agentic_task")
@patch("pdd.agentic_sync._load_architecture_json")
@patch("pdd.agentic_sync._run_gh_command")
@patch("pdd.agentic_sync._check_gh_cli", return_value=True)
def test_run_agentic_sync_with_prompt_compliant_llm_does_not_write_undeclared_dep(
    mock_gh_cli,
    mock_gh_cmd,
    mock_load_arch,
    mock_agentic_task,
    mock_build_graph,
    mock_dry_run,
    mock_branch_diff,
    mock_filter_synced,
    mock_runner_cls,
    tmp_path: Path,
) -> None:
    """End-to-end: when the LLM follows the Step-7-fixed prompt, ``pdd sync``
    must NOT leave a fabricated ``sync_order_python.prompt`` dependency in
    ``architecture.json``.

    A prompt-following LLM, given the #1055-shape arch (``sync_order_python.prompt``
    listed under ``agentic_update_python.prompt``) and the prompt's
    ``<pdd-dependency>agentic_update_LLM.prompt</pdd-dependency>`` declaration,
    should emit ``DEPS_VALID: false`` with a correction that *removes* the
    spurious dep (per the new Authoritative Source Rule). This test verifies
    that the caller (``run_agentic_sync``) faithfully passes that correction
    through ``_apply_architecture_corrections`` and the final on-disk arch
    matches the prompt's ``<pdd-dependency>`` declaration.

    Cross-check vs Step 4: the only external boundary is the LLM call, mocked
    here via ``run_agentic_task``. No HTTP/SDK calls are issued by the writers,
    consistent with Step 4 findings.
    """
    # Real arch on disk so _apply_architecture_corrections can rewrite it.
    arch_path = tmp_path / "architecture.json"
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "agentic_update_python.prompt").write_text(
        _PROMPT_1055_SHAPE, encoding="utf-8"
    )
    (prompts / "agentic_update_LLM.prompt").write_text("%", encoding="utf-8")
    (prompts / "sync_order_python.prompt").write_text("%", encoding="utf-8")
    architecture = [
        _arch_entry(
            "agentic_update_python.prompt",
            ["agentic_update_LLM.prompt", "sync_order_python.prompt"],
        ),
        _arch_entry("agentic_update_LLM.prompt", []),
        _arch_entry("sync_order_python.prompt", []),
    ]
    arch_path.write_text(json.dumps(architecture, indent=2), encoding="utf-8")

    mock_gh_cmd.return_value = (True, json.dumps({"title": "t", "body": "b", "comments_url": ""}))
    mock_load_arch.return_value = (architecture, arch_path)
    mock_dry_run.return_value = (True, {"agentic_update": tmp_path}, [], 0.0)
    mock_build_graph.return_value = MagicMock(graph={"agentic_update": []}, warnings=[])
    mock_runner = MagicMock()
    mock_runner.run.return_value = (True, "ok", 0.0)
    mock_runner_cls.return_value = mock_runner

    # Prompt-compliant LLM: trims sync_order_python.prompt, leaving the only
    # <pdd-dependency> declaration (agentic_update_LLM.prompt).
    mock_agentic_task.return_value = (
        True,
        (
            'MODULES_TO_SYNC: ["agentic_update"]\n'
            "DEPS_VALID: false\n"
            "DEPS_CORRECTIONS: ["
            '{"filename": "agentic_update_python.prompt", '
            '"dependencies": ["agentic_update_LLM.prompt"]}'
            "]"
        ),
        0.01,
        "anthropic",
    )

    from pdd.agentic_sync import run_agentic_sync

    with patch("pdd.agentic_sync._find_project_root", return_value=tmp_path):
        success, _msg, _cost, _model = run_agentic_sync(
            "https://github.com/promptdriven/pdd/issues/1061",
            quiet=True,
        )
    assert success, "run_agentic_sync should succeed with prompt-compliant LLM output"

    final = json.loads(arch_path.read_text(encoding="utf-8"))
    entry = next(e for e in final if e["filename"] == "agentic_update_python.prompt")
    assert entry["dependencies"] == ["agentic_update_LLM.prompt"], (
        "After sync, architecture.json must match the prompt's <pdd-dependency> "
        f"declaration; got {entry['dependencies']!r}"
    )


@patch("pdd.agentic_sync.AsyncSyncRunner")
@patch("pdd.agentic_sync._filter_already_synced", side_effect=lambda mods, *a, **kw: mods)
@patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
@patch("pdd.agentic_sync._run_dry_run_validation")
@patch("pdd.agentic_sync.build_dep_graph_from_architecture_data")
@patch("pdd.agentic_sync._apply_architecture_corrections")
@patch("pdd.agentic_sync.run_agentic_task")
@patch("pdd.agentic_sync._load_architecture_json")
@patch("pdd.agentic_sync._run_gh_command")
@patch("pdd.agentic_sync._check_gh_cli", return_value=True)
def test_caller_passes_llm_corrections_through_to_apply_corrections(
    mock_gh_cli,
    mock_gh_cmd,
    mock_load_arch,
    mock_agentic_task,
    mock_apply,
    mock_build_graph,
    mock_dry_run,
    mock_branch_diff,
    mock_filter_synced,
    mock_runner_cls,
    tmp_path: Path,
) -> None:
    """Caller-side behavior: ``run_agentic_sync`` must invoke
    ``_apply_architecture_corrections`` with the corrections parsed from the
    LLM. This test mocks the callee (``_apply_architecture_corrections``) and
    drives the caller, verifying the call boundary.

    Per the "Testing Caller Behavior Bugs" rule: testing only the callee here
    would always pass because the callee was never broken — the prompt/LLM
    contract is. This test asserts the callee was called and inspects
    ``call_args`` to confirm the caller wired up correctly.
    """
    arch_path = tmp_path / "architecture.json"
    architecture = [
        _arch_entry(
            "agentic_update_python.prompt",
            ["agentic_update_LLM.prompt", "sync_order_python.prompt"],
        ),
    ]
    arch_path.write_text(json.dumps(architecture, indent=2), encoding="utf-8")

    mock_gh_cmd.return_value = (True, json.dumps({"title": "t", "body": "b", "comments_url": ""}))
    mock_load_arch.return_value = (architecture, arch_path)
    mock_dry_run.return_value = (True, {"agentic_update": tmp_path}, [], 0.0)
    mock_build_graph.return_value = MagicMock(graph={"agentic_update": []}, warnings=[])
    # Mock apply to return arch unchanged (we only care it was called correctly).
    mock_apply.return_value = architecture
    mock_runner = MagicMock()
    mock_runner.run.return_value = (True, "ok", 0.0)
    mock_runner_cls.return_value = mock_runner

    expected_corrections = [
        {
            "filename": "agentic_update_python.prompt",
            "dependencies": ["agentic_update_LLM.prompt"],
        }
    ]
    mock_agentic_task.return_value = (
        True,
        (
            'MODULES_TO_SYNC: ["agentic_update"]\n'
            "DEPS_VALID: false\n"
            f"DEPS_CORRECTIONS: {json.dumps(expected_corrections)}"
        ),
        0.01,
        "anthropic",
    )

    from pdd.agentic_sync import run_agentic_sync

    run_agentic_sync(
        "https://github.com/promptdriven/pdd/issues/1061",
        quiet=True,
    )

    # The caller MUST have invoked _apply_architecture_corrections with the
    # parsed corrections, not skipped them.
    mock_apply.assert_called()
    call = mock_apply.call_args
    # Corrections is the 3rd positional arg (or `corrections` kwarg). Be
    # liberal about kwargs vs args, but pick by *position*/*name*, not by
    # shape-match (the architecture list has the same dict shape).
    if "corrections" in call.kwargs:
        forwarded = call.kwargs["corrections"]
    else:
        assert len(call.args) >= 3, (
            f"Expected at least 3 positional args to _apply_architecture_corrections; "
            f"got args={call.args!r} kwargs={call.kwargs!r}"
        )
        forwarded = call.args[2]
    assert forwarded == expected_corrections, (
        "Caller must forward LLM-parsed corrections verbatim to "
        f"_apply_architecture_corrections; got {forwarded!r}"
    )


# Scope addition: covers expansion item "_apply_architecture_corrections caller
# at pdd/agentic_sync.py:1890-1900 is not filtered to modules_to_sync so
# corrections to modules outside the sync set bypass the deterministic
# per-module update_architecture_from_prompt re-convergence" identified by
# Step 6 but only loosely covered by Step 8's plan.
@patch("pdd.agentic_sync.AsyncSyncRunner")
@patch("pdd.agentic_sync._filter_already_synced", side_effect=lambda mods, *a, **kw: mods)
@patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
@patch("pdd.agentic_sync._run_dry_run_validation")
@patch("pdd.agentic_sync.build_dep_graph_from_architecture_data")
@patch("pdd.agentic_sync.run_agentic_task")
@patch("pdd.agentic_sync._load_architecture_json")
@patch("pdd.agentic_sync._run_gh_command")
@patch("pdd.agentic_sync._check_gh_cli", return_value=True)
def test_out_of_scope_corrections_do_not_fabricate_undeclared_deps(
    mock_gh_cli,
    mock_gh_cmd,
    mock_load_arch,
    mock_agentic_task,
    mock_build_graph,
    mock_dry_run,
    mock_branch_diff,
    mock_filter_synced,
    mock_runner_cls,
    tmp_path: Path,
) -> None:
    """A misbehaving LLM that proposes a correction for a module OUTSIDE the
    sync set (here: ``other_python.prompt``) and tries to ADD a dependency
    the prompt does not declare via ``<pdd-dependency>`` must NOT be allowed
    to leave ``architecture.json`` in a state that fails
    ``validate-arch-includes``.

    This is the Step 6 scope-expansion bug: corrections are applied verbatim
    even for modules not in ``modules_to_sync``, bypassing the deterministic
    per-module re-convergence via ``update_architecture_from_prompt``. The
    fix must either (a) filter corrections to ``modules_to_sync`` only, or
    (b) re-converge every touched entry from the prompt's ``<pdd-dependency>``
    source-of-truth.

    The test sets up a real prompts tree so that ``<pdd-dependency>`` can be
    consulted by the fix, then asserts the final on-disk arch is consistent
    with the prompt declarations — i.e. the spurious dep is NOT present.
    """
    # Real project tree the fix can read pdd-dependency tags from.
    project_root = tmp_path
    (project_root / ".git").mkdir()
    prompts_dir = project_root / "prompts"
    prompts_dir.mkdir()
    # "other" is OUT of modules_to_sync. Its prompt only declares foo_LLM.prompt.
    (prompts_dir / "other_python.prompt").write_text(
        "<pdd-reason>r</pdd-reason>\n\n"
        "<pdd-dependency>foo_LLM.prompt</pdd-dependency>\n\n"
        "% Body\n",
        encoding="utf-8",
    )
    (prompts_dir / "foo_python.prompt").write_text(
        "<pdd-reason>r</pdd-reason>\n\n% Body\n", encoding="utf-8"
    )
    (prompts_dir / "foo_LLM.prompt").write_text("%", encoding="utf-8")
    (prompts_dir / "sync_order_python.prompt").write_text("%", encoding="utf-8")

    arch_path = project_root / "architecture.json"
    architecture = [
        _arch_entry("foo_python.prompt", []),
        _arch_entry("other_python.prompt", ["foo_LLM.prompt"]),
        _arch_entry("foo_LLM.prompt", []),
        _arch_entry("sync_order_python.prompt", []),
    ]
    arch_path.write_text(json.dumps(architecture, indent=2), encoding="utf-8")

    mock_gh_cmd.return_value = (True, json.dumps({"title": "t", "body": "b", "comments_url": ""}))
    mock_load_arch.return_value = (architecture, arch_path)
    mock_dry_run.return_value = (True, {"foo": project_root}, [], 0.0)
    mock_build_graph.return_value = MagicMock(graph={"foo": []}, warnings=[])
    mock_runner = MagicMock()
    mock_runner.run.return_value = (True, "ok", 0.0)
    mock_runner_cls.return_value = mock_runner

    # MODULES_TO_SYNC = ["foo"]  (so "other" is OUT OF SCOPE), but the LLM
    # tries to corrupt "other"'s deps anyway by adding sync_order_python.prompt
    # — which "other_python.prompt" does NOT declare via <pdd-dependency>.
    mock_agentic_task.return_value = (
        True,
        (
            'MODULES_TO_SYNC: ["foo"]\n'
            "DEPS_VALID: false\n"
            "DEPS_CORRECTIONS: ["
            '{"filename": "other_python.prompt", '
            '"dependencies": ["foo_LLM.prompt", "sync_order_python.prompt"]}'
            "]"
        ),
        0.01,
        "anthropic",
    )

    from pdd.agentic_sync import run_agentic_sync

    with patch("pdd.agentic_sync._find_project_root", return_value=project_root):
        run_agentic_sync(
            "https://github.com/promptdriven/pdd/issues/1061",
            quiet=True,
        )

    final = json.loads(arch_path.read_text(encoding="utf-8"))
    other_entry = next(e for e in final if e["filename"] == "other_python.prompt")
    assert "sync_order_python.prompt" not in other_entry["dependencies"], (
        "Out-of-scope LLM-proposed corrections must not fabricate a dep the "
        "prompt does not declare via <pdd-dependency>; got "
        f"{other_entry['dependencies']!r}"
    )
    # And validate-arch-includes must be clean for the out-of-scope module.
    warnings = cross_validate_architecture_with_prompt_includes(final, project_root)
    bad = [w for w in warnings if "other_python.prompt" in w]
    assert bad == [], (
        f"validate-arch-includes warnings for out-of-scope module: {bad!r}"
    )


# ---------------------------------------------------------------------------
# iter-1 codex review follow-ups.
#
# [B1] Re-convergence MUST include module-prompt <include> targets, not only
# <pdd-dependency> tags — the validator
# (cross_validate_architecture_with_prompt_includes) still treats
# <include select="def:x">b_python.prompt</include> as a required dep.
#
# [B2] modules_to_sync gate MUST use path-preserving basename normalization,
# matching architecture graph alias rules: a correction for
# 'commands/fix_python.prompt' must match modules_to_sync=['commands/fix'].
#
# [M1] auto-deps context-only filter MUST apply only to non-prompt source
# includes, NOT to <include select=...> on module prompts.
# ---------------------------------------------------------------------------


def test_b1_reconverge_preserves_module_prompt_select_include(tmp_path: Path) -> None:
    """[B1] An ``<include select="def:x">b_python.prompt</include>`` MUST
    survive ``_apply_architecture_corrections``' re-convergence even when
    no matching ``<pdd-dependency>`` tag is present.

    Without this, the validator
    (``cross_validate_architecture_with_prompt_includes``) re-warns:
    "a_python.prompt <include>s module 'b' ... but architecture.json
    dependencies do not list that module".
    """
    from pdd.agentic_sync import _apply_architecture_corrections

    project_root = tmp_path
    (project_root / ".git").mkdir()
    prompts = project_root / "prompts"
    prompts.mkdir()
    (prompts / "a_python.prompt").write_text(
        "<pdd-reason>r</pdd-reason>\n\n"
        "<pdd-dependency>a_LLM.prompt</pdd-dependency>\n\n"
        "% Pull in b's interface as context.\n"
        '<include select="def:x">b_python.prompt</include>\n',
        encoding="utf-8",
    )
    (prompts / "a_LLM.prompt").write_text("%", encoding="utf-8")
    (prompts / "b_python.prompt").write_text("%", encoding="utf-8")
    (prompts / "extra_python.prompt").write_text("%", encoding="utf-8")

    arch_path = project_root / "architecture.json"
    architecture = [
        {
            "filename": "a_python.prompt",
            "dependencies": ["a_LLM.prompt", "b_python.prompt", "extra_python.prompt"],
        },
        {"filename": "a_LLM.prompt", "dependencies": []},
        {"filename": "b_python.prompt", "dependencies": []},
        {"filename": "extra_python.prompt", "dependencies": []},
    ]
    arch_path.write_text(json.dumps(architecture, indent=2), encoding="utf-8")

    # LLM proposes trimming to ['a_LLM.prompt'] (the iter-0 buggy direction).
    corrections = [
        {"filename": "a_python.prompt", "dependencies": ["a_LLM.prompt"]},
    ]
    _apply_architecture_corrections(
        project_root, corrections, architecture, quiet=True
    )

    final = json.loads(arch_path.read_text(encoding="utf-8"))
    entry = next(e for e in final if e["filename"] == "a_python.prompt")
    assert "b_python.prompt" in entry["dependencies"], (
        "Module-prompt <include> targets must survive re-convergence; got "
        f"{entry['dependencies']!r}"
    )
    # Spurious 'extra_python.prompt' must be removed (no <pdd-dependency>, no include).
    assert "extra_python.prompt" not in entry["dependencies"], (
        f"Undeclared dep should have been trimmed; got {entry['dependencies']!r}"
    )

    warnings = cross_validate_architecture_with_prompt_includes(final, project_root)
    bad = [w for w in warnings if "a_python.prompt" in w]
    assert bad == [], (
        "validate-arch-includes must not warn for a_python.prompt after "
        f"re-convergence; got: {bad!r}"
    )


def test_b2_path_qualified_correction_not_skipped_as_out_of_scope(
    tmp_path: Path,
) -> None:
    """[B2] A correction for ``commands/fix_python.prompt`` must NOT be
    skipped when ``modules_to_sync=['commands/fix']`` — the gate must use
    path-preserving basename normalization (``commands/fix_python.prompt``
    → ``commands/fix``), not the bare-stem form (``fix``) which loses the
    directory and would mismatch.
    """
    from pdd.agentic_sync import _apply_architecture_corrections

    project_root = tmp_path
    (project_root / ".git").mkdir()
    prompts = project_root / "prompts" / "commands"
    prompts.mkdir(parents=True)
    (prompts / "fix_python.prompt").write_text(
        "<pdd-reason>r</pdd-reason>\n\n"
        "<pdd-dependency>fix_LLM.prompt</pdd-dependency>\n\n"
        "% Body\n",
        encoding="utf-8",
    )
    (project_root / "prompts" / "fix_LLM.prompt").write_text("%", encoding="utf-8")

    arch_path = project_root / "architecture.json"
    architecture = [
        {
            "filename": "commands/fix_python.prompt",
            "dependencies": ["fix_LLM.prompt", "stale_python.prompt"],
        },
        {"filename": "fix_LLM.prompt", "dependencies": []},
        {"filename": "stale_python.prompt", "dependencies": []},
    ]
    arch_path.write_text(json.dumps(architecture, indent=2), encoding="utf-8")

    corrections = [
        {
            "filename": "commands/fix_python.prompt",
            "dependencies": ["fix_LLM.prompt"],
        }
    ]
    _apply_architecture_corrections(
        project_root,
        corrections,
        architecture,
        quiet=True,
        modules_to_sync=["commands/fix"],
    )

    final = json.loads(arch_path.read_text(encoding="utf-8"))
    entry = next(
        e for e in final if e["filename"] == "commands/fix_python.prompt"
    )
    assert "stale_python.prompt" not in entry["dependencies"], (
        "The correction for the in-scope path-qualified module 'commands/fix' "
        "must have been applied (stale dep removed); got "
        f"{entry['dependencies']!r}"
    )


def test_b2_bare_basename_modules_to_sync_still_matches_flat_correction(
    tmp_path: Path,
) -> None:
    """[B2] Backwards-compat: a flat correction filename
    ``fix_python.prompt`` must still match ``modules_to_sync=['fix']``,
    even with the new path-preserving alias rules.
    """
    from pdd.agentic_sync import _apply_architecture_corrections

    project_root = tmp_path
    (project_root / ".git").mkdir()
    prompts = project_root / "prompts"
    prompts.mkdir()
    (prompts / "fix_python.prompt").write_text(
        "<pdd-dependency>fix_LLM.prompt</pdd-dependency>\n", encoding="utf-8"
    )

    arch_path = project_root / "architecture.json"
    architecture = [
        {"filename": "fix_python.prompt", "dependencies": ["fix_LLM.prompt", "stale.prompt"]},
        {"filename": "fix_LLM.prompt", "dependencies": []},
    ]
    arch_path.write_text(json.dumps(architecture, indent=2), encoding="utf-8")

    _apply_architecture_corrections(
        project_root,
        [{"filename": "fix_python.prompt", "dependencies": ["fix_LLM.prompt"]}],
        architecture,
        quiet=True,
        modules_to_sync=["fix"],
    )

    final = json.loads(arch_path.read_text(encoding="utf-8"))
    entry = next(e for e in final if e["filename"] == "fix_python.prompt")
    assert "stale.prompt" not in entry["dependencies"], (
        f"correction should have been applied for flat 'fix' module; got "
        f"{entry['dependencies']!r}"
    )


def test_m1_auto_deps_promotes_module_prompt_select_include(tmp_path: Path) -> None:
    """[M1] ``extract_include_paths_from_prompt_text`` MUST keep
    ``<include select="def:x">b_python.prompt</include>`` because the
    validator still treats that as a module dep. Only non-prompt
    source-file includes (``pdd/sync_order.py`` with ``select=``/
    ``mode="interface"``) are filtered as context-only.
    """
    from pdd.auto_deps_architecture import extract_include_paths_from_prompt_text

    text = (
        '<include select="def:foo">b_python.prompt</include>\n'
        '<include mode="interface" select="def:bar">c_python.prompt</include>\n'
        '<include>full_python.prompt</include>\n'
        '<include select="def:baz" mode="interface">pdd/source.py</include>\n'
    )
    paths = extract_include_paths_from_prompt_text(text)

    # Module-prompt targets survive the filter even with select=/mode=.
    assert "b_python.prompt" in paths, (
        f"select= on a module prompt must remain an architecture dep; got {paths!r}"
    )
    assert "c_python.prompt" in paths, (
        f"mode=interface on a module prompt must remain an architecture dep; got {paths!r}"
    )
    assert "full_python.prompt" in paths, (
        f"plain include of a module prompt must remain an architecture dep; got {paths!r}"
    )
    # Non-prompt source include with select=/mode= is context-only and filtered out.
    assert "pdd/source.py" not in paths, (
        f"context-only source include must be filtered; got {paths!r}"
    )


def test_b1_self_include_does_not_create_self_edge(tmp_path: Path) -> None:
    """Self-includes (a module-prompt including itself) MUST NOT be turned
    into a self-edge in arch deps. This mirrors the validator's
    ``m != self_mod`` / ``m != mod_base`` filter in
    ``cross_validate_architecture_with_prompt_includes``.
    """
    from pdd.agentic_sync import _apply_architecture_corrections

    project_root = tmp_path
    (project_root / ".git").mkdir()
    prompts = project_root / "prompts"
    prompts.mkdir()
    (prompts / "a_python.prompt").write_text(
        "<pdd-reason>r</pdd-reason>\n\n"
        "<pdd-dependency>a_LLM.prompt</pdd-dependency>\n\n"
        "% Self-include for self-context (should NOT become a self-edge dep).\n"
        "<include>a_python.prompt</include>\n",
        encoding="utf-8",
    )
    (prompts / "a_LLM.prompt").write_text("%", encoding="utf-8")

    arch_path = project_root / "architecture.json"
    architecture = [
        {"filename": "a_python.prompt", "dependencies": ["a_LLM.prompt"]},
        {"filename": "a_LLM.prompt", "dependencies": []},
    ]
    arch_path.write_text(json.dumps(architecture, indent=2), encoding="utf-8")

    _apply_architecture_corrections(
        project_root,
        [{"filename": "a_python.prompt", "dependencies": []}],
        architecture,
        quiet=True,
    )

    final = json.loads(arch_path.read_text(encoding="utf-8"))
    entry = next(e for e in final if e["filename"] == "a_python.prompt")
    assert "a_python.prompt" not in entry["dependencies"], (
        "Self-include must not produce a self-edge dep; got "
        f"{entry['dependencies']!r}"
    )
    assert entry["dependencies"] == ["a_LLM.prompt"], (
        f"Re-converged deps should match <pdd-dependency> declarations only; got "
        f"{entry['dependencies']!r}"
    )


def test_m1_auto_deps_merge_preserves_select_include_of_module_prompt(
    tmp_path: Path,
) -> None:
    """[M1] End-to-end at the merge boundary: when a prompt gains
    ``<include select="def:x">b_python.prompt</include>``, the auto-deps
    merge must add ``b_python.prompt`` to the architecture entry so the
    validator stays happy.
    """
    from pdd.auto_deps_architecture import merge_auto_deps_includes_into_architecture

    project_root = tmp_path
    (project_root / ".git").mkdir()
    prompts = project_root / "prompts"
    prompts.mkdir()
    a_prompt = prompts / "a_python.prompt"
    a_prompt.write_text("<pdd-reason>r</pdd-reason>\n% Body\n", encoding="utf-8")
    (prompts / "b_python.prompt").write_text("%", encoding="utf-8")

    arch_path = project_root / "architecture.json"
    architecture = [
        {"filename": "a_python.prompt", "dependencies": []},
        {"filename": "b_python.prompt", "dependencies": []},
    ]
    arch_path.write_text(json.dumps(architecture, indent=2), encoding="utf-8")

    old_text = "<pdd-reason>r</pdd-reason>\n% Body\n"
    new_text = (
        "<pdd-reason>r</pdd-reason>\n"
        '<include select="def:bar">b_python.prompt</include>\n'
        "% Body\n"
    )

    report = merge_auto_deps_includes_into_architecture(
        project_root, a_prompt, old_text, new_text
    )
    assert "b_python.prompt" in report["added_dependencies"], (
        "auto-deps must promote a select= include of a module prompt to an "
        f"architecture dep; got {report!r}"
    )


def test_b1_iter2_same_tail_path_qualified_correction_rejected_for_flat_scope(
    tmp_path: Path,
) -> None:
    """[B1.iter2] A correction for the path-qualified module
    ``core/cli_python.prompt`` must be REJECTED when
    ``modules_to_sync=['cli']`` even though the tail basename matches.

    Reason: iter-1 added a bare-stem alias for every correction filename,
    which turned ``core/cli_python.prompt`` into the alias set
    ``{"core/cli", "cli"}``. That collision let an out-of-scope correction
    cross scope boundaries and mutate an unrelated path-qualified module
    that merely shared the same tail basename. The gate must be
    path-preserving: only fall back to the bare stem when both sides are
    unqualified (no ``/``).
    """
    from pdd.agentic_sync import _apply_architecture_corrections

    project_root = tmp_path
    (project_root / ".git").mkdir()
    core_prompts = project_root / "prompts" / "core"
    core_prompts.mkdir(parents=True)
    flat_prompts = project_root / "prompts"
    (core_prompts / "cli_python.prompt").write_text(
        "<pdd-dependency>cli_LLM.prompt</pdd-dependency>\n", encoding="utf-8"
    )
    (flat_prompts / "cli_python.prompt").write_text(
        "<pdd-dependency>cli_LLM.prompt</pdd-dependency>\n", encoding="utf-8"
    )
    (flat_prompts / "cli_LLM.prompt").write_text("%", encoding="utf-8")

    arch_path = project_root / "architecture.json"
    architecture = [
        {
            "filename": "core/cli_python.prompt",
            "dependencies": ["cli_LLM.prompt", "stale_core.prompt"],
        },
        {
            "filename": "cli_python.prompt",
            "dependencies": ["cli_LLM.prompt"],
        },
        {"filename": "cli_LLM.prompt", "dependencies": []},
        {"filename": "stale_core.prompt", "dependencies": []},
    ]
    arch_path.write_text(json.dumps(architecture, indent=2), encoding="utf-8")

    # A correction targeting the OUT-of-scope path-qualified module.
    corrections = [
        {
            "filename": "core/cli_python.prompt",
            "dependencies": ["cli_LLM.prompt"],
        }
    ]
    _apply_architecture_corrections(
        project_root,
        corrections,
        architecture,
        quiet=True,
        modules_to_sync=["cli"],  # flat — must NOT match core/cli
    )

    final = json.loads(arch_path.read_text(encoding="utf-8"))
    core_entry = next(
        e for e in final if e["filename"] == "core/cli_python.prompt"
    )
    assert "stale_core.prompt" in core_entry["dependencies"], (
        "Out-of-scope path-qualified correction (core/cli) MUST NOT be "
        "applied when modules_to_sync targets the flat 'cli' module; "
        f"got core entry deps {core_entry['dependencies']!r}"
    )


def test_b1_iter2_symmetric_bare_correction_rejected_for_path_qualified_scope(
    tmp_path: Path,
) -> None:
    """[B1.iter2 — symmetric] The mirror case must also reject: a
    correction for flat ``cli_python.prompt`` must NOT be accepted when
    ``modules_to_sync=['core/cli']`` even though the tail basename
    matches. Without the path-qualified guard on
    ``_normalise_sync_module_names``, the iter-1 bare-stem alias on the
    sync entry made the allowed set contain ``"cli"``, which then matched
    the unqualified correction's bare-stem alias.
    """
    from pdd.agentic_sync import _apply_architecture_corrections

    project_root = tmp_path
    (project_root / ".git").mkdir()
    flat_prompts = project_root / "prompts"
    flat_prompts.mkdir()
    core_prompts = flat_prompts / "core"
    core_prompts.mkdir()
    (flat_prompts / "cli_python.prompt").write_text(
        "<pdd-dependency>cli_LLM.prompt</pdd-dependency>\n", encoding="utf-8"
    )
    (core_prompts / "cli_python.prompt").write_text(
        "<pdd-dependency>cli_LLM.prompt</pdd-dependency>\n", encoding="utf-8"
    )
    (flat_prompts / "cli_LLM.prompt").write_text("%", encoding="utf-8")

    arch_path = project_root / "architecture.json"
    architecture = [
        {
            "filename": "cli_python.prompt",
            "dependencies": ["cli_LLM.prompt", "stale_flat.prompt"],
        },
        {
            "filename": "core/cli_python.prompt",
            "dependencies": ["cli_LLM.prompt"],
        },
        {"filename": "cli_LLM.prompt", "dependencies": []},
        {"filename": "stale_flat.prompt", "dependencies": []},
    ]
    arch_path.write_text(json.dumps(architecture, indent=2), encoding="utf-8")

    corrections = [
        {
            "filename": "cli_python.prompt",
            "dependencies": ["cli_LLM.prompt"],
        }
    ]
    _apply_architecture_corrections(
        project_root,
        corrections,
        architecture,
        quiet=True,
        modules_to_sync=["core/cli"],  # path-qualified — must NOT match flat
    )

    final = json.loads(arch_path.read_text(encoding="utf-8"))
    flat_entry = next(
        e for e in final if e["filename"] == "cli_python.prompt"
    )
    assert "stale_flat.prompt" in flat_entry["dependencies"], (
        "Out-of-scope flat correction MUST NOT be applied when "
        "modules_to_sync targets the path-qualified 'core/cli' module; "
        f"got flat entry deps {flat_entry['dependencies']!r}"
    )


def test_m1_iter2_same_tail_path_qualified_include_kept_as_dep(
    tmp_path: Path,
) -> None:
    """[M1.iter2] Same-tail path-qualified include must be KEPT as a dep.

    ``commands/fix_python.prompt`` that ``<include>``s
    ``server/fix_python.prompt`` is **not** a self-include — the two
    modules live in different directories and the validator (and the
    architecture graph) consider them distinct modules. iter-1's
    self-edge guard compared bare basenames and would silently drop the
    ``server/fix_python.prompt`` dependency during re-convergence.

    The path-preserving guard keeps the dep when self/inc directories
    differ.
    """
    from pdd.agentic_sync import (
        _apply_architecture_corrections,
        _module_prompt_include_dependencies,
    )

    project_root = tmp_path
    (project_root / ".git").mkdir()
    commands_dir = project_root / "prompts" / "commands"
    commands_dir.mkdir(parents=True)
    server_dir = project_root / "prompts" / "server"
    server_dir.mkdir(parents=True)

    self_prompt = commands_dir / "fix_python.prompt"
    self_prompt.write_text(
        "<pdd-reason>r</pdd-reason>\n\n"
        "% Body — include a same-tail module prompt from another folder.\n"
        '<include select="def:fix">server/fix_python.prompt</include>\n',
        encoding="utf-8",
    )
    (server_dir / "fix_python.prompt").write_text("%", encoding="utf-8")

    # Direct unit-level: re-conv must keep the cross-folder same-tail dep.
    direct_deps = _module_prompt_include_dependencies(
        self_prompt, self_filename="commands/fix_python.prompt"
    )
    assert "server/fix_python.prompt" in direct_deps, (
        "Path-preserving self-edge guard must keep same-tail cross-folder "
        f"include as a dep; got {direct_deps!r}"
    )

    # End-to-end through ``_apply_architecture_corrections``: the
    # correction's re-convergence must write the include-backed dep into
    # the owning architecture.json entry.
    arch_path = project_root / "architecture.json"
    architecture = [
        {
            "filename": "commands/fix_python.prompt",
            # Start empty; re-convergence must add ``server/fix_python.prompt``
            # because the prompt <include>s it.
            "dependencies": [],
        },
        {"filename": "server/fix_python.prompt", "dependencies": []},
    ]
    arch_path.write_text(json.dumps(architecture, indent=2), encoding="utf-8")

    _apply_architecture_corrections(
        project_root,
        [{"filename": "commands/fix_python.prompt", "dependencies": []}],
        architecture,
        quiet=True,
    )

    final = json.loads(arch_path.read_text(encoding="utf-8"))
    entry = next(
        e for e in final if e["filename"] == "commands/fix_python.prompt"
    )
    assert "server/fix_python.prompt" in entry["dependencies"], (
        "Re-converged deps must include the same-tail cross-folder "
        f"<include> target; got {entry['dependencies']!r}"
    )
    # commands/fix_python.prompt is NOT in its own deps (real self-edge filter).
    assert "commands/fix_python.prompt" not in entry["dependencies"], (
        "Self filename must never appear as its own dep; got "
        f"{entry['dependencies']!r}"
    )


def test_m1_iter2_real_path_qualified_self_include_still_dropped(
    tmp_path: Path,
) -> None:
    """[M1.iter2] Sanity check the symmetric direction: a *real*
    path-qualified self-include (same folder, same name) must still be
    dropped as a self-edge. Without this, the path-preserving guard
    would over-correct and allow self-edges in nested layouts.
    """
    from pdd.agentic_sync import _module_prompt_include_dependencies

    prompts_dir = tmp_path / "prompts" / "commands"
    prompts_dir.mkdir(parents=True)
    self_prompt = prompts_dir / "fix_python.prompt"
    self_prompt.write_text(
        "% Self-include for self-context (path-qualified).\n"
        "<include>commands/fix_python.prompt</include>\n",
        encoding="utf-8",
    )

    deps = _module_prompt_include_dependencies(
        self_prompt, self_filename="commands/fix_python.prompt"
    )
    assert "commands/fix_python.prompt" not in deps, (
        "Real path-qualified self-include must still be dropped; got "
        f"{deps!r}"
    )


def test_n1_iter2_include_dependencies_preserve_source_order(
    tmp_path: Path,
) -> None:
    """[N1.iter2] Multiple module-prompt ``<include>``s must produce
    dependencies in **source declaration order**, not hash-dependent
    set order. iter-1 iterated a ``set`` from
    ``extract_includes_from_file`` and produced churn in
    ``architecture.json`` diffs whenever the hash seed changed.
    """
    from pdd.agentic_sync import _module_prompt_include_dependencies

    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    # Use names that hash very differently and would shuffle in a set.
    self_prompt = prompts_dir / "owner_python.prompt"
    body = (
        "<pdd-reason>order test</pdd-reason>\n"
        "<include>zeta_python.prompt</include>\n"
        "<include>alpha_python.prompt</include>\n"
        "<include>mu_python.prompt</include>\n"
        "<include>beta_python.prompt</include>\n"
        "<include>gamma_python.prompt</include>\n"
    )
    self_prompt.write_text(body, encoding="utf-8")
    # Touch dep targets so the helper sees them as module prompts.
    for name in ("zeta", "alpha", "mu", "beta", "gamma"):
        (prompts_dir / f"{name}_python.prompt").write_text("%", encoding="utf-8")

    deps = _module_prompt_include_dependencies(
        self_prompt, self_filename="owner_python.prompt"
    )

    expected = [
        "zeta_python.prompt",
        "alpha_python.prompt",
        "mu_python.prompt",
        "beta_python.prompt",
        "gamma_python.prompt",
    ]
    assert deps == expected, (
        "Include-backed deps must preserve source declaration order; got "
        f"{deps!r} (expected {expected!r})"
    )


def test_n1_iter2_ordered_extractor_in_sync_order(tmp_path: Path) -> None:
    """[N1.iter2] Direct unit test for ``extract_includes_from_file_ordered``:
    declarations come back in source order with first-occurrence dedup,
    and the three include forms (body, self-closing, include-many) all
    interleave correctly.
    """
    from pdd.sync_order import extract_includes_from_file_ordered

    path = tmp_path / "mixed.prompt"
    path.write_text(
        "<include>first.md</include>\n"
        '<include path="second.md" />\n'
        "<include-many>third.md, fourth.md</include-many>\n"
        "<include>second.md</include>\n"  # dup of self-closing -> dropped
        "<include>fifth.md</include>\n",
        encoding="utf-8",
    )

    ordered = extract_includes_from_file_ordered(path)
    assert ordered == [
        "first.md",
        "second.md",
        "third.md",
        "fourth.md",
        "fifth.md",
    ], f"Expected source-order with first-occurrence dedup; got {ordered!r}"


def test_m1_iter3_prompts_prefixed_self_include_is_dropped(
    tmp_path: Path,
) -> None:
    """[M1.iter3] A self-include spelled with the ``prompts/`` prefix
    must be recognized as a self-edge and dropped during re-convergence.

    iter-2's self-edge guard compared
    ``_basename_from_architecture_filename(inc)`` directly against the
    architecture filename key, so ``<include>prompts/self_python.prompt</include>``
    inside ``self_python.prompt`` became ``prompts/self`` vs ``self`` —
    not equal — and the dep was incorrectly written into the entry's own
    ``dependencies``. The fix canonicalizes the include path (stripping
    ``./`` and leading ``prompts/``) before the basename compare so the
    common prompt-root-prefixed spelling is treated as a self-edge.
    """
    from pdd.agentic_sync import _module_prompt_include_dependencies

    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    self_prompt = prompts_dir / "self_python.prompt"
    self_prompt.write_text(
        "% Self-include with ``prompts/`` prefix — must be dropped.\n"
        "<include>prompts/self_python.prompt</include>\n",
        encoding="utf-8",
    )

    deps = _module_prompt_include_dependencies(
        self_prompt, self_filename="self_python.prompt"
    )
    assert "prompts/self_python.prompt" not in deps, (
        "``prompts/`` prefixed self-include must be canonicalized and "
        f"dropped as a self-edge; got {deps!r}"
    )
    assert deps == [], (
        "No deps expected (only the self-edge was present); got "
        f"{deps!r}"
    )


def test_m1_iter3_dot_slash_prefixed_self_include_is_dropped(
    tmp_path: Path,
) -> None:
    """[M1.iter3] Symmetric coverage: a ``./``-prefixed self-include
    must also be canonicalized and dropped. ``_normalize_prompt_filename``
    strips both ``./`` and ``prompts/``, so the path-preserving basename
    compare must work for either spelling.
    """
    from pdd.agentic_sync import _module_prompt_include_dependencies

    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    self_prompt = prompts_dir / "owner_python.prompt"
    self_prompt.write_text(
        "% Self-include with ``./`` prefix — must be dropped.\n"
        "<include>./owner_python.prompt</include>\n",
        encoding="utf-8",
    )

    deps = _module_prompt_include_dependencies(
        self_prompt, self_filename="owner_python.prompt"
    )
    assert deps == [], (
        "``./``-prefixed self-include must be canonicalized and dropped; "
        f"got {deps!r}"
    )


def test_m2_iter3_path_attribute_wins_over_body_in_auto_deps() -> None:
    """[M2.iter3] ``<include path="X">Y</include>`` must resolve to ``X``
    (the validator/preprocessor contract), not ``Y``. iter-2's
    ``extract_include_paths_from_prompt_text`` ignored ``path=`` and used
    the body, so an include like
    ``<include path="pdd/source.py">b_python.prompt</include>`` caused
    auto-deps to add ``b_python.prompt`` as a module dependency while the
    validator/preprocessor resolved the include to ``pdd/source.py`` —
    fabricating the exact kind of dependency #1061 is meant to prevent.
    """
    from pdd.auto_deps_architecture import extract_include_paths_from_prompt_text

    text = '<include path="pdd/source.py">b_python.prompt</include>\n'
    paths = extract_include_paths_from_prompt_text(text)

    assert "b_python.prompt" not in paths, (
        "Body content must NOT be returned as an architecture dep when "
        f"path= is set; got {paths!r}"
    )
    # ``pdd/source.py`` with no selector/interface attrs is a full
    # source-file include, so it remains a candidate (handled later by
    # ``_architecture_filename_for_module_include`` if it maps to a
    # module entry).
    assert paths == {"pdd/source.py"}, (
        "path= attribute must be the effective include target; got "
        f"{paths!r}"
    )


def test_m2_iter3_path_attribute_context_include_skipped_for_module_dep(
    tmp_path: Path,
) -> None:
    """[M2.iter3] End-to-end: a ``<include path="pdd/source.py" select=...>``
    that names ``b_python.prompt`` in its body must NOT cause
    ``merge_auto_deps_includes_into_architecture`` to add
    ``b_python.prompt`` as a fabricated dep, and must NOT add
    ``pdd/source.py`` either (it's a context-only source-file include
    with a selector, not a full source dep).
    """
    from pdd.auto_deps_architecture import merge_auto_deps_includes_into_architecture

    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    src = tmp_path / "pdd"
    src.mkdir()
    (src / "source.py").write_text("def foo(): ...\n", encoding="utf-8")
    (prompts / "a_python.prompt").write_text("%\n", encoding="utf-8")
    (prompts / "b_python.prompt").write_text("%\n", encoding="utf-8")
    arch = [
        {"filename": "a_python.prompt", "dependencies": []},
        {"filename": "b_python.prompt", "dependencies": []},
    ]
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps(arch), encoding="utf-8")

    old = "%\n"
    # path= attribute resolves to pdd/source.py; the body b_python.prompt
    # is a human-readable hint to the LLM but is NOT the include target.
    new = (
        '%\n<include path="pdd/source.py" select="def:foo">'
        "b_python.prompt</include>\n"
    )

    report = merge_auto_deps_includes_into_architecture(
        tmp_path, prompts / "a_python.prompt", old, new
    )

    data = json.loads(arch_path.read_text(encoding="utf-8"))
    a = next(e for e in data if e["filename"] == "a_python.prompt")
    assert "b_python.prompt" not in a["dependencies"], (
        "Body content of a path= include must NOT be added as a "
        f"fabricated dep; got {a['dependencies']!r}"
    )
    # The path= target pdd/source.py has a selector, so it's a
    # context-only include and not a module dep either.
    assert report["added_dependencies"] == [], (
        "No module deps should be added for a context-only path= "
        f"include; got {report['added_dependencies']!r}"
    )


def test_m1_iter4_self_closing_path_include_adds_architecture_dep(
    tmp_path: Path,
) -> None:
    """[M1.iter4] Self-closing ``<include path="b_python.prompt" />`` must
    add ``b_python.prompt`` to the architecture dependencies of the
    enclosing prompt.

    Iter-3's ``extract_include_paths_from_prompt_text`` only matched the
    body-form ``<include ...>body</include>``, so a self-closing
    ``<include path="b_python.prompt" />`` was silently dropped by
    auto-deps. The preprocessor (``pdd.preprocess.process_include_tags``)
    and the validator
    (``architecture_include_validation._extract_include_references``) both
    accept the self-closing form, so the validator would then report
    ``a_python.prompt includes module 'b' but architecture deps don't
    list it`` — recreating the exact #1061 auto-deps / validator drift.

    This test exercises the full pipeline through
    ``merge_auto_deps_includes_into_architecture`` and asserts the dep is
    written into ``architecture.json``.
    """
    from pdd.auto_deps_architecture import merge_auto_deps_includes_into_architecture

    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "a_python.prompt").write_text("%\n", encoding="utf-8")
    (prompts / "b_python.prompt").write_text("%\n", encoding="utf-8")
    arch = [
        {"filename": "a_python.prompt", "dependencies": []},
        {"filename": "b_python.prompt", "dependencies": []},
    ]
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps(arch), encoding="utf-8")

    old = "%\n"
    # Self-closing include — no body, path= attribute carries the
    # module-prompt target.
    new = '%\n<include path="b_python.prompt" />\n'

    report = merge_auto_deps_includes_into_architecture(
        tmp_path, prompts / "a_python.prompt", old, new
    )

    assert report["updated"] is True, (
        "Self-closing <include path=.../> must drive an architecture "
        f"update; got report={report!r}"
    )
    assert report["added_dependencies"] == ["b_python.prompt"], (
        "Self-closing include must add b_python.prompt as a dep; "
        f"got {report['added_dependencies']!r}"
    )

    data = json.loads(arch_path.read_text(encoding="utf-8"))
    a = next(e for e in data if e["filename"] == "a_python.prompt")
    assert a["dependencies"] == ["b_python.prompt"], (
        "architecture.json must list b_python.prompt as a dep of "
        f"a_python.prompt; got {a['dependencies']!r}"
    )


def test_m1_iter5_self_closing_followed_by_body_form_both_extracted() -> None:
    """[M1.iter5] A self-closing ``<include path="b" />`` immediately
    followed by a body-form ``<include>c</include>`` must extract BOTH
    targets.

    Iter-4 added a self-closing branch alongside the body-form branch,
    but the body-form regex lacked the ``(?<!/)>`` negative lookbehind
    that ``pdd/sync_order.py::extract_includes_from_file`` uses. As a
    result, the body-form pattern would greedily span from the
    self-closing ``<include ... />`` opener to a later ``</include>``,
    swallowing the inner body-form include and silently dropping its
    target.

    ``cross_validate_architecture_with_prompt_includes`` uses
    ``sync_order``'s extractor, so the validator sees both includes
    but architecture deps only get one — recreating the exact
    auto-deps/validator drift #1061 is supposed to close.

    The plain ``<include>...</include>`` assertion is intentional: the
    new lookbehind is applied to a position that previously had no
    guard, so we sanity-check that bare body-form includes still
    extract correctly.
    """
    from pdd.auto_deps_architecture import extract_include_paths_from_prompt_text

    text = (
        '<include path="b_python.prompt" />\n'
        "<include>c_python.prompt</include>\n"
    )
    paths = extract_include_paths_from_prompt_text(text)
    assert paths == {"b_python.prompt", "c_python.prompt"}, (
        "Self-closing include followed by a body-form include must "
        f"extract both targets; got {paths!r}"
    )

    # Sanity: a bare body-form include (no attrs) still extracts.
    bare = extract_include_paths_from_prompt_text(
        "<include>plain.prompt</include>\n"
    )
    assert bare == {"plain.prompt"}, (
        "Bare body-form <include>plain.prompt</include> must still "
        f"extract after adding the lookbehind; got {bare!r}"
    )


def test_m1_iter5_self_closing_then_body_form_both_added_as_deps(
    tmp_path: Path,
) -> None:
    """[M1.iter5] End-to-end: with adjacent self-closing and body-form
    includes naming two different module prompts,
    ``merge_auto_deps_includes_into_architecture`` must add BOTH as
    architecture dependencies.

    Without the self-closing guard on the body-form branch, the
    extractor returned only the self-closing target, so the body-form
    module dep was silently dropped and the validator would then
    report missing-dep drift on the next checkup pass.
    """
    from pdd.auto_deps_architecture import merge_auto_deps_includes_into_architecture

    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "a_python.prompt").write_text("%\n", encoding="utf-8")
    (prompts / "b_python.prompt").write_text("%\n", encoding="utf-8")
    (prompts / "c_python.prompt").write_text("%\n", encoding="utf-8")
    arch = [
        {"filename": "a_python.prompt", "dependencies": []},
        {"filename": "b_python.prompt", "dependencies": []},
        {"filename": "c_python.prompt", "dependencies": []},
    ]
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps(arch), encoding="utf-8")

    old = "%\n"
    # Adjacent self-closing + body-form. Iter-4 dropped c_python.prompt
    # because the body-form regex absorbed the self-closing opener.
    new = (
        "%\n"
        '<include path="b_python.prompt" />\n'
        "<include>c_python.prompt</include>\n"
    )

    report = merge_auto_deps_includes_into_architecture(
        tmp_path, prompts / "a_python.prompt", old, new
    )

    assert report["updated"] is True, (
        "Both adjacent includes must drive an architecture update; "
        f"got report={report!r}"
    )
    assert sorted(report["added_dependencies"]) == [
        "b_python.prompt",
        "c_python.prompt",
    ], (
        "Both module-prompt includes must be added as deps; "
        f"got {report['added_dependencies']!r}"
    )

    data = json.loads(arch_path.read_text(encoding="utf-8"))
    a = next(e for e in data if e["filename"] == "a_python.prompt")
    assert sorted(a["dependencies"]) == ["b_python.prompt", "c_python.prompt"], (
        "architecture.json must list both b_python.prompt and "
        f"c_python.prompt as deps of a_python.prompt; got {a['dependencies']!r}"
    )


def test_f1_prompt_specifies_module_prompt_include_is_dep() -> None:
    """[F1 / third-party codex review] The rendered identify-modules LLM
    prompt MUST tell the model that a ``<include>`` whose target is another
    **module prompt** is an architectural dependency *regardless of
    attributes* (``mode="interface"`` / ``select=`` / ``query=`` / ``lines=``
    / ``path=``).

    The previous wording said "<include> directives (in any form, including
    mode='interface', select='def:...', etc.) are LLM context only and MUST
    NOT be treated as architectural dependencies." That was a flat
    contradiction of the actual re-convergence code in
    ``_declared_prompt_dependencies`` (``pdd/agentic_sync.py``), which
    treats module-prompt includes as part of the authoritative dep union
    so they survive the validator (``cross_validate_architecture_with_prompt_includes``).
    An LLM following the contradictory rule would correctly return
    ``DEPS_VALID: true`` after the LLM call, the correction code path
    would never engage, and ``validate-arch-includes`` would then flag the
    missing module-prompt edge — the exact #1061 inverse drift.

    This test asserts the rendered prompt now:
    1) explicitly identifies module-prompt includes as architectural edges,
    2) ties that rule to the word "architecture" (not just generic "deps"),
    3) calls out that attributes do not change the classification, and
    4) does NOT carry the prior contradictory "any form" wording that
       lumped module-prompt includes with context-only source includes.
    """
    rendered = _render_identify_modules_prompt(
        issue_content="Validate dependencies for issue #1061.",
        arch_json="[]",
        issue_number=1061,
    )

    # 1) The prompt must explicitly use the term "module prompt" (or
    #    "module-prompt") together with the word "architecture" so the
    #    classification rule is unambiguous.
    lower = rendered.lower()
    assert ("module prompt" in lower) or ("module-prompt" in lower), (
        "Prompt must explicitly name 'module prompt' / 'module-prompt' "
        "includes as a distinct class — got rendered template that does "
        "not mention them."
    )
    assert "architecture" in lower, (
        "Prompt must tie the module-prompt include rule to the word "
        "'architecture' so the LLM links the rule to architecture.json deps"
    )

    # 2) The prompt must explicitly say module-prompt includes are deps
    #    *regardless of attributes*. We don't pin a single phrasing, but
    #    the prompt must couple "module prompt" with a "regardless"-style
    #    qualifier so an LLM cannot read it as "only when bare include".
    assert ("regardless of attributes" in lower) or (
        "regardless of any" in lower
    ) or ("always an architecture edge" in lower), (
        "Prompt must state that module-prompt includes are architectural "
        "edges regardless of attributes (e.g. 'regardless of attributes', "
        "'regardless of any ... attribute', or 'always an architecture edge')."
    )

    # 3) The prompt must explicitly enumerate the attributes that do NOT
    #    demote a module-prompt include to context-only. mode="interface"
    #    is the canonical #1055 / #1061 shape and must appear in the rule.
    assert 'mode="interface"' in rendered, (
        "Prompt must explicitly call out mode=\"interface\" in the "
        "module-prompt include rule"
    )
    assert ("select=" in rendered) or ('select="def:' in rendered), (
        "Prompt must explicitly call out select= as an attribute that "
        "does NOT demote a module-prompt include"
    )

    # 4) The prior contradictory wording — "<include> directives (in any
    #    form, including mode='interface', select='def:...', etc.) are
    #    LLM context only" — must be GONE. It is the direct contradiction
    #    of the production re-convergence behavior and the root cause of
    #    the third-party F1 finding.
    contradictory_lower = (
        "<include> directives (in any form, including".lower()
    )
    assert contradictory_lower not in lower, (
        "Prompt must NOT carry the prior 'in any form ... are LLM context "
        "only' rule that contradicts the production correction code in "
        "_declared_prompt_dependencies (pdd/agentic_sync.py)."
    )

    # 5) Worked Example B must exist: a module-prompt include with
    #    selector attributes that IS treated as a dep. Without this
    #    counter-example the LLM only sees the existing
    #    non-prompt-source-file context-only example and may overgeneralize.
    assert "b_python.prompt" in rendered, (
        "Prompt must carry a worked example whose <include> target is a "
        "module prompt (e.g. b_python.prompt) so the LLM has a concrete "
        "example of an attribute-bearing module-prompt include that IS a dep."
    )


def test_f2_path_qualified_same_tail_include_kept_as_dep(tmp_path: Path) -> None:
    """[F2 / third-party codex review] ``merge_auto_deps_includes_into_architecture``
    must NOT silently self-skip a path-qualified same-tail dep.

    Setup: ``commands/fix_python.prompt`` newly ``<include>``s
    ``server/fix_python.prompt``. Both prompts are independent modules in
    ``architecture.json``. Before this fix, both
    ``_architecture_filename_for_module_include`` and the
    ``merge_auto_deps_includes_into_architecture`` self-skip compared via
    ``extract_module_from_include`` — a bare-stem function that returns
    ``"fix"`` for both paths. The result: either the include resolved to
    the wrong entry, or the self-skip dropped the dep (the include's
    ``dep_base`` matched the current entry's ``current_base`` even though
    the two prompts live in different folders).

    Path-preserving keys distinguish the two, so the
    ``server/fix_python.prompt`` dep is correctly added to the
    ``commands/fix_python.prompt`` entry.

    Regression scope: ensures the F2 fix does NOT regress flat-layout
    behavior — a self-include in a flat layout (same dir, same stem) is
    still self-skipped via the bare-stem degradation.
    """
    from pdd.auto_deps_architecture import (
        _architecture_filename_for_module_include,
        merge_auto_deps_includes_into_architecture,
    )

    project_root = tmp_path
    (project_root / ".git").mkdir()
    prompts = project_root / "prompts"
    commands = prompts / "commands"
    server = prompts / "server"
    commands.mkdir(parents=True)
    server.mkdir(parents=True)

    self_prompt = commands / "fix_python.prompt"
    self_prompt.write_text("%\n", encoding="utf-8")
    (server / "fix_python.prompt").write_text("%\n", encoding="utf-8")

    architecture = [
        {"filename": "commands/fix_python.prompt", "dependencies": []},
        {"filename": "server/fix_python.prompt", "dependencies": []},
    ]
    arch_path = project_root / "architecture.json"
    arch_path.write_text(json.dumps(architecture, indent=2), encoding="utf-8")

    # 1) Direct unit-level: same-tail include must resolve to the
    #    cross-folder entry, NOT the same-folder same-tail self entry.
    resolved = _architecture_filename_for_module_include(
        "server/fix_python.prompt", architecture
    )
    assert resolved == "server/fix_python.prompt", (
        "Path-preserving include→arch mapping must pick the cross-folder "
        f"same-tail entry; got {resolved!r}"
    )

    # 2) End-to-end via merge_auto_deps_includes_into_architecture: the
    #    new include must drive an architecture update that adds the
    #    cross-folder dep, NOT silently self-skip on bare-stem collision.
    old = "%\n"
    new = (
        "%\n"
        "<include>server/fix_python.prompt</include>\n"
    )
    report = merge_auto_deps_includes_into_architecture(
        project_root, self_prompt, old, new
    )

    assert report["updated"] is True, (
        "Same-tail cross-folder include must drive an arch update; "
        f"got report={report!r}"
    )
    assert report["added_dependencies"] == ["server/fix_python.prompt"], (
        "Cross-folder same-tail dep must be added (not self-skipped); "
        f"got {report['added_dependencies']!r}"
    )

    data = json.loads(arch_path.read_text(encoding="utf-8"))
    entry = next(
        e for e in data if e["filename"] == "commands/fix_python.prompt"
    )
    assert "server/fix_python.prompt" in entry["dependencies"], (
        "Architecture entry must list the cross-folder same-tail dep; "
        f"got {entry['dependencies']!r}"
    )
    # Sanity: the current module must NOT have been added to its own deps.
    assert "commands/fix_python.prompt" not in entry["dependencies"], (
        "Self-edge must still be suppressed for the current path-qualified "
        f"entry; got {entry['dependencies']!r}"
    )


def test_f4_validator_reverse_missing_dep_path_qualified_same_tail(
    tmp_path: Path,
) -> None:
    """[F4 / third-party codex review] Validator must flag a missing arch
    dep when a path-qualified prompt ``<include>``s a same-tail prompt from
    a different folder that is NOT listed in its arch dependencies.

    Pre-fix, ``cross_validate_architecture_with_prompt_includes`` used
    ``extract_module_from_include`` for every comparison key —
    ``commands/fix_python.prompt`` and ``server/fix_python.prompt`` both
    collapsed to ``"fix"``, so the include and the self-entry's arch
    basename matched. The drift was silently masked. With path-preserving
    keys (``"commands/fix"`` vs ``"server/fix"``), the validator can see
    that ``server/fix`` is an arch module the prompt includes without
    the entry listing it as a dep.

    Asserts:
      * The single returned warning names ``server/fix`` (path-preserved),
        not collapsed to ``fix``.
      * The warning text references ``server/fix_python.prompt`` (the
        original include target) so a reader can locate the offending tag.
    """
    from pdd.architecture_include_validation import (
        cross_validate_architecture_with_prompt_includes,
    )

    project_root = tmp_path / "proj"
    prompts = project_root / "prompts"
    (prompts / "commands").mkdir(parents=True)
    (prompts / "server").mkdir(parents=True)

    (prompts / "commands" / "fix_python.prompt").write_text(
        "%\n<include>server/fix_python.prompt</include>\n",
        encoding="utf-8",
    )
    (prompts / "server" / "fix_python.prompt").write_text(
        "%\n", encoding="utf-8"
    )

    arch = [
        {"filename": "commands/fix_python.prompt", "dependencies": []},
        {"filename": "server/fix_python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, project_root)
    # Filter for warnings about the commands/fix entry (only one expected).
    cmd_warnings = [
        w for w in warnings if "commands/fix_python.prompt" in w
    ]
    assert cmd_warnings, (
        "Validator must emit at least one warning for the "
        f"commands/fix_python.prompt entry; got all={warnings!r}"
    )
    # Path-preserving key must appear in at least one warning.
    assert any("server/fix" in w for w in cmd_warnings), (
        "Path-preserving warning must reference 'server/fix' "
        f"(not collapsed to 'fix'); got {cmd_warnings!r}"
    )


def test_f4_validator_forward_missing_prompt_decl_path_qualified_same_tail(
    tmp_path: Path,
) -> None:
    """[F4 / third-party codex review] Validator must flag a missing prompt
    declaration when arch lists a same-tail cross-folder module as a dep but
    the prompt has neither ``<include>`` nor ``<pdd-dependency>`` of it.

    Pre-fix, the forward check used bare-stem keys throughout, so an arch
    dep on ``server/fix_python.prompt`` collapsed to ``"fix"`` and matched
    the self entry's basename ``"fix"`` — the dep was treated as the
    self-edge and silently dropped from ``arch_modules``. With
    path-preserving keys, ``server/fix`` differs from ``commands/fix`` and
    the missing declaration is correctly surfaced.

    Asserts:
      * The single returned warning names ``server/fix`` (path-preserved).
      * The warning text references ``server/fix_python.prompt`` so the
        offending arch dep is locatable.
    """
    from pdd.architecture_include_validation import (
        cross_validate_architecture_with_prompt_includes,
    )

    project_root = tmp_path / "proj"
    prompts = project_root / "prompts"
    (prompts / "commands").mkdir(parents=True)
    (prompts / "server").mkdir(parents=True)

    # Prompt has no <pdd-dependency> and no <include> for server/fix.
    (prompts / "commands" / "fix_python.prompt").write_text(
        "%\n", encoding="utf-8"
    )
    (prompts / "server" / "fix_python.prompt").write_text(
        "%\n", encoding="utf-8"
    )

    arch = [
        {
            "filename": "commands/fix_python.prompt",
            "dependencies": ["server/fix_python.prompt"],
        },
        {"filename": "server/fix_python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, project_root)
    cmd_warnings = [
        w for w in warnings if "commands/fix_python.prompt" in w
    ]
    assert cmd_warnings, (
        "Validator must emit at least one warning for the "
        f"commands/fix_python.prompt entry; got all={warnings!r}"
    )
    # Path-preserving key must appear in the warning.
    assert any("server/fix" in w for w in cmd_warnings), (
        "Path-preserving warning must reference 'server/fix' "
        f"(not collapsed to 'fix'); got {cmd_warnings!r}"
    )
    # Sanity: the warning must reference the original arch dep target so
    # the reader can locate the missing declaration.
    assert any("server/fix_python.prompt" in w for w in cmd_warnings), (
        "Warning must reference the arch dep target "
        f"'server/fix_python.prompt'; got {cmd_warnings!r}"
    )


def test_f4_validator_flat_layout_still_works(tmp_path: Path) -> None:
    """[F4 regression guard] Flat-layout validator behavior is preserved.

    A flat ``fix_python.prompt`` including ``helper_python.prompt`` with a
    matching arch dep must produce no warnings — path-preserving keys must
    degrade to bare stems when no directory segment is present, otherwise
    flat-layout architectures would regress.

    A second arch dep on ``other_python.prompt`` without a matching
    include/dep tag must still warn (forward direction works as before).

    Asserts the union: aligned deps produce no warnings, missing deps
    still emit warnings with the expected (bare) module key.
    """
    from pdd.architecture_include_validation import (
        cross_validate_architecture_with_prompt_includes,
    )

    project_root = tmp_path / "proj"
    prompts = project_root / "prompts"
    prompts.mkdir(parents=True)

    # Aligned: fix includes helper, arch lists helper as dep.
    (prompts / "fix_python.prompt").write_text(
        "%\n<include>helper_python.prompt</include>\n",
        encoding="utf-8",
    )
    (prompts / "helper_python.prompt").write_text("%\n", encoding="utf-8")

    arch_aligned = [
        {
            "filename": "fix_python.prompt",
            "dependencies": ["helper_python.prompt"],
        },
        {"filename": "helper_python.prompt", "dependencies": []},
    ]
    warnings_aligned = cross_validate_architecture_with_prompt_includes(
        arch_aligned, project_root
    )
    assert warnings_aligned == [], (
        "Flat-layout aligned arch+include must produce no warnings; "
        f"got {warnings_aligned!r}"
    )

    # Forward drift still detected: arch lists other as dep but prompt
    # has no include/tag for it.
    (prompts / "other_python.prompt").write_text("%\n", encoding="utf-8")
    arch_forward_drift = [
        {
            "filename": "fix_python.prompt",
            "dependencies": ["helper_python.prompt", "other_python.prompt"],
        },
        {"filename": "helper_python.prompt", "dependencies": []},
        {"filename": "other_python.prompt", "dependencies": []},
    ]
    warnings_forward_drift = cross_validate_architecture_with_prompt_includes(
        arch_forward_drift, project_root
    )
    assert warnings_forward_drift, (
        "Flat-layout forward drift must still emit a warning; "
        f"got {warnings_forward_drift!r}"
    )
    assert any("'other'" in w or " other " in w for w in warnings_forward_drift), (
        "Flat-layout warning must use the bare module key 'other'; "
        f"got {warnings_forward_drift!r}"
    )


def test_f2_flat_layout_self_include_still_self_skipped(tmp_path: Path) -> None:
    """[F2 regression guard] A true self-include in a flat layout must
    still be self-skipped by ``merge_auto_deps_includes_into_architecture``.

    Without this check, the F2 path-preserving keys could over-correct and
    let a flat ``a_python.prompt`` include itself become a dependency of
    itself. ``_path_preserving_module_key`` degrades to the bare stem when
    no directory segment is present, so flat layouts retain the original
    self-skip behavior.
    """
    from pdd.auto_deps_architecture import merge_auto_deps_includes_into_architecture

    project_root = tmp_path
    (project_root / ".git").mkdir()
    prompts = project_root / "prompts"
    prompts.mkdir()
    self_prompt = prompts / "a_python.prompt"
    self_prompt.write_text("%\n", encoding="utf-8")

    architecture = [
        {"filename": "a_python.prompt", "dependencies": []},
    ]
    arch_path = project_root / "architecture.json"
    arch_path.write_text(json.dumps(architecture, indent=2), encoding="utf-8")

    old = "%\n"
    # Flat-layout self-include — bare stem identical, no directory.
    new = "%\n<include>a_python.prompt</include>\n"

    report = merge_auto_deps_includes_into_architecture(
        project_root, self_prompt, old, new
    )

    # Either updated=False (because the only fresh include is a
    # self-edge) or, if updated=True, the dep must NOT include
    # ``a_python.prompt``.
    if report["updated"]:
        assert "a_python.prompt" not in report["added_dependencies"], (
            "Flat-layout self-include must still be self-skipped; "
            f"got {report['added_dependencies']!r}"
        )
    data = json.loads(arch_path.read_text(encoding="utf-8"))
    entry = data[0]
    assert "a_python.prompt" not in entry["dependencies"], (
        "Flat-layout self-include must not become a self-edge in arch; "
        f"got {entry['dependencies']!r}"
    )


def test_f8_modified_prompts_extractor_returns_only_legitimate_includes():
    """F8 regression: extract_includes_from_file_ordered must not parse documentation
    prose <include> tags as live tags. PR #1073 touched three prompts that contain
    inline <include> examples in docs; the extractor must return ONLY the real
    dependency includes (live tags in the % Dependencies section).

    Follow-up: the PR also touched the architecture/<include> validator, the
    architecture_sync, and the commands/checkup prompts. Both pre-existing and
    newly-added prose <include> mentions in those three prompts must remain
    entity-escaped so the extractor does not absorb live includes nor produce
    garbage matches like ``path.py`` / ``ignored_body.py`` from a regex run
    against documentation prose."""
    import re
    from pathlib import Path
    from pdd.sync_order import extract_includes_from_file_ordered

    repo_root = Path(__file__).resolve().parent.parent
    prompts = [
        repo_root / "pdd" / "prompts" / "agentic_sync_python.prompt",
        repo_root / "pdd" / "prompts" / "auto_deps_architecture_python.prompt",
        repo_root / "pdd" / "prompts" / "agentic_sync_identify_modules_LLM.prompt",
        repo_root / "pdd" / "prompts" / "architecture_include_validation_python.prompt",
        repo_root / "pdd" / "prompts" / "architecture_sync_python.prompt",
        repo_root / "pdd" / "prompts" / "commands" / "checkup_python.prompt",
    ]
    path_re = re.compile(r"^[\w./\-]+$")

    for prompt_path in prompts:
        assert prompt_path.is_file(), f"Missing fixture: {prompt_path}"
        out = extract_includes_from_file_ordered(prompt_path)
        for entry in out:
            assert len(entry) < 500, (
                f"{prompt_path.name}: garbage extracted (len={len(entry)}): "
                f"{entry[:120]!r}"
            )
            assert "\n" not in entry, (
                f"{prompt_path.name}: newline in extracted include {entry!r}"
            )
            assert "</include>" not in entry, (
                f"{prompt_path.name}: </include> in extracted include {entry!r}"
            )
            assert "<" not in entry, (
                f"{prompt_path.name}: '<' in extracted include {entry!r}"
            )
            assert path_re.match(entry), (
                f"{prompt_path.name}: doesn't look like a path: {entry!r}"
            )

    # Spot-check the three prompts the follow-up commit fixed: they must each
    # extract their known live-include shapes — no live include should have
    # been accidentally swallowed by the prose escaping.
    validator_prompt = (
        repo_root / "pdd" / "prompts" / "architecture_include_validation_python.prompt"
    )
    validator_includes = extract_includes_from_file_ordered(validator_prompt)
    assert "context/architecture_sync_example.py" in validator_includes, (
        f"validator prompt lost arch_sync example include: {validator_includes!r}"
    )
    assert "context/architecture_registry_example.py" in validator_includes, (
        f"validator prompt lost arch_registry example include: {validator_includes!r}"
    )

    arch_sync_prompt = (
        repo_root / "pdd" / "prompts" / "architecture_sync_python.prompt"
    )
    arch_sync_includes = extract_includes_from_file_ordered(arch_sync_prompt)
    assert "./context/python_preamble.prompt" in arch_sync_includes, (
        f"arch_sync prompt lost python_preamble include: {arch_sync_includes!r}"
    )

    checkup_prompt = (
        repo_root / "pdd" / "prompts" / "commands" / "checkup_python.prompt"
    )
    checkup_includes = extract_includes_from_file_ordered(checkup_prompt)
    assert "context/agentic_common_example.py" in checkup_includes, (
        f"checkup prompt lost agentic_common example include: {checkup_includes!r}"
    )
    assert "context/python_preamble.prompt" in checkup_includes, (
        f"checkup prompt lost python_preamble include: {checkup_includes!r}"
    )


def test_f7_validator_bare_pdd_dep_resolves_to_path_qualified_arch_entry(tmp_path):
    """F7 regression: a bare <pdd-dependency>fix_python.prompt</pdd-dependency>
    declaration must resolve to the unambiguous path-qualified arch entry
    (e.g. server/fix_python.prompt) — the validator must NOT warn that the
    declaration is missing."""
    from pdd.architecture_include_validation import (
        cross_validate_architecture_with_prompt_includes,
    )

    prompts = tmp_path / "prompts"
    (prompts / "server").mkdir(parents=True)

    # commands/cli_python.prompt declares a bare <pdd-dependency>fix_python.prompt</pdd-dependency>
    (prompts / "commands").mkdir(parents=True)
    cli_path = prompts / "commands" / "cli_python.prompt"
    cli_path.write_text(
        "<pdd-dependency>fix_python.prompt</pdd-dependency>\nsome prompt body\n"
    )

    # server/fix_python.prompt exists as the only fix entry in arch (no flat fix)
    fix_path = prompts / "server" / "fix_python.prompt"
    fix_path.write_text("server fix prompt\n")

    arch_data = [
        {
            "filename": "commands/cli_python.prompt",
            "dependencies": ["server/fix_python.prompt"],
        },
        {"filename": "server/fix_python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(
        arch_data, tmp_path
    )
    # Filter to only warnings about commands/cli — others are unrelated noise
    cli_warnings = [w for w in warnings if "commands/cli" in w or "cli_python.prompt" in w]
    assert cli_warnings == [], (
        f"F7: bare <pdd-dependency>fix_python.prompt</pdd-dependency> should resolve "
        f"to the unambiguous server/fix_python.prompt arch entry, but validator "
        f"warned: {cli_warnings!r}"
    )


def test_f7_validator_warns_on_truly_ambiguous_bare_pdd_dep(tmp_path):
    """F7 mirror: when bare <pdd-dependency>fix_python.prompt</pdd-dependency> could
    match multiple arch entries (commands/fix AND server/fix), validator must NOT
    silently treat them as matched — it should warn about the missing declaration
    (the arch dep can't be unambiguously resolved against the bare name)."""
    from pdd.architecture_include_validation import (
        cross_validate_architecture_with_prompt_includes,
    )

    prompts = tmp_path / "prompts"
    (prompts / "commands").mkdir(parents=True)
    (prompts / "server").mkdir(parents=True)
    (prompts / "other").mkdir(parents=True)

    # other/cli_python.prompt has a bare <pdd-dependency>fix_python.prompt</pdd-dependency>
    cli_path = prompts / "other" / "cli_python.prompt"
    cli_path.write_text(
        "<pdd-dependency>fix_python.prompt</pdd-dependency>\nbody\n"
    )

    (prompts / "commands" / "fix_python.prompt").write_text("c fix\n")
    (prompts / "server" / "fix_python.prompt").write_text("s fix\n")

    arch_data = [
        {
            "filename": "other/cli_python.prompt",
            "dependencies": ["server/fix_python.prompt"],
        },
        {"filename": "commands/fix_python.prompt", "dependencies": []},
        {"filename": "server/fix_python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(
        arch_data, tmp_path
    )
    # The bare dep is ambiguous (could be commands/fix OR server/fix), so it should
    # NOT resolve to either; validator should warn that other/cli arch lists
    # server/fix as a dep but the prompt does not declare it.
    cli_warnings = [
        w for w in warnings
        if "other/cli" in w or w.startswith("other/cli_python.prompt")
    ]
    assert any("server/fix" in w or "server" in w for w in cli_warnings), (
        f"F7: ambiguous bare <pdd-dependency> should NOT silently match a "
        f"specific path-qualified arch entry; validator should warn. Got: {cli_warnings!r}"
    )


def test_f10_graph_builder_resolves_bare_dep_to_path_qualified_arch_entry():
    """F10 regression: a stale/hand-edited arch.json with dependencies
    ['fix_python.prompt'] (bare) when the actual entry is
    'server/fix_python.prompt' must NOT be dropped from the sync graph as
    an orphan. The graph builder must use the same normalization as the
    validator so both agree on the canonical filename."""
    from pdd.agentic_sync_runner import build_dep_graph_from_architecture_data

    architecture = [
        {
            "filename": "commands/cli_python.prompt",
            "dependencies": ["fix_python.prompt"],  # BARE, not server/fix_python.prompt
        },
        {"filename": "server/fix_python.prompt", "dependencies": []},
    ]
    targets = ["commands/cli", "server/fix"]
    result = build_dep_graph_from_architecture_data(
        architecture, targets, source_name="test_f10"
    )
    # Edge from commands/cli to server/fix must be present after normalization
    # (without F10, bare 'fix_python.prompt' would be reported as orphan).
    assert result.graph.get("commands/cli") == ["server/fix"], (
        f"F10: bare arch dep should resolve to unambiguous path-qualified entry; "
        f"got graph={result.graph!r} warnings={result.warnings!r}"
    )
    orphan_warnings = [w for w in result.warnings if "orphan" in w.lower()]
    assert orphan_warnings == [], (
        f"F10: bare dep should not be reported as orphan when unambiguous; "
        f"got warnings: {orphan_warnings!r}"
    )


def test_f10_graph_builder_warns_on_truly_ambiguous_bare_dep():
    """F10 mirror: when the bare dep could match multiple path-qualified arch
    entries, the graph builder must NOT silently pick one — it should report
    the orphan/ambiguous edge."""
    from pdd.agentic_sync_runner import build_dep_graph_from_architecture_data

    architecture = [
        {
            "filename": "other/cli_python.prompt",
            "dependencies": ["fix_python.prompt"],
        },
        {"filename": "commands/fix_python.prompt", "dependencies": []},
        {"filename": "server/fix_python.prompt", "dependencies": []},
    ]
    targets = ["other/cli", "commands/fix", "server/fix"]
    result = build_dep_graph_from_architecture_data(
        architecture, targets, source_name="test_f10_ambig"
    )
    # The bare dep is ambiguous — must NOT silently match either entry.
    # The edge should not bridge to commands/fix OR server/fix.
    assert result.graph.get("other/cli") == [], (
        f"F10: ambiguous bare dep must not silently match a specific entry; "
        f"got graph={result.graph!r}"
    )


def test_f11_dependency_resolver_built_once_for_validation_run(mocker):
    """F11 perf regression: cross_validate_architecture_with_prompt_includes must
    build the dependency resolver ONCE per call, not once per arch entry. With
    N entries the validator should call build_dependency_resolver exactly once,
    not N times."""
    from pdd.architecture_include_validation import (
        cross_validate_architecture_with_prompt_includes,
    )
    import pdd.architecture_include_validation as mod

    # Spy on the import-site reference
    original = mod.cross_validate_architecture_with_prompt_includes
    call_count = {"build_dependency_resolver": 0}

    import pdd.architecture_sync as arch_sync
    real_builder = arch_sync.build_dependency_resolver

    def counting_builder(arch_data):
        call_count["build_dependency_resolver"] += 1
        return real_builder(arch_data)

    mocker.patch.object(arch_sync, "build_dependency_resolver", counting_builder)

    arch_data = [
        {"filename": f"mod_{i}_python.prompt", "dependencies": []}
        for i in range(20)
    ]
    # Even with 20 entries, the resolver should be built only once.
    cross_validate_architecture_with_prompt_includes(
        arch_data, Path("/tmp/nonexistent-project-root-for-f11-test")
    )
    assert call_count["build_dependency_resolver"] == 1, (
        f"F11: expected exactly 1 call to build_dependency_resolver per validation "
        f"run; got {call_count['build_dependency_resolver']}"
    )
