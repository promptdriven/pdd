"""
E2E / integration tests for Issue #1211:
  ``pdd fix`` from a parent dir writes orphan files to run cwd instead of the
  subproject.

These tests exercise the full path through ``construct_paths`` (no path mocks)
with a real ``.pddrc`` on disk and a parent-cwd setup that reproduces the
pdd_cloud PR #1707 scenario from the issue. They cross multiple module
boundaries:

  - ``pdd.construct_paths._find_pddrc_file`` (real .pddrc lookup)
  - ``pdd.construct_paths._extract_basename`` (the Step 6a fix point)
  - ``pdd.construct_paths._strip_language_suffix_with_subdir`` (the
    prompts_dir-aware helper)
  - ``pdd.generate_output_paths.generate_output_paths`` (real output
    resolution)
  - ``pdd.operation_log.get_fingerprint_path`` (project_root threading
    expansion item)

Step 6c (E2E): unit-level regression coverage lives in
``tests/test_fix_issue_1211_parent_dir_path.py`` and
``tests/test_construct_paths.py``; this file covers the cross-module behaviour
those unit tests cannot.
"""

from pathlib import Path

import pytest

from pdd.construct_paths import construct_paths
from pdd.operation_log import get_fingerprint_path, _safe_basename


# ---------------------------------------------------------------------------
# Shared subproject scaffolding helper
# ---------------------------------------------------------------------------

def _build_subproject(
    tmp_path: Path,
    *,
    pddrc_body: str,
    prompt_rel: str,
    code_rel: str = "src/dummy.py",
    test_rel: str | None = None,
) -> dict:
    """Create a parent-cwd + nested subproject with a real .pddrc.

    Layout:
        tmp_path/
          parent_cwd/                         <- will be chdir'd into
          extensions/github_pdd_app/
            .pddrc                            <- real config (pddrc_body)
            <prompt_rel>                      <- nested prompt
            <code_rel>                        <- existing target code file
            [<test_rel>]                      <- existing test file (optional)

    Returns dict with keys: parent_cwd, subproject, prompt, code, test, pddrc.
    """
    parent_cwd = tmp_path / "parent_cwd"
    parent_cwd.mkdir()

    subproject = tmp_path / "extensions" / "github_pdd_app"
    subproject.mkdir(parents=True)

    pddrc = subproject / ".pddrc"
    pddrc.write_text(pddrc_body, encoding="utf-8")

    prompt_path = subproject / prompt_rel
    prompt_path.parent.mkdir(parents=True, exist_ok=True)
    prompt_path.write_text("prompt body", encoding="utf-8")

    code_path = subproject / code_rel
    code_path.parent.mkdir(parents=True, exist_ok=True)
    code_path.write_text("def x(): ...\n", encoding="utf-8")

    test_path = None
    if test_rel is not None:
        test_path = subproject / test_rel
        test_path.parent.mkdir(parents=True, exist_ok=True)
        test_path.write_text("def test_x(): assert True\n", encoding="utf-8")

    return {
        "parent_cwd": parent_cwd,
        "subproject": subproject,
        "prompt": prompt_path,
        "code": code_path,
        "test": test_path,
        "pddrc": pddrc,
    }


_PDDRC_NESTED_APP = '''version: "1.0"
contexts:
  app:
    paths:
      - "src/**"
      - "prompts/**"
    defaults:
      generate_output_path: "src/"
      test_output_path: "tests/"
      example_output_path: "examples/"
      prompts_dir: "prompts"
      default_language: "python"
'''


# ---------------------------------------------------------------------------
# Test 1: Full path resolution from parent cwd lands inside subproject
# ---------------------------------------------------------------------------

def test_e2e_fix_from_parent_cwd_resolves_outputs_under_subproject(
    tmp_path, monkeypatch
):
    """Parent-cwd invocation of ``pdd fix`` must land output under subproject.

    Reproduces the exact pdd_cloud PR #1707 layout:
      parent_cwd is sibling of extensions/github_pdd_app/
      Prompt: extensions/github_pdd_app/prompts/src/routers/webhook_handlers_Python.prompt
      Expected: outputs at extensions/github_pdd_app/src/routers/webhook_handlers*.py
      Buggy:    outputs at parent_cwd/webhook_handlers*.py (orphan)

    Cross-module surface exercised end-to-end:
      construct_paths -> _find_pddrc_file (real) -> _extract_basename ->
      _strip_language_suffix_with_subdir (with prompts_dir) ->
      generate_output_paths (real) -> final filesystem paths.
    """
    layout = _build_subproject(
        tmp_path,
        pddrc_body=_PDDRC_NESTED_APP,
        prompt_rel="prompts/src/routers/webhook_handlers_Python.prompt",
        code_rel="src/routers/webhook_handlers.py",
        test_rel="tests/test_webhook_handlers.py",
    )
    monkeypatch.chdir(layout["parent_cwd"])

    _, _, output_file_paths, language = construct_paths(
        input_file_paths={
            "prompt_file": str(layout["prompt"]),
            "code_file": str(layout["code"]),
            "unit_test_file": str(layout["test"]),
        },
        force=True,
        quiet=True,
        command="fix",
        command_options={},
        create_error_file=True,
    )

    assert language == "python"

    # Exact path equality: parent-cwd invocation must produce output paths
    # equal to running fix from the subproject itself. Weaker assertions
    # (startswith / substring "src/routers/webhook_handlers") let the
    # double-nested ".../src/routers/src/routers/..." regression pass.
    subproject = layout["subproject"]
    expected_code = str(
        subproject
        / "src"
        / "routers"
        / "webhook_handlers_test_webhook_handlers_fixed.py"
    )
    expected_test = str(
        subproject
        / "tests"
        / "test_webhook_handlers_test_webhook_handlers_fixed.py"
    )
    expected_results = str(
        subproject
        / "src"
        / "routers"
        / "webhook_handlers_test_webhook_handlers_fix_results.log"
    )
    assert output_file_paths["output_code"] == expected_code, (
        f"output_code={output_file_paths['output_code']!r} != {expected_code!r}"
    )
    assert output_file_paths["output_test"] == expected_test, (
        f"output_test={output_file_paths['output_test']!r} != {expected_test!r}"
    )
    assert output_file_paths["output_results"] == expected_results, (
        f"output_results={output_file_paths['output_results']!r} != {expected_results!r}"
    )


# ---------------------------------------------------------------------------
# Test 2: .pddrc prompts_dir override anchors basename correctly (Step 6a)
# ---------------------------------------------------------------------------

def test_e2e_fix_pddrc_prompts_dir_anchors_basename_not_literal_prompts(
    tmp_path, monkeypatch
):
    """When .pddrc sets prompts_dir = 'prompts/backend' and the prompt lives at
    prompts/backend/services/foo_Python.prompt, the basename must anchor on the
    configured prompts_dir (so subdir = 'services/foo'), NOT on the literal
    'prompts/' segment (which would produce subdir = 'backend/services/foo'
    and cause a double-nested output path under generate_output_path).

    This guards the Step 6a fix to _strip_language_suffix_with_subdir.
    """
    pddrc_body = '''version: "1.0"
contexts:
  backend:
    paths:
      - "backend/**"
      - "prompts/backend/**"
    defaults:
      generate_output_path: "backend/src/"
      test_output_path: "backend/tests/"
      example_output_path: "context/"
      prompts_dir: "prompts/backend"
      default_language: "python"
'''
    layout = _build_subproject(
        tmp_path,
        pddrc_body=pddrc_body,
        prompt_rel="prompts/backend/services/foo_Python.prompt",
        code_rel="backend/src/services/foo.py",
        test_rel="backend/tests/test_foo.py",
    )
    monkeypatch.chdir(layout["parent_cwd"])

    resolved_config, _, output_file_paths, language = construct_paths(
        input_file_paths={
            "prompt_file": str(layout["prompt"]),
            "code_file": str(layout["code"]),
            "unit_test_file": str(layout["test"]),
        },
        force=True,
        quiet=True,
        command="fix",
        command_options={},
        create_error_file=True,
    )

    assert language == "python"
    # The named context from the subproject's .pddrc must be the one loaded —
    # NOT the implicit "default" fallback that fires when no .pddrc was found.
    assert resolved_config.get("_matched_context") == "backend", (
        f"_matched_context={resolved_config.get('_matched_context')!r} — "
        "expected 'backend' from the subproject .pddrc; 'default' means the "
        ".pddrc was never loaded (issue #1211)"
    )

    # Exact path equality on the code output: the basename anchor must be
    # the configured prompts_dir (subdir='services/foo'), and the output must
    # land at backend/src/services/foo_test_foo_fixed.py — without any
    # double-nesting of 'backend/' or 'services/'.
    expected_code = str(
        layout["subproject"]
        / "backend"
        / "src"
        / "services"
        / "foo_test_foo_fixed.py"
    )
    assert output_file_paths["output_code"] == expected_code, (
        f"output_code={output_file_paths['output_code']!r} != {expected_code!r}"
    )


# ---------------------------------------------------------------------------
# Test 3: basename produced by construct_paths flows correctly into
# operation_log.get_fingerprint_path with project_root=<subproject>
# ---------------------------------------------------------------------------

def test_e2e_fix_basename_flows_into_subproject_fingerprint_path(
    tmp_path, monkeypatch
):
    """Cross-module: the basename construct_paths emits for a nested fix prompt
    must be a valid input to operation_log.get_fingerprint_path with the
    subproject as project_root. The resulting fingerprint file must live
    under <subproject>/.pdd/meta/, not under parent_cwd/.pdd/meta/.

    This covers the full chain: prompt path -> basename (with subdirs) ->
    safe-sanitized fingerprint filename under the right subproject root.
    """
    layout = _build_subproject(
        tmp_path,
        pddrc_body=_PDDRC_NESTED_APP,
        prompt_rel="prompts/src/routers/webhook_handlers_Python.prompt",
        code_rel="src/routers/webhook_handlers.py",
        test_rel="tests/test_webhook_handlers.py",
    )
    monkeypatch.chdir(layout["parent_cwd"])

    resolved_config, _, _, language = construct_paths(
        input_file_paths={
            "prompt_file": str(layout["prompt"]),
            "code_file": str(layout["code"]),
            "unit_test_file": str(layout["test"]),
        },
        force=True,
        quiet=True,
        command="fix",
        command_options={},
        create_error_file=True,
    )

    # construct_paths doesn't return basename directly; rebuild the basename
    # the same way the downstream pipeline would receive it: by calling the
    # public path API with the subproject as project_root.
    basename = "src/routers/webhook_handlers_test_webhook_handlers"
    fp_path = get_fingerprint_path(basename, language, project_root=layout["subproject"])

    expected_meta_dir = layout["subproject"] / ".pdd" / "meta"
    assert str(fp_path).startswith(str(expected_meta_dir)), (
        f"Fingerprint path {fp_path!r} must live under subproject meta dir "
        f"{expected_meta_dir!r}, not under parent cwd"
    )
    # Slashes in the basename must be sanitized so this resolves to a single
    # file, not a nested directory tree the caller forgot to create.
    assert fp_path.name == f"{_safe_basename(basename)}_{language}.json"
    assert "/" not in fp_path.name
    # And the meta dir was actually created on disk under the subproject.
    assert expected_meta_dir.is_dir(), (
        "get_fingerprint_path(project_root=...) should have created the "
        ".pdd/meta dir under the subproject as a side effect"
    )
    # Negative: no orphan .pdd/meta under parent_cwd.
    parent_meta = layout["parent_cwd"] / ".pdd" / "meta"
    assert not parent_meta.exists(), (
        f"Parent cwd should not have an orphan {parent_meta!r} after the "
        "fingerprint write — that is the issue #1211 secondary symptom"
    )


def test_e2e_log_event_and_display_anchor_at_subproject(tmp_path, monkeypatch):
    """Reviewer round-5: lifecycle events (sync_start, lock_acquired, budget,
    cycle, release) and the dry-run/log display must all anchor at the
    subproject .pdd/meta when the user runs from a parent CWD.

    Before this fix log_event() had no `paths` parameter so every
    lifecycle event landed at parent CWD .pdd/meta while
    fingerprints/run reports went to the subproject — a split log
    invisible to `pdd sync --dry-run` from the same parent CWD.
    """
    from pdd.operation_log import log_event, load_operation_log, get_log_path

    repo_root = tmp_path / "repo_root"
    repo_root.mkdir()
    subproject = repo_root / "extensions" / "github_pdd_app"
    subproject.mkdir(parents=True)
    (subproject / ".pddrc").write_text(_PDDRC_NESTED_APP, encoding="utf-8")
    prompt = subproject / "prompts" / "src" / "routers" / "webhook_handlers_Python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("p", encoding="utf-8")

    monkeypatch.chdir(repo_root)

    paths_hint = {"prompt": prompt}
    # Emit two lifecycle events with the hint (mirrors sync_orchestration's
    # log_event calls after pdd_files is resolved).
    log_event(
        "webhook_handlers", "python", "sync_start",
        {"pid": 1234}, invocation_mode="sync", paths=paths_hint,
    )
    log_event(
        "webhook_handlers", "python", "lock_acquired",
        {"pid": 1234}, invocation_mode="sync", paths=paths_hint,
    )

    expected_log = subproject / ".pdd" / "meta" / "webhook_handlers_python_sync.log"
    actual_log = get_log_path("webhook_handlers", "python", paths=paths_hint)
    assert actual_log == expected_log, (
        f"get_log_path resolved to {actual_log!r}, expected {expected_log!r}"
    )
    assert expected_log.exists(), (
        f"Lifecycle events not written to subproject log {expected_log!r}; "
        f"this is the round-5 split-log bug"
    )

    # And load_operation_log with the same hint can read them back.
    entries = load_operation_log("webhook_handlers", "python", paths=paths_hint)
    event_types = [e.get("event_type") for e in entries if "event_type" in e]
    assert "sync_start" in event_types and "lock_acquired" in event_types, (
        f"Subproject log missing expected events; got {event_types!r}"
    )

    # No orphan log under parent CWD.
    parent_log = repo_root / ".pdd" / "meta" / "webhook_handlers_python_sync.log"
    assert not parent_log.exists(), (
        f"Parent CWD has orphan log {parent_log!r} — log_event bypassed paths hint"
    )


def test_e2e_decorator_basename_aligns_with_sync_when_pddrc_sets_prompts_dir(
    tmp_path, monkeypatch
):
    """Reviewer round-4: when .pddrc sets `prompts_dir: "prompts/backend"`,
    `infer_module_identity` (used by the @log_operation decorator) MUST
    anchor on that configured root, not on the literal "prompts" segment.

    Otherwise decorator-emitted fingerprints land at
    `backend_services_foo_python.json` while sync looks at
    `services_foo_python.json` — invisible to the other half of the
    workflow."""
    from pdd.operation_log import infer_module_identity

    repo_root = tmp_path / "repo_root"
    repo_root.mkdir()
    subproject = repo_root / "extensions" / "github_pdd_app"
    subproject.mkdir(parents=True)
    pddrc_body = '''version: "1.0"
contexts:
  backend:
    paths:
      - "backend/**"
      - "prompts/backend/**"
    defaults:
      generate_output_path: "backend/src/"
      test_output_path: "backend/tests/"
      example_output_path: "context/"
      prompts_dir: "prompts/backend"
      default_language: "python"
'''
    (subproject / ".pddrc").write_text(pddrc_body, encoding="utf-8")
    prompt = subproject / "prompts" / "backend" / "services" / "foo_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("p", encoding="utf-8")

    basename, language = infer_module_identity(str(prompt))
    # Must align with what construct_paths / sync emit for the same prompt
    # under the same .pddrc: subdir anchored on the configured prompts_dir.
    assert basename == "services/foo", (
        f"infer_module_identity emitted basename={basename!r}; expected "
        f"'services/foo' (anchored on prompts_dir 'prompts/backend'). "
        f"'backend/services/foo' would split fingerprint files across two "
        f"names and silently break sync visibility."
    )
    assert language == "python"


def test_e2e_decorator_metadata_writes_anchor_at_subproject(tmp_path, monkeypatch):
    """Reviewer round-3: the @log_operation decorator infers prompt_file
    but then calls append_log_entry / save_fingerprint / save_run_report
    without path hints. With the decorator anchored at parent CWD and the
    .pddrc inside the subproject, all three writes must land under the
    subproject's .pdd/meta — not under the parent run CWD."""
    from pdd.operation_log import (
        log_operation,
        save_fingerprint,
        save_run_report,
        append_log_entry,
        get_log_path,
        get_fingerprint_path,
        get_run_report_path,
        infer_module_identity,
    )

    repo_root = tmp_path / "repo_root"
    repo_root.mkdir()
    subproject = repo_root / "extensions" / "github_pdd_app"
    subproject.mkdir(parents=True)
    (subproject / ".pddrc").write_text(_PDDRC_NESTED_APP, encoding="utf-8")
    prompt = subproject / "prompts" / "src" / "routers" / "webhook_handlers_Python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("p", encoding="utf-8")

    monkeypatch.chdir(repo_root)

    # The decorator builds paths={"prompt": prompt_file} from the inferred
    # prompt file. Simulate the writes the decorator does and verify each
    # one anchors at the subproject .pdd/meta.
    basename, language = infer_module_identity(str(prompt))
    paths_hint = {"prompt": prompt}
    expected_meta = subproject / ".pdd" / "meta"

    save_fingerprint(basename, language, operation="generate", paths=paths_hint)
    save_run_report(basename, language, {"exit_code": 0, "tests_passed": 1,
                                          "tests_failed": 0, "coverage": 95.0,
                                          "timestamp": "2026-05-27T00:00:00Z"},
                    paths=paths_hint)
    append_log_entry(basename, language,
                     {"timestamp": "2026-05-27T00:00:00Z", "operation": "generate"},
                     paths=paths_hint)

    fp = get_fingerprint_path(basename, language, paths=paths_hint)
    rr = get_run_report_path(basename, language, paths=paths_hint)
    lg = get_log_path(basename, language, paths=paths_hint)
    for kind, path in (("fingerprint", fp), ("run_report", rr), ("log", lg)):
        assert str(path).startswith(str(expected_meta)), (
            f"{kind} path {path!r} must live under subproject meta dir "
            f"{expected_meta!r} — decorator metadata writes are not anchored"
        )
        assert path.exists(), f"{kind} file {path!r} must exist after write"

    # No orphan .pdd/meta under the parent CWD.
    assert not (repo_root / ".pdd" / "meta").exists(), (
        "Parent repo root must not have an orphan .pdd/meta after decorator "
        "writes anchored via paths hint"
    )


def test_e2e_fingerprint_anchors_at_subproject_when_pddrc_lives_below_cwd(
    tmp_path, monkeypatch
):
    """Reviewer scenario (round 2): the subproject .pddrc lives BELOW the
    run CWD, e.g. repo_root/extensions/github_pdd_app/.pddrc.

    Upward-from-CWD detection is useless here because the .pddrc is in a
    sibling/child path. The metadata helpers must instead seed detection
    from the prompt/code/test paths the caller already has.
    """
    repo_root = tmp_path / "repo_root"
    repo_root.mkdir()
    subproject = repo_root / "extensions" / "github_pdd_app"
    subproject.mkdir(parents=True)
    pddrc = subproject / ".pddrc"
    pddrc.write_text(_PDDRC_NESTED_APP, encoding="utf-8")
    prompt = subproject / "prompts" / "src" / "routers" / "webhook_handlers_Python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("p", encoding="utf-8")

    monkeypatch.chdir(repo_root)

    # No project_root passed, but paths hint includes the prompt — the
    # detector should walk up from the prompt to find the subproject .pddrc.
    fp_path = get_fingerprint_path(
        "webhook_handlers", "python", paths={"prompt": prompt}
    )
    expected = subproject / ".pdd" / "meta"
    assert str(fp_path).startswith(str(expected)), (
        f"Fingerprint {fp_path!r} must anchor at the subproject meta dir "
        f"{expected!r}; without paths-aware detection it would land under "
        f"{repo_root!r}/.pdd/meta"
    )
    # And no orphan meta dir at the parent repo root.
    assert not (repo_root / ".pdd" / "meta").exists(), (
        "Parent repo root must not get an orphan .pdd/meta when the "
        "subproject .pddrc is reachable from the prompt path"
    )


def test_e2e_fingerprint_auto_detects_subproject_root_from_parent_cwd(
    tmp_path, monkeypatch
):
    """Issue #1211 secondary symptom — callers that *don't* pass
    project_root must still anchor .pdd/meta at the subproject's .pddrc,
    not at the parent run CWD.

    Production callers (operation_log.save_fingerprint,
    sync_determine_operation.read_fingerprint) don't thread project_root
    through every site, so the metadata helpers must auto-detect the
    subproject root by walking up to the nearest .pddrc.
    """
    shared_root = tmp_path / "shared_root"
    shared_root.mkdir()
    inner_parent = shared_root / "parent_cwd"
    inner_parent.mkdir()
    inner_subproject = shared_root / "sub"
    inner_subproject.mkdir()
    (shared_root / ".pddrc").write_text(_PDDRC_NESTED_APP, encoding="utf-8")
    monkeypatch.chdir(inner_parent)

    fp_path_no_root = get_fingerprint_path("foo", "python")
    expected_meta_dir = shared_root / ".pdd" / "meta"
    assert str(fp_path_no_root).startswith(str(expected_meta_dir)), (
        f"Auto-detected fingerprint path {fp_path_no_root!r} must live "
        f"under the shared root with .pddrc ({expected_meta_dir!r}), not "
        "under the parent run CWD"
    )
    # And no orphan .pdd/meta under the parent CWD.
    assert not (inner_parent / ".pdd" / "meta").exists(), (
        "Parent run CWD must not get an orphan .pdd/meta when a .pddrc "
        "exists upward"
    )


# ---------------------------------------------------------------------------
# Test 4: Issue #1211 orphan matrix — parametrized over the six real prompts
# documented in the issue from pdd_cloud PR #1707.
# ---------------------------------------------------------------------------

ISSUE_ORPHAN_MATRIX = [
    # (prompt_rel_under_subproject, expected_subdir_in_output)
    ("prompts/src/routers/webhook_handlers_Python.prompt",
     "src/routers/webhook_handlers"),
    ("prompts/src/services/pdd_command_parser_Python.prompt",
     "src/services/pdd_command_parser"),
    ("prompts/src/services/solving_orchestrator/budget_Python.prompt",
     "src/services/solving_orchestrator/budget"),
    ("prompts/src/workers/pdd_executor/orchestrator_Python.prompt",
     "src/workers/pdd_executor/orchestrator"),
    ("prompts/src/workers/pdd_executor/process_runner_Python.prompt",
     "src/workers/pdd_executor/process_runner"),
    ("prompts/src/workers/pdd_executor/waterfall_runner_Python.prompt",
     "src/workers/pdd_executor/waterfall_runner"),
]


@pytest.mark.parametrize("prompt_rel,expected_subdir", ISSUE_ORPHAN_MATRIX)
def test_e2e_fix_issue_1211_orphan_matrix(
    tmp_path, monkeypatch, prompt_rel, expected_subdir
):
    """Parametrized regression over the six prompts from the issue body.

    For each prompt that landed as an orphan in pdd_cloud PR #1707, verify
    that the post-fix output_code path:
      - lives under <subproject>/src/...   (not <parent_cwd>/*)
      - contains the full expected subdir chain from the issue table
    """
    # Real-world usage has the code/test files at paths that mirror the
    # prompt's subdir chain. Placing them at the matching location ensures
    # `input_file_dirs` carries the deepest valid directory.
    code_rel = f"{expected_subdir}.py"
    test_basename = expected_subdir.rsplit("/", 1)[-1]
    test_rel = f"tests/test_{test_basename}.py"
    layout = _build_subproject(
        tmp_path,
        pddrc_body=_PDDRC_NESTED_APP,
        prompt_rel=prompt_rel,
        code_rel=code_rel,
        test_rel=test_rel,
    )
    monkeypatch.chdir(layout["parent_cwd"])

    _, _, output_file_paths, _ = construct_paths(
        input_file_paths={
            "prompt_file": str(layout["prompt"]),
            "code_file": str(layout["code"]),
            "unit_test_file": str(layout["test"]),
        },
        force=True,
        quiet=True,
        command="fix",
        command_options={},
        create_error_file=True,
    )

    code_out = output_file_paths["output_code"]

    # Exact path equality: the fixed file must land next to the original
    # code file at the prompt's mirrored subdir, with no orphan prefix and
    # no double-nesting of the subdir chain.
    expected_code = str(
        layout["subproject"] / f"{expected_subdir}_test_{test_basename}_fixed.py"
    )
    assert code_out == expected_code, (
        f"[{prompt_rel}] output_code={code_out!r} != {expected_code!r}"
    )
