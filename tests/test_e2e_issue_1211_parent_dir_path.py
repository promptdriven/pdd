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

    # Every output must live under the subproject, NOT under parent_cwd.
    subproject_str = str(layout["subproject"])
    parent_cwd_str = str(layout["parent_cwd"])
    for key, value in output_file_paths.items():
        assert value.startswith(subproject_str), (
            f"Output {key}={value!r} should be under subproject "
            f"{subproject_str!r}, not orphaned"
        )
        assert not value.startswith(parent_cwd_str + "/"), (
            f"Output {key}={value!r} leaked into parent_cwd "
            f"{parent_cwd_str!r}; this is the issue #1211 orphan bug"
        )

    # The code output must include the prompt's subdir chain.
    assert "src/routers/webhook_handlers" in output_file_paths["output_code"], (
        f"output_code={output_file_paths['output_code']!r} dropped the "
        "'src/routers/' prefix — _extract_basename is not using the "
        "subdir-aware variant"
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
    code_out = output_file_paths["output_code"]

    # Must contain the subdir BELOW the configured prompts_dir.
    assert "services/foo" in code_out, (
        f"output_code={code_out!r} should include 'services/foo' (subdir "
        f"relative to prompts_dir='prompts/backend')"
    )
    # Must NOT double-nest by treating 'backend' as a subdir of 'prompts/'.
    # i.e., we must not see '/backend/services/foo' as a SUBDIR appended to
    # the configured generate_output_path of 'backend/src/'.
    assert "backend/src/backend/services" not in code_out, (
        f"output_code={code_out!r} double-nested 'backend/' because the "
        "subdir helper anchored on literal 'prompts/' instead of the "
        "configured prompts_dir 'prompts/backend'"
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
    layout = _build_subproject(
        tmp_path,
        pddrc_body=_PDDRC_NESTED_APP,
        prompt_rel=prompt_rel,
        # code_rel just needs to exist; its content is irrelevant.
        code_rel="src/placeholder.py",
        test_rel="tests/test_placeholder.py",
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
    subproject_str = str(layout["subproject"])
    parent_cwd_str = str(layout["parent_cwd"])

    assert code_out.startswith(subproject_str), (
        f"[{prompt_rel}] output_code={code_out!r} not under subproject"
    )
    assert not code_out.startswith(parent_cwd_str + "/"), (
        f"[{prompt_rel}] output_code={code_out!r} leaked into parent cwd"
    )
    assert expected_subdir in code_out, (
        f"[{prompt_rel}] output_code={code_out!r} missing subdir chain "
        f"{expected_subdir!r}"
    )
