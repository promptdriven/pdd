"""Regression + integration tests for issue #1237.

Locks in the prompt-contract fix that lets `pdd sync fix_error_loop` pass
strict preflight: `pdd/prompts/fix_error_loop_python.prompt` must include
source context for the existing public symbols it declares
(`cloud_fix_errors`, `fix_error_loop`).

The unit-style tests check the live repo state. The integration tests
exercise the cross-module flow agentic_sync -> architecture_include_validation
end-to-end against a tmp git repo so the strict-mode trigger
(`_prompt_contract_strict_self_context_required`) runs for real.
"""
from __future__ import annotations

import ast
import json
import re
import shutil
import subprocess
from pathlib import Path

import pytest

from pdd.agentic_sync import (
    _format_prompt_contract_preflight_error,
    _prompt_contract_errors_for_module,
    _prompt_contract_strict_self_context_required,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
PROMPT_PATH = REPO_ROOT / "pdd" / "prompts" / "fix_error_loop_python.prompt"
MODULE_PATH = REPO_ROOT / "pdd" / "fix_error_loop.py"


def _git(repo: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=repo,
        capture_output=True,
        text=True,
        check=True,
    )


def _seed_fix_error_loop_repo(tmp_path: Path) -> Path:
    """Create a tmp git repo mirroring the fix_error_loop sync target.

    Copies the real prompt + module into a fresh repo with an
    architecture.json entry shaped like the live one, commits an initial
    state, and then leaves the prompt as an uncommitted modification so
    `_prompt_contract_strict_self_context_required` returns True.
    """
    repo = tmp_path / "repo"
    (repo / "prompts").mkdir(parents=True)
    (repo / "pdd").mkdir(parents=True)

    shutil.copy(MODULE_PATH, repo / "pdd" / "fix_error_loop.py")
    shutil.copy(
        PROMPT_PATH, repo / "prompts" / "fix_error_loop_python.prompt"
    )

    arch_entry = {
        "filename": "fix_error_loop_python.prompt",
        "filepath": "pdd/fix_error_loop.py",
        "dependencies": [],
        "interface": {
            "type": "module",
            "module": {
                "functions": [
                    {
                        "name": "cloud_fix_errors",
                        "signature": "(...)",
                        "returns": "tuple",
                    },
                    {
                        "name": "fix_error_loop",
                        "signature": "(...)",
                        "returns": "None",
                    },
                ]
            },
        },
    }
    (repo / "architecture.json").write_text(
        json.dumps([arch_entry]), encoding="utf-8"
    )

    _git(repo, "init", "-q", "-b", "main")
    _git(repo, "config", "user.email", "test@example.com")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "seed")

    prompt = repo / "prompts" / "fix_error_loop_python.prompt"
    prompt.write_text(
        prompt.read_text(encoding="utf-8") + "\n<!-- touched -->\n",
        encoding="utf-8",
    )
    return repo


def test_fix_error_loop_prompt_self_includes_module_source() -> None:
    """Prompt must carry source context for its declared public symbols.

    Either a full `<include>pdd/fix_error_loop.py</include>` or per-symbol
    `<include select="def:...">pdd/fix_error_loop.py</include>` lines
    satisfy strict preflight. A revert that drops both would regress #1237.
    """
    assert PROMPT_PATH.is_file(), f"missing prompt: {PROMPT_PATH}"
    text = PROMPT_PATH.read_text(encoding="utf-8")

    full_include = "<include>pdd/fix_error_loop.py</include>" in text
    has_cloud_select = (
        '<include select="def:cloud_fix_errors">pdd/fix_error_loop.py</include>'
        in text
    )
    has_loop_select = (
        '<include select="def:fix_error_loop">pdd/fix_error_loop.py</include>'
        in text
    )

    assert full_include or (has_cloud_select and has_loop_select), (
        "fix_error_loop_python.prompt must self-include pdd/fix_error_loop.py "
        "(full include, or per-symbol selects for cloud_fix_errors and "
        "fix_error_loop) so strict prompt-contract preflight has source "
        "context for the declared existing public symbols."
    )


def test_fix_error_loop_prompt_contract_preflight_has_no_errors() -> None:
    """Deterministic preflight check from the issue must return no errors."""
    if not MODULE_PATH.is_file():
        pytest.skip(f"module not present at expected path: {MODULE_PATH}")

    errors = _prompt_contract_errors_for_module(
        "fix_error_loop", REPO_ROOT, REPO_ROOT
    )

    assert errors == [], (
        "Strict prompt-contract preflight regressed for fix_error_loop "
        "(issue #1237). Errors: " + "\n".join(errors)
    )


# --- Integration tests: cross-module flow with git-driven strict mode ---


def test_strict_mode_triggers_and_preflight_passes_in_simulated_sync(
    tmp_path: Path,
) -> None:
    """End-to-end: changed prompt + live module pass strict preflight.

    Exercises the agentic_sync -> architecture_include_validation handoff
    that failed for #1230 before #1237 landed: strict mode kicks in
    because the prompt has uncommitted changes, and validation finds the
    self-include so no errors are produced.
    """
    repo = _seed_fix_error_loop_repo(tmp_path)
    prompt = repo / "prompts" / "fix_error_loop_python.prompt"

    assert _prompt_contract_strict_self_context_required(prompt, repo) is True, (
        "Strict mode should engage when the prompt has uncommitted changes "
        "relative to the working tree (issue #1237 reproduction path)."
    )

    errors = _prompt_contract_errors_for_module("fix_error_loop", repo, repo)
    assert errors == [], (
        "Cross-module preflight should report no errors when the prompt "
        "self-includes pdd/fix_error_loop.py. Got: " + "\n".join(errors)
    )


def test_removing_self_include_reproduces_issue_1237_dry_run_error(
    tmp_path: Path,
) -> None:
    """Inverse end-to-end: dropping the self-include reproduces the original
    sync failure message exactly as reported in the issue.

    Locks in that the cross-module pipeline (validator -> formatter) still
    surfaces the symbols by name, so a future regression would block sync
    with an actionable error rather than silently passing.
    """
    repo = _seed_fix_error_loop_repo(tmp_path)
    prompt = repo / "prompts" / "fix_error_loop_python.prompt"

    stripped = re.sub(
        r"<include[^>]*>pdd/fix_error_loop\.py</include>\s*",
        "",
        prompt.read_text(encoding="utf-8"),
    )
    prompt.write_text(stripped, encoding="utf-8")

    errors = _prompt_contract_errors_for_module("fix_error_loop", repo, repo)
    assert errors, "Removing the self-include must trigger preflight errors."
    joined = "\n".join(errors)
    assert "cloud_fix_errors" in joined and "fix_error_loop" in joined
    assert "includes no existing module source context" in joined

    formatted = _format_prompt_contract_preflight_error("fix_error_loop", errors)
    assert formatted.startswith("fix_error_loop: prompt contract preflight failed:")
    assert "missing cloud_fix_errors, fix_error_loop" in formatted


def test_prompt_interface_symbols_match_live_module_definitions() -> None:
    """The prompt's declared <pdd-interface> symbols must exist in the
    real module file.

    This is the cross-module invariant the issue depends on: if anyone
    renames/removes `cloud_fix_errors` or `fix_error_loop` from the module
    without updating the prompt, strict preflight would block sync with a
    misleading 'missing source context' message even when the include is
    present. Catch that drift here.
    """
    prompt_text = PROMPT_PATH.read_text(encoding="utf-8")
    match = re.search(
        r"<pdd-interface>(.*?)</pdd-interface>", prompt_text, re.DOTALL
    )
    assert match, "fix_error_loop prompt must declare a <pdd-interface>."
    interface = json.loads(match.group(1))
    declared = {
        fn["name"]
        for fn in interface.get("module", {}).get("functions", [])
    }
    assert {"cloud_fix_errors", "fix_error_loop"}.issubset(declared), (
        "Prompt must keep declaring both public symbols that #1237 fixed "
        f"source-context coverage for; got {sorted(declared)}."
    )

    module_tree = ast.parse(MODULE_PATH.read_text(encoding="utf-8"))
    module_defs = {
        node.name
        for node in module_tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }
    missing = declared - module_defs
    assert not missing, (
        "Prompt declares symbols not defined at module top-level in "
        f"pdd/fix_error_loop.py: {sorted(missing)}. Either restore the "
        "definitions or update the prompt interface."
    )
