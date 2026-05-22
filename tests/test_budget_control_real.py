"""Real-LLM tests for the GitHub App budget-control surface.

These tests regenerate the slash-command parser module from its prompt and
re-verify the Finding 4 (``metadata.amount``) and Finding 5 (verb-scoped
authorization) contracts on the regenerated code. They exist to catch LLM
drift: a future ``pdd sync`` could silently change the parser's metadata
shape or its auth gating posture and otherwise pass review.

Skip gate: set ``PDD_RUN_REAL_LLM_TESTS=1`` to run. Cost: one ``pdd
generate`` invocation on the parser prompt (typically < $1).
"""

from __future__ import annotations

import importlib.util
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest


pytestmark = pytest.mark.real


def _skip_unless_real() -> None:
    if not (os.getenv("PDD_RUN_REAL_LLM_TESTS") or os.getenv("PDD_RUN_ALL_TESTS") == "1"):
        pytest.skip("Real LLM tests require API access; set PDD_RUN_REAL_LLM_TESTS=1")
    if shutil.which("pdd") is None:
        pytest.skip("`pdd` CLI not on PATH; install pdd to run these tests")


def _repo_root() -> Path:
    here = Path(__file__).resolve()
    for ancestor in (here, *here.parents):
        if (ancestor / "pdd" / "prompts" / "server" / "slash_command_parser_python.prompt").exists():
            return ancestor
    pytest.skip("Could not locate the pdd repo root containing the parser prompt")


def _import_from_path(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"Could not load spec for {name} at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _ensure_dependencies_importable(workdir: Path, repo_root: Path) -> None:
    """Mirror the parser's import dependencies (models + budget_settings) into
    ``workdir`` so the regenerated ``slash_command_parser.py`` can be loaded
    in isolation without dragging in the rest of ``pdd/__init__.py``.
    """
    for relpath in (
        "pdd/server/models.py",
        "pdd/server/budget_settings.py",
    ):
        dst = workdir / relpath
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(repo_root / relpath, dst)
    (workdir / "pdd" / "__init__.py").write_text("", encoding="utf-8")
    (workdir / "pdd" / "server" / "__init__.py").write_text("", encoding="utf-8")


def test_regenerated_parser_preserves_findings_4_and_5_contracts(tmp_path):
    """Generate ``slash_command_parser.py`` via real LLM and assert the
    Finding 4 (``metadata.amount`` on budget-mutating kinds) and Finding 5
    (``/pdd settings`` returns ``settings`` kind without auth gating) contracts.
    """
    _skip_unless_real()
    repo = _repo_root()
    prompt = repo / "pdd" / "prompts" / "server" / "slash_command_parser_python.prompt"

    workdir = tmp_path / "regen"
    workdir.mkdir()
    _ensure_dependencies_importable(workdir, repo)

    output_dir = workdir / "pdd" / "server"
    result = subprocess.run(
        [
            "pdd",
            "--force",
            "generate",
            str(prompt),
            "--output",
            str(output_dir / "slash_command_parser.py"),
        ],
        capture_output=True,
        text=True,
        timeout=600,
        cwd=str(repo),
    )
    if result.returncode != 0:
        pytest.skip(
            f"pdd generate failed (likely API credential issue): "
            f"stderr={result.stderr[:500]}"
        )

    sys.path.insert(0, str(workdir))
    try:
        models = _import_from_path("pdd.server.models", workdir / "pdd" / "server" / "models.py")
        # budget_settings must import first so the parser's `from .budget_settings import ...` resolves.
        _import_from_path(
            "pdd.server.budget_settings",
            workdir / "pdd" / "server" / "budget_settings.py",
        )
        parser = _import_from_path(
            "pdd.server.slash_command_parser",
            output_dir / "slash_command_parser.py",
        )
    finally:
        if str(workdir) in sys.path:
            sys.path.remove(str(workdir))

    CommentInput = parser.CommentInput
    parse = parser.parse_comment

    settings_result = parse(
        CommentInput(id=1, body="/pdd settings", user_login="alice", user_type="User")
    )
    assert settings_result.kind == "settings", (
        f"Finding 5 regression: parser did not return read-only `settings` "
        f"kind for /pdd settings (got {settings_result.kind!r})."
    )
    assert settings_result.metadata == {}, (
        f"Finding 4 regression: read-only kinds must have empty metadata "
        f"(got {settings_result.metadata!r})."
    )

    budget_result = parse(
        CommentInput(id=2, body="/pdd budget 30", user_login="alice", user_type="User")
    )
    assert budget_result.kind == "budget_set"
    assert isinstance(budget_result.metadata, dict)
    assert budget_result.metadata.get("amount") == 30.0, (
        f"Finding 4 regression: budget_set must carry metadata['amount']=30.0 "
        f"(got {budget_result.metadata!r})."
    )

    issue_alias = parse(
        CommentInput(id=3, body="/pdd budget 30", user_login="alice", user_type="User"),
        active_command="issue",
    )
    assert issue_alias.kind == "budget_max_set", (
        "R6 regression: bare /pdd budget N on a pdd-issue job must alias to "
        "budget_max_set."
    )
    assert issue_alias.metadata.get("amount") == 30.0
