"""
Reproduction tests for issue #1074: global sync misreads nested worktrees and
path-aware architecture metadata.

Each test asserts the *correct/expected* behavior described in the issue's
Acceptance Criteria. On the current (buggy) code most of these tests are
expected to FAIL; once the bug is fixed they should pass and act as
permanent regression tests.

Issue: https://github.com/promptdriven/pdd/issues/1074

Acceptance criteria covered:
  1. Global sync ignores nested ``.pddrc`` files under hidden/tooling
     directories such as ``.pdd/worktrees/`` and ``.worktrees/``.
  2. Global sync schedules duplicate absolute output filepaths only once.
  3. ``sync-architecture`` can infer path-aware output filepaths from prompt
     names such as ``src/workers/runtime/gemini_cli_python.prompt``.
  4. ``sync-architecture`` resolves nested architecture files with an
     ancestor ``prompts/`` root.
  5. Dependency tags using stale basenames or case variants are normalized
     to the existing architecture filename when unambiguous.
"""

from __future__ import annotations

import json
import os
import tempfile
from pathlib import Path

import pytest

from pdd.agentic_sync import _architecture_sync_modules
from pdd.architecture_registry import find_architecture_for_project
from pdd.architecture_sync import (
    _infer_filepath,
    _resolve_sync_paths,
    update_architecture_from_prompt,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _write_pddrc(path: Path) -> None:
    path.write_text(
        "contexts:\n"
        "  default:\n"
        "    defaults:\n"
        "      prompts_dir: prompts\n"
        "      generate_output_path: pdd/\n"
        "    paths:\n"
        "      - '**'\n",
        encoding="utf-8",
    )


# ---------------------------------------------------------------------------
# AC 1: Nested .pddrc/architecture under hidden/tooling dirs are ignored
# ---------------------------------------------------------------------------


def test_global_sync_ignores_architecture_under_pdd_worktrees(tmp_path: Path) -> None:
    """Architecture files inside ``.pdd/worktrees/`` must not be scheduled.

    The README documents ``.pdd/worktrees/`` as transient local scratch state,
    not project state. Global sync that discovers and schedules an
    ``architecture.json`` from a stale worktree copy would run sync against
    the wrong tree.
    """
    (tmp_path / "prompts").mkdir()
    real_arch = [
        {"filename": "real_python.prompt", "filepath": "pdd/real.py", "priority": 1}
    ]
    (tmp_path / "architecture.json").write_text(json.dumps(real_arch))

    worktree = tmp_path / ".pdd" / "worktrees" / "fix-issue-9999"
    worktree.mkdir(parents=True)
    (worktree / "architecture.json").write_text(
        json.dumps(
            [
                {
                    "filename": "stale_python.prompt",
                    "filepath": "pdd/stale.py",
                    "priority": 1,
                }
            ]
        )
    )
    _write_pddrc(worktree / ".pddrc")

    arch_paths = find_architecture_for_project(tmp_path)
    basenames = {p.parent.name for p in arch_paths}
    assert worktree.name not in basenames, (
        f"find_architecture_for_project must skip .pdd/worktrees/, got {arch_paths!r}"
    )

    modules, _arch, _root_arch = _architecture_sync_modules(tmp_path)
    scheduled = {m.basename for m in modules}
    assert "real" in scheduled
    assert "stale" not in scheduled, (
        f"global sync scheduled stale worktree module: {scheduled!r}"
    )


def test_global_sync_ignores_architecture_under_dot_worktrees(tmp_path: Path) -> None:
    """``.worktrees/`` (dot-prefixed tooling dir) must also be skipped.

    The issue cites ``.worktrees/`` explicitly as an example of a
    hidden/tooling directory that should be ignored by global sync.
    """
    (tmp_path / "prompts").mkdir()
    (tmp_path / "architecture.json").write_text(
        json.dumps(
            [{"filename": "real_python.prompt", "filepath": "pdd/real.py", "priority": 1}]
        )
    )

    wt = tmp_path / ".worktrees" / "feature-branch"
    wt.mkdir(parents=True)
    (wt / "architecture.json").write_text(
        json.dumps(
            [
                {
                    "filename": "stale_python.prompt",
                    "filepath": "pdd/stale.py",
                    "priority": 1,
                }
            ]
        )
    )
    _write_pddrc(wt / ".pddrc")

    modules, _arch, _root_arch = _architecture_sync_modules(tmp_path)
    scheduled = {m.basename for m in modules}
    assert "stale" not in scheduled, (
        f"global sync scheduled stale .worktrees/ module: {scheduled!r}"
    )


# ---------------------------------------------------------------------------
# AC 2: Duplicate absolute output filepaths are scheduled only once
# ---------------------------------------------------------------------------


def test_global_sync_dedupes_duplicate_output_filepaths(tmp_path: Path) -> None:
    """Two architecture entries with the same absolute output ``filepath``
    must be scheduled as a single module to avoid duplicate scheduling and
    noisy false staleness."""
    (tmp_path / "prompts").mkdir()
    arch = [
        {"filename": "api_python.prompt", "filepath": "pdd/api.py", "priority": 1},
        # Same output filepath, different filename — must be deduped.
        {"filename": "api_v2_python.prompt", "filepath": "pdd/api.py", "priority": 2},
    ]
    (tmp_path / "architecture.json").write_text(json.dumps(arch))

    modules, _arch, _root_arch = _architecture_sync_modules(tmp_path)
    filepaths = [m.entry.get("filepath") for m in modules]
    # Resolve to absolute for a fair comparison.
    abs_filepaths = [
        str((tmp_path / fp).resolve()) if fp else None for fp in filepaths
    ]
    unique = {p for p in abs_filepaths if p is not None}
    assert len(modules) == len(unique), (
        "duplicate absolute output filepaths must be scheduled only once; "
        f"got {len(modules)} module(s) for {len(unique)} unique filepath(s): "
        f"{abs_filepaths!r}"
    )


# ---------------------------------------------------------------------------
# AC 3: Path-aware prompt filenames infer path-aware output filepaths
# ---------------------------------------------------------------------------


def test_infer_filepath_path_aware_lowercase_language() -> None:
    """``src/workers/runtime/gemini_cli_python.prompt`` must map to a
    path-aware output filepath such as ``src/workers/runtime/gemini_cli.py``
    — not flattened into ``pdd/``."""
    out = _infer_filepath("src/workers/runtime/gemini_cli_python.prompt")
    assert out.endswith("gemini_cli.py"), out
    assert "src/workers/runtime" in out.replace(os.sep, "/"), (
        f"_infer_filepath must preserve the prompt's directory structure, got {out!r}"
    )
    # Specifically, must not flatten everything under pdd/.
    assert not out.replace(os.sep, "/").startswith("pdd/src/"), (
        f"_infer_filepath must not prepend pdd/ to an already-nested prompt path, got {out!r}"
    )


def test_infer_filepath_path_aware_pascal_language() -> None:
    """Same as above but for the PascalCase variant
    (``..._Python.prompt``). The function should infer the language
    suffix case-insensitively and preserve the directory structure."""
    out = _infer_filepath("src/workers/runtime/gemini_cli_Python.prompt")
    out_norm = out.replace(os.sep, "/")
    # Must look like an output file under src/workers/runtime, not a prompts/ copy.
    assert out_norm.endswith("gemini_cli.py"), out_norm
    assert "src/workers/runtime" in out_norm, out_norm
    assert not out_norm.startswith("prompts/"), (
        f"path-aware prompt name must not fall back to prompts/<filename>, got {out_norm!r}"
    )


# ---------------------------------------------------------------------------
# AC 4: Nested architecture files resolve via ancestor prompts/ root
# ---------------------------------------------------------------------------


def test_resolve_sync_paths_uses_ancestor_prompts_dir(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """When invoked from a nested directory that contains an
    ``architecture.json`` but no local ``prompts/``, ``sync-architecture``
    must resolve the prompts root to the nearest ancestor ``prompts/``
    directory."""
    real_prompts = tmp_path / "prompts"
    real_prompts.mkdir()
    nested = tmp_path / "modules" / "auth"
    nested.mkdir(parents=True)
    (nested / "architecture.json").write_text("[]")

    monkeypatch.chdir(nested)
    prompts_dir, _arch = _resolve_sync_paths(None, None)
    assert prompts_dir.resolve() == real_prompts.resolve(), (
        "nested architecture with no local prompts/ must resolve to ancestor "
        f"prompts/, got {prompts_dir!r} (expected {real_prompts!r})"
    )


# ---------------------------------------------------------------------------
# AC 5: <pdd-dependency> tags using stale basename / case variants are
#       normalized to the existing architecture filename when unambiguous
# ---------------------------------------------------------------------------


def test_dependency_tag_normalized_to_existing_basename(tmp_path: Path) -> None:
    """A prompt that lists a *basename-only* ``<pdd-dependency>`` tag must
    have it normalized to the existing architecture entry's full filename
    when the match is unambiguous."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()

    api_prompt = prompts_dir / "api_python.prompt"
    api_prompt.write_text(
        "<pdd-reason>API module</pdd-reason>\n", encoding="utf-8"
    )

    consumer_prompt = prompts_dir / "consumer_python.prompt"
    consumer_prompt.write_text(
        "<pdd-reason>Consumer module</pdd-reason>\n"
        # Stale basename — actual architecture uses api_python.prompt.
        "<pdd-dependency>api</pdd-dependency>\n",
        encoding="utf-8",
    )

    arch = [
        {
            "filename": "api_python.prompt",
            "filepath": "pdd/api.py",
            "priority": 1,
            "dependencies": [],
        },
        {
            "filename": "consumer_python.prompt",
            "filepath": "pdd/consumer.py",
            "priority": 2,
            "dependencies": [],
        },
    ]
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps(arch))

    result = update_architecture_from_prompt(
        "consumer_python.prompt",
        prompts_dir=prompts_dir,
        architecture_path=arch_path,
    )
    assert result["success"], result.get("error")

    written = json.loads(arch_path.read_text())
    consumer = next(m for m in written if m["filename"] == "consumer_python.prompt")
    deps = consumer.get("dependencies", [])
    assert "api_python.prompt" in deps, (
        "stale basename <pdd-dependency>api</pdd-dependency> must be "
        f"normalized to api_python.prompt, got {deps!r}"
    )
    assert "api" not in deps, (
        f"raw basename must not be retained as a dependency: {deps!r}"
    )


def test_dependency_tag_normalized_to_existing_case_variant(tmp_path: Path) -> None:
    """A ``<pdd-dependency>`` whose only difference from an existing
    architecture filename is letter-case (e.g. ``API_Python.prompt`` vs
    ``api_python.prompt``) must be normalized to the existing filename."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    (prompts_dir / "api_python.prompt").write_text(
        "<pdd-reason>API</pdd-reason>\n", encoding="utf-8"
    )
    (prompts_dir / "consumer_python.prompt").write_text(
        "<pdd-reason>Consumer</pdd-reason>\n"
        # Wrong case for both the module name and the language suffix.
        "<pdd-dependency>API_Python.prompt</pdd-dependency>\n",
        encoding="utf-8",
    )

    arch = [
        {
            "filename": "api_python.prompt",
            "filepath": "pdd/api.py",
            "priority": 1,
            "dependencies": [],
        },
        {
            "filename": "consumer_python.prompt",
            "filepath": "pdd/consumer.py",
            "priority": 2,
            "dependencies": [],
        },
    ]
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps(arch))

    result = update_architecture_from_prompt(
        "consumer_python.prompt",
        prompts_dir=prompts_dir,
        architecture_path=arch_path,
    )
    assert result["success"], result.get("error")

    written = json.loads(arch_path.read_text())
    consumer = next(m for m in written if m["filename"] == "consumer_python.prompt")
    deps = consumer.get("dependencies", [])
    assert "api_python.prompt" in deps, (
        "case-variant dependency tag must be normalized to existing arch "
        f"filename, got {deps!r}"
    )
    assert "API_Python.prompt" not in deps, (
        f"unnormalized case variant retained in dependencies: {deps!r}"
    )
