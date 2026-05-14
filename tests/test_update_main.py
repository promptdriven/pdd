"""
Test plan for pdd.update_main
=============================

Spec requirements (mapped to test functions below):

1.  update_main signature returns Optional[Tuple[str, float, str]].
    -> test_signature_returns_tuple_on_success
    -> test_returns_none_on_value_error
2.  use_git and input_code_file are mutually exclusive (raise ValueError).
    -> test_use_git_and_input_code_file_mutually_exclusive
3.  Agentic routing: try agentic first, fall back to legacy (single-file).
    -> test_single_file_agentic_first_then_legacy
4.  After successful agentic update, read updated prompt from file.
    -> test_agentic_success_reads_prompt_from_disk
5.  strength/temperature resolution: explicit overrides ctx.obj; ctx.obj updates.
    -> test_strength_temperature_resolution_explicit_overrides
    -> test_strength_temperature_falls_back_to_ctx_obj
6.  Validate prompt non-empty before writing in true-update mode.
    -> test_empty_prompt_aborts_write
7.  Without --output, overwrite input_prompt_file in place.
    -> test_no_output_overwrites_prompt_in_place
8.  Sanitize prompt output before writing (legacy paths).
    -> test_sanitize_called_before_write
9.  Single-file always-on metadata finalization, failure raises Exit(1).
    -> test_single_file_metadata_helper_always_called_on_success
    -> test_single_file_metadata_failure_raises_exit_1
10. _run_single_file_metadata_sync helper contract.
    -> test_helper_returns_true_on_ok_result
    -> test_helper_returns_false_on_failed_stage
    -> test_helper_writes_failures_to_stderr
    -> test_helper_returns_false_on_orchestrator_exception
    -> test_helper_passes_dry_run_through
11. Regeneration mode: derive prompt path via resolve_prompt_code_pair.
    -> test_regeneration_mode_resolves_prompt_path
12. Repo mode: not in git repo => None.
    -> test_repo_mode_not_in_git_repo
13. Repo mode: no scannable code files => None.
    -> test_repo_mode_no_pairs_returns_none
14. Repo mode: no changed pairs => None.
    -> test_repo_mode_no_changes_returns_none
15. Repo mode success returns (msg, cost, models).
    -> test_repo_mode_success_returns_tuple
16. Repo mode sync_metadata=True: orchestrator called per pair.
    -> test_repo_mode_sync_metadata_calls_orchestrator
17. Repo mode sync_metadata=True with a failed stage => Exit(1).
    -> test_repo_mode_sync_metadata_failure_raises_exit_1
18. Repo mode legacy: save_fingerprint + arch sync inline.
    -> test_repo_mode_legacy_calls_save_fingerprint
19. derive_basename_and_language uses relative path.
    -> test_derive_basename_uses_relative_path
20. get_git_changed_files merges multiple git outputs.
    -> test_get_git_changed_files_combines_sources
21. is_code_changed: git fallback when no fingerprint.
    -> test_is_code_changed_git_fallback
22. is_code_changed: fingerprint match returns False.
    -> test_is_code_changed_fingerprint_match
23. is_code_changed: fingerprint mismatch returns True.
    -> test_is_code_changed_fingerprint_mismatch
24. _has_skip_suffix recognizes skip suffixes.
    -> test_has_skip_suffix
25. _has_meaningful_code distinguishes blank/comment-only files.
    -> test_has_meaningful_code
26. _is_pddignored handles all three pattern shapes.
    -> test_is_pddignored
27. find_and_resolve_all_pairs filters non-code files.
    -> test_find_and_resolve_all_pairs_filters
28. _meta_status_string transitions.
    -> test_meta_status_synced
    -> test_meta_status_failed
    -> test_meta_status_skipped
29. _find_prd_file discovery.
    -> test_find_prd_file
30. update_file_pair legacy fallback.
    -> test_update_file_pair_legacy_path
31. Sanitization integration test (regression for include-tag bug).
    -> test_sanitize_invalid_include_tag_removed
"""

from __future__ import annotations

import os
import io
import json
import hashlib
import subprocess
from pathlib import Path
from types import SimpleNamespace
from typing import Any, Dict, Optional, Tuple
from unittest.mock import patch, MagicMock

import click
import pytest

import sys as _sys
import pdd.update_main  # noqa: F401  (ensure submodule registered in sys.modules)
um = _sys.modules["pdd.update_main"]  # bypass __init__.py shadow to get the module
from pdd.update_main import (
    _find_prd_file,
    _has_meaningful_code,
    _has_skip_suffix,
    _is_pddignored,
    _meta_status_string,
    _run_single_file_metadata_sync,
    derive_basename_and_language,
    find_and_resolve_all_pairs,
    get_git_changed_files,
    is_code_changed,
    update_file_pair,
    update_main,
)


# --------------------------------------------------------------------------- #
# Fixtures
# --------------------------------------------------------------------------- #
def _make_ctx(**overrides: Any) -> click.Context:
    ctx = click.Context(click.Command("update"))
    ctx.obj = {
        "strength": 0.5,
        "temperature": 0.0,
        "verbose": False,
        "quiet": True,
        "time": 0.25,
        "force": False,
        "context": None,
        "confirm_callback": None,
    }
    ctx.obj.update(overrides)
    return ctx


@pytest.fixture
def ctx() -> click.Context:
    return _make_ctx()


def _stage(status: str = "ok", reason: Optional[str] = None, detail: Optional[str] = None) -> SimpleNamespace:
    return SimpleNamespace(status=status, reason=reason, detail=detail)


def _make_meta_result(
    ok: bool = True,
    dry_run: bool = False,
    stages: Optional[Dict[str, SimpleNamespace]] = None,
) -> SimpleNamespace:
    if stages is None:
        stages = {"prompt": _stage("ok"), "fingerprint": _stage("ok")}
    return SimpleNamespace(ok=ok, dry_run=dry_run, stages=stages)


# --------------------------------------------------------------------------- #
# 1. & 2. signature, mutual exclusion
# --------------------------------------------------------------------------- #
class TestSignatureAndMutualExclusion:
    def test_signature_returns_tuple_on_success(self, ctx, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("orig\n", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("def x(): pass\n", encoding="utf-8")
        old_code = tmp_path / "old.py"
        old_code.write_text("def x(): pass\n", encoding="utf-8")
        with patch("pdd.update_main.update_prompt",
                   return_value=("new prompt", 0.01, "m")), \
             patch("pdd.update_main._run_single_file_metadata_sync",
                   return_value=True):
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(old_code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        assert isinstance(result, tuple)
        assert len(result) == 3
        assert result[0] == "new prompt"
        assert result[1] == 0.01
        assert result[2] == "m"

    def test_use_git_and_input_code_file_mutually_exclusive(self, ctx):
        # Per spec rule 9: use_git and input_code_file together must raise ValueError.
        with pytest.raises(ValueError, match="mutually exclusive"):
            update_main(
                ctx=ctx,
                input_prompt_file="p",
                modified_code_file="c",
                input_code_file="ic",  # both supplied -> error
                output=None,
                use_git=True,           # both supplied -> error
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )

    def test_returns_none_on_value_error(self, ctx):
        # Missing modified_code_file outside repo mode raises ValueError -> None.
        result = update_main(
            ctx=ctx,
            input_prompt_file=None,
            modified_code_file=None,
            input_code_file=None,
            output=None,
            use_git=False,
            repo=False,
            extensions=None,
            directory=None,
            strength=None,
            temperature=None,
            simple=True,
        )
        assert result is None


# --------------------------------------------------------------------------- #
# 3. & 4. agentic routing & post-update read
# --------------------------------------------------------------------------- #
class TestAgenticRouting:
    def test_single_file_agentic_first_then_legacy(self, ctx, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("orig\n", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("def x(): pass\n", encoding="utf-8")
        old_code = tmp_path / "old.py"
        old_code.write_text("def x(): pass\n", encoding="utf-8")

        agentic = MagicMock(return_value=(False, "no agents", 0.0, "", []))
        legacy = MagicMock(return_value=("legacy prompt", 0.02, "legacy-m"))

        with patch("pdd.agentic_update.run_agentic_update", agentic), \
             patch("pdd.update_main.update_prompt", legacy), \
             patch("pdd.update_main._run_single_file_metadata_sync",
                   return_value=True):
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(old_code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=False,  # allow agentic
            )
        assert agentic.called
        assert legacy.called
        assert result[0] == "legacy prompt"

    def test_agentic_success_reads_prompt_from_disk(self, ctx, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("old\n", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("def x(): pass\n", encoding="utf-8")
        old_code = tmp_path / "old.py"
        old_code.write_text("def x(): pass\n", encoding="utf-8")

        def agentic_writes(*args, **kwargs):
            prompt.write_text("AGENTIC-WROTE-THIS\n", encoding="utf-8")
            return (True, "ok", 0.07, "agent-model", [str(prompt)])

        with patch("pdd.agentic_update.run_agentic_update",
                   side_effect=agentic_writes), \
             patch("pdd.update_main._run_single_file_metadata_sync",
                   return_value=True):
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(old_code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=False,
            )
        # Must return the *post-write* file content.
        assert result is not None
        assert "AGENTIC-WROTE-THIS" in result[0]
        assert result[1] == 0.07
        assert result[2] == "agent-model"


# --------------------------------------------------------------------------- #
# 5. strength/temperature resolution
# --------------------------------------------------------------------------- #
class TestStrengthTemperatureResolution:
    def test_strength_temperature_resolution_explicit_overrides(self, ctx, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("x\n", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("def x(): pass\n", encoding="utf-8")
        old_code = tmp_path / "old.py"
        old_code.write_text("def x(): pass\n", encoding="utf-8")
        captured: Dict[str, Any] = {}

        def fake_update_prompt(**kwargs):
            captured.update(kwargs)
            return ("new", 0.0, "m")

        with patch("pdd.update_main.update_prompt", side_effect=fake_update_prompt), \
             patch("pdd.update_main._run_single_file_metadata_sync", return_value=True):
            update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(old_code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=0.9,        # explicit override
                temperature=0.42,    # explicit override
                simple=True,
            )
        assert captured["strength"] == 0.9
        assert captured["temperature"] == 0.42
        # ctx.obj should be updated with the resolved values.
        assert ctx.obj["strength"] == 0.9
        assert ctx.obj["temperature"] == 0.42

    def test_strength_temperature_falls_back_to_ctx_obj(self, ctx, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("x\n", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("def x(): pass\n", encoding="utf-8")
        old_code = tmp_path / "old.py"
        old_code.write_text("def x(): pass\n", encoding="utf-8")
        ctx.obj["strength"] = 0.33
        ctx.obj["temperature"] = 0.11
        captured: Dict[str, Any] = {}

        def fake_update_prompt(**kwargs):
            captured.update(kwargs)
            return ("new", 0.0, "m")

        with patch("pdd.update_main.update_prompt", side_effect=fake_update_prompt), \
             patch("pdd.update_main._run_single_file_metadata_sync", return_value=True):
            update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(old_code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        assert captured["strength"] == 0.33
        assert captured["temperature"] == 0.11


# --------------------------------------------------------------------------- #
# 6., 7., 8. write semantics & sanitization
# --------------------------------------------------------------------------- #
class TestWriteSemantics:
    def test_empty_prompt_aborts_write(self, ctx, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("original-content\n", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("def x(): pass\n", encoding="utf-8")
        old_code = tmp_path / "old.py"
        old_code.write_text("def x(): pass\n", encoding="utf-8")

        with patch("pdd.update_main.update_prompt",
                   return_value=("", 0.0, "m")), \
             patch("pdd.update_main._run_single_file_metadata_sync",
                   return_value=True):
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(old_code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        # On empty prompt, function returns None and DOES NOT overwrite the file.
        assert result is None
        assert prompt.read_text(encoding="utf-8") == "original-content\n"

    def test_no_output_overwrites_prompt_in_place(self, ctx, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("old prompt\n", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("def x(): pass\n", encoding="utf-8")
        old_code = tmp_path / "old.py"
        old_code.write_text("def x(): pass\n", encoding="utf-8")

        with patch("pdd.update_main.update_prompt",
                   return_value=("NEW PROMPT BODY", 0.0, "m")), \
             patch("pdd.update_main._run_single_file_metadata_sync",
                   return_value=True):
            update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(old_code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        assert "NEW PROMPT BODY" in prompt.read_text(encoding="utf-8")

    def test_sanitize_called_before_write(self, ctx, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("old\n", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("def x(): pass\n", encoding="utf-8")
        old_code = tmp_path / "old.py"
        old_code.write_text("def x(): pass\n", encoding="utf-8")

        # We confirm the sanitize hook is invoked before write by returning a
        # marker.  The implementation imports sanitize_prompt_output lazily.
        with patch("pdd.update_main.update_prompt",
                   return_value=("RAW", 0.0, "m")), \
             patch("pdd.validate_prompt_includes.sanitize_prompt_output",
                   return_value=("SANITIZED", [])) as san, \
             patch("pdd.update_main._run_single_file_metadata_sync",
                   return_value=True):
            update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(old_code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        assert san.called
        assert prompt.read_text(encoding="utf-8") == "SANITIZED"


# --------------------------------------------------------------------------- #
# 9. & 10. metadata sync helper contract
# --------------------------------------------------------------------------- #
class TestMetadataSyncHelper:
    def test_helper_returns_true_on_ok_result(self, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("x", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("y", encoding="utf-8")
        with patch("pdd.metadata_sync.run_metadata_sync",
                   return_value=_make_meta_result(ok=True)):
            assert _run_single_file_metadata_sync(prompt, code, dry_run=False) is True

    def test_helper_returns_false_on_failed_stage(self, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("x", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("y", encoding="utf-8")
        result = _make_meta_result(
            ok=False,
            stages={
                "prompt": _stage("ok"),
                "fingerprint": _stage("failed", reason="disk full"),
            },
        )
        with patch("pdd.metadata_sync.run_metadata_sync", return_value=result):
            assert _run_single_file_metadata_sync(prompt, code) is False

    def test_helper_returns_false_on_orchestrator_exception(self, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("x", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("y", encoding="utf-8")
        with patch("pdd.metadata_sync.run_metadata_sync",
                   side_effect=RuntimeError("boom")):
            assert _run_single_file_metadata_sync(prompt, code) is False

    def test_helper_writes_failures_to_stderr(self, tmp_path, capsys):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("x", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("y", encoding="utf-8")
        # Re-bind both consoles to the captured streams so writes show up.
        from rich.console import Console as RichConsole
        with patch.object(um, "_err_console",
                          RichConsole(file=os.sys.stderr, force_terminal=False)), \
             patch.object(um, "console",
                          RichConsole(file=os.sys.stdout, force_terminal=False)), \
             patch("pdd.metadata_sync.run_metadata_sync",
                   return_value=_make_meta_result(
                       ok=False,
                       stages={"fingerprint":
                               _stage("failed", reason="permission denied")},
                   )):
            _run_single_file_metadata_sync(prompt, code)
        captured = capsys.readouterr()
        assert "fingerprint" in captured.err
        assert "permission denied" in captured.err

    def test_helper_passes_dry_run_through(self, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("x", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("y", encoding="utf-8")
        seen: Dict[str, Any] = {}

        def fake(prompt_p, code_p, dry_run=False):
            seen["dry_run"] = dry_run
            return _make_meta_result(ok=True, dry_run=dry_run)

        with patch("pdd.metadata_sync.run_metadata_sync", side_effect=fake):
            _run_single_file_metadata_sync(prompt, code, dry_run=True)
        assert seen["dry_run"] is True


# --------------------------------------------------------------------------- #
# 11. always-on metadata for single-file & failure raises Exit(1)
# --------------------------------------------------------------------------- #
class TestSingleFileMetadataFinalization:
    def _setup(self, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("old\n", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("def x(): pass\n", encoding="utf-8")
        old_code = tmp_path / "old.py"
        old_code.write_text("def x(): pass\n", encoding="utf-8")
        return prompt, code, old_code

    def test_single_file_metadata_helper_always_called_on_success(self, ctx, tmp_path):
        prompt, code, old_code = self._setup(tmp_path)
        with patch("pdd.update_main.update_prompt",
                   return_value=("new prompt", 0.01, "m")), \
             patch("pdd.update_main._run_single_file_metadata_sync",
                   return_value=True) as helper:
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(old_code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
                sync_metadata=False,  # always-on even when False
            )
        assert result is not None
        assert helper.called

    def test_single_file_metadata_failure_raises_exit_1(self, ctx, tmp_path):
        prompt, code, old_code = self._setup(tmp_path)
        with patch("pdd.update_main.update_prompt",
                   return_value=("new prompt", 0.01, "m")), \
             patch("pdd.update_main._run_single_file_metadata_sync",
                   return_value=False):
            with pytest.raises(click.exceptions.Exit) as exc_info:
                update_main(
                    ctx=ctx,
                    input_prompt_file=str(prompt),
                    modified_code_file=str(code),
                    input_code_file=str(old_code),
                    output=None,
                    use_git=False,
                    repo=False,
                    extensions=None,
                    directory=None,
                    strength=None,
                    temperature=None,
                    simple=True,
                )
            assert exc_info.value.exit_code == 1


# --------------------------------------------------------------------------- #
# 12. regeneration mode
# --------------------------------------------------------------------------- #
class TestRegenerationMode:
    def test_regeneration_mode_resolves_prompt_path(self, ctx, tmp_path):
        code = tmp_path / "calc.py"
        code.write_text("def add(a, b): return a+b\n", encoding="utf-8")

        # Pretend the resolver returns a prompt path under tmp_path.
        prompt_path = tmp_path / "prompts" / "calc_python.prompt"
        prompt_path.parent.mkdir(parents=True)
        prompt_path.write_text("", encoding="utf-8")

        with patch("pdd.update_main.resolve_prompt_code_pair",
                   return_value=(prompt_path, code)), \
             patch("pdd.update_main.update_prompt",
                   return_value=("regenerated body", 0.01, "m")), \
             patch("pdd.update_main._run_single_file_metadata_sync",
                   return_value=True):
            result = update_main(
                ctx=ctx,
                input_prompt_file=None,
                modified_code_file=str(code),
                input_code_file=None,
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        assert result is not None
        assert "regenerated body" in prompt_path.read_text(encoding="utf-8")


# --------------------------------------------------------------------------- #
# 13.–18. repo mode behavior
# --------------------------------------------------------------------------- #
class TestRepoMode:
    def _ctx(self):
        return _make_ctx()

    def test_repo_mode_not_in_git_repo(self, tmp_path):
        # subprocess returns non-zero -> repo mode aborts with None.
        with patch("pdd.update_main.subprocess.run",
                   return_value=SimpleNamespace(returncode=128, stdout="", stderr="")):
            result = update_main(
                ctx=self._ctx(),
                input_prompt_file=None,
                modified_code_file=None,
                input_code_file=None,
                output=None,
                use_git=False,
                repo=True,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        assert result is None

    def test_repo_mode_no_pairs_returns_none(self, tmp_path):
        def fake_run(cmd, **kwargs):
            return SimpleNamespace(returncode=0, stdout=str(tmp_path) + "\n", stderr="")

        with patch("pdd.update_main.subprocess.run", side_effect=fake_run), \
             patch("pdd.update_main.find_and_resolve_all_pairs", return_value=[]):
            result = update_main(
                ctx=self._ctx(),
                input_prompt_file=None,
                modified_code_file=None,
                input_code_file=None,
                output=None,
                use_git=False,
                repo=True,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        assert result is None

    def test_repo_mode_no_changes_returns_none(self, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("body", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("x", encoding="utf-8")

        def fake_run(cmd, **kwargs):
            return SimpleNamespace(returncode=0, stdout=str(tmp_path) + "\n", stderr="")

        with patch("pdd.update_main.subprocess.run", side_effect=fake_run), \
             patch("pdd.update_main.find_and_resolve_all_pairs",
                   return_value=[(prompt, code)]), \
             patch("pdd.update_main.get_git_changed_files", return_value=set()), \
             patch("pdd.update_main.is_code_changed",
                   return_value=(False, "fingerprint matches")):
            result = update_main(
                ctx=self._ctx(),
                input_prompt_file=None,
                modified_code_file=None,
                input_code_file=None,
                output=None,
                use_git=False,
                repo=True,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        assert result is None

    def test_repo_mode_success_returns_tuple(self, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("body", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("x", encoding="utf-8")

        pair_result = {
            "prompt_file": str(prompt),
            "status": "updated",
            "cost": 0.07,
            "model": "MM",
            "error": "",
        }

        def fake_run(cmd, **kwargs):
            return SimpleNamespace(returncode=0, stdout=str(tmp_path) + "\n", stderr="")

        with patch("pdd.update_main.subprocess.run", side_effect=fake_run), \
             patch("pdd.update_main.find_and_resolve_all_pairs",
                   return_value=[(prompt, code)]), \
             patch("pdd.update_main.get_git_changed_files",
                   return_value={str(code.resolve())}), \
             patch("pdd.update_main.is_code_changed",
                   return_value=(True, "git reports change")), \
             patch("pdd.update_main.update_file_pair",
                   return_value=pair_result), \
             patch("pdd.update_main.save_fingerprint"), \
             patch("pdd.update_main.infer_module_identity",
                   return_value=("p", "python")):
            result = update_main(
                ctx=self._ctx(),
                input_prompt_file=None,
                modified_code_file=None,
                input_code_file=None,
                output=None,
                use_git=False,
                repo=True,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
                sync_metadata=False,
            )
        assert result is not None
        msg, cost, models = result
        assert msg == "Repository update complete."
        assert cost == pytest.approx(0.07)
        assert "MM" in models

    def test_repo_mode_sync_metadata_calls_orchestrator(self, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("body", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("x", encoding="utf-8")

        pair_result = {
            "prompt_file": str(prompt),
            "status": "updated",
            "cost": 0.07,
            "model": "MM",
            "error": "",
        }

        def fake_run(cmd, **kwargs):
            return SimpleNamespace(returncode=0, stdout=str(tmp_path) + "\n", stderr="")

        orchestrator = MagicMock(return_value=_make_meta_result(ok=True))
        with patch("pdd.update_main.subprocess.run", side_effect=fake_run), \
             patch("pdd.update_main.find_and_resolve_all_pairs",
                   return_value=[(prompt, code)]), \
             patch("pdd.update_main.get_git_changed_files",
                   return_value={str(code.resolve())}), \
             patch("pdd.update_main.is_code_changed",
                   return_value=(True, "git reports change")), \
             patch("pdd.update_main.update_file_pair",
                   return_value=pair_result), \
             patch("pdd.metadata_sync.run_metadata_sync", orchestrator):
            result = update_main(
                ctx=self._ctx(),
                input_prompt_file=None,
                modified_code_file=None,
                input_code_file=None,
                output=None,
                use_git=False,
                repo=True,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
                sync_metadata=True,
            )
        assert orchestrator.called
        assert result is not None

    def test_repo_mode_sync_metadata_failure_raises_exit_1(self, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("body", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("x", encoding="utf-8")

        pair_result = {
            "prompt_file": str(prompt),
            "status": "updated",
            "cost": 0.0,
            "model": "MM",
            "error": "",
        }

        def fake_run(cmd, **kwargs):
            return SimpleNamespace(returncode=0, stdout=str(tmp_path) + "\n", stderr="")

        failed = _make_meta_result(
            ok=False,
            stages={"fingerprint": _stage("failed", reason="x")},
        )
        with patch("pdd.update_main.subprocess.run", side_effect=fake_run), \
             patch("pdd.update_main.find_and_resolve_all_pairs",
                   return_value=[(prompt, code)]), \
             patch("pdd.update_main.get_git_changed_files",
                   return_value={str(code.resolve())}), \
             patch("pdd.update_main.is_code_changed",
                   return_value=(True, "git reports change")), \
             patch("pdd.update_main.update_file_pair",
                   return_value=pair_result), \
             patch("pdd.metadata_sync.run_metadata_sync",
                   return_value=failed):
            with pytest.raises(click.exceptions.Exit) as exc:
                update_main(
                    ctx=self._ctx(),
                    input_prompt_file=None,
                    modified_code_file=None,
                    input_code_file=None,
                    output=None,
                    use_git=False,
                    repo=True,
                    extensions=None,
                    directory=None,
                    strength=None,
                    temperature=None,
                    simple=True,
                    sync_metadata=True,
                )
            assert exc.value.exit_code == 1

    def test_repo_mode_legacy_calls_save_fingerprint(self, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("body", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("x", encoding="utf-8")

        pair_result = {
            "prompt_file": str(prompt),
            "status": "updated",
            "cost": 0.0,
            "model": "MM",
            "error": "",
        }

        def fake_run(cmd, **kwargs):
            return SimpleNamespace(returncode=0, stdout=str(tmp_path) + "\n", stderr="")

        save_fp = MagicMock()
        with patch("pdd.update_main.subprocess.run", side_effect=fake_run), \
             patch("pdd.update_main.find_and_resolve_all_pairs",
                   return_value=[(prompt, code)]), \
             patch("pdd.update_main.get_git_changed_files",
                   return_value={str(code.resolve())}), \
             patch("pdd.update_main.is_code_changed",
                   return_value=(True, "git reports change")), \
             patch("pdd.update_main.update_file_pair",
                   return_value=pair_result), \
             patch("pdd.update_main.save_fingerprint", save_fp), \
             patch("pdd.update_main.infer_module_identity",
                   return_value=("p", "python")):
            update_main(
                ctx=self._ctx(),
                input_prompt_file=None,
                modified_code_file=None,
                input_code_file=None,
                output=None,
                use_git=False,
                repo=True,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
                sync_metadata=False,
            )
        assert save_fp.called


# --------------------------------------------------------------------------- #
# 19.–23. helpers around fingerprints/git
# --------------------------------------------------------------------------- #
class TestHelperFunctions:
    def test_derive_basename_uses_relative_path(self, tmp_path):
        repo = tmp_path
        nested = repo / "src" / "api" / "handler.py"
        nested.parent.mkdir(parents=True)
        nested.write_text("# x", encoding="utf-8")
        basename, lang = derive_basename_and_language(nested, repo)
        assert basename == "src_api_handler"
        assert lang == "python"

    def test_get_git_changed_files_combines_sources(self, tmp_path):
        def fake_run(cmd, **kwargs):
            res = SimpleNamespace(returncode=0, stdout="", stderr="")
            if "diff" in cmd and "main...HEAD" in cmd:
                res.stdout = "a.py\n"
            elif "diff" in cmd and "--cached" in cmd:
                res.stdout = "b.py\n"
            elif "diff" in cmd:
                res.stdout = "c.py\n"
            elif "ls-files" in cmd and "--others" in cmd:
                res.stdout = "d.py\n"
            return res

        with patch("pdd.update_main.subprocess.run", side_effect=fake_run):
            changed = get_git_changed_files(tmp_path, base_branch="main")
        names = {Path(p).name for p in changed}
        assert names == {"a.py", "b.py", "c.py", "d.py"}

    def test_is_code_changed_git_fallback(self, tmp_path):
        code = tmp_path / "x.py"
        code.write_text("# x", encoding="utf-8")
        # No fingerprint dir present -> git fallback decides.
        changed, _ = is_code_changed(
            code, tmp_path, git_changed_files={str(code.resolve())}
        )
        assert changed is True
        changed, _ = is_code_changed(code, tmp_path, git_changed_files=set())
        assert changed is False

    def test_is_code_changed_fingerprint_match(self, tmp_path):
        code = tmp_path / "x.py"
        code.write_text("body", encoding="utf-8")
        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)
        code_hash = hashlib.sha256(b"body").hexdigest()
        # derive_basename: "x", lang "python".
        (meta_dir / "x_python.json").write_text(
            json.dumps({"code_hash": code_hash}), encoding="utf-8"
        )
        changed, reason = is_code_changed(
            code, tmp_path, git_changed_files={str(code.resolve())}
        )
        assert changed is False
        assert "matches" in reason

    def test_is_code_changed_fingerprint_mismatch(self, tmp_path):
        code = tmp_path / "x.py"
        code.write_text("body", encoding="utf-8")
        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)
        (meta_dir / "x_python.json").write_text(
            json.dumps({"code_hash": "0" * 64}), encoding="utf-8"
        )
        changed, reason = is_code_changed(code, tmp_path, git_changed_files=set())
        assert changed is True
        assert "differs" in reason


# --------------------------------------------------------------------------- #
# 24.–26. filter primitives
# --------------------------------------------------------------------------- #
class TestFilterPrimitives:
    def test_has_skip_suffix(self):
        assert _has_skip_suffix(Path("foo.test.py")) is True
        assert _has_skip_suffix(Path("foo.spec.ts")) is True
        assert _has_skip_suffix(Path("foo.config.js")) is True
        assert _has_skip_suffix(Path("foo.py")) is False
        assert _has_skip_suffix(Path("types.d.ts")) is True

    def test_has_meaningful_code(self, tmp_path):
        meaningful = tmp_path / "yes.py"
        meaningful.write_text("def f():\n    return 1\n", encoding="utf-8")
        blank = tmp_path / "blank.py"
        blank.write_text("\n\n# comment-only\n# more\n", encoding="utf-8")
        empty = tmp_path / "empty.py"
        empty.write_text("", encoding="utf-8")
        assert _has_meaningful_code(meaningful) is True
        assert _has_meaningful_code(blank) is False
        assert _has_meaningful_code(empty) is False

    def test_is_pddignored(self, tmp_path):
        patterns = ["*.tmp", "build/", "src/internal/*.py"]
        root = tmp_path

        # Basename glob.
        f1 = root / "thing.tmp"
        f1.parent.mkdir(parents=True, exist_ok=True)
        f1.write_text("x", encoding="utf-8")
        assert _is_pddignored(f1, root, patterns) is True

        # Directory prefix.
        f2 = root / "build" / "artifact.py"
        f2.parent.mkdir(parents=True, exist_ok=True)
        f2.write_text("x", encoding="utf-8")
        assert _is_pddignored(f2, root, patterns) is True

        # Path glob.
        f3 = root / "src" / "internal" / "secret.py"
        f3.parent.mkdir(parents=True, exist_ok=True)
        f3.write_text("x", encoding="utf-8")
        assert _is_pddignored(f3, root, patterns) is True

        # Not ignored.
        f4 = root / "src" / "public.py"
        f4.parent.mkdir(parents=True, exist_ok=True)
        f4.write_text("x", encoding="utf-8")
        assert _is_pddignored(f4, root, patterns) is False


# --------------------------------------------------------------------------- #
# 27. find_and_resolve_all_pairs filtering
# --------------------------------------------------------------------------- #
class TestFindAndResolveAllPairs:
    def test_find_and_resolve_all_pairs_filters(self, tmp_path):
        repo = tmp_path
        # Keep: a meaningful .py with no skip suffix.
        keep = repo / "src" / "module.py"
        keep.parent.mkdir(parents=True)
        keep.write_text("def x(): return 1\n", encoding="utf-8")
        # Skip: .json
        (repo / "data.json").write_text("{}", encoding="utf-8")
        # Skip: .prompt
        (repo / "module.prompt").write_text("body", encoding="utf-8")
        # Skip: test_ prefix
        (repo / "test_module.py").write_text("def x(): pass\n", encoding="utf-8")
        # Skip: _example suffix
        (repo / "module_example.py").write_text("def x(): pass\n", encoding="utf-8")
        # Skip: .test suffix
        (repo / "module.test.py").write_text("def x(): pass\n", encoding="utf-8")
        # Skip: comment-only
        (repo / "blank.py").write_text("# comment-only\n", encoding="utf-8")

        # Force os.walk path: pretend git ls-files fails.
        def fake_run(cmd, **kwargs):
            return SimpleNamespace(returncode=1, stdout="", stderr="")

        with patch("pdd.update_main.subprocess.run", side_effect=fake_run), \
             patch("pdd.update_main._resolve_prompt_from_pddrc",
                   return_value=None):
            pairs = find_and_resolve_all_pairs(
                repo_root=repo, quiet=True, extensions=None, output_dir=None
            )
        code_files = [c for _, c in pairs]
        names = {c.name for c in code_files}
        assert "module.py" in names
        # All skips excluded:
        for excluded in ("data.json", "test_module.py", "module_example.py",
                         "module.test.py", "blank.py"):
            assert excluded not in names
        for c in code_files:
            assert c.suffix != ".prompt"


# --------------------------------------------------------------------------- #
# 28. _meta_status_string transitions
# --------------------------------------------------------------------------- #
class TestMetaStatusString:
    def test_meta_status_synced(self):
        r = _make_meta_result(
            ok=True, stages={"a": _stage("ok"), "b": _stage("ok")}
        )
        assert _meta_status_string(r) == "synced"

    def test_meta_status_failed(self):
        r = _make_meta_result(
            ok=False, stages={"a": _stage("ok"), "b": _stage("failed")}
        )
        assert _meta_status_string(r) == "failed:b"

    def test_meta_status_skipped(self):
        r = _make_meta_result(
            ok=True, stages={"a": _stage("skipped"), "b": _stage("skipped")}
        )
        assert _meta_status_string(r) == "skipped"

    def test_meta_status_dry_run(self):
        r = _make_meta_result(
            ok=True, dry_run=True,
            stages={"a": _stage("dry_run"), "b": _stage("dry_run")}
        )
        assert _meta_status_string(r) == "dry-run"

    def test_meta_status_none(self):
        assert _meta_status_string(None) == "skipped"


# --------------------------------------------------------------------------- #
# 29. PRD discovery
# --------------------------------------------------------------------------- #
class TestFindPrdFile:
    def test_find_prd_file_capital(self, tmp_path):
        prd = tmp_path / "PRD.md"
        prd.write_text("# prd\n", encoding="utf-8")
        assert _find_prd_file(tmp_path) == prd.resolve()

    def test_find_prd_file_glob(self, tmp_path):
        prd = tmp_path / "auth_prd.md"
        prd.write_text("# prd\n", encoding="utf-8")
        assert _find_prd_file(tmp_path) == prd

    def test_find_prd_file_none(self, tmp_path):
        assert _find_prd_file(tmp_path) is None


# --------------------------------------------------------------------------- #
# 30. update_file_pair legacy fallback
# --------------------------------------------------------------------------- #
class TestUpdateFilePair:
    def test_update_file_pair_legacy_path(self, ctx, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("orig\n", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("def x(): pass\n", encoding="utf-8")

        with patch("pdd.update_main.git_update",
                   return_value=("UPDATED PROMPT", 0.03, "the-model")):
            result = update_file_pair(prompt, code, ctx, repo=True, simple=True)
        assert result["status"] == "updated"
        assert result["cost"] == pytest.approx(0.03)
        assert result["model"] == "the-model"
        assert "UPDATED PROMPT" in prompt.read_text(encoding="utf-8")

    def test_update_file_pair_empty_prompt_is_regeneration(self, ctx, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("def x(): pass\n", encoding="utf-8")

        with patch("pdd.update_main.update_prompt",
                   return_value=("REGEN BODY", 0.05, "regen-model")):
            result = update_file_pair(prompt, code, ctx, repo=True, simple=True)
        assert result["status"] == "regenerated"
        assert "REGEN BODY" in prompt.read_text(encoding="utf-8")


# --------------------------------------------------------------------------- #
# 31. Sanitization regression (issue #813 carries through to this module).
# --------------------------------------------------------------------------- #
class TestSanitizationRegression:
    def test_sanitize_invalid_include_tag_removed(self, ctx, tmp_path):
        prompt = tmp_path / "p.prompt"
        prompt.write_text("orig\n", encoding="utf-8")
        code = tmp_path / "c.py"
        code.write_text("def x(): pass\n", encoding="utf-8")
        old_code = tmp_path / "old.py"
        old_code.write_text("def x(): pass\n", encoding="utf-8")
        bad = ('<include select="class:Foo">context/nonexistent.py</include>\n'
               '% Goal\nDo a thing.\n')
        with patch("pdd.update_main.update_prompt",
                   return_value=(bad, 0.0, "m")), \
             patch("pdd.update_main._run_single_file_metadata_sync",
                   return_value=True):
            update_main(
                ctx=ctx,
                input_prompt_file=str(prompt),
                modified_code_file=str(code),
                input_code_file=str(old_code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )
        saved = prompt.read_text(encoding="utf-8")
        # The actual sanitizer leaves a marker; we just verify the original
        # invalid select string didn't survive verbatim.
        assert 'select="class:Foo"' not in saved or "Invalid" in saved
