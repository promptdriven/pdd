"""
Tests for ``pdd.metadata_sync``.

Test plan (mapped to spec requirements in prompts/metadata_sync_python.prompt):

1. Single entry point — run_metadata_sync(prompt_path, code_path=None, *, dry_run=False,
   repo_root=None, architecture_path=None) -> MetadataSyncResult
   • test_run_metadata_sync_signature_returns_result_type
2. Fixed stage pipeline order: prompt → tags → architecture → run_report → fingerprint
   • test_stage_pipeline_runs_in_fixed_order
3. Result type (MetadataSyncResult): Pydantic v2 model with prompt_path, code_path,
   dry_run, stages; ok property; failing_stage property
   • test_result_is_pydantic_model_with_expected_fields
   • test_ok_property_true_when_all_ok
   • test_ok_property_true_with_dry_run_stages
   • test_ok_property_false_when_any_stage_failed
   • test_failing_stage_returns_first_failed_stage_name
   • test_failing_stage_returns_none_when_no_failure
4. Fail-soft per stage; prompt failure short-circuits remaining as skipped
   • test_missing_prompt_file_short_circuits_pipeline
   • test_empty_prompt_file_short_circuits_pipeline
   • test_tags_failure_does_not_short_circuit_pipeline
5. Idempotent re-run
   • test_idempotent_dry_run_invocations_produce_equivalent_results
6. dry_run=True — no file/state writes, dry_run status reported
   • test_dry_run_does_not_write_to_prompt_file
   • test_dry_run_does_not_call_clear_run_report
   • test_dry_run_does_not_call_save_fingerprint
   • test_dry_run_passes_dry_run_to_architecture_call
7. repo_root resolution — walk up to find .git / .pddrc / pyproject.toml
   • test_repo_root_inferred_from_pddrc_marker
   • test_repo_root_explicit_param_is_used
8. architecture_path resolution — uses find_architecture_for_project;
   skipped with reason "no architecture.json found" if none
   • test_architecture_skipped_when_no_arch_file
   • test_find_architecture_called_when_arch_path_is_none
   • test_explicit_architecture_path_used_when_provided
9. Multi-language compatibility — tag generation uses architecture-derived
   primitive (no language-specific AST). Behavior is identical for any
   language stem.
   • test_tag_generation_works_for_non_python_language
10. Logging — Rich Console with custom theme; each stage logged on entry and
    exit; failure line names the stage.
    • test_each_stage_logged_on_entry_and_exit
    • test_failure_log_line_contains_failed_stage_name
11. No regeneration side effects — must not call regeneration primitives.
    • test_no_regeneration_primitives_invoked
12. No partial writes — tags refresh is atomic.
    • test_tag_refresh_is_atomic_temp_then_rename

Stage-specific behavior:
• Tags stage:
   - test_tags_stage_preserves_existing_pdd_tags
   - test_tags_stage_prepends_arch_tags_when_missing
   - test_tags_stage_dry_run_does_not_write
• Architecture stage:
   - test_architecture_stage_forwards_refreshed_prompt_content_override
   - test_architecture_stage_handles_update_returning_failure
   - test_architecture_stage_skipped_with_correct_reason
• Run report stage:
   - test_run_report_clears_via_clear_run_report
   - test_run_report_skipped_when_identity_cannot_be_inferred
• Fingerprint stage:
   - test_fingerprint_gated_on_no_prior_failure
   - test_fingerprint_runs_last_after_other_stages
   - test_fingerprint_dry_run_does_not_persist
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path
from typing import Any, Dict, List
from unittest.mock import patch, MagicMock

import pytest

# Ensure the local pdd package wins over any site-installed copy.
_REPO_ROOT = Path(__file__).resolve().parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from pdd import metadata_sync as ms
from pdd.metadata_sync import (
    MetadataSyncResult,
    StageStatus,
    STAGE_ORDER,
    run_metadata_sync,
)


# ---------------------------------------------------------------------------
# Helpers / fixtures
# ---------------------------------------------------------------------------

PROMPT_WITH_TAGS = (
    "<pdd-reason>example reason</pdd-reason>\n"
    "<pdd-interface>{\"type\": \"module\", \"module\": {\"functions\": []}}</pdd-interface>\n"
    "<pdd-dependency>some_dep_python.prompt</pdd-dependency>\n"
    "\n"
    "% body content here\n"
)

PROMPT_NO_TAGS = "% just a body, no pdd tags here\n"


def _make_workspace(tmp_path: Path, prompt_text: str = PROMPT_WITH_TAGS,
                    prompt_name: str = "demo_python.prompt") -> Dict[str, Path]:
    """Build a workspace with .pddrc + prompts/<name>; return useful paths."""
    (tmp_path / ".pddrc").write_text("# marker\n", encoding="utf-8")
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    prompt_path = prompts / prompt_name
    prompt_path.write_text(prompt_text, encoding="utf-8")
    return {
        "repo_root": tmp_path,
        "prompts_dir": prompts,
        "prompt_path": prompt_path,
    }


def _arch_update_ok(updated: bool = False, changes: Dict[str, Any] | None = None) -> Dict[str, Any]:
    return {
        "success": True,
        "updated": updated,
        "changes": changes or {},
        "error": None,
    }


# ---------------------------------------------------------------------------
# Requirement 1 — entry point + return type
# ---------------------------------------------------------------------------

def test_run_metadata_sync_signature_returns_result_type(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    result = run_metadata_sync(ws["prompt_path"], dry_run=True)
    assert isinstance(result, MetadataSyncResult)
    assert result.prompt_path == ws["prompt_path"]
    assert result.code_path is None
    assert result.dry_run is True


# ---------------------------------------------------------------------------
# Requirement 2 — fixed pipeline order
# ---------------------------------------------------------------------------

def test_stage_pipeline_runs_in_fixed_order(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    call_order: List[str] = []

    def _enter(stage: str) -> None:
        call_order.append(stage)

    with patch.object(ms, "_stage_log_enter", side_effect=_enter):
        run_metadata_sync(ws["prompt_path"], dry_run=True)
    assert call_order == ["prompt", "tags", "architecture", "run_report", "fingerprint"]
    assert STAGE_ORDER == ["prompt", "tags", "architecture", "run_report", "fingerprint"]


# ---------------------------------------------------------------------------
# Requirement 3 — result type fields + properties
# ---------------------------------------------------------------------------

def test_result_is_pydantic_model_with_expected_fields(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    result = run_metadata_sync(ws["prompt_path"], code_path=tmp_path / "code.py", dry_run=True)
    dumped = result.model_dump()
    assert set(dumped.keys()) == {"prompt_path", "code_path", "dry_run", "stages"}
    assert set(dumped["stages"].keys()) == {"prompt", "tags", "architecture", "run_report", "fingerprint"}
    for stage in dumped["stages"].values():
        assert set(stage.keys()) == {"status", "reason", "detail"}


def test_ok_property_true_when_all_ok() -> None:
    r = MetadataSyncResult(prompt_path=Path("/x"))
    for name in STAGE_ORDER:
        r.stages[name] = StageStatus(status="ok")
    assert r.ok is True
    assert r.failing_stage is None


def test_ok_property_true_with_dry_run_stages() -> None:
    r = MetadataSyncResult(prompt_path=Path("/x"), dry_run=True)
    for name in STAGE_ORDER:
        r.stages[name] = StageStatus(status="dry_run")
    assert r.ok is True


def test_ok_property_false_when_any_stage_failed() -> None:
    r = MetadataSyncResult(prompt_path=Path("/x"))
    r.stages["prompt"] = StageStatus(status="ok")
    r.stages["tags"] = StageStatus(status="failed", reason="boom")
    r.stages["architecture"] = StageStatus(status="ok")
    r.stages["run_report"] = StageStatus(status="ok")
    r.stages["fingerprint"] = StageStatus(status="skipped")
    assert r.ok is False


def test_failing_stage_returns_first_failed_stage_name() -> None:
    r = MetadataSyncResult(prompt_path=Path("/x"))
    r.stages["prompt"] = StageStatus(status="ok")
    r.stages["tags"] = StageStatus(status="failed", reason="boom1")
    r.stages["architecture"] = StageStatus(status="failed", reason="boom2")
    r.stages["run_report"] = StageStatus(status="ok")
    r.stages["fingerprint"] = StageStatus(status="skipped")
    # 'tags' comes before 'architecture' in STAGE_ORDER
    assert r.failing_stage == "tags"


def test_failing_stage_returns_none_when_no_failure() -> None:
    r = MetadataSyncResult(prompt_path=Path("/x"))
    for name in STAGE_ORDER:
        r.stages[name] = StageStatus(status="ok")
    assert r.failing_stage is None


# ---------------------------------------------------------------------------
# Requirement 4 — fail-soft / prompt short-circuit
# ---------------------------------------------------------------------------

def test_missing_prompt_file_short_circuits_pipeline(tmp_path: Path) -> None:
    (tmp_path / ".pddrc").write_text("# marker\n", encoding="utf-8")
    missing = tmp_path / "prompts" / "nope_python.prompt"
    (tmp_path / "prompts").mkdir()

    result = run_metadata_sync(missing, dry_run=True)
    assert result.failing_stage == "prompt"
    assert result.ok is False
    assert result.stages["prompt"].status == "failed"
    for stage in ["tags", "architecture", "run_report", "fingerprint"]:
        assert result.stages[stage].status == "skipped", f"{stage} should be skipped"
        assert "prompt stage failed" in (result.stages[stage].reason or "")


def test_empty_prompt_file_short_circuits_pipeline(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path, prompt_text="")
    result = run_metadata_sync(ws["prompt_path"], dry_run=True)
    assert result.failing_stage == "prompt"
    assert result.stages["prompt"].status == "failed"
    assert "empty" in (result.stages["prompt"].reason or "").lower()
    for stage in ["tags", "architecture", "run_report", "fingerprint"]:
        assert result.stages[stage].status == "skipped"


def test_tags_failure_does_not_short_circuit_pipeline(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    with patch.object(ms, "parse_prompt_tags", side_effect=RuntimeError("tag parse boom")), \
         patch.object(ms, "_refresh_tags_content", side_effect=RuntimeError("tag boom")):
        result = run_metadata_sync(ws["prompt_path"], dry_run=True)
    assert result.stages["tags"].status == "failed"
    # Architecture, run_report should still execute (not skipped due to prompt fail)
    assert result.stages["architecture"].status in ("dry_run", "ok", "skipped")
    assert result.stages["run_report"].status in ("dry_run", "ok", "skipped")
    # Fingerprint MUST be skipped because tags failed (gated)
    assert result.stages["fingerprint"].status == "skipped"
    assert "tags" in (result.stages["fingerprint"].reason or "")


# ---------------------------------------------------------------------------
# Requirement 5 — idempotent
# ---------------------------------------------------------------------------

def test_idempotent_dry_run_invocations_produce_equivalent_results(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    r1 = run_metadata_sync(ws["prompt_path"], dry_run=True)
    r2 = run_metadata_sync(ws["prompt_path"], dry_run=True)
    for name in STAGE_ORDER:
        assert r1.stages[name].status == r2.stages[name].status, f"{name} differs"


# ---------------------------------------------------------------------------
# Requirement 6 — dry_run behavior
# ---------------------------------------------------------------------------

def test_dry_run_does_not_write_to_prompt_file(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path, prompt_text=PROMPT_NO_TAGS)
    original = ws["prompt_path"].read_text(encoding="utf-8")
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps({
        "modules": [
            {"prompt": "demo_python.prompt", "reason": "seed reason", "dependencies": ["x.prompt"]}
        ]
    }), encoding="utf-8")
    with patch.object(ms, "update_architecture_from_prompt", return_value=_arch_update_ok()), \
         patch.object(ms, "clear_run_report") as mock_clear, \
         patch.object(ms, "save_fingerprint") as mock_save:
        run_metadata_sync(ws["prompt_path"], dry_run=True, architecture_path=arch_path)
    assert ws["prompt_path"].read_text(encoding="utf-8") == original
    mock_clear.assert_not_called()
    mock_save.assert_not_called()


def test_dry_run_does_not_call_clear_run_report(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    with patch.object(ms, "clear_run_report") as mock_clear:
        run_metadata_sync(ws["prompt_path"], dry_run=True)
    mock_clear.assert_not_called()


def test_dry_run_does_not_call_save_fingerprint(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    with patch.object(ms, "save_fingerprint") as mock_save:
        run_metadata_sync(ws["prompt_path"], dry_run=True)
    mock_save.assert_not_called()


def test_dry_run_passes_dry_run_to_architecture_call(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps({"modules": []}), encoding="utf-8")
    with patch.object(ms, "update_architecture_from_prompt", return_value=_arch_update_ok()) as mock_upd:
        run_metadata_sync(ws["prompt_path"], dry_run=True, architecture_path=arch_path)
    assert mock_upd.called
    _, kwargs = mock_upd.call_args
    assert kwargs["dry_run"] is True


# ---------------------------------------------------------------------------
# Requirement 7 — repo_root resolution
# ---------------------------------------------------------------------------

def test_repo_root_inferred_from_pddrc_marker(tmp_path: Path) -> None:
    # Build deep tree with .pddrc at top.
    (tmp_path / ".pddrc").write_text("", encoding="utf-8")
    deep = tmp_path / "a" / "b" / "c"
    deep.mkdir(parents=True)
    resolved = ms._resolve_repo_root(deep / "prompt.prompt")
    assert resolved == tmp_path.resolve()


def test_repo_root_explicit_param_is_used(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    other_root = tmp_path / "other"
    other_root.mkdir()
    # Drive find_architecture_for_project off the explicit repo_root.
    with patch.object(ms, "find_architecture_for_project", return_value=[]) as mock_find:
        run_metadata_sync(ws["prompt_path"], dry_run=True, repo_root=other_root)
    mock_find.assert_called_once()
    called_with = mock_find.call_args[0][0]
    assert Path(called_with).resolve() == other_root.resolve()


# ---------------------------------------------------------------------------
# Requirement 8 — architecture_path resolution
# ---------------------------------------------------------------------------

def test_architecture_skipped_when_no_arch_file(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    with patch.object(ms, "find_architecture_for_project", return_value=[]):
        result = run_metadata_sync(ws["prompt_path"], dry_run=True)
    assert result.stages["architecture"].status == "skipped"
    assert result.stages["architecture"].reason == "no architecture.json found"


def test_find_architecture_called_when_arch_path_is_none(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    with patch.object(ms, "find_architecture_for_project", return_value=[]) as mock_find:
        run_metadata_sync(ws["prompt_path"], dry_run=True)
    assert mock_find.called


def test_explicit_architecture_path_used_when_provided(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps({"modules": []}), encoding="utf-8")
    with patch.object(ms, "find_architecture_for_project") as mock_find, \
         patch.object(ms, "update_architecture_from_prompt", return_value=_arch_update_ok()) as mock_upd:
        run_metadata_sync(ws["prompt_path"], dry_run=True, architecture_path=arch_path)
    mock_find.assert_not_called()
    assert mock_upd.called
    _, kwargs = mock_upd.call_args
    assert Path(kwargs["architecture_path"]) == arch_path


# ---------------------------------------------------------------------------
# Requirement 9 — multi-language compatibility
# ---------------------------------------------------------------------------

def test_tag_generation_works_for_non_python_language(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path, prompt_name="demo_typescript.prompt")
    result = run_metadata_sync(ws["prompt_path"], dry_run=True)
    # Identity inference picked the language correctly → run_report not skipped.
    assert result.stages["run_report"].status in ("dry_run", "ok"), \
        result.stages["run_report"]
    assert "typescript" in (result.stages["run_report"].detail or "")


# ---------------------------------------------------------------------------
# Requirement 10 — logging
# ---------------------------------------------------------------------------

def test_each_stage_logged_on_entry_and_exit(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    enter_calls: List[str] = []
    exit_calls: List[tuple] = []

    def _enter(stage: str) -> None:
        enter_calls.append(stage)

    def _exit(stage: str, status: str, detail: Any = None) -> None:
        exit_calls.append((stage, status))

    with patch.object(ms, "_stage_log_enter", side_effect=_enter), \
         patch.object(ms, "_stage_log_exit", side_effect=_exit):
        run_metadata_sync(ws["prompt_path"], dry_run=True)
    assert enter_calls == STAGE_ORDER
    # One exit per stage in order.
    exit_stages = [c[0] for c in exit_calls]
    assert exit_stages == STAGE_ORDER


def test_failure_log_line_contains_failed_stage_name(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path, prompt_text="")  # empty -> prompt fails
    exit_calls: List[tuple] = []

    def _exit(stage: str, status: str, detail: Any = None) -> None:
        exit_calls.append((stage, status))

    with patch.object(ms, "_stage_log_exit", side_effect=_exit):
        run_metadata_sync(ws["prompt_path"], dry_run=True)
    # The prompt exit call must report "failed" so operators see the stage name.
    assert ("prompt", "failed") in exit_calls


# ---------------------------------------------------------------------------
# Requirement 11 — no regeneration side effects
# ---------------------------------------------------------------------------

def test_no_regeneration_primitives_invoked(tmp_path: Path) -> None:
    # The module should only depend on the dependency primitives. Make sure
    # the module exposes none of the regeneration entry points.
    src = (Path(ms.__file__)).read_text(encoding="utf-8")
    for forbidden in [
        "pdd generate", "pdd example", "pdd test", "pdd sync",
        "subprocess.run", "subprocess.Popen", "requests.post", "requests.get",
        "os.system",
    ]:
        assert forbidden not in src, f"forbidden token found: {forbidden}"


# ---------------------------------------------------------------------------
# Requirement 12 — atomic tag refresh
# ---------------------------------------------------------------------------

def test_tag_refresh_is_atomic_temp_then_rename(tmp_path: Path) -> None:
    target = tmp_path / "f.txt"
    ms._atomic_write(target, "hello world")
    assert target.read_text(encoding="utf-8") == "hello world"
    # No leftover temp files (".f.txt.*")
    leftovers = [p.name for p in tmp_path.iterdir() if p.name != "f.txt"]
    assert leftovers == [], f"unexpected leftovers: {leftovers}"


# ---------------------------------------------------------------------------
# Stage-specific behavior — tags
# ---------------------------------------------------------------------------

def test_tags_stage_preserves_existing_pdd_tags(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)  # already has tags
    before = ws["prompt_path"].read_text(encoding="utf-8")
    with patch.object(ms, "save_fingerprint"), patch.object(ms, "clear_run_report"):
        result = run_metadata_sync(ws["prompt_path"], dry_run=False)
    after = ws["prompt_path"].read_text(encoding="utf-8")
    assert before == after
    assert result.stages["tags"].status == "ok"
    assert "preserved" in (result.stages["tags"].detail or "").lower() or \
           "tags" in (result.stages["tags"].detail or "").lower()


def test_tags_stage_prepends_arch_tags_when_missing(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path, prompt_text=PROMPT_NO_TAGS)
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps({
        "modules": [
            {"prompt": "demo_python.prompt", "reason": "seed reason",
             "dependencies": ["x.prompt"]}
        ]
    }), encoding="utf-8")
    with patch.object(ms, "update_architecture_from_prompt", return_value=_arch_update_ok()), \
         patch.object(ms, "clear_run_report"), \
         patch.object(ms, "save_fingerprint"):
        result = run_metadata_sync(ws["prompt_path"], dry_run=False, architecture_path=arch_path)
    after = ws["prompt_path"].read_text(encoding="utf-8")
    assert "<pdd-reason>" in after
    assert "seed reason" in after
    assert result.stages["tags"].status == "ok"


def test_tags_stage_dry_run_does_not_write(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path, prompt_text=PROMPT_NO_TAGS)
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps({
        "modules": [{"prompt": "demo_python.prompt", "reason": "r", "dependencies": []}]
    }), encoding="utf-8")
    original = ws["prompt_path"].read_text(encoding="utf-8")
    with patch.object(ms, "update_architecture_from_prompt", return_value=_arch_update_ok()):
        result = run_metadata_sync(ws["prompt_path"], dry_run=True, architecture_path=arch_path)
    assert ws["prompt_path"].read_text(encoding="utf-8") == original
    assert result.stages["tags"].status == "dry_run"


# ---------------------------------------------------------------------------
# Stage-specific behavior — architecture
# ---------------------------------------------------------------------------

def test_architecture_stage_forwards_refreshed_prompt_content_override(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path, prompt_text=PROMPT_NO_TAGS)
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps({
        "modules": [{"prompt": "demo_python.prompt", "reason": "seed reason",
                     "dependencies": ["x.prompt"]}]
    }), encoding="utf-8")
    captured = {}

    def _fake_upd(**kwargs: Any) -> Dict[str, Any]:
        captured.update(kwargs)
        return _arch_update_ok()

    with patch.object(ms, "update_architecture_from_prompt", side_effect=_fake_upd), \
         patch.object(ms, "clear_run_report"), \
         patch.object(ms, "save_fingerprint"):
        run_metadata_sync(ws["prompt_path"], dry_run=False, architecture_path=arch_path)
    # The architecture stage must receive the in-memory (possibly refreshed) prompt content.
    assert "prompt_content_override" in captured
    assert isinstance(captured["prompt_content_override"], str)
    # If tags were prepended, the override should reflect that.
    assert "<pdd-reason>" in captured["prompt_content_override"]
    # Forwards prompt filename and architecture_path too.
    assert captured["prompt_filename"] == "demo_python.prompt"
    assert Path(captured["architecture_path"]) == arch_path


def test_architecture_stage_handles_update_returning_failure(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps({"modules": []}), encoding="utf-8")
    with patch.object(ms, "update_architecture_from_prompt",
                       return_value={"success": False, "updated": False, "changes": {},
                                     "error": "kaboom"}), \
         patch.object(ms, "clear_run_report"), \
         patch.object(ms, "save_fingerprint") as mock_save:
        result = run_metadata_sync(ws["prompt_path"], dry_run=False, architecture_path=arch_path)
    assert result.stages["architecture"].status == "failed"
    assert "kaboom" in (result.stages["architecture"].reason or "")
    # Fingerprint gated → skipped.
    assert result.stages["fingerprint"].status == "skipped"
    mock_save.assert_not_called()


def test_architecture_stage_skipped_with_correct_reason(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    with patch.object(ms, "find_architecture_for_project", return_value=[]):
        result = run_metadata_sync(ws["prompt_path"], dry_run=True)
    assert result.stages["architecture"].status == "skipped"
    assert result.stages["architecture"].reason == "no architecture.json found"


# ---------------------------------------------------------------------------
# Stage-specific behavior — run_report
# ---------------------------------------------------------------------------

def test_run_report_clears_via_clear_run_report(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    with patch.object(ms, "clear_run_report") as mock_clear, \
         patch.object(ms, "save_fingerprint"):
        result = run_metadata_sync(ws["prompt_path"], dry_run=False)
    mock_clear.assert_called_once_with("demo", "python")
    assert result.stages["run_report"].status == "ok"


def test_run_report_skipped_when_identity_cannot_be_inferred(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    with patch.object(ms, "infer_module_identity", return_value=(None, None)), \
         patch.object(ms, "clear_run_report") as mock_clear, \
         patch.object(ms, "save_fingerprint") as mock_save:
        result = run_metadata_sync(ws["prompt_path"], dry_run=False)
    assert result.stages["run_report"].status == "skipped"
    mock_clear.assert_not_called()
    assert result.stages["fingerprint"].status == "skipped"
    mock_save.assert_not_called()


# ---------------------------------------------------------------------------
# Stage-specific behavior — fingerprint
# ---------------------------------------------------------------------------

def test_fingerprint_gated_on_no_prior_failure(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    # Force the architecture stage to fail.
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps({"modules": []}), encoding="utf-8")
    with patch.object(ms, "update_architecture_from_prompt",
                       side_effect=RuntimeError("arch boom")), \
         patch.object(ms, "clear_run_report"), \
         patch.object(ms, "save_fingerprint") as mock_save:
        result = run_metadata_sync(ws["prompt_path"], dry_run=False, architecture_path=arch_path)
    assert result.stages["architecture"].status == "failed"
    assert result.stages["fingerprint"].status == "skipped"
    assert "architecture" in (result.stages["fingerprint"].reason or "")
    mock_save.assert_not_called()


def test_fingerprint_runs_last_after_other_stages(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    call_order: List[str] = []

    def _record_clear(*a: Any, **kw: Any) -> None:
        call_order.append("clear_run_report")

    def _record_save(*a: Any, **kw: Any) -> None:
        call_order.append("save_fingerprint")

    with patch.object(ms, "clear_run_report", side_effect=_record_clear), \
         patch.object(ms, "save_fingerprint", side_effect=_record_save):
        run_metadata_sync(ws["prompt_path"], dry_run=False)
    # save_fingerprint must run AFTER clear_run_report.
    assert call_order == ["clear_run_report", "save_fingerprint"], call_order


def test_fingerprint_dry_run_does_not_persist(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    with patch.object(ms, "save_fingerprint") as mock_save:
        result = run_metadata_sync(ws["prompt_path"], dry_run=True)
    mock_save.assert_not_called()
    assert result.stages["fingerprint"].status == "dry_run"


# ---------------------------------------------------------------------------
# Regression: refreshed_prompt_content carries through on tags fail
# ---------------------------------------------------------------------------

def test_architecture_stage_runs_even_when_tags_failed(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps({"modules": []}), encoding="utf-8")
    with patch.object(ms, "_refresh_tags_content", side_effect=RuntimeError("tags boom")), \
         patch.object(ms, "update_architecture_from_prompt",
                       return_value=_arch_update_ok()) as mock_upd, \
         patch.object(ms, "clear_run_report"), \
         patch.object(ms, "save_fingerprint"):
        result = run_metadata_sync(ws["prompt_path"], dry_run=False, architecture_path=arch_path)
    assert result.stages["tags"].status == "failed"
    # Architecture stage still runs.
    mock_upd.assert_called_once()
    # Fingerprint blocked due to tags failure.
    assert result.stages["fingerprint"].status == "skipped"


# ---------------------------------------------------------------------------
# KeyboardInterrupt / SystemExit must propagate
# ---------------------------------------------------------------------------

def test_keyboard_interrupt_in_stage_propagates(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    with patch.object(ms, "parse_prompt_tags", side_effect=KeyboardInterrupt):
        with pytest.raises(KeyboardInterrupt):
            run_metadata_sync(ws["prompt_path"], dry_run=True)


def test_system_exit_in_stage_propagates(tmp_path: Path) -> None:
    ws = _make_workspace(tmp_path)
    with patch.object(ms, "parse_prompt_tags", side_effect=SystemExit(1)):
        with pytest.raises(SystemExit):
            run_metadata_sync(ws["prompt_path"], dry_run=True)
