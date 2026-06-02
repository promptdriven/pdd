"""Human-verifiable touchpoints for issue #830 / PR #1291.

Run:
  pytest -vv tests/test_issue_830_contract_summary_touchpoint.py
  ./examples/architecture_contract_summary_demo/run_demo.sh
"""
from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest

from pdd.architecture_sync import (
    sync_all_prompts_to_architecture,
    validate_contract_summary,
)
from pdd.evidence_manifest import write_evidence_manifest

REPO_ROOT = Path(__file__).resolve().parent.parent
DEMO_ROOT = REPO_ROOT / "examples" / "architecture_contract_summary_demo"


@pytest.fixture
def demo_workspace(tmp_path: Path) -> Path:
    """Copy the checked-in demo project into an isolated temp directory."""
    workspace = tmp_path / "demo"
    shutil.copytree(
        DEMO_ROOT,
        workspace,
        ignore=shutil.ignore_patterns(
            "__pycache__",
            "*.pyc",
            ".pdd/evidence/devunits/*.latest.json",
        ),
    )
    prompt = workspace / "prompts" / "refund_python.prompt"
    output = workspace / "src" / "refund.py"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("def refund():\n    pass\n", encoding="utf-8")
    write_evidence_manifest(
        command="pdd generate",
        prompt_file=prompt,
        output_files=[output],
        model="local-model",
        cost_usd=0.0,
        temperature=0.0,
        project_root=workspace,
    )
    return workspace


def test_touchpoint_demo_sync_writes_contract_summary(demo_workspace: Path) -> None:
    """Refund module gets contract_summary; legacy module stays without it."""
    prompts_dir = demo_workspace / "prompts"
    arch_path = demo_workspace / "architecture.json"

    result = sync_all_prompts_to_architecture(
        prompts_dir=prompts_dir,
        architecture_path=arch_path,
        dry_run=False,
    )

    assert result["success"] is True
    modules = {m["filename"]: m for m in json.loads(arch_path.read_text(encoding="utf-8"))}

    refund = modules["refund_python.prompt"]
    assert "contract_summary" in refund
    summary = refund["contract_summary"]
    assert "R1" in summary["rules"]
    assert "R2" in summary["rules"]
    assert "R2" in summary["critical"]
    assert "reads_payments" in summary["capabilities"]
    assert summary["evidence_status"] == "fresh"
    assert summary["coverage_status"] in ("partial", "story-only", "full")
    assert validate_contract_summary(summary) == []

    legacy = modules["legacy_python.prompt"]
    assert "contract_summary" not in legacy


def test_touchpoint_demo_dry_run_reports_summary(demo_workspace: Path) -> None:
    """Dry-run still returns per-module contract_summary in results."""
    result = sync_all_prompts_to_architecture(
        prompts_dir=demo_workspace / "prompts",
        architecture_path=demo_workspace / "architecture.json",
        dry_run=True,
    )
    refund_row = next(r for r in result["results"] if r["filename"] == "refund_python.prompt")
    assert refund_row["contract_summary"]["rules"]


def test_touchpoint_failed_story_coverage_is_partial(tmp_path: Path) -> None:
    """Story validation failures yield partial coverage_status, not none."""
    from pdd.architecture_sync import _extract_contract_summary

    prompts = tmp_path / "prompts"
    prompts.mkdir()
    stories = tmp_path / "user_stories"
    stories.mkdir()
    prompt = prompts / "mod_python.prompt"
    prompt.write_text(
        "<contract_rules>\nR1 - X\nMUST x.\n</contract_rules>\n",
        encoding="utf-8",
    )
    (stories / "story__bad.md").write_text(
        "## Covers\n- R1: x\n",
        encoding="utf-8",
    )
    summary, _ = _extract_contract_summary(prompt, tmp_path)
    assert summary["coverage_status"] == "partial"


def test_validate_contract_summary_rejects_invalid() -> None:
    errors = validate_contract_summary({"rules": "not-a-list"})
    assert errors


def test_touchpoint_nested_prompt_evidence_status_fresh(tmp_path: Path) -> None:
    """Nested modules slug evidence like production (frontend-page.latest.json)."""
    from pdd.architecture_sync import _extract_contract_summary

    root = tmp_path
    (root / ".pdd").mkdir()
    (root / "prompts" / "frontend").mkdir(parents=True)
    (root / "tests").mkdir()
    (root / "user_stories").mkdir()
    prompt = root / "prompts" / "frontend" / "page_python.prompt"
    prompt.write_text(
        "<contract_rules>\nR1 - Page\nThe system MUST render page.\n</contract_rules>\n",
        encoding="utf-8",
    )
    write_evidence_manifest(command="pdd generate", prompt_file=prompt, project_root=root)

    nested_wrong = root / ".pdd" / "evidence" / "devunits" / "frontend" / "page.latest.json"
    assert not nested_wrong.is_file()
    assert (root / ".pdd" / "evidence" / "devunits" / "frontend-page.latest.json").is_file()

    summary, _ = _extract_contract_summary(prompt, root)
    assert summary["evidence_status"] == "fresh"
