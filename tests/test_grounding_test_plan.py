"""Automated coverage for PR #1286 / issue #827 test-plan checklist items."""
from __future__ import annotations

import inspect
import json
from pathlib import Path
from typing import Any
from unittest.mock import MagicMock, patch

import jsonschema
import pytest
from click.testing import CliRunner

from pdd.commands.generate import generate
from pdd.evidence_manifest import write_evidence_manifest
from pdd.grounding_policy import check, load_policy
from pdd.grounding_provenance import (
    build_grounding_metadata,
    review_grounding_examples_interactive,
    reviewed_from_decisions,
    stash_grounding_overrides_on_ctx,
)


def _schema() -> dict[str, Any]:
    schema_path = Path(__file__).parents[1] / "pdd" / "schemas" / "evidence_manifest.schema.json"
    return json.loads(schema_path.read_text(encoding="utf-8"))


def test_grounding_modules_expose_prompt_contract_surface() -> None:
    """Hand-written modules match the public API described in grounding prompts."""
    from pdd import evidence_manifest, grounding_policy, grounding_provenance

    assert inspect.isfunction(grounding_policy.load_policy)
    assert inspect.isfunction(grounding_policy.check)
    assert inspect.isfunction(grounding_provenance.build_grounding_metadata)
    assert inspect.isfunction(grounding_provenance.extract_grounding_overrides)
    assert inspect.isfunction(evidence_manifest.write_evidence_manifest)
    assert inspect.isfunction(evidence_manifest.grounding_kwargs_from_ctx)


def test_policy_check_on_written_evidence_manifest(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Future gate integration: load policy + latest evidence grounding block."""
    monkeypatch.chdir(tmp_path)
    policy_file = tmp_path / ".pdd" / "grounding_policy.yaml"
    policy_file.parent.mkdir(parents=True)
    policy_file.write_text(
        """
grounding:
  require_review_for_critical_modules: true
  require_pinned_examples_for:
    - payments
""",
        encoding="utf-8",
    )

    prompt = tmp_path / "prompts" / "payments_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("Generate payments.\n", encoding="utf-8")

    grounding = {
        "mode": "cloud",
        "selected_examples": [{"module": "payments", "prompt_sha256": "abc"}],
        "pinned": ["payments"],
        "excluded": [],
        "reviewed": True,
    }
    manifest_path = write_evidence_manifest(
        command="pdd generate",
        prompt_file=prompt,
        project_root=tmp_path,
        grounding=grounding,
        reviewed=True,
    )
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    policy = load_policy()
    violations = check(policy, "payments", manifest["generation"]["grounding"])
    assert violations == []


def test_policy_check_flags_missing_review_on_critical_module(tmp_path: Path) -> None:
    policy = load_policy(str(tmp_path / "missing.yaml"))
    policy.require_review_for_critical_modules = True
    policy.require_pinned_examples_for = ["payments"]
    violations = check(
        policy,
        "payments",
        {"mode": "cloud", "pinned": ["payments"], "reviewed": False},
    )
    assert any(v.code == "grounding.review_required" for v in violations)


@pytest.mark.timeout(60)
def test_generate_pin_tags_appear_in_evidence_artifact(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.chdir(tmp_path)
    prompt = tmp_path / "payments_python.prompt"
    output = tmp_path / "src" / "payments.py"
    prompt.parent.mkdir(parents=True, exist_ok=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    prompt.write_text(
        "Use <pin>payments</pin> and skip <exclude>legacy</exclude>.\n",
        encoding="utf-8",
    )

    def fake_code_generator_main(ctx, prompt_file, output, **kwargs):  # type: ignore[no-untyped-def]
        text = Path(prompt_file).read_text(encoding="utf-8")
        stash_grounding_overrides_on_ctx(ctx.obj, text)
        if isinstance(ctx.obj, dict):
            ctx.obj["last_grounding"] = build_grounding_metadata(
                mode="cloud",
                examples_used=[{"slug": "payments"}],
                grounding_overrides=ctx.obj.get("grounding_overrides"),
            )
        return ("def pay():\n    pass\n", False, 0.01, "model")

    with patch("pdd.commands.generate.code_generator_main", side_effect=fake_code_generator_main):
        result = CliRunner().invoke(
            generate,
            [str(prompt), "--output", str(output), "--evidence"],
            obj={"temperature": 0.0, "quiet": True},
        )

    assert result.exit_code == 0, result.output
    manifest = json.loads(
        (tmp_path / ".pdd" / "evidence" / "devunits" / "payments.latest.json").read_text(
            encoding="utf-8"
        )
    )
    grounding = manifest["generation"]["grounding"]
    assert grounding["pinned"] == ["payments"]
    assert grounding["excluded"] == ["legacy"]
    jsonschema.validate(instance=manifest, schema=_schema())


@pytest.mark.timeout(60)
def test_generate_review_examples_records_reviewed_in_evidence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr("pdd.grounding_provenance.click.confirm", lambda *_, **__: True)

    prompt = tmp_path / "payments_python.prompt"
    output = tmp_path / "src" / "payments.py"
    prompt.parent.mkdir(parents=True, exist_ok=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    prompt.write_text("Generate payments.\n", encoding="utf-8")

    examples_used = [{"slug": "payments", "title": "Payments example"}]

    def fake_code_generator_main(ctx, prompt_file, output, **kwargs):  # type: ignore[no-untyped-def]
        obj = ctx.obj if isinstance(ctx.obj, dict) else {}
        if obj.get("grounding_review_decisions") is None:
            obj["grounding_review_decisions"] = []
        review_grounding_examples_interactive(
            examples_used, obj, quiet=True, force=False
        )
        stash_grounding_overrides_on_ctx(obj, Path(prompt_file).read_text(encoding="utf-8"))
        obj["last_grounding"] = build_grounding_metadata(
            mode="cloud",
            examples_used=examples_used,
            grounding_overrides=obj.get("grounding_overrides"),
            reviewed=reviewed_from_decisions(obj.get("grounding_review_decisions")),
        )
        return ("def pay():\n    pass\n", False, 0.01, "model")

    with patch("pdd.commands.generate.code_generator_main", side_effect=fake_code_generator_main):
        result = CliRunner().invoke(
            generate,
            [str(prompt), "--output", str(output), "--evidence"],
            obj={
                "temperature": 0.0,
                "quiet": True,
                "review_examples": True,
                "grounding_review_decisions": [],
            },
        )

    assert result.exit_code == 0, result.output
    manifest = json.loads(
        (tmp_path / ".pdd" / "evidence" / "devunits" / "payments.latest.json").read_text(
            encoding="utf-8"
        )
    )
    assert manifest["generation"]["grounding"]["reviewed"] is True
