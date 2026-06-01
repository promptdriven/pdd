"""Integration-style tests for generate grounding evidence."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import MagicMock, patch

import jsonschema
import pytest
from click.testing import CliRunner

from pdd.commands.generate import generate


def _schema() -> dict:
    schema_path = Path(__file__).parents[1] / "pdd" / "schemas" / "evidence_manifest.schema.json"
    return json.loads(schema_path.read_text(encoding="utf-8"))


@pytest.mark.timeout(60)
def test_generate_cloud_evidence_writes_grounding_block(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.chdir(tmp_path)
    prompt = tmp_path / "payments_python.prompt"
    output = tmp_path / "src" / "payments.py"
    prompt.parent.mkdir(parents=True, exist_ok=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    prompt.write_text("Generate payments.\n", encoding="utf-8")

    cloud_response = MagicMock()
    cloud_response.status_code = 200
    cloud_response.json.return_value = {
        "generatedCode": "def pay():\n    return True\n",
        "totalCost": 0.05,
        "modelName": "cloud-model",
        "examplesUsed": [
            {
                "slug": "payments",
                "promptSha256": "abc",
                "similarity": 0.9,
                "source": "cloud-history",
            }
        ],
    }

    def fake_code_generator_main(ctx, prompt_file, output, **kwargs):  # type: ignore[no-untyped-def]
        from pdd.grounding_provenance import (
            build_grounding_metadata,
            stash_grounding_overrides_on_ctx,
        )

        stash_grounding_overrides_on_ctx(ctx.obj, "Generate payments.\n")
        if isinstance(ctx.obj, dict):
            ctx.obj["last_grounding"] = build_grounding_metadata(
                mode="cloud",
                examples_used=cloud_response.json.return_value["examplesUsed"],
                grounding_overrides=ctx.obj.get("grounding_overrides"),
                reviewed=False,
            )
        return ("def pay():\n    return True\n", False, 0.05, "cloud-model")

    with patch("pdd.commands.generate.code_generator_main", side_effect=fake_code_generator_main):
        result = CliRunner().invoke(
            generate,
            [str(prompt), "--output", str(output), "--evidence"],
            obj={"temperature": 0.0, "quiet": True},
        )

    assert result.exit_code == 0, result.output
    latest = tmp_path / ".pdd" / "evidence" / "devunits" / "payments.latest.json"
    manifest = json.loads(latest.read_text(encoding="utf-8"))
    grounding = manifest["generation"]["grounding"]
    assert grounding["mode"] == "cloud"
    assert grounding["selected_examples"][0]["module"] == "payments"
    assert manifest["schema_version"] == 2
    jsonschema.validate(instance=manifest, schema=_schema())


@pytest.mark.timeout(60)
def test_generate_with_verbose_ctx_writes_schema_valid_grounding(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Mocked cloud generate with verbose ctx still writes generation.grounding."""
    monkeypatch.chdir(tmp_path)
    prompt = tmp_path / "payments_python.prompt"
    output = tmp_path / "src" / "payments.py"
    prompt.parent.mkdir(parents=True, exist_ok=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    prompt.write_text("Generate payments.\n", encoding="utf-8")

    def fake_code_generator_main(ctx, prompt_file, output, **kwargs):  # type: ignore[no-untyped-def]
        from pdd.grounding_provenance import build_grounding_metadata

        if (ctx.obj or {}).get("verbose"):
            print("[verbose] grounding examples: payments", file=__import__("sys").stderr)
        if isinstance(ctx.obj, dict):
            ctx.obj["last_grounding"] = build_grounding_metadata(
                mode="cloud",
                examples_used=[{"slug": "payments", "similarity": 0.95}],
            )
        return ("def pay():\n    return 1\n", False, 0.02, "cloud-model")

    with patch("pdd.commands.generate.code_generator_main", side_effect=fake_code_generator_main):
        result = CliRunner().invoke(
            generate,
            [str(prompt), "--output", str(output), "--evidence"],
            obj={"temperature": 0.0, "quiet": False, "verbose": True},
        )

    assert result.exit_code == 0, result.output
    manifest = json.loads(
        (tmp_path / ".pdd" / "evidence" / "devunits" / "payments.latest.json").read_text(
            encoding="utf-8"
        )
    )
    jsonschema.validate(instance=manifest, schema=_schema())
    assert manifest["generation"]["grounding"]["mode"] == "cloud"
    assert manifest["generation"]["grounding"]["selected_examples"][0]["module"] == "payments"
