"""Integration-style tests for generate grounding evidence."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest
from click.testing import CliRunner

from pdd.commands.generate import generate


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
