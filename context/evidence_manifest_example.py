"""Minimal executable example for :mod:`pdd.evidence_manifest`.

The example writes a real schema-v2 receipt in an isolated temporary project,
then returns the decoded payload so callers can inspect the result without
leaving repository artifacts behind.
"""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path
from typing import Any

PROJECT_ROOT = Path(__file__).resolve().parents[1]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from pdd.evidence_manifest import SCHEMA_VERSION, write_evidence_manifest  # noqa: E402


def main() -> dict[str, Any]:
    """Create one isolated evidence receipt and return its decoded payload."""
    with tempfile.TemporaryDirectory(prefix="evidence_manifest_example_") as tmp:
        project = Path(tmp)
        prompt = project / "prompts" / "greeting_python.prompt"
        output = project / "pdd" / "greeting.py"
        prompt.parent.mkdir(parents=True)
        output.parent.mkdir(parents=True)
        prompt.write_text("Write a greeting function.\n", encoding="utf-8")
        output.write_text(
            "def greeting(name: str) -> str:\n"
            "    return f'Hello, {name}!'\n",
            encoding="utf-8",
        )

        manifest_path = write_evidence_manifest(
            command="pdd generate",
            prompt_file=prompt,
            output_files=[output],
            model="example-model",
            cost_usd=0.0,
            project_root=project,
        )
        payload = json.loads(manifest_path.read_text(encoding="utf-8"))

    assert payload["schema_version"] == SCHEMA_VERSION
    assert payload["outputs"][0]["path"] == "pdd/greeting.py"
    print(f"Evidence manifest example completed (schema v{SCHEMA_VERSION}).")
    return payload


if __name__ == "__main__":
    main()
