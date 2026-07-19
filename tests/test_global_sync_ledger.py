"""Tests for deterministic global-sync evidence-ledger rendering."""
# pylint: disable=missing-function-docstring

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

from pdd.sync_core.global_sync_ledger import LedgerError, load_unique_yaml, run


ROOT = Path(__file__).resolve().parents[1]


def _write_fixture(tmp_path: Path, source_text: str | None = None) -> tuple[Path, Path, Path]:
    plan = tmp_path / "plan.md"
    source = tmp_path / "ledger_source.yaml"
    output = tmp_path / "ledger.yaml"
    plan.write_text(
        "# Plan\n\n<!-- global-sync-ledger-source: ledger_source.yaml -->\n",
        encoding="utf-8",
    )
    source.write_text(
        source_text
        or """schema_version: 4
controlling_plan: plan.md
status_vocabulary: [pending, in-progress, passed]
evidence_state_vocabulary: [pending, in-progress, passed]
required_gate_state_fields:
  - implemented
  - local_green
  - independently_reviewed
  - hosted_green
  - merged
  - released
  - deployed
  - certified
ledger_generation:
  status: in-progress
  source: ledger_source.yaml
  trust_boundary: reviewed-source-only
  evidence_state:
    implemented: passed
    local_green: passed
    independently_reviewed: pending
    hosted_green: pending
    merged: pending
    released: pending
    deployed: pending
    certified: pending
steps:
  - order: 1
    status: in-progress
    evidence_state:
      implemented: passed
      local_green: passed
      independently_reviewed: pending
      hosted_green: pending
      merged: pending
      released: pending
      deployed: pending
      certified: pending
    required_predicate: {}
""",
        encoding="utf-8",
    )
    return plan, source, output


def test_global_sync_ledger_generation_is_deterministic(tmp_path: Path) -> None:
    plan, source, output = _write_fixture(tmp_path)

    assert run(plan, output, source) == 0
    first = output.read_bytes()
    assert run(plan, output, source) == 0

    assert output.read_bytes() == first == source.read_bytes()


def test_global_sync_ledger_check_detects_drift_without_writing(tmp_path: Path, capsys) -> None:
    plan, source, output = _write_fixture(tmp_path)
    output.write_text("drifted\n", encoding="utf-8")

    assert run(plan, output, source, check=True) == 1

    assert output.read_text(encoding="utf-8") == "drifted\n"
    assert "global-sync ledger drift" in capsys.readouterr().err


@pytest.mark.parametrize(
    "source_text, expected",
    [
        ("schema_version: 4\nschema_version: 4\n", "duplicate YAML key"),
        ("schema_version: [\n", "cannot parse YAML input"),
        (
            "schema_version: 3\n",
            "ledger schema_version must be 4",
        ),
        (
            """schema_version: 4
status_vocabulary: [pending, in-progress, passed]
evidence_state_vocabulary: [pending, in-progress, passed]
required_gate_state_fields: [implemented]
ledger_generation:
  status: pending
  source: ledger_source.yaml
  trust_boundary: reviewed-source-only
steps: []
""",
            "required_gate_state_fields",
        ),
    ],
)
def test_global_sync_ledger_rejects_malformed_schema(
    tmp_path: Path, source_text: str, expected: str
) -> None:
    plan, source, output = _write_fixture(tmp_path, source_text)

    with pytest.raises(LedgerError, match=expected):
        run(plan, output, source)


def test_global_sync_ledger_rejects_missing_required_gate_state(tmp_path: Path) -> None:
    plan, source, output = _write_fixture(tmp_path)
    source.write_text(
        source.read_text(encoding="utf-8").replace("      certified: pending\n", ""),
        encoding="utf-8",
    )

    with pytest.raises(LedgerError, match="exactly the required gate states"):
        run(plan, output, source)


def test_global_sync_ledger_cli_generation_and_check(tmp_path: Path) -> None:
    plan, _source, output = _write_fixture(tmp_path)
    command = [
        sys.executable,
        "-m",
        "pdd.sync_core.global_sync_ledger",
        "--plan",
        str(plan),
        "--output",
        str(output),
    ]

    generated = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, check=False)
    checked = subprocess.run(
        [*command, "--check"], cwd=ROOT, text=True, capture_output=True, check=False
    )

    assert generated.returncode == 0
    assert "generated global-sync ledger" in generated.stdout
    assert checked.returncode == 0
    assert "global-sync ledger check passed" in checked.stdout


def test_global_sync_ledger_rejects_duplicate_yaml_keys() -> None:
    source = ROOT / "docs" / "global_sync_evidence_ledger.yaml"

    payload = load_unique_yaml(source)

    assert payload["schema_version"] == 4
