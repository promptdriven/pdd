"""Tests for deterministic, fail-closed global-sync ledger rendering."""
# pylint: disable=duplicate-code,missing-function-docstring

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest
import yaml

from pdd.sync_core.global_sync_ledger import (
    GitHubPromotionVerifier,
    LedgerError,
    load_unique_yaml,
    run,
    validate_ledger,
)


ROOT = Path(__file__).resolve().parents[1]
STATE_FIELDS = (
    "implemented",
    "local_green",
    "independently_reviewed",
    "hosted_green",
    "merged",
    "released",
    "deployed",
    "certified",
)
HEAD_SHA = "a" * 40
MERGE_SHA = "b" * 40


def _state(**overrides: str) -> dict[str, str]:
    return {field: overrides.get(field, "pending") for field in STATE_FIELDS}


def _payload() -> dict[str, object]:
    steps = [
        {
            "order": order,
            "status": "in-progress" if order == 1 else "pending",
            "evidence_state": _state(implemented="in-progress")
            if order == 1
            else _state(),
            "required_predicate": {"bounded": True},
        }
        for order in range(1, 11)
    ]
    return {
        "schema_version": 4,
        "controlling_plan": "plan.md",
        "status_vocabulary": ["pending", "in-progress", "passed"],
        "evidence_state_vocabulary": ["pending", "in-progress", "passed"],
        "required_gate_state_fields": list(STATE_FIELDS),
        "ledger_generation": {
            "status": "in-progress",
            "source": "ledger_source.yaml",
            "trust_boundary": "source-claims-require-protected-verification",
            "evidence_state": _state(implemented="in-progress"),
        },
        "promotion_bundles": {},
        "live_rebaseline": {"gates_required": 10, "gates_passed": 0},
        "steps": steps,
    }


def _promotion_bundle() -> dict[str, object]:
    return {
        "repository": "promptdriven/pdd",
        "repository_sha": MERGE_SHA,
        "head_sha": HEAD_SHA,
        "validation_command": "gh api repos/promptdriven/pdd/pulls/2214",
        "machine_predicate": {"name": "hosted-gate", "result": "passed"},
        "artifact_bindings": [
            {
                "kind": "github_actions_job",
                "url": "https://github.com/promptdriven/pdd/actions/runs/123/job/456",
            }
        ],
        "protected_verification": {"mode": "github-pr-checks", "pull_request": 2214},
    }


def _add_hosted_merge_claim(payload: dict[str, object]) -> None:
    steps = payload["steps"]
    assert isinstance(steps, list)
    step = steps[0]
    assert isinstance(step, dict)
    step["evidence_state"] = _state(
        implemented="passed",
        local_green="passed",
        independently_reviewed="passed",
        hosted_green="passed",
        merged="passed",
    )
    step["promotion_evidence"] = {
        field: "gate_1" for field in STATE_FIELDS[:5]
    }
    bundles = payload["promotion_bundles"]
    assert isinstance(bundles, dict)
    bundles["gate_1"] = _promotion_bundle()


def _write_fixture(
    tmp_path: Path, source_text: str | None = None, payload: dict[str, object] | None = None
) -> tuple[Path, Path, Path]:
    plan = tmp_path / "plan.md"
    source = tmp_path / "ledger_source.yaml"
    output = tmp_path / "ledger.yaml"
    plan.write_text(
        "# Plan\n\n<!-- global-sync-ledger-source: ledger_source.yaml -->\n",
        encoding="utf-8",
    )
    if source_text is None:
        source_text = yaml.safe_dump(payload or _payload(), sort_keys=False)
    source.write_text(source_text, encoding="utf-8")
    return plan, source, output


def _valid_github_responses() -> dict[str, dict[str, object]]:
    return {
        "/repos/promptdriven/pdd/pulls/2214": {
            "head": {"sha": HEAD_SHA},
            "merged": True,
            "merge_commit_sha": MERGE_SHA,
        },
        "/repos/promptdriven/pdd/actions/runs/123": {
            "head_sha": HEAD_SHA,
            "conclusion": "success",
        },
        "/repos/promptdriven/pdd/actions/jobs/456": {"conclusion": "success"},
    }


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
        ("schema_version: 3\n", "ledger schema_version must be 4"),
    ],
)
def test_global_sync_ledger_rejects_malformed_schema(
    tmp_path: Path, source_text: str, expected: str
) -> None:
    plan, source, output = _write_fixture(tmp_path, source_text)

    with pytest.raises(LedgerError, match=expected):
        run(plan, output, source)


def test_global_sync_ledger_rejects_all_passed_exploit(tmp_path: Path) -> None:
    payload = _payload()
    steps = payload["steps"]
    assert isinstance(steps, list)
    for step in steps:
        assert isinstance(step, dict)
        step["status"] = "passed"
        step["evidence_state"] = _state(**{field: "passed" for field in STATE_FIELDS})
        step["required_predicate"] = {}
    payload["live_rebaseline"] = {"gates_required": 10, "gates_passed": 10}
    plan, source, output = _write_fixture(tmp_path, payload=payload)

    with pytest.raises(LedgerError, match="required_predicate cannot be empty"):
        run(plan, output, source)


@pytest.mark.parametrize(
    "mutate, expected",
    [
        (
            lambda payload: payload["promotion_bundles"].clear(),
            "promotion_bundles must contain exactly the referenced promotion claims",
        ),
        (
            lambda payload: payload["promotion_bundles"]["gate_1"].update(
                {"repository_sha": "not-a-sha"}
            ),
            "repository_sha must be an exact",
        ),
        (
            lambda payload: payload["promotion_bundles"]["gate_1"].update(
                {"artifact_bindings": []}
            ),
            "requires an artifact binding",
        ),
        (
            lambda payload: payload["promotion_bundles"]["gate_1"][
                "artifact_bindings"
            ][0].update({"url": "https://example.invalid/fabricated"}),
            "GitHub artifact binding URL is malformed",
        ),
    ],
)
def test_global_sync_ledger_rejects_incomplete_promotion_bundle(
    tmp_path: Path, mutate, expected: str
) -> None:
    payload = _payload()
    _add_hosted_merge_claim(payload)
    mutate(payload)
    plan, source, output = _write_fixture(tmp_path, payload=payload)

    with pytest.raises(LedgerError, match=expected):
        run(plan, output, source)


def test_global_sync_ledger_rejects_passed_gate_with_incomplete_lifecycle(
    tmp_path: Path,
) -> None:
    payload = _payload()
    steps = payload["steps"]
    assert isinstance(steps, list)
    step = steps[0]
    assert isinstance(step, dict)
    step["status"] = "passed"
    step["required_predicate"] = {"machine": True}
    plan, source, output = _write_fixture(tmp_path, payload=payload)

    with pytest.raises(LedgerError, match="cannot pass before every lifecycle state"):
        run(plan, output, source)


def test_global_sync_ledger_rejects_noncanonical_gate_order(tmp_path: Path) -> None:
    payload = _payload()
    steps = payload["steps"]
    assert isinstance(steps, list)
    step = steps[1]
    assert isinstance(step, dict)
    step["order"] = 9
    plan, source, output = _write_fixture(tmp_path, payload=payload)

    with pytest.raises(LedgerError, match="stable order 2"):
        run(plan, output, source)


def test_global_sync_ledger_rejects_missing_required_gate_state(tmp_path: Path) -> None:
    payload = _payload()
    generation = payload["ledger_generation"]
    assert isinstance(generation, dict)
    state = generation["evidence_state"]
    assert isinstance(state, dict)
    state.pop("certified")
    plan, source, output = _write_fixture(tmp_path, payload=payload)

    with pytest.raises(LedgerError, match="exactly the required gate states"):
        run(plan, output, source)


def test_global_sync_ledger_rejects_mismatched_remote_metadata(tmp_path: Path, monkeypatch) -> None:
    payload = _payload()
    _add_hosted_merge_claim(payload)
    plan, source, _output = _write_fixture(tmp_path, payload=payload)
    responses = _valid_github_responses()
    responses["/repos/promptdriven/pdd/pulls/2214"]["head"] = {"sha": "c" * 40}
    verifier = GitHubPromotionVerifier()
    monkeypatch.setattr(verifier, "_get", responses.__getitem__)

    with pytest.raises(LedgerError, match="head SHA does not match"):
        validate_ledger(
            load_unique_yaml(source), plan, source, verify_remote=True, promotion_verifier=verifier
        )


def test_global_sync_ledger_accepts_valid_mocked_remote_hosted_merge(
    tmp_path: Path, monkeypatch
) -> None:
    payload = _payload()
    _add_hosted_merge_claim(payload)
    plan, source, _output = _write_fixture(tmp_path, payload=payload)
    verifier = GitHubPromotionVerifier()
    monkeypatch.setattr(verifier, "_get", _valid_github_responses().__getitem__)

    validate_ledger(
        load_unique_yaml(source), plan, source, verify_remote=True, promotion_verifier=verifier
    )


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
    payload = load_unique_yaml(ROOT / "docs" / "global_sync_evidence_ledger.yaml")

    assert payload["schema_version"] == 4
