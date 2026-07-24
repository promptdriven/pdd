"""Tests for deterministic, fail-closed global-sync ledger rendering."""
# pylint: disable=duplicate-code,missing-function-docstring

from __future__ import annotations

import subprocess
import sys
from pathlib import Path
from urllib.parse import urlparse

import pytest
import yaml

from pdd.sync_core.global_sync_ledger import (
    GitHubPromotionVerifier,
    LedgerError,
    canonical_predicate_digest,
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
GITHUB_PR_CHECK_STATES = ("implemented", "hosted_green", "merged")
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
        "schema_version": 5,
        "controlling_plan": "plan.md",
        "status_vocabulary": ["pending", "in-progress", "passed"],
        "evidence_state_vocabulary": ["pending", "in-progress", "passed"],
        "required_gate_state_fields": list(STATE_FIELDS),
        "ledger_generation": {
            "status": "in-progress",
            "source": "ledger_source.yaml",
            "trust_boundary": "source-claims-require-protected-verification",
            "evidence_state": _state(implemented="in-progress"),
            "required_predicate": {"generator": True},
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
        "subject": {
            "record": {"kind": "gate", "order": 1},
            "states": list(GITHUB_PR_CHECK_STATES),
            "required_predicate_sha256": canonical_predicate_digest({"bounded": True}),
            "record_claims": {
                "repository": "promptdriven/pdd",
                "exact_repository_sha": MERGE_SHA,
                "reviewed_head_sha": HEAD_SHA,
                "merge_sha": MERGE_SHA,
            },
        },
        "validation_command": (
            "gh api repos/promptdriven/pdd/pulls/2214 "
            "--jq '.head.sha, .merged, .merge_commit_sha, .base.repo.full_name, .base.ref'"
        ),
        "machine_predicate": {
            "name": "hosted-gate",
            "result": "passed",
            "binding_url": "https://github.com/promptdriven/pdd/actions/runs/123/job/456",
        },
        "artifact_bindings": [
            {
                "kind": "github_actions_job",
                "url": "https://github.com/promptdriven/pdd/actions/runs/123/job/456",
                "expected": {
                    "job_name": "hosted-gate",
                    "workflow_id": 1,
                    "workflow_name": "Hosted Gate",
                    "workflow_path": ".github/workflows/hosted-gate.yml",
                    "event": "pull_request",
                },
            }
        ],
        "protected_verification": {
            "mode": "github-pr-checks",
            "pull_request": 2214,
            "base_repository": "promptdriven/pdd",
            "base_ref": "main",
        },
    }


def _add_hosted_merge_claim(payload: dict[str, object]) -> None:
    steps = payload["steps"]
    assert isinstance(steps, list)
    step = steps[0]
    assert isinstance(step, dict)
    step["evidence_state"] = _state(
        implemented="passed",
        local_green="in-progress",
        independently_reviewed="in-progress",
        hosted_green="passed",
        merged="passed",
    )
    step["repository"] = "promptdriven/pdd"
    step["exact_repository_sha"] = MERGE_SHA
    step["reviewed_head_sha"] = HEAD_SHA
    step["merge_sha"] = MERGE_SHA
    step["promotion_evidence"] = {field: "gate_1" for field in GITHUB_PR_CHECK_STATES}
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
            "base": {"repo": {"full_name": "promptdriven/pdd"}, "ref": "main"},
            "merged": True,
            "merge_commit_sha": MERGE_SHA,
        },
        "/repos/promptdriven/pdd/actions/runs/123": {
            "workflow_id": 1,
            "name": "Hosted Gate",
            "path": ".github/workflows/hosted-gate.yml",
            "event": "pull_request",
            "head_sha": HEAD_SHA,
            "conclusion": "success",
        },
        "/repos/promptdriven/pdd/actions/jobs/456": {
            "conclusion": "success",
            "run_id": 123,
            "head_sha": HEAD_SHA,
            "name": "hosted-gate",
            "workflow_name": "Hosted Gate",
        },
    }


def _current_source_promotion_responses(  # pylint: disable=too-many-locals
    payload: dict[str, object],
) -> dict[str, dict[str, object]]:
    """Build exact GitHub API responses for every source promotion bundle."""
    bundles = payload["promotion_bundles"]
    assert isinstance(bundles, dict)
    responses: dict[str, dict[str, object]] = {}

    def add_response(path: str, response: dict[str, object]) -> None:
        existing = responses.get(path)
        assert existing is None or existing == response
        responses[path] = response

    def action_run_response(expected: dict[str, object], head_sha: str) -> dict[str, object]:
        return {
            "workflow_id": expected["workflow_id"],
            "name": expected["workflow_name"],
            "path": expected["workflow_path"],
            "event": expected["event"],
            "head_sha": head_sha,
            "conclusion": "success",
        }

    for bundle in bundles.values():
        assert isinstance(bundle, dict)
        repository = bundle["repository"]
        head_sha = bundle["head_sha"]
        repository_sha = bundle["repository_sha"]
        verification = bundle["protected_verification"]
        assert isinstance(repository, str)
        assert isinstance(head_sha, str)
        assert isinstance(repository_sha, str)
        assert isinstance(verification, dict)
        pull_request = verification["pull_request"]
        base_repository = verification["base_repository"]
        base_ref = verification["base_ref"]
        assert isinstance(pull_request, int)
        assert isinstance(base_repository, str)
        assert isinstance(base_ref, str)
        add_response(
            f"/repos/{repository}/pulls/{pull_request}",
            {
                "head": {"sha": head_sha},
                "base": {"repo": {"full_name": base_repository}, "ref": base_ref},
                "merged": True,
                "merge_commit_sha": repository_sha,
            },
        )

        bindings = bundle["artifact_bindings"]
        assert isinstance(bindings, list)
        for binding in bindings:
            assert isinstance(binding, dict)
            kind = binding["kind"]
            artifact_url = binding["url"]
            expected = binding["expected"]
            assert isinstance(kind, str)
            assert isinstance(artifact_url, str)
            assert isinstance(expected, dict)
            path = urlparse(artifact_url).path
            parts = path.strip("/").split("/")
            assert "/".join(parts[:2]) == repository
            if kind == "github_actions_run":
                run_id = parts[-1]
                add_response(
                    f"/repos/{repository}/actions/runs/{run_id}",
                    action_run_response(expected, head_sha),
                )
            elif kind == "github_actions_job":
                run_id, job_id = parts[-3], parts[-1]
                add_response(
                    f"/repos/{repository}/actions/runs/{run_id}",
                    action_run_response(expected, head_sha),
                )
                add_response(
                    f"/repos/{repository}/actions/jobs/{job_id}",
                    {
                        "conclusion": "success",
                        "run_id": int(run_id),
                        "head_sha": head_sha,
                        "name": expected["job_name"],
                        "workflow_name": expected["workflow_name"],
                    },
                )
            elif kind == "github_check_run":
                check_id = parts[-1]
                add_response(
                    f"/repos/{repository}/check-runs/{check_id}",
                    {
                        "conclusion": "success",
                        "head_sha": head_sha,
                        "name": expected["check_name"],
                        "app": {
                            "id": expected["app_id"],
                            "slug": expected["app_slug"],
                            "owner": {"login": expected["app_owner"]},
                        },
                    },
                )
            else:
                pytest.fail(f"unexpected source artifact binding kind: {kind}")
    return responses


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
        ("schema_version: 5\nschema_version: 5\n", "duplicate YAML key"),
        ("schema_version: [\n", "cannot parse YAML input"),
        ("schema_version: 3\n", "ledger schema_version must be 5"),
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
        (
            lambda payload: payload["promotion_bundles"]["gate_1"].update(
                {"validation_command": "gh api repos/attacker/scratch/pulls/1"}
            ),
            "validation command must target the protected PR",
        ),
        (
            lambda payload: payload["promotion_bundles"]["gate_1"][
                "protected_verification"
            ].pop("base_ref"),
            "protected verification is malformed",
        ),
        (
            lambda payload: payload["promotion_bundles"]["gate_1"][
                "machine_predicate"
            ].update({"name": "unrelated-success"}),
            "machine predicate is not bound to an artifact",
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


def test_canonical_predicate_digest_is_deterministic_and_type_safe() -> None:
    assert canonical_predicate_digest({"a": [1, True], "b": None}) == (
        canonical_predicate_digest({"b": None, "a": [1, True]})
    )
    assert canonical_predicate_digest({"value": True}) != canonical_predicate_digest(
        {"value": "true"}
    )
    with pytest.raises(LedgerError, match="unsupported canonical value type float"):
        canonical_predicate_digest({"value": 1.5})


@pytest.mark.parametrize(
    "state, is_authorized",
    [
        ("implemented", True),
        ("hosted_green", True),
        ("merged", True),
        ("local_green", False),
        ("independently_reviewed", False),
        ("released", False),
        ("deployed", False),
        ("certified", False),
    ],
)
def test_github_pr_checks_authorization_matrix(
    tmp_path: Path, state: str, is_authorized: bool
) -> None:
    payload = _payload()
    _add_hosted_merge_claim(payload)
    step = payload["steps"][0]
    assert isinstance(step, dict)
    step["evidence_state"] = _state(**{state: "passed"})
    step["promotion_evidence"] = {state: "gate_1"}
    payload["promotion_bundles"]["gate_1"]["subject"]["states"] = [state]
    plan, source, output = _write_fixture(tmp_path, payload=payload)

    if is_authorized:
        assert run(plan, output, source) == 0
    else:
        with pytest.raises(LedgerError, match=f"cannot authorize states: {state}"):
            run(plan, output, source)


def test_github_pr_checks_rejects_self_consistent_terminal_expansion(
    tmp_path: Path,
) -> None:
    payload = _payload()
    _add_hosted_merge_claim(payload)
    step = payload["steps"][0]
    assert isinstance(step, dict)
    step["evidence_state"] = _state(**{field: "passed" for field in STATE_FIELDS})
    step["status"] = "passed"
    step["promotion_evidence"] = {
        **{field: "gate_1" for field in STATE_FIELDS},
        "status": "gate_1",
    }
    payload["promotion_bundles"]["gate_1"]["subject"]["states"] = [
        *STATE_FIELDS,
        "status",
    ]
    payload["live_rebaseline"]["gates_passed"] = 1
    plan, source, output = _write_fixture(tmp_path, payload=payload)

    with pytest.raises(LedgerError, match="mode 'github-pr-checks' cannot authorize states"):
        run(plan, output, source)


def test_global_sync_ledger_rejects_cross_gate_promotion_replay(tmp_path: Path) -> None:
    payload = _payload()
    _add_hosted_merge_claim(payload)
    steps = payload["steps"]
    assert isinstance(steps, list)
    gate_2 = steps[1]
    assert isinstance(gate_2, dict)
    gate_2.update(
        {
            "evidence_state": _state(**{field: "passed" for field in STATE_FIELDS[:5]}),
            "repository": "promptdriven/pdd",
            "exact_repository_sha": MERGE_SHA,
            "reviewed_head_sha": HEAD_SHA,
            "merge_sha": MERGE_SHA,
            "promotion_evidence": {field: "gate_1" for field in STATE_FIELDS[:5]},
        }
    )
    plan, source, output = _write_fixture(tmp_path, payload=payload)

    with pytest.raises(LedgerError, match="replayed across records or predicates"):
        run(plan, output, source)


def test_global_sync_ledger_rejects_state_absent_from_subject(tmp_path: Path) -> None:
    payload = _payload()
    _add_hosted_merge_claim(payload)
    step = payload["steps"][0]
    assert isinstance(step, dict)
    step["evidence_state"]["released"] = "passed"
    step["promotion_evidence"]["released"] = "gate_1"
    plan, source, output = _write_fixture(tmp_path, payload=payload)

    with pytest.raises(LedgerError, match="subject does not match its record"):
        run(plan, output, source)


def test_global_sync_ledger_rejects_changed_predicate_after_bundle_creation(
    tmp_path: Path,
) -> None:
    payload = _payload()
    _add_hosted_merge_claim(payload)
    step = payload["steps"][0]
    assert isinstance(step, dict)
    step["required_predicate"] = {"bounded": False}
    plan, source, output = _write_fixture(tmp_path, payload=payload)

    with pytest.raises(LedgerError, match="subject does not match its record"):
        run(plan, output, source)


def test_global_sync_ledger_rejects_unreferenced_promotion_bundle(tmp_path: Path) -> None:
    payload = _payload()
    _add_hosted_merge_claim(payload)
    payload["promotion_bundles"]["unreferenced"] = _promotion_bundle()
    plan, source, output = _write_fixture(tmp_path, payload=payload)

    with pytest.raises(LedgerError, match="exactly the referenced promotion claims"):
        run(plan, output, source)


@pytest.mark.parametrize("claim", ["exact_repository_sha", "reviewed_head_sha", "merge_sha"])
def test_global_sync_ledger_rejects_mismatched_record_claims(
    tmp_path: Path, claim: str
) -> None:
    payload = _payload()
    _add_hosted_merge_claim(payload)
    step = payload["steps"][0]
    assert isinstance(step, dict)
    changed_sha = "c" * 40
    step[claim] = changed_sha
    if claim == "merge_sha":
        step["exact_repository_sha"] = changed_sha
    elif claim == "exact_repository_sha":
        step["merge_sha"] = changed_sha
    plan, source, output = _write_fixture(tmp_path, payload=payload)

    with pytest.raises(LedgerError, match="subject does not match its record"):
        run(plan, output, source)


@pytest.mark.parametrize(
    "field, expected",
    [
        ("repository_sha", "repository_sha disagrees with subject"),
        ("head_sha", "head SHA disagrees with subject"),
    ],
)
def test_global_sync_ledger_rejects_mismatched_bundle_claims(
    tmp_path: Path, field: str, expected: str
) -> None:
    payload = _payload()
    _add_hosted_merge_claim(payload)
    payload["promotion_bundles"]["gate_1"][field] = "c" * 40
    plan, source, output = _write_fixture(tmp_path, payload=payload)

    with pytest.raises(LedgerError, match=expected):
        run(plan, output, source)


@pytest.mark.parametrize(
    "preceding_states, status",
    [
        (("released",), "in-progress"),
        (("released", "deployed"), "in-progress"),
        (("released", "deployed", "certified"), "in-progress"),
        (STATE_FIELDS, "passed"),
    ],
)
def test_global_sync_ledger_rejects_unapproved_terminal_state(
    tmp_path: Path, preceding_states: tuple[str, ...], status: str
) -> None:
    payload = _payload()
    _add_hosted_merge_claim(payload)
    step = payload["steps"][0]
    assert isinstance(step, dict)
    for state_name in preceding_states:
        step["evidence_state"][state_name] = "passed"
        step["promotion_evidence"][state_name] = "gate_1"
    step["status"] = status
    if status == "passed":
        step["promotion_evidence"]["status"] = "gate_1"
        payload["live_rebaseline"]["gates_passed"] = 1
    plan, source, output = _write_fixture(tmp_path, payload=payload)

    with pytest.raises(LedgerError, match="subject does not match its record"):
        run(plan, output, source)


@pytest.mark.parametrize(
    "mutate, expected",
    [
        (
            lambda subject: subject["states"].append("merged"),
            "subject states are malformed or duplicate",
        ),
        (
            lambda subject: subject["states"].append("released"),
            "cannot authorize states: released",
        ),
    ],
)
def test_global_sync_ledger_rejects_duplicate_or_overbroad_subject_states(
    tmp_path: Path, mutate, expected: str
) -> None:
    payload = _payload()
    _add_hosted_merge_claim(payload)
    subject = payload["promotion_bundles"]["gate_1"]["subject"]
    assert isinstance(subject, dict)
    mutate(subject)
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


@pytest.mark.parametrize(
    "field, value, expected",
    [
        ("run_id", 999, "action job run ID does not match"),
        ("head_sha", "c" * 40, "action job head SHA does not match"),
    ],
)
def test_global_sync_ledger_rejects_job_not_bound_to_run_and_head(
    tmp_path: Path, monkeypatch, field: str, value: object, expected: str
) -> None:
    payload = _payload()
    _add_hosted_merge_claim(payload)
    plan, source, _output = _write_fixture(tmp_path, payload=payload)
    responses = _valid_github_responses()
    responses["/repos/promptdriven/pdd/actions/jobs/456"][field] = value
    verifier = GitHubPromotionVerifier()
    monkeypatch.setattr(verifier, "_get", responses.__getitem__)

    with pytest.raises(LedgerError, match=expected):
        validate_ledger(
            load_unique_yaml(source), plan, source, verify_remote=True, promotion_verifier=verifier
        )


def test_global_sync_ledger_rejects_signed_digest_for_hosted_green(tmp_path: Path) -> None:
    """A candidate digest cannot substitute for remotely verifiable hosted evidence."""
    payload = _payload()
    _add_hosted_merge_claim(payload)
    bundle = payload["promotion_bundles"]["gate_1"]
    assert isinstance(bundle, dict)
    bundle["artifact_bindings"] = [
        {"kind": "signed_digest", "sha256": "a" * 64}
    ]
    plan, source, output = _write_fixture(tmp_path, payload=payload)

    with pytest.raises(LedgerError, match="not remotely verifiable"):
        run(plan, output, source)


@pytest.mark.parametrize(
    "case",
    [
        {
            "binding": {
                "kind": "github_actions_job",
                "url": "https://github.com/promptdriven/pdd/actions/runs/123/job/456",
                "expected": {
                    "job_name": "hosted-gate",
                    "workflow_id": 1,
                    "workflow_name": "Hosted Gate",
                    "workflow_path": ".github/workflows/hosted-gate.yml",
                    "event": "pull_request",
                },
            },
            "response_path": "/repos/promptdriven/pdd/actions/jobs/456",
            "response_update": {"name": "unrelated successful job"},
            "expected_error": "action job identity does not match",
        },
        {
            "binding": {
                "kind": "github_actions_run",
                "url": "https://github.com/promptdriven/pdd/actions/runs/123",
                "expected": {
                    "workflow_id": 1,
                    "workflow_name": "Hosted Gate",
                    "workflow_path": ".github/workflows/hosted-gate.yml",
                    "event": "pull_request",
                },
            },
            "response_path": "/repos/promptdriven/pdd/actions/runs/123",
            "response_update": {"workflow_id": 99},
            "expected_error": "action run identity does not match",
        },
        {
            "binding": {
                "kind": "github_check_run",
                "url": "https://github.com/promptdriven/pdd/runs/789",
                "expected": {
                    "check_name": "Hosted Check",
                    "app_id": 1,
                    "app_slug": "hosted-app",
                    "app_owner": "hosted-owner",
                },
            },
            "response_path": "/repos/promptdriven/pdd/check-runs/789",
            "response_update": {"name": "unrelated successful check"},
            "expected_error": "check run identity does not match",
        },
    ],
)
def test_global_sync_ledger_rejects_unrelated_successful_remote_evidence(
    tmp_path: Path,
    monkeypatch,
    case: dict[str, object],
) -> None:
    """Success and head SHA are insufficient without the reviewed remote identity."""
    binding = case["binding"]
    response_path = case["response_path"]
    response_update = case["response_update"]
    expected_error = case["expected_error"]
    assert isinstance(binding, dict)
    assert isinstance(response_path, str)
    assert isinstance(response_update, dict)
    assert isinstance(expected_error, str)
    payload = _payload()
    _add_hosted_merge_claim(payload)
    bundle = payload["promotion_bundles"]["gate_1"]
    assert isinstance(bundle, dict)
    bundle["artifact_bindings"] = [binding]
    bundle["machine_predicate"] = {
        "name": (
            binding["expected"]["job_name"]
            if binding["kind"] == "github_actions_job"
            else binding["expected"].get("workflow_name", binding["expected"].get("check_name"))
        ),
        "result": "passed",
        "binding_url": binding["url"],
    }
    plan, source, _output = _write_fixture(tmp_path, payload=payload)
    responses = _valid_github_responses()
    if binding["kind"] == "github_check_run":
        responses[response_path] = {
            "conclusion": "success",
            "head_sha": HEAD_SHA,
            "name": "Hosted Check",
            "app": {
                "id": 1,
                "slug": "hosted-app",
                "owner": {"login": "hosted-owner"},
            },
        }
    responses[response_path].update(response_update)
    verifier = GitHubPromotionVerifier()
    monkeypatch.setattr(verifier, "_get", responses.__getitem__)

    with pytest.raises(LedgerError, match=expected_error):
        validate_ledger(
            load_unique_yaml(source), plan, source, verify_remote=True, promotion_verifier=verifier
        )


def test_global_sync_ledger_rejects_nonprotected_merge_target(
    tmp_path: Path, monkeypatch
) -> None:
    """A merged PR into a scratch target cannot authorize the protected state."""
    payload = _payload()
    _add_hosted_merge_claim(payload)
    plan, source, _output = _write_fixture(tmp_path, payload=payload)
    responses = _valid_github_responses()
    responses["/repos/promptdriven/pdd/pulls/2214"]["base"] = {
        "repo": {"full_name": "attacker/scratch"},
        "ref": "scratch",
    }
    verifier = GitHubPromotionVerifier()
    monkeypatch.setattr(verifier, "_get", responses.__getitem__)

    with pytest.raises(LedgerError, match="pull request base does not match"):
        validate_ledger(
            load_unique_yaml(source), plan, source, verify_remote=True, promotion_verifier=verifier
        )


def test_global_sync_ledger_accepts_current_source_promotion_identities(monkeypatch) -> None:
    """Every committed promotion bundle binds to its reviewed GitHub identities."""
    source = ROOT / "docs" / "global_sync_evidence_ledger_source.yaml"
    plan = ROOT / "docs" / "global_sync_resolution_plan.md"
    payload = load_unique_yaml(source)
    responses = _current_source_promotion_responses(payload)
    requested_paths: list[str] = []
    verifier = GitHubPromotionVerifier()

    def get_response(path: str) -> dict[str, object]:
        requested_paths.append(path)
        return responses[path]

    monkeypatch.setattr(verifier, "_get", get_response)

    validate_ledger(payload, plan, source, verify_remote=True, promotion_verifier=verifier)

    assert set(requested_paths) == set(responses)


def test_archived_gates_are_not_live_authority_or_remotely_verified(monkeypatch) -> None:
    """Archived Gate records remain tamper-evident but cannot drive current work."""
    source = ROOT / "docs" / "global_sync_evidence_ledger_source.yaml"
    plan = ROOT / "docs" / "global_sync_resolution_plan.md"
    payload = load_unique_yaml(source)

    assert payload["schema_version"] == 6
    assert "steps" not in payload
    historical_steps = payload["historical_steps"]
    assert isinstance(historical_steps, list)
    assert len(historical_steps) == 10
    assert {step["execution_state"] for step in historical_steps} == {"ARCHIVED"}

    milestones = payload["milestones"]
    assert isinstance(milestones, list)
    assert [milestone["id"] for milestone in milestones] == [
        "M0",
        "M1",
        "M2",
        "M3",
        "M4",
        "M5",
    ]
    assert milestones[0]["status"] == "in-progress"
    assert milestones[0]["blocker_id"] == "m0-executable-baseline"
    assert payload["live_rebaseline"]["milestones_passed"] == 0

    responses = _current_source_promotion_responses(payload)
    requested_paths: list[str] = []
    verifier = GitHubPromotionVerifier()

    def get_response(path: str) -> dict[str, object]:
        requested_paths.append(path)
        return responses[path]

    monkeypatch.setattr(verifier, "_get", get_response)
    validate_ledger(payload, plan, source, verify_remote=True, promotion_verifier=verifier)

    assert "/repos/promptdriven/pdd/pulls/2214" not in requested_paths


@pytest.mark.parametrize("failure", ["metadata-mismatch", "outage"])
def test_global_sync_ledger_remote_failure_fails_closed_without_writing(
    tmp_path: Path, monkeypatch, failure: str
) -> None:
    payload = _payload()
    _add_hosted_merge_claim(payload)
    plan, source, output = _write_fixture(tmp_path, payload=payload)
    output.write_text("preserve this ledger\n", encoding="utf-8")

    if failure == "metadata-mismatch":
        responses = _valid_github_responses()
        responses["/repos/promptdriven/pdd/pulls/2214"]["head"] = {"sha": "c" * 40}
        monkeypatch.setattr(GitHubPromotionVerifier, "_get", lambda _self, path: responses[path])
        expected = "head SHA does not match"
    else:
        def outage(_self, _path) -> None:
            raise LedgerError("protected GitHub verification failed")

        monkeypatch.setattr(GitHubPromotionVerifier, "_get", outage)
        expected = "protected GitHub verification failed"

    with pytest.raises(LedgerError, match=expected):
        run(plan, output, source, verify_remote=True)

    assert output.read_text(encoding="utf-8") == "preserve this ledger\n"


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

    assert payload["schema_version"] == 5
