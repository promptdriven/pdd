"""Tests for protected independent certificate expectations."""

import base64
import json

import pytest

from pdd.sync_core.certificate_verifier import load_expectations


def _payload():
    return {
        "schema_version": 1,
        "issuer": "global-sync-checker",
        "public_key_base64": base64.b64encode(b"k" * 32).decode(),
        "checker": {
            "wheel_sha256": "c" * 64,
            "release_ref": "refs/tags/v1.0.0",
            "workflow_identity": (
                "promptdriven/pdd/.github/workflows/global-sync.yml@refs/tags/v1.0.0"
            ),
        },
        "candidate_artifact_policy": {
            "issuer": "candidate-builder",
            "public_key_base64": base64.b64encode(b"w" * 32).decode(),
            "builder_workflow_identity": (
                "promptdriven/pdd/.github/workflows/candidate-wheel.yml@refs/heads/main"
            ),
            "dependency_lock_sha256": "e" * 64,
            "python": {
                "implementation": "CPython",
                "version": "3.12.3",
                "abi": "cp312",
                "platform": "manylinux_2_17_x86_64",
            },
        },
        "repositories": {
            "pdd": {
                "repository_id": "pdd-id",
                "base_sha": "a" * 40,
                "head_sha": "b" * 40,
            },
            "pdd_cloud": {
                "repository_id": "cloud-id",
                "base_sha": "c" * 40,
                "head_sha": "d" * 40,
            },
        },
    }


def test_expectations_bind_ids_shas_checker_and_key(tmp_path) -> None:
    path = tmp_path / "expectations.json"
    path.write_text(json.dumps(_payload()))
    expected = load_expectations(path)
    assert expected.repository_ids == {"pdd": "pdd-id", "pdd_cloud": "cloud-id"}
    assert expected.repository_shas["pdd"] == ("a" * 40, "b" * 40)
    assert expected.checker.wheel_sha256 == "c" * 64
    assert expected.public_key == b"k" * 32
    assert expected.candidate_artifact_policy.issuer == "candidate-builder"
    assert expected.candidate_artifact_policy.public_key == b"w" * 32


@pytest.mark.parametrize(
    "mutation",
    [
        lambda payload: payload["repositories"].pop("pdd_cloud"),
        lambda payload: payload["repositories"]["pdd"].update(base_sha="short"),
        lambda payload: payload["repositories"]["pdd"].update(repository_id=""),
        lambda payload: payload.update(public_key_base64="not-base64"),
        lambda payload: payload["candidate_artifact_policy"].pop("python"),
    ],
)
def test_malformed_expectations_fail_closed(tmp_path, mutation) -> None:
    payload = _payload()
    mutation(payload)
    path = tmp_path / "expectations.json"
    path.write_text(json.dumps(payload))
    with pytest.raises(ValueError):
        load_expectations(path)
