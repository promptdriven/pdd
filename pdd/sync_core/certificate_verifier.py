"""Independent command for accepting a signed exact-SHA global certificate."""

from __future__ import annotations

import argparse
import base64
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .artifact_provenance import CandidateArtifactPolicy
from .certificate import CheckerIdentity, verify_global_certificate


@dataclass(frozen=True)
class CertificateExpectations:
    """Protected acceptance inputs independent of the certificate body."""

    issuer: str
    public_key: bytes
    checker: CheckerIdentity
    candidate_artifact_policy: CandidateArtifactPolicy
    repository_shas: dict[str, tuple[str, str]]
    repository_ids: dict[str, str]
    minimum_nightly_streak: int = 7


def _sha(value: Any) -> str:
    text = str(value)
    if len(text) != 40 or any(character not in "0123456789abcdef" for character in text):
        raise ValueError("expected repository SHA is malformed")
    return text


def _candidate_policy(payload: Any) -> CandidateArtifactPolicy:
    if not isinstance(payload, dict):
        raise ValueError("candidate artifact policy is malformed")
    python = payload.get("python")
    if not isinstance(python, dict):
        raise ValueError("candidate artifact policy interpreter is malformed")
    public_key = base64.b64decode(str(payload["public_key_base64"]), validate=True)
    return CandidateArtifactPolicy(
        str(payload["issuer"]),
        public_key,
        str(payload["builder_workflow_identity"]),
        str(payload["dependency_lock_sha256"]),
        str(python["implementation"]),
        str(python["version"]),
        str(python["abi"]),
        str(python["platform"]),
    )


def load_expectations(path: Path) -> CertificateExpectations:
    """Load and strictly validate one protected expectations document."""
    try:
        payload = json.loads(Path(path).read_text(encoding="utf-8"))
        if not isinstance(payload, dict) or payload.get("schema_version") != 1:
            raise ValueError("expectations schema is invalid")
        minimum_nightly_streak = int(payload.get("minimum_nightly_streak", 7))
        if minimum_nightly_streak < 7:
            raise ValueError("protected expectations require seven nightly observations")
        checker_payload = payload["checker"]
        candidate_policy_payload = payload["candidate_artifact_policy"]
        repositories = payload["repositories"]
        if not isinstance(checker_payload, dict) or not isinstance(repositories, dict):
            raise ValueError("expectations payload is malformed")
        if set(repositories) != {"pdd", "pdd_cloud"}:
            raise ValueError("expectations must name exactly pdd and pdd_cloud")
        checker = CheckerIdentity(
            str(checker_payload["wheel_sha256"]),
            str(checker_payload["release_ref"]),
            str(checker_payload["workflow_identity"]),
        )
        public_key = base64.b64decode(str(payload["public_key_base64"]), validate=True)
        if len(public_key) != 32:
            raise ValueError("certificate public key is malformed")
        issuer = str(payload["issuer"])
        if not issuer:
            raise ValueError("certificate issuer is absent")
        candidate_policy = _candidate_policy(candidate_policy_payload)
        repository_shas: dict[str, tuple[str, str]] = {}
        repository_ids: dict[str, str] = {}
        for name, row in repositories.items():
            if not isinstance(row, dict) or not str(row.get("repository_id", "")):
                raise ValueError("expected repository identity is malformed")
            repository_shas[name] = (_sha(row["base_sha"]), _sha(row["head_sha"]))
            repository_ids[name] = str(row["repository_id"])
    except (KeyError, TypeError, json.JSONDecodeError, OSError) as exc:
        raise ValueError("protected certificate expectations are malformed") from exc
    return CertificateExpectations(
        issuer,
        public_key,
        checker,
        candidate_policy,
        repository_shas,
        repository_ids,
        minimum_nightly_streak,
    )


def main() -> None:
    """Verify one certificate against protected independent expectations."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--expectations", type=Path, required=True)
    arguments = parser.parse_args()
    try:
        certificate = json.loads(arguments.certificate.read_text(encoding="utf-8"))
        if not isinstance(certificate, dict):
            raise ValueError("certificate root is not an object")
        expected = load_expectations(arguments.expectations)
        verified = verify_global_certificate(
            certificate,
            expected.public_key,
            expected_issuer=expected.issuer,
            expected_repository_shas=expected.repository_shas,
            expected_repository_ids=expected.repository_ids,
            expected_checker_identity=expected.checker,
            expected_candidate_artifact_policy=expected.candidate_artifact_policy,
            expected_minimum_nightly_streak=expected.minimum_nightly_streak,
        )
    except (OSError, ValueError, json.JSONDecodeError):
        verified = False
    print(json.dumps({"verified": verified}, sort_keys=True))
    if not verified:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
