#!/usr/bin/env python3
"""Reproducible, read-only M0 global-sync inventory and patch samples.

The input checkout is never changed.  Candidate commits and fingerprint files
exist only in a temporary shared clone and are removed before this program
returns.  The primary JSON is deliberately deterministic; timing and RSS are
emitted only to the optional metrics JSON.
"""
# pylint: disable=too-many-branches,too-many-locals,too-many-statements,line-too-long,subprocess-run-check

from __future__ import annotations

import argparse
import hashlib
import json
import resource
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Callable, TypeVar

# A direct ``python scripts/...`` invocation must import this checkout's public
# API, independently of the caller's current directory.
SCRIPT_ROOT = Path(__file__).resolve().parents[1]
if str(SCRIPT_ROOT) not in sys.path:
    sys.path.insert(0, str(SCRIPT_ROOT))

from pdd.sync_core import (
    FingerprintProvenance,
    FingerprintRecord,
    FingerprintStore,
    ManifestError,
    SemanticStatus,
    SnapshotError,
    build_unit_manifest,
    build_unit_snapshot,
    load_verification_profiles,
)


SAMPLE_PATHS = (
    "pdd/prompts/commands/checkup_python.prompt",
    "pdd/prompts/sync_main_python.prompt",
    "pdd/prompts/core/cli_python.prompt",
    "pdd/prompts/sync_orchestration_python.prompt",
    "pdd/prompts/Makefile_makefile.prompt",
    "pdd/prompts/agentic_architecture_python.prompt",
    "pdd/prompts/auto_deps_main_python.prompt",
    "pdd/prompts/ci_detect_changed_modules_python.prompt",
    "pdd/prompts/_keyring_timeout_python.prompt",
    "pdd/prompts/frontend/components/DependencyViewer_typescriptreact.prompt",
)
T = TypeVar("T")


def validate_arguments(*, closure_limit: int, sample_paths: tuple[str, ...]) -> None:
    """Reject a vacuous benchmark or an unspecified sample population."""
    if closure_limit <= 0:
        raise ValueError("closure limit must be positive")
    if not sample_paths:
        raise ValueError("at least one sample path is required")


def require_sample_paths(root: Path, sample_paths: tuple[str, ...]) -> None:
    """Require every declared representative input instead of silently thinning it."""
    missing = [path for path in sample_paths if not (root / path).is_file()]
    if missing:
        raise ValueError("required sample paths are absent: " + ", ".join(missing))


def deterministic_payload(
    *, base_sha: str, partition: dict[str, int], cases: list[dict[str, Any]],
    closure: dict[str, Any],
) -> dict[str, Any]:
    """Build the stable artifact, intentionally excluding host measurements."""
    return {
        "schema_version": 1,
        "base_sha": base_sha,
        "partition": partition,
        "cases": cases,
        "closure": closure,
    }


def _git(root: Path, *args: str, capture: bool = False) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args], cwd=root, text=True, capture_output=capture, check=False
    )


def _commit(root: Path, message: str) -> str:
    result = _git(root, "add", "-A")
    if result.returncode:
        raise ValueError(f"cannot stage temporary candidate: {message}")
    result = _git(
        root, "-c", "user.name=m0-sample", "-c", "user.email=m0@example.invalid",
        "commit", "--quiet", "-m", message,
    )
    if result.returncode:
        raise ValueError(f"cannot commit temporary candidate: {message}")
    result = _git(root, "rev-parse", "HEAD", capture=True)
    if result.returncode:
        raise ValueError("cannot resolve temporary candidate commit")
    return result.stdout.strip()


def _patch_bytes(root: Path) -> bytes:
    result = subprocess.run(
        ["git", "diff", "--binary", "HEAD"], cwd=root, capture_output=True, check=False
    )
    if result.returncode or not result.stdout:
        raise ValueError("candidate patch was not generated")
    return result.stdout


def _reset_candidate(root: Path, base_sha: str) -> None:
    result = _git(root, "reset", "--hard", base_sha)
    if result.returncode:
        raise ValueError("cannot reset temporary candidate clone")
    result = _git(root, "clean", "-ffd")
    if result.returncode:
        raise ValueError("cannot clean temporary candidate clone")


def _profile_candidate(root: Path, path: str, case_id: str) -> None:
    profile_path = root / ".pdd/verification-profiles.json"
    payload = json.loads(profile_path.read_text(encoding="utf-8"))
    rows = payload.get("profiles") if isinstance(payload, dict) else None
    if not isinstance(rows, list):
        raise ValueError("verification profile schema is not a profile list")
    row = next((item for item in rows if item.get("prompt_path") == path), None)
    if not isinstance(row, dict) or not isinstance(row.get("obligations"), list):
        raise ValueError(f"sample profile is absent or malformed: {path}")
    requirements = row.get("required_requirement_ids")
    if not isinstance(requirements, list) or not all(isinstance(item, str) for item in requirements):
        raise ValueError(f"sample profile has malformed requirements: {path}")
    row["obligations"].append({
        "obligation_id": f"m0-sample-{case_id}",
        "kind": "test",
        "validator_id": "pytest",
        "validator_config_digest": "m0-sample-v1",
        "requirement_ids": requirements,
        "artifact_paths": [path],
        "required": True,
    })
    profile_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _profile_case(root: Path, base_sha: str, path: str, index: int) -> dict[str, Any]:
    case_id = f"{index:02d}-profile"
    _profile_candidate(root, path, case_id)
    patch = _patch_bytes(root)
    candidate_sha = _commit(root, f"m0 sample {case_id}")
    manifest = build_unit_manifest(root, base_ref=base_sha, head_ref=candidate_sha)
    profiles = load_verification_profiles(root, manifest)
    if not profiles.invalid_reasons:
        raise ValueError(f"{case_id}: candidate unexpectedly bypassed profile validation")
    _reset_candidate(root, base_sha)
    return {
        "id": case_id, "kind": "profile", "sample_path": path,
        "patch_sha256": hashlib.sha256(patch).hexdigest(), "patch_bytes": len(patch),
        "outcome": "rejected-by-public-profile-api",
        "invalid_digest": hashlib.sha256(
            "\n".join(profiles.invalid_reasons).encode()
        ).hexdigest(),
    }


def _ownership_case(root: Path, base_sha: str) -> dict[str, Any]:
    path = root / ".pdd/sync-ownership.json"
    payload = json.loads(path.read_text(encoding="utf-8"))
    rules = payload.get("rules") if isinstance(payload, dict) else None
    if not isinstance(rules, list) or not rules or not isinstance(rules[0], dict):
        raise ValueError("ownership policy schema is not a non-empty rule list")
    rules.append(dict(rules[0]))
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    patch = _patch_bytes(root)
    candidate_sha = _commit(root, "m0 sample ownership")
    outcome = ""
    try:
        build_unit_manifest(root, base_ref=base_sha, head_ref=candidate_sha)
    except ManifestError as error:
        outcome = f"rejected-by-public-manifest-api:{type(error).__name__}"
    else:
        raise ValueError("ownership candidate unexpectedly bypassed manifest validation")
    _reset_candidate(root, base_sha)
    return {
        "id": "09-ownership", "kind": "ownership", "sample_path": ".pdd/sync-ownership.json",
        "patch_sha256": hashlib.sha256(patch).hexdigest(), "patch_bytes": len(patch),
        "outcome": outcome,
    }


def _fingerprint_case(root: Path, base_sha: str, preferred_path: str) -> dict[str, Any]:
    manifest = build_unit_manifest(root, base_ref=base_sha, head_ref=base_sha)
    profiles = load_verification_profiles(root, manifest)
    unit = next((item for item in manifest.managed_units if item.unit_id.prompt_relpath.as_posix() == preferred_path), None)
    if unit is None:
        raise ValueError(f"fingerprint sample is not managed: {preferred_path}")
    profile = profiles.for_unit(unit.unit_id)
    if profile is None:
        raise ValueError(f"fingerprint sample has no profile: {preferred_path}")
    try:
        snapshot = build_unit_snapshot(root, manifest, unit, profile)
    except SnapshotError as error:
        raise ValueError(f"fingerprint sample closure is invalid: {error}") from error
    record = FingerprintRecord(
        snapshot, 2, 2,
        FingerprintProvenance("generated", "m0-sample", "m0-sample-10", base_sha,
                              "1970-01-01T00:00:00+00:00", "m0-sample"),
        SemanticStatus.UNKNOWN, None,
    )
    store = FingerprintStore(root)
    store.write(record)
    patch = _patch_bytes(root)
    loaded = store.load(unit.unit_id)
    if loaded != record:
        raise ValueError("fingerprint candidate did not round-trip through public API")
    _reset_candidate(root, base_sha)
    return {
        "id": "10-fingerprint", "kind": "fingerprint", "sample_path": preferred_path,
        "patch_sha256": hashlib.sha256(patch).hexdigest(), "patch_bytes": len(patch),
        "outcome": "accepted-by-public-fingerprint-api-semantic-unknown",
    }


def _partition(manifest: Any, profiles: Any, root: Path) -> dict[str, int]:
    human = [profile for profile in profiles.profiles if all(
        item.kind == "human-attestation" for item in profile.obligations
    )]
    derived = missing = scope = 0
    for profile in human:
        prompt = profile.unit_id.prompt_relpath
        stem = prompt.stem.rsplit("_", 1)[0]
        relative = prompt.parent.relative_to("pdd/prompts")
        tests = (root / "tests" / relative / f"test_{stem}.py", root / "tests" / f"test_{stem}.py")
        code = root / "pdd" / relative / f"{stem}.py"
        if any(path.is_file() for path in tests):
            derived += 1
        elif profile.unit_id.language_id == "python" and code.is_file():
            missing += 1
        else:
            scope += 1
    if derived + missing + scope != len(human):
        raise ValueError("human-attestation partition lost profiles")
    return {
        "profiles": len(profiles.profiles), "managed_units": len(manifest.managed_units),
        "human_attestation_only": len(human), "derivable": derived,
        "missing_tests": missing, "ownership_or_scope": scope,
    }


def _measure(action: Callable[[], T]) -> tuple[T, dict[str, Any]]:
    calls = 0
    original = subprocess.run

    def counted(*args: Any, **kwargs: Any) -> Any:
        nonlocal calls
        calls += 1
        return original(*args, **kwargs)

    started = time.perf_counter()
    subprocess.run = counted  # type: ignore[assignment]
    try:
        result = action()
    finally:
        subprocess.run = original  # type: ignore[assignment]
    return result, {
        "seconds": round(time.perf_counter() - started, 6),
        "peak_rss": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "subprocess_calls": calls,
    }


def run(root: Path, base_sha: str, closure_limit: int, sample_paths: tuple[str, ...]) -> tuple[dict[str, Any], dict[str, Any]]:
    """Run all M0 samples and return `(deterministic, volatile_metrics)`."""
    validate_arguments(closure_limit=closure_limit, sample_paths=sample_paths)
    root = root.resolve()
    resolved = _git(root, "rev-parse", "--verify", f"{base_sha}^{{commit}}", capture=True)
    if resolved.returncode:
        raise ValueError(f"base SHA cannot be resolved: {base_sha}")
    base_sha = resolved.stdout.strip()
    require_sample_paths(root, sample_paths)

    def inventory() -> tuple[Any, Any, dict[str, int]]:
        manifest = build_unit_manifest(root, base_ref=base_sha, head_ref=base_sha)
        profiles = load_verification_profiles(root, manifest)
        return manifest, profiles, _partition(manifest, profiles, root)

    (manifest, profiles, partition), inventory_metrics = _measure(inventory)
    closure_invalid: list[dict[str, str]] = []

    def closure() -> int:
        completed = 0
        for unit in manifest.managed_units:
            profile = profiles.for_unit(unit.unit_id)
            if profile is None:
                closure_invalid.append({"path": unit.unit_id.prompt_relpath.as_posix(), "reason": "missing-profile"})
                continue
            try:
                build_unit_snapshot(root, manifest, unit, profile)
            except SnapshotError as error:
                closure_invalid.append({"path": unit.unit_id.prompt_relpath.as_posix(), "reason": str(error)})
                continue
            completed += 1
            if completed == closure_limit:
                return completed
        raise ValueError(f"only {completed} valid closures; requested {closure_limit}")

    completed, closure_metrics = _measure(closure)
    with tempfile.TemporaryDirectory(prefix="pdd-m0-samples-") as directory:
        candidate_root = Path(directory) / "candidate"
        clone = subprocess.run(
            ["git", "clone", "--quiet", "--shared", str(root), str(candidate_root)],
            capture_output=True,
            check=False,
        )
        if clone.returncode:
            raise ValueError("cannot create temporary shared candidate clone")
        if _git(candidate_root, "checkout", "--quiet", "--detach", base_sha).returncode:
            raise ValueError("cannot check out base SHA in temporary candidate clone")
        cases = [_profile_case(candidate_root, base_sha, path, index) for index, path in enumerate(sample_paths[:8], 1)]
        cases.append(_ownership_case(candidate_root, base_sha))
        cases.append(_fingerprint_case(candidate_root, base_sha, sample_paths[8]))
    deterministic = deterministic_payload(
        base_sha=base_sha, partition=partition, cases=cases,
        closure={"requested": closure_limit, "completed": completed, "invalid": closure_invalid},
    )
    metrics = {"schema_version": 1, "base_sha": base_sha, "inventory": inventory_metrics, "closure": closure_metrics}
    return deterministic, metrics


def main() -> int:  # pylint: disable=missing-function-docstring
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--base-sha", default="HEAD")
    parser.add_argument("--closure-limit", type=int, default=20)
    parser.add_argument("--output", type=Path, required=True, help="deterministic JSON output")
    parser.add_argument("--metrics-output", type=Path, help="optional volatile timing/RSS JSON output")
    arguments = parser.parse_args()
    try:
        deterministic, metrics = run(arguments.root, arguments.base_sha, arguments.closure_limit, SAMPLE_PATHS)
    except (OSError, ValueError, json.JSONDecodeError, ManifestError) as error:
        print(f"global-sync M0 samples failed: {error}")
        return 1
    arguments.output.write_text(json.dumps(deterministic, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if arguments.metrics_output:
        arguments.metrics_output.write_text(json.dumps(metrics, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"base_sha": deterministic["base_sha"], "cases": len(deterministic["cases"]), "closure": deterministic["closure"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
