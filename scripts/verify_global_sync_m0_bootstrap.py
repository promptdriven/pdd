#!/usr/bin/env python3
"""Verify the protected M0 bootstrap boundary without running candidate code.

This file is executed only from the protected pull-request-target checkout.
Candidate refs are fetched as Git objects, parsed as data, and materialized
only as non-executable temporary files for the independently frozen sample
replay.  The candidate package and candidate scripts are never imported or
executed by this verifier.
"""
# pylint: disable=too-many-arguments,too-many-branches,too-many-lines,too-many-locals,too-many-return-statements,too-many-statements

from __future__ import annotations

import argparse
import base64
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tarfile
import tempfile
from typing import Mapping, Sequence
import urllib.error
import urllib.request

import yaml


POLICY_RELATIVE_PATH = Path(".pdd/global-sync/m0-bootstrap-policy.json")
STATE_PATH = "docs/global_sync_execution_state.yaml"
MAX_CANDIDATE_STATE_BYTES = 2 * 1024 * 1024
MAX_CANDIDATE_ARCHIVE_BYTES = 64 * 1024 * 1024
SHA_PATTERN = re.compile(r"[0-9a-f]{40}")
STATUS_PATTERN = re.compile(r"([A-Z])([0-9]{1,3})?")
CANONICAL_STATUS = frozenset({"A", "C", "D", "M", "R", "T", "U", "X", "B"})


class BootstrapVerificationError(ValueError):
    """Raised for invalid protected inputs or unsafe candidate Git data."""


def _canonical_json(value: object) -> bytes:
    return json.dumps(
        value, ensure_ascii=True, separators=(",", ":"), sort_keys=True
    ).encode("utf-8")


def canonical_policy_digest(policy: Mapping[str, object]) -> str:
    """Return the digest of the policy's canonical semantic representation."""
    return hashlib.sha256(_canonical_json(policy)).hexdigest()


def _validate_sha(value: object, label: str) -> str:
    if not isinstance(value, str) or not SHA_PATTERN.fullmatch(value):
        raise BootstrapVerificationError(f"{label} must be a lowercase 40-character SHA")
    return value


def _validate_path(value: object, label: str) -> str:
    if not isinstance(value, str) or not value or "\x00" in value or "\\" in value:
        raise BootstrapVerificationError(f"{label} must be a non-empty POSIX path")
    path = PurePosixPath(value)
    if path.is_absolute() or path == PurePosixPath(".") or any(
        part in {"", ".", ".."} for part in path.parts
    ):
        raise BootstrapVerificationError(f"{label} is not a canonical relative path")
    if path.as_posix() != value:
        raise BootstrapVerificationError(f"{label} is not normalized")
    return value


def _string_list(value: object, label: str, *, sorted_unique: bool = False) -> list[str]:
    if not isinstance(value, list):
        raise BootstrapVerificationError(f"{label} must be a list")
    paths = [_validate_path(item, label) for item in value]
    if len(paths) != len(set(paths)):
        raise BootstrapVerificationError(f"{label} must not contain duplicate paths")
    if sorted_unique and paths != sorted(paths):
        raise BootstrapVerificationError(f"{label} must use lexical path order")
    return paths


def _mapping(value: object, label: str, keys: set[str]) -> dict[str, object]:
    if not isinstance(value, dict) or set(value) != keys:
        raise BootstrapVerificationError(f"{label} has an unexpected schema")
    return value


def validate_policy(raw: object) -> dict[str, object]:
    """Validate the immutable, exact policy before it is used as authority."""
    policy = _mapping(
        raw,
        "policy",
        {
            "allowed_changes",
            "frozen_sample_verifier",
            "m0_track_write_set_universe",
            "post_sample_allowed_paths",
            "private_canary",
            "pull_request_number",
            "replay",
            "repository",
            "reviewed_source_base_sha",
            "schema_version",
            "state_projection",
            "workflow",
        },
    )
    if policy["schema_version"] != 1:
        raise BootstrapVerificationError("policy schema_version must be 1")
    if policy["repository"] != "promptdriven/pdd":
        raise BootstrapVerificationError("policy repository is not the protected repository")
    if policy["pull_request_number"] != 2301:
        raise BootstrapVerificationError("policy pull request is not the reviewed M0 PR")
    _validate_sha(policy["reviewed_source_base_sha"], "reviewed_source_base_sha")

    allowed_raw = policy["allowed_changes"]
    if not isinstance(allowed_raw, list) or not allowed_raw:
        raise BootstrapVerificationError("allowed_changes must be a non-empty list")
    allowed: list[tuple[str, str]] = []
    for index, item in enumerate(allowed_raw):
        row = _mapping(item, f"allowed_changes[{index}]", {"path", "status"})
        status = row["status"]
        if status not in {"A", "M"}:
            raise BootstrapVerificationError("allowed_changes only permits reviewed A/M entries")
        allowed.append((str(status), _validate_path(row["path"], "allowed change path")))
    allowed_paths = [path for _status, path in allowed]
    if len(allowed_paths) != len(set(allowed_paths)) or allowed_paths != sorted(allowed_paths):
        raise BootstrapVerificationError("allowed_changes must be lexically ordered and unique")

    projection = _mapping(
        policy["state_projection"],
        "state_projection",
        {"integration_write_set", "m0_bootstrap_allowlist"},
    )
    integration_write_set = _string_list(
        projection["integration_write_set"], "integration_write_set"
    )
    allowlist = _string_list(
        projection["m0_bootstrap_allowlist"],
        "m0_bootstrap_allowlist",
        sorted_unique=True,
    )
    if set(integration_write_set) != set(allowed_paths) or allowlist != allowed_paths:
        raise BootstrapVerificationError("state projection does not equal the exact diff paths")

    _string_list(
        policy["m0_track_write_set_universe"],
        "m0_track_write_set_universe",
        sorted_unique=True,
    )
    post_sample_paths = _string_list(
        policy["post_sample_allowed_paths"],
        "post_sample_allowed_paths",
        sorted_unique=True,
    )
    if not set(post_sample_paths).issubset(allowed_paths):
        raise BootstrapVerificationError(
            "post-sample paths must be a protected subset of the reviewed diff"
        )

    frozen = _mapping(
        policy["frozen_sample_verifier"],
        "frozen_sample_verifier",
        {"path", "sha256", "source_commit", "source_parent"},
    )
    frozen_path = _validate_path(frozen["path"], "frozen sample verifier path")
    if frozen_path in allowed_paths or frozen_path in integration_write_set:
        raise BootstrapVerificationError(
            "candidate policy must not authorize the frozen sample verifier"
        )
    if not isinstance(frozen["sha256"], str) or not re.fullmatch(r"[0-9a-f]{64}", frozen["sha256"]):
        raise BootstrapVerificationError("frozen sample verifier digest is invalid")
    _validate_sha(frozen["source_commit"], "frozen sample source_commit")
    _validate_sha(frozen["source_parent"], "frozen sample source_parent")

    canary = _mapping(policy["private_canary"], "private_canary", {"repository", "sha"})
    if canary["repository"] != "promptdriven/pdd_cloud":
        raise BootstrapVerificationError("private canary repository is not pinned")
    _validate_sha(canary["sha"], "private canary SHA")

    replay = _mapping(policy["replay"], "replay", {"closure_limit", "result_path"})
    if not isinstance(replay["closure_limit"], int) or replay["closure_limit"] <= 0:
        raise BootstrapVerificationError("replay closure_limit must be positive")
    _validate_path(replay["result_path"], "replay result_path")
    if replay["result_path"] not in allowed_paths:
        raise BootstrapVerificationError("replay result path is not in the reviewed diff")

    workflow = _mapping(policy["workflow"], "workflow", {"event_name", "path"})
    if workflow["event_name"] != "pull_request_target":
        raise BootstrapVerificationError("workflow event must be pull_request_target")
    _validate_path(workflow["path"], "workflow path")
    return policy


def _git(
    root: Path,
    arguments: Sequence[str],
    *,
    input_bytes: bytes | None = None,
) -> bytes:
    result = subprocess.run(
        ["git", *arguments],
        cwd=root,
        input=input_bytes,
        capture_output=True,
        check=False,
    )
    if result.returncode:
        raise BootstrapVerificationError("protected Git operation failed")
    return result.stdout


def _resolve_commit(root: Path, value: str) -> str:
    _validate_sha(value, "commit SHA")
    resolved = _git(root, ("rev-parse", "--verify", f"{value}^{{commit}}")).decode(
        "ascii"
    ).strip()
    return _validate_sha(resolved, "resolved commit SHA")


def _resolve_parent(root: Path, value: str) -> str:
    _validate_sha(value, "parent commit SHA")
    resolved = _git(root, ("rev-parse", "--verify", f"{value}^")).decode("ascii").strip()
    return _validate_sha(resolved, "resolved parent commit SHA")


def _is_ancestor(root: Path, older: str, newer: str) -> bool:
    result = subprocess.run(
        ["git", "merge-base", "--is-ancestor", older, newer],
        cwd=root,
        capture_output=True,
        check=False,
    )
    if result.returncode not in {0, 1}:
        raise BootstrapVerificationError("protected Git ancestry operation failed")
    return result.returncode == 0


def _read_git_blob(root: Path, commit: str, path: str) -> bytes:
    _validate_sha(commit, "blob commit SHA")
    _validate_path(path, "blob path")
    return _git(root, ("show", f"{commit}:{path}"))


def parse_name_status(raw: bytes) -> tuple[dict[str, object], ...]:
    """Parse Git's NUL-delimited name-status stream, including R/C pairs."""
    fields = raw.split(b"\0")
    if fields and fields[-1] == b"":
        fields.pop()
    entries: list[dict[str, object]] = []
    index = 0
    while index < len(fields):
        try:
            status_text = fields[index].decode("ascii")
        except UnicodeDecodeError as error:
            raise BootstrapVerificationError("name-status contains a non-ASCII status") from error
        match = STATUS_PATTERN.fullmatch(status_text)
        if match is None or match.group(1) not in CANONICAL_STATUS:
            raise BootstrapVerificationError("name-status contains an unsupported status")
        status, score_text = match.groups()
        index += 1
        if status in {"R", "C"}:
            if score_text is None or index + 1 >= len(fields):
                raise BootstrapVerificationError("rename/copy name-status entry is malformed")
            old_path = _decode_candidate_path(fields[index])
            path = _decode_candidate_path(fields[index + 1])
            entries.append(
                {
                    "status": status,
                    "score": int(score_text),
                    "old_path": old_path,
                    "path": path,
                }
            )
            index += 2
            continue
        if score_text is not None or index >= len(fields):
            raise BootstrapVerificationError("single-path name-status entry is malformed")
        entries.append({"status": status, "path": _decode_candidate_path(fields[index])})
        index += 1
    return tuple(entries)


def _decode_candidate_path(raw: bytes) -> str:
    try:
        path = raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise BootstrapVerificationError("candidate path is not UTF-8") from error
    return _validate_path(path, "candidate path")


def _candidate_state_violations(
    root: Path,
    policy: Mapping[str, object],
    candidate_head_sha: str,
    protected_base_sha: str,
) -> list[str]:
    try:
        raw = _read_git_blob(root, candidate_head_sha, STATE_PATH)
    except BootstrapVerificationError:
        return ["candidate-execution-state-is-unreadable"]
    if len(raw) > MAX_CANDIDATE_STATE_BYTES:
        return ["candidate-execution-state-exceeds-byte-limit"]
    try:
        state = yaml.safe_load(raw)
    except yaml.YAMLError:
        return ["candidate-execution-state-is-not-safe-yaml"]
    if not isinstance(state, dict):
        return ["candidate-execution-state-is-not-a-mapping"]
    violations: list[str] = []
    if state.get("protected_base_sha") != protected_base_sha:
        violations.append("candidate-protected-base-sha-does-not-match-current-base")
    preflight = state.get("preflight")
    if not isinstance(preflight, dict) or preflight.get("protected_base_sha") != protected_base_sha:
        violations.append("candidate-preflight-base-sha-does-not-match-current-base")
    integration = state.get("integration")
    if not isinstance(integration, dict):
        return [*violations, "candidate-integration-state-is-not-a-mapping"]
    if integration.get("base_sha") != protected_base_sha:
        violations.append("candidate-integration-base-sha-does-not-match-current-base")
    projection = policy["state_projection"]
    assert isinstance(projection, dict)
    if state.get("m0_bootstrap_allowlist") != projection["m0_bootstrap_allowlist"]:
        violations.append("candidate-m0-bootstrap-allowlist-does-not-match-policy")
    if integration.get("write_set") != projection["integration_write_set"]:
        violations.append("candidate-integration-write-set-does-not-match-policy")
    tracks = state.get("tracks")
    if not isinstance(tracks, list):
        return [*violations, "candidate-tracks-is-not-a-list"]
    universe = set(policy["m0_track_write_set_universe"])
    for track in tracks:
        if not isinstance(track, dict):
            violations.append("candidate-track-is-not-a-mapping")
            continue
        track_id = track.get("id")
        if not isinstance(track_id, str):
            violations.append("candidate-track-id-is-not-a-string")
            continue
        if not track_id.startswith("m0-"):
            continue
        write_set = track.get("write_set")
        if not isinstance(write_set, list) or not all(isinstance(item, str) for item in write_set):
            violations.append("m0-track-write-set-is-not-a-string-list")
            continue
        if len(write_set) != len(set(write_set)):
            violations.append("m0-track-write-set-has-duplicates")
        if any(item not in universe for item in write_set):
            violations.append("m0-track-write-set-outside-protected-universe")
    return violations


def _frozen_sample_violations(
    root: Path,
    policy: Mapping[str, object],
    candidate_head_sha: str,
    changes: Sequence[Mapping[str, object]],
) -> tuple[list[str], dict[str, object]]:
    frozen = policy["frozen_sample_verifier"]
    assert isinstance(frozen, dict)
    path = str(frozen["path"])
    expected_digest = str(frozen["sha256"])
    violations: list[str] = []
    for change in changes:
        if change.get("path") == path or change.get("old_path") == path:
            violations.append("candidate-touched-frozen-sample-verifier")
            break
    try:
        protected_digest = hashlib.sha256((root / path).read_bytes()).hexdigest()
    except OSError:
        protected_digest = ""
    if protected_digest != expected_digest:
        violations.append("protected-frozen-sample-verifier-digest-does-not-match-policy")
    try:
        source_bytes = _read_git_blob(root, str(frozen["source_commit"]), path)
        source_digest = hashlib.sha256(source_bytes).hexdigest()
        candidate_digest = hashlib.sha256(
            _read_git_blob(root, candidate_head_sha, path)
        ).hexdigest()
        source_parent = _resolve_parent(root, str(frozen["source_commit"]))
        source_is_ancestor = _is_ancestor(
            root, str(frozen["source_commit"]), candidate_head_sha
        )
    except BootstrapVerificationError:
        source_digest = ""
        candidate_digest = ""
        source_parent = ""
        source_is_ancestor = False
        violations.append("frozen-sample-source-ancestry-is-unavailable")
    if source_digest != expected_digest:
        violations.append("frozen-sample-source-digest-does-not-match-policy")
    if candidate_digest != expected_digest:
        violations.append("candidate-frozen-sample-digest-does-not-match-policy")
    if source_parent != frozen["source_parent"]:
        violations.append("frozen-sample-source-parent-does-not-match-policy")
    if not source_is_ancestor:
        violations.append("frozen-sample-source-is-not-an-ancestor-of-candidate")
    return violations, {
        "candidate_sha256": candidate_digest,
        "path": path,
        "protected_sha256": protected_digest,
        "source_commit": frozen["source_commit"],
        "source_is_ancestor_of_candidate": source_is_ancestor,
        "source_parent": frozen["source_parent"],
        "source_sha256": source_digest,
    }


def _diff_records(
    root: Path, protected_base_sha: str, candidate_head_sha: str
) -> tuple[tuple[dict[str, object], ...], str]:
    raw = _git(
        root,
        (
            "diff",
            "--name-status",
            "-z",
            "--no-ext-diff",
            "-M",
            "-C",
            protected_base_sha,
            candidate_head_sha,
        ),
    )
    return parse_name_status(raw), hashlib.sha256(raw).hexdigest()


def _base_proof(
    *,
    policy: Mapping[str, object],
    pr_number: int,
    protected_base_sha: str,
    candidate_head_sha: str,
    workflow_base_sha: str,
    diff_digest: str | None,
    violations: Sequence[str],
) -> dict[str, object]:
    workflow = policy["workflow"]
    assert isinstance(workflow, dict)
    return {
        "candidate_head_sha": candidate_head_sha,
        "current_protected_base_sha": protected_base_sha,
        "diff_sha256": diff_digest,
        "policy_sha256": canonical_policy_digest(policy),
        "pr_number": pr_number,
        "schema_version": 1,
        "violations": sorted(set(violations)),
        "workflow_base_sha": workflow_base_sha,
        "workflow_identity": {
            "event_name": workflow["event_name"],
            "path": workflow["path"],
        },
    }


def evaluate_candidate(
    *,
    repository_root: Path,
    policy: Mapping[str, object],
    pr_number: int,
    protected_base_sha: str,
    candidate_head_sha: str,
    event_name: str,
    workflow_base_sha: str,
) -> dict[str, object]:
    """Evaluate locally available candidate Git objects against protected policy."""
    policy = validate_policy(policy)
    violations: list[str] = []
    if pr_number != policy["pull_request_number"]:
        violations.append("event-pr-number-does-not-match-protected-policy")
    if event_name != policy["workflow"]["event_name"]:  # type: ignore[index]
        violations.append("event-name-does-not-match-protected-policy")
    try:
        resolved_base = _resolve_commit(repository_root, protected_base_sha)
        resolved_head = _resolve_commit(repository_root, candidate_head_sha)
        resolved_workflow_base = _resolve_commit(repository_root, workflow_base_sha)
    except BootstrapVerificationError:
        return _base_proof(
            policy=policy,
            pr_number=pr_number,
            protected_base_sha=protected_base_sha,
            candidate_head_sha=candidate_head_sha,
            workflow_base_sha=workflow_base_sha,
            diff_digest=None,
            violations=[*violations, "protected-base-or-candidate-commit-is-unavailable"],
        )
    if resolved_base != protected_base_sha or resolved_workflow_base != protected_base_sha:
        violations.append("workflow-base-sha-does-not-match-current-protected-base")
    if not _is_ancestor(repository_root, resolved_base, resolved_head):
        violations.append("candidate-head-is-not-descended-from-current-protected-base")
    try:
        changes, diff_digest = _diff_records(repository_root, resolved_base, resolved_head)
    except BootstrapVerificationError:
        return _base_proof(
            policy=policy,
            pr_number=pr_number,
            protected_base_sha=resolved_base,
            candidate_head_sha=resolved_head,
            workflow_base_sha=resolved_workflow_base,
            diff_digest=None,
            violations=[*violations, "candidate-diff-is-unreadable"],
        )
    expected = tuple(
        (str(row["status"]), str(row["path"]))
        for row in policy["allowed_changes"]  # type: ignore[index]
    )
    actual = tuple(
        (str(change["status"]), str(change["path"]))
        for change in changes
        if "old_path" not in change
    )
    if any("old_path" in change for change in changes) or actual != expected:
        violations.append("candidate-diff-does-not-match-protected-policy")
    state_violations = _candidate_state_violations(
        repository_root, policy, resolved_head, resolved_base
    )
    frozen_violations, frozen_proof = _frozen_sample_violations(
        repository_root, policy, resolved_head, changes
    )
    proof = _base_proof(
        policy=policy,
        pr_number=pr_number,
        protected_base_sha=resolved_base,
        candidate_head_sha=resolved_head,
        workflow_base_sha=resolved_workflow_base,
        diff_digest=diff_digest,
        violations=[*violations, *state_violations, *frozen_violations],
    )
    proof["diff"] = {"changes": list(changes), "sha256": diff_digest}
    proof["frozen_sample_verifier"] = frozen_proof
    return proof


def replay_artifact_proof(candidate_artifact: bytes, replay_artifact: bytes) -> dict[str, object]:
    """Return deterministic equality evidence for committed and replayed bytes."""
    artifact_digest = hashlib.sha256(candidate_artifact).hexdigest()
    replay_digest = hashlib.sha256(replay_artifact).hexdigest()
    return {
        "artifact_sha256": artifact_digest,
        "byte_equal": candidate_artifact == replay_artifact,
        "replay_sha256": replay_digest,
    }


def sampled_implementation_proof(
    *,
    repository_root: Path,
    policy: Mapping[str, object],
    candidate_head_sha: str,
) -> dict[str, object]:
    """Bind replay to a real candidate ancestor and a protected post-sample scope."""
    policy = validate_policy(policy)
    candidate_head_sha = _resolve_commit(repository_root, candidate_head_sha)
    replay = policy["replay"]
    assert isinstance(replay, dict)
    violations: list[str] = []
    sampled_sha: str | None = None
    post_sample_digest: str | None = None
    changes: tuple[dict[str, object], ...] = ()
    try:
        artifact = _read_git_blob(
            repository_root, candidate_head_sha, str(replay["result_path"])
        )
        if len(artifact) > MAX_CANDIDATE_STATE_BYTES:
            raise BootstrapVerificationError("sample artifact exceeds byte limit")
        payload = json.loads(artifact)
        if not isinstance(payload, dict):
            raise BootstrapVerificationError("sample artifact is not an object")
        sampled_sha = _validate_sha(payload.get("base_sha"), "sampled implementation SHA")
    except (BootstrapVerificationError, json.JSONDecodeError):
        violations.append("sampled-implementation-sha-is-invalid")
        return {
            "post_sample_changes": [],
            "post_sample_diff_sha256": None,
            "sampled_implementation_is_ancestor_of_candidate": False,
            "sampled_implementation_sha": None,
            "violations": violations,
        }
    try:
        sampled_sha = _resolve_commit(repository_root, sampled_sha)
    except BootstrapVerificationError:
        violations.append("sampled-implementation-is-unavailable")
        return {
            "post_sample_changes": [],
            "post_sample_diff_sha256": None,
            "sampled_implementation_is_ancestor_of_candidate": False,
            "sampled_implementation_sha": sampled_sha,
            "violations": violations,
        }
    ancestor = _is_ancestor(repository_root, sampled_sha, candidate_head_sha)
    if not ancestor:
        violations.append("sampled-implementation-is-not-an-ancestor-of-candidate")
        return {
            "post_sample_changes": [],
            "post_sample_diff_sha256": None,
            "sampled_implementation_is_ancestor_of_candidate": False,
            "sampled_implementation_sha": sampled_sha,
            "violations": violations,
        }
    changes, post_sample_digest = _diff_records(
        repository_root, sampled_sha, candidate_head_sha
    )
    allowed_paths = set(policy["post_sample_allowed_paths"])
    for change in changes:
        if "old_path" in change:
            violations.append("post-sample-diff-uses-rename-or-copy")
        if change.get("path") not in allowed_paths or (
            "old_path" in change and change.get("old_path") not in allowed_paths
        ):
            violations.append("post-sample-diff-outside-protected-allowlist")
    return {
        "post_sample_changes": list(changes),
        "post_sample_diff_sha256": post_sample_digest,
        "sampled_implementation_is_ancestor_of_candidate": True,
        "sampled_implementation_sha": sampled_sha,
        "violations": sorted(set(violations)),
    }


def materialize_git_data_tree(root: Path, commit_sha: str, destination: Path) -> None:
    """Materialize regular Git blobs as read-only data without a checkout."""
    commit_sha = _resolve_commit(root, commit_sha)
    archive = _git(root, ("archive", "--format=tar", commit_sha))
    if len(archive) > MAX_CANDIDATE_ARCHIVE_BYTES:
        raise BootstrapVerificationError("candidate archive exceeds byte limit")
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:") as stream:
        members = stream.getmembers()
        total = 0
        for member in members:
            _validate_path(member.name.rstrip("/"), "candidate archive member")
            if not (member.isdir() or member.isfile()):
                raise BootstrapVerificationError("candidate archive contains a non-regular entry")
            total += member.size
            if total > MAX_CANDIDATE_ARCHIVE_BYTES:
                raise BootstrapVerificationError("candidate archive exceeds content limit")
        for member in members:
            target = destination / member.name
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
                target.chmod(0o700)
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            source = stream.extractfile(member)
            if source is None:
                raise BootstrapVerificationError("candidate archive member cannot be read")
            target.write_bytes(source.read())
            target.chmod(0o400)
    git_dir = _git(root, ("rev-parse", "--absolute-git-dir")).decode("utf-8").strip()
    (destination / ".git").write_text(f"gitdir: {git_dir}\n", encoding="utf-8")


def _run_frozen_replay(
    *,
    repository_root: Path,
    sampled_implementation_sha: str,
    policy: Mapping[str, object],
    pdd_cloud_git_dir: Path,
) -> bytes:
    """Run the protected frozen sample script with inert PDD and canary data."""
    sample = policy["frozen_sample_verifier"]
    replay = policy["replay"]
    canary = policy["private_canary"]
    assert isinstance(sample, dict)
    assert isinstance(replay, dict)
    assert isinstance(canary, dict)
    sample_path = repository_root / str(sample["path"])
    if hashlib.sha256(sample_path.read_bytes()).hexdigest() != sample["sha256"]:
        raise BootstrapVerificationError("protected sample script does not match policy")
    with tempfile.TemporaryDirectory(prefix="pdd-m0-bootstrap-") as temporary:
        temporary_root = Path(temporary)
        candidate_root = temporary_root / "candidate-data"
        candidate_root.mkdir(mode=0o700)
        materialize_git_data_tree(
            repository_root, sampled_implementation_sha, candidate_root
        )
        canary_root = temporary_root / "pdd-cloud-canary-data"
        canary_root.mkdir(mode=0o700)
        materialize_git_data_tree(pdd_cloud_git_dir, str(canary["sha"]), canary_root)
        output_path = temporary_root / "replay.json"
        home = temporary_root / "home"
        home.mkdir(mode=0o700)
        environment = {
            "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_TERMINAL_PROMPT": "0",
            "HOME": str(home),
            "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8",
            "PATH": os.environ.get("PATH", ""),
            "PYTHONNOUSERSITE": "1",
        }
        command = [
            sys.executable,
            "-I",
            str(sample_path),
            "--root",
            str(candidate_root),
            "--base-sha",
            sampled_implementation_sha,
            "--closure-limit",
            str(replay["closure_limit"]),
            "--pdd-cloud-root",
            str(canary_root),
            "--pdd-cloud-sha",
            str(canary["sha"]),
            "--output",
            str(output_path),
        ]
        result = subprocess.run(
            command,
            cwd=repository_root,
            env=environment,
            capture_output=True,
            check=False,
        )
        if result.returncode or not output_path.is_file():
            raise BootstrapVerificationError("protected frozen sample replay failed")
        return output_path.read_bytes()


def _replay_payload_violations(
    replay_artifact: bytes, policy: Mapping[str, object], sampled_implementation_sha: str
) -> list[str]:
    try:
        payload = json.loads(replay_artifact)
    except json.JSONDecodeError:
        return ["protected-replay-output-is-not-json"]
    if not isinstance(payload, dict):
        return ["protected-replay-output-is-not-an-object"]
    canary = policy["private_canary"]
    assert isinstance(canary, dict)
    violations: list[str] = []
    if payload.get("base_sha") != sampled_implementation_sha:
        violations.append("protected-replay-base-sha-does-not-match-sampled-implementation")
    if payload.get("pdd_cloud_sha") != canary["sha"]:
        violations.append("protected-replay-pdd-cloud-sha-does-not-match-policy")
    canary_payload = payload.get("pdd_cloud_canary")
    if not isinstance(canary_payload, dict) or canary_payload.get("sha") != canary["sha"]:
        violations.append("protected-replay-canary-binding-does-not-match-policy")
    return violations


def _request_pr_metadata(repository: str, pr_number: int, token: str) -> dict[str, object]:
    if not token:
        raise BootstrapVerificationError("GitHub token is unavailable")
    request = urllib.request.Request(
        f"https://api.github.com/repos/{repository}/pulls/{pr_number}",
        headers={
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {token}",
            "User-Agent": "pdd-m0-bootstrap-verifier",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    try:
        with urllib.request.urlopen(request, timeout=20) as response:  # nosec B310
            payload = json.loads(response.read())
    except (OSError, urllib.error.URLError, json.JSONDecodeError) as error:
        raise BootstrapVerificationError("GitHub pull request metadata cannot be read") from error
    if not isinstance(payload, dict):
        raise BootstrapVerificationError("GitHub pull request metadata is malformed")
    return payload


def _metadata_values(payload: Mapping[str, object]) -> tuple[str, str, str]:
    base = payload.get("base")
    head = payload.get("head")
    if not isinstance(base, dict) or not isinstance(head, dict):
        raise BootstrapVerificationError("GitHub pull request metadata has no base/head")
    base_repo = base.get("repo")
    head_repo = head.get("repo")
    if not isinstance(base_repo, dict) or not isinstance(head_repo, dict):
        raise BootstrapVerificationError("GitHub pull request repository metadata is malformed")
    if base_repo.get("full_name") != "promptdriven/pdd":
        raise BootstrapVerificationError("GitHub pull request base repository is unexpected")
    base_sha = _validate_sha(base.get("sha"), "GitHub API base SHA")
    head_sha = _validate_sha(head.get("sha"), "GitHub API head SHA")
    head_repository = head_repo.get("full_name")
    if not isinstance(head_repository, str) or not head_repository:
        raise BootstrapVerificationError("GitHub pull request head repository is absent")
    return base_sha, head_sha, head_repository


def _fetch_candidate_pull_ref(root: Path, pr_number: int, expected_head_sha: str) -> str:
    _git(
        root,
        (
            "fetch",
            "--force",
            "--no-tags",
            "origin",
            f"refs/pull/{pr_number}/head:refs/m0-bootstrap/pr-{pr_number}",
        ),
    )
    fetched = _git(root, ("rev-parse", "refs/m0-bootstrap/pr-" + str(pr_number))).decode(
        "ascii"
    ).strip()
    if fetched != expected_head_sha:
        raise BootstrapVerificationError("fetched pull ref does not match the GitHub API head")
    return fetched


def fetch_private_canary(git_dir: Path, expected_sha: str, token: str) -> str:
    """Fetch one private commit with a non-persistent, env-scoped auth header."""
    expected_sha = _validate_sha(expected_sha, "private canary SHA")
    if not token:
        raise BootstrapVerificationError("private canary token is unavailable")
    initialized = subprocess.run(
        ["git", "init", "--bare", str(git_dir)], capture_output=True, check=False
    )
    if initialized.returncode:
        raise BootstrapVerificationError("private canary Git directory cannot be initialized")
    basic = base64.b64encode(f"x-access-token:{token}".encode("utf-8")).decode("ascii")
    environment = {
        "GIT_CONFIG_COUNT": "1",
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_CONFIG_KEY_0": "http.https://github.com/.extraheader",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_VALUE_0": f"AUTHORIZATION: basic {basic}",
        "GIT_TERMINAL_PROMPT": "0",
        "HOME": str(git_dir),
        "PATH": os.environ.get("PATH", ""),
    }
    fetched = subprocess.run(
        [
            "git",
            "-C",
            str(git_dir),
            "fetch",
            "--no-tags",
            "https://github.com/promptdriven/pdd_cloud.git",
            expected_sha,
        ],
        capture_output=True,
        check=False,
        env=environment,
    )
    if fetched.returncode:
        raise BootstrapVerificationError("private canary Git object cannot be fetched")
    resolved = _resolve_commit(git_dir, expected_sha)
    if resolved != expected_sha:
        raise BootstrapVerificationError("private canary SHA does not resolve exactly")
    return resolved


def verify_remote_event(
    *,
    repository_root: Path,
    policy: Mapping[str, object],
    repository: str,
    pr_number: int,
    protected_base_sha: str,
    candidate_head_sha: str,
    event_name: str,
    workflow_base_sha: str,
    github_token: str,
) -> dict[str, object]:
    """Bind a target workflow event to GitHub metadata and fetched Git objects."""
    policy = validate_policy(policy)
    if repository != policy["repository"]:
        raise BootstrapVerificationError("workflow repository does not match policy")
    metadata = _request_pr_metadata(repository, pr_number, github_token)
    api_base_sha, api_head_sha, head_repository = _metadata_values(metadata)
    if api_base_sha != protected_base_sha or api_head_sha != candidate_head_sha:
        proof = _base_proof(
            policy=policy,
            pr_number=pr_number,
            protected_base_sha=protected_base_sha,
            candidate_head_sha=candidate_head_sha,
            workflow_base_sha=workflow_base_sha,
            diff_digest=None,
            violations=["event-shas-do-not-match-current-GitHub-pr-metadata"],
        )
        proof["event_metadata"] = {
            "api_base_sha": api_base_sha,
            "api_head_sha": api_head_sha,
            "head_repository": head_repository,
        }
        return proof
    fetched = _fetch_candidate_pull_ref(repository_root, pr_number, api_head_sha)
    proof = evaluate_candidate(
        repository_root=repository_root,
        policy=policy,
        pr_number=pr_number,
        protected_base_sha=protected_base_sha,
        candidate_head_sha=fetched,
        event_name=event_name,
        workflow_base_sha=workflow_base_sha,
    )
    if not proof["violations"]:
        sampled = sampled_implementation_proof(
            repository_root=repository_root,
            policy=policy,
            candidate_head_sha=fetched,
        )
        proof["sampled_implementation"] = sampled
        proof["violations"] = sorted(
            set(proof["violations"] + sampled["violations"])
        )
    proof["event_metadata"] = {
        "api_base_sha": api_base_sha,
        "api_head_sha": api_head_sha,
        "head_repository": head_repository,
    }
    return proof


def _load_policy(repository_root: Path) -> dict[str, object]:
    try:
        raw = json.loads((repository_root / POLICY_RELATIVE_PATH).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise BootstrapVerificationError("protected M0 policy cannot be read") from error
    return validate_policy(raw)


def _load_prior_proof(
    path: Path, policy: Mapping[str, object], arguments: argparse.Namespace
) -> dict[str, object]:
    try:
        prior = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise BootstrapVerificationError("prior protected gate proof cannot be read") from error
    if not isinstance(prior, dict) or prior.get("violations") != []:
        raise BootstrapVerificationError("prior protected gate proof did not pass")
    expected = {
        "candidate_head_sha": arguments.candidate_head_sha,
        "current_protected_base_sha": arguments.protected_base_sha,
        "policy_sha256": canonical_policy_digest(policy),
        "pr_number": arguments.pr_number,
        "workflow_base_sha": arguments.workflow_base_sha,
    }
    if any(prior.get(key) != value for key, value in expected.items()):
        raise BootstrapVerificationError("prior protected gate proof is bound to different inputs")
    sampled = prior.get("sampled_implementation")
    if not isinstance(sampled, dict) or sampled.get("violations") != []:
        raise BootstrapVerificationError("prior protected gate has no valid sampled implementation")
    return prior


def _write_proof(path: Path, proof: Mapping[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(proof, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _arguments() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository-root", type=Path, default=Path.cwd())
    parser.add_argument("--repository", required=True)
    parser.add_argument("--pr-number", type=int, required=True)
    parser.add_argument("--protected-base-sha", required=True)
    parser.add_argument("--candidate-head-sha", required=True)
    parser.add_argument("--workflow-base-sha", required=True)
    parser.add_argument("--event-name", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--phase", choices=("gate", "canary-fetch", "replay"), required=True)
    parser.add_argument("--prior-proof", type=Path)
    parser.add_argument("--pdd-cloud-git-dir", type=Path)
    parser.add_argument("--pdd-cloud-sha")
    return parser


def main() -> int:  # pylint: disable=too-many-return-statements
    """Execute the metadata gate or post-revocation deterministic replay."""
    arguments = _arguments().parse_args()
    try:
        policy = _load_policy(arguments.repository_root)
        if arguments.phase == "gate":
            proof = verify_remote_event(
                repository_root=arguments.repository_root,
                policy=policy,
                repository=arguments.repository,
                pr_number=arguments.pr_number,
                protected_base_sha=arguments.protected_base_sha,
                candidate_head_sha=arguments.candidate_head_sha,
                event_name=arguments.event_name,
                workflow_base_sha=arguments.workflow_base_sha,
                github_token=os.environ.get("GH_TOKEN", ""),
            )
        elif arguments.phase == "canary-fetch":
            if arguments.pdd_cloud_git_dir is None or arguments.pdd_cloud_sha is None:
                raise BootstrapVerificationError(
                    "private canary fetch requires Git directory and SHA"
                )
            canary = policy["private_canary"]
            assert isinstance(canary, dict)
            if arguments.pdd_cloud_sha != canary["sha"]:
                raise BootstrapVerificationError(
                    "workflow private canary SHA does not match policy"
                )
            resolved_canary = fetch_private_canary(
                arguments.pdd_cloud_git_dir,
                arguments.pdd_cloud_sha,
                os.environ.get("PDD_CLOUD_TOKEN", ""),
            )
            proof = {
                "private_canary_sha": resolved_canary,
                "schema_version": 1,
                "violations": [],
            }
        else:
            if arguments.prior_proof is None or arguments.pdd_cloud_git_dir is None:
                raise BootstrapVerificationError(
                    "replay requires prior proof and private canary Git data"
                )
            prior = _load_prior_proof(arguments.prior_proof, policy, arguments)
            proof = evaluate_candidate(
                repository_root=arguments.repository_root,
                policy=policy,
                pr_number=arguments.pr_number,
                protected_base_sha=arguments.protected_base_sha,
                candidate_head_sha=arguments.candidate_head_sha,
                event_name=arguments.event_name,
                workflow_base_sha=arguments.workflow_base_sha,
            )
            if not proof["violations"]:
                sampled = sampled_implementation_proof(
                    repository_root=arguments.repository_root,
                    policy=policy,
                    candidate_head_sha=str(proof["candidate_head_sha"]),
                )
                proof["sampled_implementation"] = sampled
                proof["event_metadata"] = prior.get("event_metadata")
                if _canonical_json(sampled) != _canonical_json(prior["sampled_implementation"]):
                    proof["violations"] = [
                        "protected-gate-sampled-implementation-does-not-match-replay",
                    ]
                else:
                    proof["violations"] = list(sampled["violations"])
            if not proof["violations"]:
                sampled = proof["sampled_implementation"]
                assert isinstance(sampled, dict)
                candidate_artifact = _read_git_blob(
                    arguments.repository_root,
                    str(proof["candidate_head_sha"]),
                    str(policy["replay"]["result_path"]),  # type: ignore[index]
                )
                replay_artifact = _run_frozen_replay(
                    repository_root=arguments.repository_root,
                    sampled_implementation_sha=str(sampled["sampled_implementation_sha"]),
                    policy=policy,
                    pdd_cloud_git_dir=arguments.pdd_cloud_git_dir,
                )
                replay = replay_artifact_proof(candidate_artifact, replay_artifact)
                replay["pdd_cloud_sha"] = policy["private_canary"]["sha"]  # type: ignore[index]
                frozen_policy = policy["frozen_sample_verifier"]
                assert isinstance(frozen_policy, dict)
                replay["sample_source_commit"] = frozen_policy["source_commit"]
                replay["sampled_implementation_sha"] = sampled[
                    "sampled_implementation_sha"
                ]
                replay["post_sample_diff_sha256"] = sampled["post_sample_diff_sha256"]
                replay["sample_source_is_ancestor_of_candidate"] = proof[
                    "frozen_sample_verifier"
                ]["source_is_ancestor_of_candidate"]  # type: ignore[index]
                proof["replay"] = replay
                proof["gate_proof_sha256"] = hashlib.sha256(
                    _canonical_json(prior)
                ).hexdigest()
                proof["violations"] = sorted(
                    set(
                        proof["violations"]
                        + _replay_payload_violations(
                            replay_artifact,
                            policy,
                            str(sampled["sampled_implementation_sha"]),
                        )
                        + (
                            []
                            if replay["byte_equal"]
                            else ["protected-replay-bytes-do-not-match-candidate-artifact"]
                        )
                    )
                )
        _write_proof(arguments.output, proof)
        return 0 if not proof["violations"] else 1
    except BootstrapVerificationError:
        # Avoid reflecting candidate-controlled error text into a privileged log.
        fallback_policy: Mapping[str, object] = {
            "workflow": {"event_name": "pull_request_target", "path": "unknown"}
        }
        proof = {
            "candidate_head_sha": arguments.candidate_head_sha,
            "current_protected_base_sha": arguments.protected_base_sha,
            "diff_sha256": None,
            "policy_sha256": None,
            "pr_number": arguments.pr_number,
            "schema_version": 1,
            "violations": ["protected-bootstrap-verifier-failed-closed"],
            "workflow_base_sha": arguments.workflow_base_sha,
            "workflow_identity": fallback_policy["workflow"],
        }
        _write_proof(arguments.output, proof)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
