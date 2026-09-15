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
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys
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
REGULAR_GIT_MODES = frozenset({"100644", "100755"})
EXACT_INERT_ALIASES = {
    "data": "pdd/data",
    "prompts": "pdd/prompts",
}
REQUIRED_COPY_RECORD = {
    "old_path": "docs/global_sync_resolution_plan.md",
    "path": "docs/archive/global_sync_resolution_plan_history_2026-07-22.md",
    "score": 96,
    "status": "C",
}
FROZEN_SAMPLE_FACADE_EXPORTS = (
    "FingerprintProvenance",
    "FingerprintRecord",
    "FingerprintStore",
    "ManifestError",
    "SemanticStatus",
    "SnapshotError",
    "build_unit_manifest",
    "build_unit_snapshot",
    "load_verification_profiles",
)

# This child process runs only protected-base code.  It deliberately installs
# namespace packages from the materialized candidate before the frozen script
# is evaluated, so neither broad package initializer can import the project's
# unrelated dependency graph.  The argv contract is (protected sample root,
# frozen sample path, candidate module root, sample args).
_FROZEN_SAMPLE_LAUNCHER = r'''
import importlib
import importlib.machinery
import importlib.util
from pathlib import Path
import runpy
import sys


FACADE_EXPORTS = (
    "FingerprintProvenance",
    "FingerprintRecord",
    "FingerprintStore",
    "ManifestError",
    "SemanticStatus",
    "SnapshotError",
    "build_unit_manifest",
    "build_unit_snapshot",
    "load_verification_profiles",
)


def _contained_path(value, root, label):
    path = Path(value).resolve(strict=True)
    try:
        path.relative_to(root)
    except ValueError as error:
        raise SystemExit(label + " escapes the protected sample root") from error
    return path


def _namespace_package(name, root):
    spec = importlib.machinery.ModuleSpec(name, loader=None, is_package=True)
    spec.submodule_search_locations = [str(root)]
    package = importlib.util.module_from_spec(spec)
    package.__path__ = [str(root)]
    sys.modules[name] = package
    return package


if len(sys.argv) < 4:
    raise SystemExit(
        "protected frozen sample launcher requires protected root, script, and candidate root"
    )

protected_root = Path(sys.argv[1]).resolve(strict=True)
sample_path = _contained_path(sys.argv[2], protected_root, "frozen sample path")
candidate_root = Path(sys.argv[3]).resolve(strict=True)
if not protected_root.is_dir() or not candidate_root.is_dir():
    raise SystemExit("protected and candidate roots must be directories")
pdd_root = _contained_path(
    candidate_root / "pdd", candidate_root, "candidate pdd package root"
)
sync_core_root = _contained_path(
    pdd_root / "sync_core", candidate_root, "candidate sync-core package root"
)
if not sample_path.is_file() or not pdd_root.is_dir() or not sync_core_root.is_dir():
    raise SystemExit("protected frozen sample runtime is incomplete")

for loaded_name in tuple(sys.modules):
    if loaded_name == "pdd" or loaded_name.startswith("pdd."):
        del sys.modules[loaded_name]

pdd = _namespace_package("pdd", pdd_root)
sync_core = _namespace_package("pdd.sync_core", sync_core_root)
setattr(pdd, "sync_core", sync_core)

types = importlib.import_module("pdd.sync_core.types")
fingerprint_store = importlib.import_module("pdd.sync_core.fingerprint_store")
manifest = importlib.import_module("pdd.sync_core.manifest")
snapshot = importlib.import_module("pdd.sync_core.snapshot")
verification = importlib.import_module("pdd.sync_core.verification")
facade = {
    "FingerprintProvenance": types.FingerprintProvenance,
    "FingerprintRecord": types.FingerprintRecord,
    "FingerprintStore": fingerprint_store.FingerprintStore,
    "ManifestError": manifest.ManifestError,
    "SemanticStatus": types.SemanticStatus,
    "SnapshotError": snapshot.SnapshotError,
    "build_unit_manifest": manifest.build_unit_manifest,
    "build_unit_snapshot": snapshot.build_unit_snapshot,
    "load_verification_profiles": verification.load_verification_profiles,
}
if tuple(facade) != FACADE_EXPORTS:
    raise SystemExit("protected frozen sample facade is not exact")
for export_name, export_value in facade.items():
    setattr(sync_core, export_name, export_value)
sync_core.__all__ = FACADE_EXPORTS

sys.argv = [str(sample_path), *sys.argv[4:]]
runpy.run_path(str(sample_path), run_name="__main__")
'''


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
    allowed: list[dict[str, object]] = []
    for index, item in enumerate(allowed_raw):
        if not isinstance(item, dict):
            raise BootstrapVerificationError(f"allowed_changes[{index}] has an unexpected schema")
        status = item.get("status")
        common_keys = {"mode", "object_type", "path", "status"}
        if status in {"A", "M"}:
            row = _mapping(item, f"allowed_changes[{index}]", common_keys)
        elif status == "C":
            row = _mapping(
                item,
                f"allowed_changes[{index}]",
                common_keys | {"old_path", "score"},
            )
        else:
            raise BootstrapVerificationError("allowed_changes only permits reviewed A/M/C entries")
        status = row["status"]
        path = _validate_path(row["path"], "allowed change path")
        mode = row["mode"]
        if not isinstance(mode, str) or mode not in REGULAR_GIT_MODES:
            raise BootstrapVerificationError("allowed change mode is not a regular Git mode")
        if row["object_type"] != "blob":
            raise BootstrapVerificationError("allowed changes must finish as blob objects")
        normalized = {
            "mode": mode,
            "object_type": "blob",
            "path": path,
            "status": status,
        }
        if status == "C":
            score = row["score"]
            old_path = _validate_path(row["old_path"], "allowed copy source path")
            if not isinstance(score, int) or score != 96:
                raise BootstrapVerificationError("allowed copy must use exact C096 similarity")
            copy_record = {
                "old_path": old_path,
                "path": path,
                "score": score,
                "status": status,
            }
            if copy_record != REQUIRED_COPY_RECORD:
                raise BootstrapVerificationError(
                    "allowed copy is not the protected resolution-plan C096"
                )
            normalized.update(copy_record)
        allowed.append(normalized)
    allowed_paths = [str(row["path"]) for row in allowed]
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
    environment = {
        **os.environ,
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_TERMINAL_PROMPT": "0",
    }
    result = subprocess.run(
        ["git", *arguments],
        cwd=root,
        env=environment,
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


def _is_shallow_repository(root: Path) -> bool:
    value = _git(root, ("rev-parse", "--is-shallow-repository")).decode("ascii").strip()
    if value not in {"true", "false"}:
        raise BootstrapVerificationError("protected Git shallow-repository state is invalid")
    return value == "true"


def _resolve_reviewed_source_base(root: Path, reviewed_source_base_sha: str) -> str:
    """Resolve protected reviewed history, deepening a target checkout if needed."""
    reviewed_source_base_sha = _validate_sha(
        reviewed_source_base_sha, "reviewed_source_base_sha"
    )
    try:
        resolved = _resolve_commit(root, reviewed_source_base_sha)
    except BootstrapVerificationError:
        resolved = ""
    try:
        shallow = _is_shallow_repository(root)
    except BootstrapVerificationError:
        shallow = False
    if resolved and not shallow:
        return resolved
    if shallow:
        _git(root, ("fetch", "--no-tags", "--unshallow", "origin"))
    elif not resolved:
        _git(root, ("fetch", "--no-tags", "origin", reviewed_source_base_sha))
    return _resolve_commit(root, reviewed_source_base_sha)


def _read_git_blob(root: Path, commit: str, path: str) -> bytes:
    _validate_sha(commit, "blob commit SHA")
    _validate_path(path, "blob path")
    return _git(root, ("show", f"{commit}:{path}"))


def _read_git_blob_object(root: Path, object_sha: str) -> bytes:
    """Read a blob object already bound by a parsed Git tree entry."""
    _validate_sha(object_sha, "blob object SHA")
    return _git(root, ("cat-file", "blob", object_sha))


def _git_tree_entries(root: Path, commit_sha: str) -> dict[str, dict[str, str]]:
    """Parse one recursive Git tree without consulting a worktree path."""
    commit_sha = _resolve_commit(root, commit_sha)
    raw = _git(root, ("ls-tree", "-rz", "--full-tree", "-r", commit_sha))
    entries: dict[str, dict[str, str]] = {}
    for raw_entry in raw.split(b"\0"):
        if not raw_entry:
            continue
        try:
            metadata, raw_path = raw_entry.split(b"\t", 1)
            mode, object_type, object_sha = metadata.decode("ascii").split(" ")
        except (UnicodeDecodeError, ValueError) as error:
            raise BootstrapVerificationError("Git tree entry is malformed") from error
        path = _decode_candidate_path(raw_path)
        _validate_sha(object_sha, "Git tree object SHA")
        if path in entries:
            raise BootstrapVerificationError("Git tree contains duplicate paths")
        entries[path] = {
            "mode": mode,
            "object_sha": object_sha,
            "object_type": object_type,
        }
    return entries


def _policy_diff_record(row: Mapping[str, object]) -> dict[str, object]:
    """Project a validated policy row into its exact name-status record."""
    record: dict[str, object] = {
        "path": row["path"],
        "status": row["status"],
    }
    if row["status"] == "C":
        record["old_path"] = row["old_path"]
        record["score"] = row["score"]
    return record


def _final_tree_binding(
    root: Path, policy: Mapping[str, object], candidate_head_sha: str
) -> tuple[list[str], list[dict[str, object]]]:
    """Bind every allowed destination to its exact final Git mode and type."""
    try:
        entries = _git_tree_entries(root, candidate_head_sha)
    except BootstrapVerificationError:
        return ["candidate-final-tree-is-unreadable"], []
    allowed = policy["allowed_changes"]
    assert isinstance(allowed, list)
    proof_entries: list[dict[str, object]] = []
    violations: list[str] = []
    for row in allowed:
        assert isinstance(row, dict)
        path = str(row["path"])
        expected_mode = str(row["mode"])
        expected_object_type = str(row["object_type"])
        actual = entries.get(path)
        proof_entry: dict[str, object] = {
            "expected_mode": expected_mode,
            "expected_object_type": expected_object_type,
            "path": path,
        }
        if actual is None:
            proof_entry["actual_mode"] = None
            proof_entry["actual_object_type"] = None
            violations.append("candidate-final-tree-entry-does-not-match-protected-policy")
        else:
            proof_entry["actual_mode"] = actual["mode"]
            proof_entry["actual_object_type"] = actual["object_type"]
            proof_entry["object_sha"] = actual["object_sha"]
            if (
                actual["mode"] != expected_mode
                or actual["object_type"] != expected_object_type
            ):
                violations.append("candidate-final-tree-entry-does-not-match-protected-policy")
        proof_entries.append(proof_entry)
    return sorted(set(violations)), proof_entries


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
    reviewed_source_base_is_ancestor_of_workflow_base: bool | None = None,
) -> dict[str, object]:
    workflow = policy["workflow"]
    assert isinstance(workflow, dict)
    return {
        "candidate_head_sha": candidate_head_sha,
        "current_protected_base_sha": protected_base_sha,
        "diff_sha256": diff_digest,
        "policy_sha256": canonical_policy_digest(policy),
        "pr_number": pr_number,
        "reviewed_source_base_is_ancestor_of_workflow_base": (
            reviewed_source_base_is_ancestor_of_workflow_base
        ),
        "reviewed_source_base_sha": policy["reviewed_source_base_sha"],
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
        reviewed_source_base = _resolve_reviewed_source_base(
            repository_root, str(policy["reviewed_source_base_sha"])
        )
        reviewed_source_is_ancestor = _is_ancestor(
            repository_root, reviewed_source_base, resolved_workflow_base
        )
    except BootstrapVerificationError:
        return _base_proof(
            policy=policy,
            pr_number=pr_number,
            protected_base_sha=resolved_base,
            candidate_head_sha=resolved_head,
            workflow_base_sha=resolved_workflow_base,
            diff_digest=None,
            violations=[*violations, "reviewed-source-base-is-unavailable"],
            reviewed_source_base_is_ancestor_of_workflow_base=False,
        )
    if not reviewed_source_is_ancestor:
        violations.append("reviewed-source-base-is-not-an-ancestor-of-workflow-base")
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
            reviewed_source_base_is_ancestor_of_workflow_base=reviewed_source_is_ancestor,
        )
    allowed_changes = policy["allowed_changes"]
    assert isinstance(allowed_changes, list)
    expected = tuple(
        _policy_diff_record(row) for row in allowed_changes if isinstance(row, dict)
    )
    if len(expected) != len(allowed_changes) or tuple(changes) != expected:
        violations.append("candidate-diff-does-not-match-protected-policy")
    final_tree_violations, final_tree_proof = _final_tree_binding(
        repository_root, policy, resolved_head
    )
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
        violations=[
            *violations,
            *final_tree_violations,
            *state_violations,
            *frozen_violations,
        ],
        reviewed_source_base_is_ancestor_of_workflow_base=reviewed_source_is_ancestor,
    )
    proof["diff"] = {"changes": list(changes), "sha256": diff_digest}
    proof["final_tree"] = {"entries": final_tree_proof}
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
    result_path = str(replay["result_path"])
    allowed_changes = policy["allowed_changes"]
    assert isinstance(allowed_changes, list)
    result_policy_rows = [
        row
        for row in allowed_changes
        if isinstance(row, dict) and row.get("path") == result_path
    ]
    if len(result_policy_rows) != 1:
        raise BootstrapVerificationError("replay result path has no exact tree policy")
    result_policy = result_policy_rows[0]
    try:
        result_entry = _git_tree_entries(repository_root, candidate_head_sha).get(result_path)
    except BootstrapVerificationError:
        result_entry = None
    if (
        result_entry is None
        or result_policy["mode"] != "100644"
        or result_policy["object_type"] != "blob"
        or result_entry["mode"] != "100644"
        or result_entry["object_type"] != "blob"
    ):
        violations.append("sample-result-path-is-not-an-allowed-regular-blob")
        return {
            "post_sample_changes": [],
            "post_sample_diff_sha256": None,
            "sampled_implementation_is_ancestor_of_candidate": False,
            "sampled_implementation_sha": None,
            "violations": violations,
        }
    try:
        artifact = _read_git_blob(repository_root, candidate_head_sha, result_path)
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
    if sampled_sha == candidate_head_sha:
        violations.append("sampled-implementation-must-precede-candidate")
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
    result_changes = [change for change in changes if change.get("path") == result_path]
    if (
        len(result_changes) != 1
        or "old_path" in result_changes[0]
        or result_changes[0].get("status") not in {"A", "M"}
    ):
        violations.append("sample-result-path-was-not-added-or-modified-after-sample")
    return {
        "post_sample_changes": list(changes),
        "post_sample_diff_sha256": post_sample_digest,
        "sampled_implementation_is_ancestor_of_candidate": True,
        "sampled_implementation_sha": sampled_sha,
        "violations": sorted(set(violations)),
    }


def _prepare_materialization_destination(destination: Path) -> None:
    """Require an empty real directory before any candidate bytes are written."""
    try:
        destination_stat = destination.lstat()
        is_empty = next(destination.iterdir(), None) is None
    except OSError as error:
        raise BootstrapVerificationError("materialization destination is unavailable") from error
    if (
        stat.S_ISLNK(destination_stat.st_mode)
        or not stat.S_ISDIR(destination_stat.st_mode)
        or not is_empty
    ):
        raise BootstrapVerificationError(
            "materialization destination is not an empty real directory"
        )


def _open_materialized_directory(destination: Path) -> int:
    """Open the destination with an OS-level no-follow guarantee."""
    try:
        return os.open(
            destination,
            os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
        )
    except OSError as error:
        raise BootstrapVerificationError(
            "materialization destination cannot be opened safely"
        ) from error


def _write_materialized_blob(destination: Path, path: str, content: bytes) -> None:
    """Write one read-only blob while rejecting symlinked parents and collisions."""
    _validate_path(path, "materialized path")
    components = PurePosixPath(path).parts
    directory_fd = _open_materialized_directory(destination)
    try:
        for component in components[:-1]:
            try:
                child_fd = os.open(
                    component,
                    os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                    dir_fd=directory_fd,
                )
            except FileNotFoundError:
                try:
                    os.mkdir(component, mode=0o700, dir_fd=directory_fd)
                    child_fd = os.open(
                        component,
                        os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                        dir_fd=directory_fd,
                    )
                except OSError as error:
                    raise BootstrapVerificationError(
                        "materialized directory cannot be created safely"
                    ) from error
            except OSError as error:
                raise BootstrapVerificationError(
                    "materialized directory cannot be opened safely"
                ) from error
            os.close(directory_fd)
            directory_fd = child_fd
        try:
            file_fd = os.open(
                components[-1],
                os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                0o400,
                dir_fd=directory_fd,
            )
        except OSError as error:
            raise BootstrapVerificationError(
                "materialized blob cannot be written safely"
            ) from error
        try:
            view = memoryview(content)
            while view:
                written = os.write(file_fd, view)
                if written <= 0:
                    raise BootstrapVerificationError("materialized blob write was incomplete")
                view = view[written:]
            os.fchmod(file_fd, 0o400)
        finally:
            os.close(file_fd)
    finally:
        os.close(directory_fd)


def _approved_inert_aliases(
    root: Path,
    protected_base_sha: str | None,
    entries: Mapping[str, Mapping[str, str]],
) -> dict[str, str]:
    """Return only exact, unchanged protected aliases eligible for regular copies."""
    aliases = {
        path: entry
        for path, entry in entries.items()
        if entry["mode"] == "120000" or entry["object_type"] != "blob"
    }
    if not aliases:
        return {}
    if protected_base_sha is None:
        raise BootstrapVerificationError("candidate tree contains an unapproved link or non-blob")
    protected_entries = _git_tree_entries(root, protected_base_sha)
    approved: dict[str, str] = {}
    for path, entry in aliases.items():
        expected_target = EXACT_INERT_ALIASES.get(path)
        if (
            expected_target is None
            or entry["mode"] != "120000"
            or entry["object_type"] != "blob"
            or protected_entries.get(path) != entry
        ):
            raise BootstrapVerificationError(
                "candidate tree contains an unapproved link or non-blob"
            )
        try:
            target = _read_git_blob_object(root, entry["object_sha"]).decode("utf-8")
        except (BootstrapVerificationError, UnicodeDecodeError) as error:
            raise BootstrapVerificationError("protected inert alias is unreadable") from error
        if target != expected_target:
            raise BootstrapVerificationError("protected inert alias target is not exact")
        approved[path] = target
    return approved


def materialize_git_data_tree(
    root: Path,
    commit_sha: str,
    destination: Path,
    *,
    protected_base_sha: str | None = None,
) -> None:
    """Materialize safe Git blobs and exact protected aliases without a checkout."""
    commit_sha = _resolve_commit(root, commit_sha)
    if protected_base_sha is not None:
        protected_base_sha = _resolve_commit(root, protected_base_sha)
    _prepare_materialization_destination(destination)
    entries = _git_tree_entries(root, commit_sha)
    aliases = _approved_inert_aliases(root, protected_base_sha, entries)
    regular_entries: dict[str, Mapping[str, str]] = {}
    for path, entry in entries.items():
        if path == ".git" or path.startswith(".git/"):
            raise BootstrapVerificationError("candidate tree attempts to materialize Git metadata")
        if path in aliases:
            continue
        if entry["mode"] not in REGULAR_GIT_MODES or entry["object_type"] != "blob":
            raise BootstrapVerificationError("candidate tree contains a non-regular entry")
        regular_entries[path] = entry

    materialized: set[str] = set()
    total_bytes = 0
    blob_cache: dict[str, bytes] = {}

    def materialize(path: str, entry: Mapping[str, str]) -> None:
        nonlocal total_bytes
        if path in materialized:
            raise BootstrapVerificationError("candidate tree materialization has a path collision")
        object_sha = entry["object_sha"]
        content = blob_cache.get(object_sha)
        if content is None:
            content = _read_git_blob_object(root, object_sha)
            blob_cache[object_sha] = content
        total_bytes += len(content)
        if total_bytes > MAX_CANDIDATE_ARCHIVE_BYTES:
            raise BootstrapVerificationError("candidate materialization exceeds content limit")
        _write_materialized_blob(destination, path, content)
        materialized.add(path)

    for path, entry in sorted(regular_entries.items()):
        materialize(path, entry)
    for alias, source_prefix in sorted(aliases.items()):
        source_entries = [
            (path, entry)
            for path, entry in regular_entries.items()
            if path.startswith(source_prefix + "/")
        ]
        if not source_entries:
            raise BootstrapVerificationError(
                "protected inert alias target is not a regular subtree"
            )
        for path, entry in sorted(source_entries):
            alias_path = alias + path[len(source_prefix) :]
            materialize(alias_path, entry)
    git_dir = _git(root, ("rev-parse", "--absolute-git-dir")).decode("utf-8").strip()
    _write_materialized_blob(destination, ".git", f"gitdir: {git_dir}\n".encode("utf-8"))


def _run_frozen_replay(
    *,
    repository_root: Path,
    protected_base_sha: str,
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
    protected_root = repository_root.resolve()
    sample_path = (protected_root / str(sample["path"])).resolve()
    try:
        sample_path.relative_to(protected_root)
    except ValueError as error:
        raise BootstrapVerificationError(
            "protected frozen sample path escapes the protected checkout"
        ) from error
    if hashlib.sha256(sample_path.read_bytes()).hexdigest() != sample["sha256"]:
        raise BootstrapVerificationError("protected sample script does not match policy")
    with tempfile.TemporaryDirectory(prefix="pdd-m0-bootstrap-") as temporary:
        temporary_root = Path(temporary)
        candidate_root = temporary_root / "candidate-data"
        candidate_root.mkdir(mode=0o700)
        materialize_git_data_tree(
            repository_root,
            sampled_implementation_sha,
            candidate_root,
            protected_base_sha=protected_base_sha,
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
            "-c",
            _FROZEN_SAMPLE_LAUNCHER,
            str(protected_root),
            str(sample_path),
            str(candidate_root),
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
        "reviewed_source_base_is_ancestor_of_workflow_base": True,
        "reviewed_source_base_sha": policy["reviewed_source_base_sha"],
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
                    protected_base_sha=str(proof["current_protected_base_sha"]),
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
