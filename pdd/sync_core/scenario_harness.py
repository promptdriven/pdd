"""Checker-owned lifecycle scenarios shipped inside the released wheel."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import tempfile
import threading
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass, replace
from datetime import datetime, timedelta, timezone
from pathlib import Path, PurePosixPath
from typing import Callable

from .certificate import count_vendored_sync_semantics
from .classifier import classify
from .identity import initialize_repository_identity
from .manifest import build_unit_manifest
from .runner import AttestationIssue, RunBinding, RunnerConfig, run_profile
from .scenario_contract import REQUIRED_SCENARIOS
from .transaction import PlannedWrite, TransactionConflict, TransactionManager
from .trust import (
    AttestationBinding,
    AttestationError,
    AttestationRequest,
    AttestationSigner,
    AttestationTrustPolicy,
)
from .types import (
    ArtifactSnapshot,
    BaselineStatus,
    EvidenceOutcome,
    FingerprintProvenance,
    FingerprintRecord,
    SemanticStatus,
    UnitId,
    UnitSnapshot,
    VerificationObligation,
    VerificationProfile,
    ObligationEvidence,
)


@dataclass(frozen=True)
# pylint: disable=too-many-instance-attributes
class ScenarioResult:
    """One checker-owned scenario outcome."""

    scenario_id: str
    status: str
    detail: str = ""
    required_tests_skipped_or_xfailed: int = 0
    collection_errors: int = 0
    timeouts: int = 0
    post_repair_second_run_writes: int = 0
    post_merge_tree_changes: int = 0


def _profile(unit: UnitId) -> VerificationProfile:
    obligation = VerificationObligation(
        "tests",
        "test",
        "pytest",
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        ("REQ-1",),
        (PurePosixPath("tests/test_widget.py"),),
    )
    return VerificationProfile(unit, (obligation,), ("REQ-1",), "profile-v1")


def _snapshot(unit: UnitId, **changes: str | None) -> UnitSnapshot:
    values: dict[str, str | None] = {
        "prompt": "prompt-v1",
        "include": "include-v1",
        "code": "code-v1",
        "example": "example-v1",
        "test": "test-v1",
    }
    values.update(changes)
    paths = {
        "prompt": "prompts/widget_python.prompt",
        "include": "docs/widget.md",
        "code": "src/widget.py",
        "example": "examples/widget.py",
        "test": "tests/test_widget.py",
    }
    return UnitSnapshot(
        unit,
        tuple(
            ArtifactSnapshot(
                role,
                PurePosixPath(paths[role]),
                digest,
                "100644" if digest is not None else None,
            )
            for role, digest in values.items()
        ),
        "manifest-v1",
        "dependency-v1",
        "profile-v1",
    )


def _baseline(snapshot: UnitSnapshot) -> FingerprintRecord:
    provenance = FingerprintProvenance(
        "generated",
        "pdd sync widget",
        "checker-transaction",
        "checked-head",
        "2026-07-10T00:00:00+00:00",
        "released-checker",
    )
    return FingerprintRecord(
        snapshot, 2, 2, provenance, SemanticStatus.VERIFIED, "checker-attestation"
    )


def _git(root: Path, *arguments: str) -> str:
    completed = subprocess.run(
        ["git", *arguments],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise AssertionError(completed.stderr.strip() or "Git fixture command failed")
    return completed.stdout.strip()


def _candidate(
    arguments: argparse.Namespace, root: Path, *command: str
) -> subprocess.CompletedProcess[str]:
    """Run one public command from the separately installed candidate wheel."""
    return subprocess.run(
        [arguments.candidate_python, "-I", "-m", "pdd.cli", *command],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
        env={
            key: value
            for key, value in os.environ.items()
            if not any(
                marker in key.upper()
                for marker in ("API_KEY", "CREDENTIAL", "PASSWORD", "SECRET", "TOKEN")
            )
            and key not in {"PYTHONPATH", "PYTHONHOME", "PDD_PATH"}
        },
    )


def _git_fixture(root: Path) -> None:
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "checker@example.com")
    _git(root, "config", "user.name", "Released Checker")


def _commit(root: Path, message: str) -> str:
    _git(root, "add", ".")
    _git(root, "commit", "-qm", message)
    return _git(root, "rev-parse", "HEAD")


def _source_edit_matrix(_arguments: argparse.Namespace) -> ScenarioResult:
    unit = UnitId("checker-fixture", PurePosixPath("prompts/widget_python.prompt"), "python")
    baseline = _snapshot(unit)
    profile = _profile(unit)
    for role in ("prompt", "include", "code", "example", "test"):
        verdict = classify(
            _snapshot(unit, **{role: f"{role}-v2"}),
            _baseline(baseline),
            profile,
            None,
        )
        if verdict.in_sync or role not in verdict.changed_roles:
            raise AssertionError(f"{role}-only edit was not blocking")
    simultaneous = classify(
        _snapshot(unit, prompt="prompt-v2", code="code-v2"),
        _baseline(baseline),
        profile,
        None,
    )
    if simultaneous.semantic is not SemanticStatus.CONFLICT:
        raise AssertionError("simultaneous prompt/code edit was not a conflict")
    return ScenarioResult("source-edit-matrix", "PASS")


def _missing_corrupt_delete_mode(_arguments: argparse.Namespace) -> ScenarioResult:
    unit = UnitId("checker-fixture", PurePosixPath("prompts/widget_python.prompt"), "python")
    baseline = _snapshot(unit)
    profile = _profile(unit)
    missing = classify(
        _snapshot(unit, code=None), _baseline(baseline), profile, None
    )
    if missing.semantic is not SemanticStatus.FAILED:
        raise AssertionError("missing required artifact did not fail")
    corrupt_artifact = classify(
        _snapshot(unit, code="corrupt-content"),
        _baseline(baseline),
        profile,
        None,
    )
    if corrupt_artifact.baseline is not BaselineStatus.DRIFTED:
        raise AssertionError("corrupt artifact content was not detected")
    invalid_fingerprint = FingerprintRecord(
        baseline,
        1,
        2,
        _baseline(baseline).provenance,
        SemanticStatus.VERIFIED,
        "checker-attestation",
    )
    corrupt_fingerprint = classify(baseline, invalid_fingerprint, profile, None)
    if corrupt_fingerprint.baseline is not BaselineStatus.CORRUPT:
        raise AssertionError("corrupt fingerprint was not rejected")

    def relocated(path: str, *, manifest: str = "manifest-v1") -> UnitSnapshot:
        artifacts = tuple(
            ArtifactSnapshot(
                item.role,
                PurePosixPath(path) if item.role == "code" else item.relpath,
                item.digest,
                item.git_mode,
                item.required,
            )
            for item in baseline.artifacts
        )
        return UnitSnapshot(
            unit,
            artifacts,
            manifest,
            baseline.dependency_snapshot_digest,
            baseline.verification_profile_digest,
        )

    renamed = classify(
        relocated("src/widget_renamed.py"), _baseline(baseline), profile, None
    )
    if (
        renamed.baseline is not BaselineStatus.DRIFTED
        or "code" not in renamed.changed_roles
    ):
        raise AssertionError("renamed artifact was not detected")
    retargeted = classify(
        relocated("generated/widget.py", manifest="manifest-retargeted"),
        _baseline(baseline),
        profile,
        None,
    )
    if not {"code", "manifest"}.issubset(retargeted.changed_roles):
        raise AssertionError("retargeted artifact declaration was not detected")
    changed_mode = tuple(
        ArtifactSnapshot(
            item.role,
            item.relpath,
            item.digest,
            "100755" if item.role == "code" else item.git_mode,
        )
        for item in baseline.artifacts
    )
    mode_snapshot = UnitSnapshot(
        unit,
        changed_mode,
        baseline.manifest_digest,
        baseline.dependency_snapshot_digest,
        baseline.verification_profile_digest,
    )
    mode = classify(mode_snapshot, _baseline(baseline), profile, None)
    if "code" not in mode.changed_roles:
        raise AssertionError("mode-only change was not detected")
    return ScenarioResult("missing-corrupt-delete-mode", "PASS")


def _prepared_recovery(writes: tuple[PlannedWrite, ...]) -> None:
    with tempfile.TemporaryDirectory(prefix="pdd-checker-prepared-") as directory:
        root = Path(directory)
        (root / "src").mkdir()
        target = root / "src/widget.py"
        target.write_text("old\n")
        manager = TransactionManager(root)
        manager.prepare("prepared", writes)
        recovered = manager.recover("prepared")
        if recovered.phase.value != "ROLLED_BACK" or target.read_text() != "old\n":
            raise AssertionError("PREPARED journal recovery changed a destination")


def _recover_after_crashes(writes: tuple[PlannedWrite, ...]) -> None:
    crash_events = (
        "after_committing",
        "after_install:0",
        "after_install:1",
        "after_commit",
    )
    for index, event in enumerate(crash_events):
        with tempfile.TemporaryDirectory(prefix="pdd-checker-transaction-") as directory:
            root = Path(directory)
            (root / "src").mkdir()
            (root / "src/widget.py").write_text("old\n")
            manager = TransactionManager(root)
            manager.prepare(f"crash-{index}", writes)

            def crash(observed: str, expected: str = event) -> None:
                if observed == expected:
                    raise SystemExit("injected crash")

            try:
                manager.commit(f"crash-{index}", crash_hook=crash)
            except SystemExit:
                pass
            manager.recover(f"crash-{index}")
            if (root / "src/widget.py").read_text() != "new\n":
                raise AssertionError(f"recovery failed after {event}")
            if (root / ".pdd/evidence/widget.json").read_text() != "{}\n":
                raise AssertionError(f"recovery left a partial state after {event}")


def _external_write_race(writes: tuple[PlannedWrite, ...]) -> None:
    with tempfile.TemporaryDirectory(prefix="pdd-checker-race-") as directory:
        root = Path(directory)
        (root / "src").mkdir()
        target = root / "src/widget.py"
        target.write_text("old\n")
        manager = TransactionManager(root)
        manager.prepare("external-race", writes)
        target.write_text("external\n")
        try:
            manager.commit("external-race")
        except TransactionConflict:
            pass
        else:
            raise AssertionError("external write race was not rejected")


def _concurrent_sync_race(writes: tuple[PlannedWrite, ...]) -> None:
    with tempfile.TemporaryDirectory(prefix="pdd-checker-concurrent-") as directory:
        root = Path(directory)
        (root / "src").mkdir()
        (root / "src/widget.py").write_text("old\n")
        first = TransactionManager(root)
        second = TransactionManager(root)
        first.prepare("concurrent-a", writes)
        second.prepare("concurrent-b", writes)
        barrier = threading.Barrier(2)

        def commit(manager: TransactionManager, transaction_id: str) -> str:
            barrier.wait(timeout=10)
            try:
                manager.commit(transaction_id)
            except TransactionConflict:
                return "CONFLICT"
            return "COMMITTED"

        with ThreadPoolExecutor(max_workers=2) as executor:
            futures = (
                executor.submit(commit, first, "concurrent-a"),
                executor.submit(commit, second, "concurrent-b"),
            )
            outcomes = tuple(sorted(future.result() for future in futures))
        if outcomes != ("COMMITTED", "CONFLICT"):
            raise AssertionError(f"concurrent sync was not serialized: {outcomes}")


def _descriptor_swap_race(writes: tuple[PlannedWrite, ...]) -> None:
    # pylint: disable=protected-access
    with tempfile.TemporaryDirectory(prefix="pdd-checker-descriptor-") as directory:
        root = Path(directory)
        source = root / "src"
        outside = root / "outside"
        source.mkdir()
        outside.mkdir()
        (source / "widget.py").write_text("old\n")
        outside_target = outside / "widget.py"
        outside_target.write_text("outside\n")
        manager = TransactionManager(root)
        manager.prepare("descriptor-race", writes)
        canonical_relpath = manager._canonical_relpath
        armed = True

        def swap_after_resolution(relpath: PurePosixPath) -> PurePosixPath:
            nonlocal armed
            canonical = canonical_relpath(relpath)
            if armed and relpath == PurePosixPath("src/widget.py"):
                armed = False
                source.rename(root / "src-before-swap")
                source.symlink_to(outside, target_is_directory=True)
            return canonical

        manager._canonical_relpath = (  # type: ignore[method-assign]
            swap_after_resolution
        )
        try:
            manager.commit("descriptor-race")
        except TransactionConflict:
            pass
        else:
            raise AssertionError("descriptor-time parent swap was not rejected")
        if outside_target.read_text() != "outside\n":
            raise AssertionError("descriptor-time parent swap redirected a write")


def _transaction_crash_race(_arguments: argparse.Namespace) -> ScenarioResult:
    writes = (
        PlannedWrite(PurePosixPath("src/widget.py"), b"new\n", "100644"),
        PlannedWrite(PurePosixPath(".pdd/evidence/widget.json"), b"{}\n", "100644"),
    )
    _prepared_recovery(writes)
    _recover_after_crashes(writes)
    _external_write_race(writes)
    _concurrent_sync_race(writes)
    _descriptor_swap_race(writes)
    return ScenarioResult("transaction-crash-race-recovery", "PASS")


def _evidence_guards(_arguments: argparse.Namespace) -> ScenarioResult:
    now = datetime.now(timezone.utc)
    signer = AttestationSigner("checker-fixture", b"e" * 32)
    unit = UnitId("checker-fixture", PurePosixPath("prompts/widget_python.prompt"), "python")
    binding = AttestationBinding(
        unit, "snapshot", "profile", "runner", "checker", "base", "head"
    )
    envelope = signer.issue(
        AttestationRequest(
            "attestation",
            binding,
            (ObligationEvidence("tests", EvidenceOutcome.PASS),),
            "nonce",
            now,
        )
    )
    policy = AttestationTrustPolicy({"checker-fixture": signer.public_key_bytes()})
    policy.verify(envelope, binding, now=now)
    policy.verify(envelope, binding, now=now)
    replayed = signer.issue(
        AttestationRequest(
            "rebound-attestation",
            binding,
            envelope.results,
            "nonce",
            now,
        )
    )
    forged = replace(envelope, signature="Zm9yZ2Vk")
    for candidate, expected in (
        (replayed, binding),
        (forged, binding),
        (
            signer.issue(
                AttestationRequest(
                    "expired",
                    binding,
                    envelope.results,
                    "expired-nonce",
                    now - timedelta(hours=2),
                    timedelta(minutes=1),
                )
            ),
            binding,
        ),
    ):
        try:
            policy.verify(candidate, expected, now=now)
        except AttestationError:
            continue
        raise AssertionError("replayed or stale evidence was accepted")
    revoked = AttestationTrustPolicy(
        {"checker-fixture": signer.public_key_bytes()},
        revoked_issuers=frozenset({"checker-fixture"}),
    )
    try:
        revoked.verify(envelope, binding, now=now)
    except AttestationError:
        pass
    else:
        raise AssertionError("revoked evidence issuer was accepted")
    return ScenarioResult("forged-stale-replayed-revoked-evidence", "PASS")


def _complete_inventory(_arguments: argparse.Namespace) -> ScenarioResult:
    with tempfile.TemporaryDirectory(prefix="pdd-checker-inventory-") as directory:
        root = Path(directory)
        _git_fixture(root)
        initialize_repository_identity(
            root, "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"
        )
        (root / "prompts").mkdir()
        (root / "src").mkdir()
        (root / "prompts/widget_python.prompt").write_text("REQ-1: widget\n")
        (root / "src/widget.py").write_text("value = 1\n")
        (root / "README.md").write_text("human documentation\n")
        (root / ".pdd/sync-ownership.json").write_text(
            json.dumps(
                {
                    "rules": [
                        {
                            "pattern": "README.md",
                            "inventory": "HUMAN_OWNED",
                            "role": "documentation",
                            "owner": "docs@example.com",
                        }
                    ]
                }
            )
        )
        (root / "architecture.json").write_text(
            '[{"filename":"widget_python.prompt","filepath":"src/widget.py"}]\n'
        )
        base = _commit(root, "protected base")
        (root / "prompts/helper_python.prompt").write_text("REQ-1: helper\n")
        head = _commit(root, "candidate adds unit")
        manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
        tracked = set(_git(root, "ls-tree", "-r", "--name-only", head).splitlines())
        partition = {
            item.candidate_id.artifact_relpath.as_posix()
            for item in manifest.candidates
        }
        if partition != tracked or manifest.unaccounted_tracked_paths:
            raise AssertionError("base/head tracked inventory was incomplete")
        if len(manifest.expected_managed) != 2:
            raise AssertionError("candidate-added managed unit was omitted")
        (root / "prompts/widget_python.prompt").unlink()
        removed = _commit(root, "candidate removes unit")
        deletion = build_unit_manifest(root, base_ref=head, head_ref=removed)
        if not any("removed managed unit" in reason for reason in deletion.invalid_reasons):
            raise AssertionError("whole-unit deletion did not remain blocking")
    return ScenarioResult("complete-base-head-inventory", "PASS")


def _run_fixture_profile(content: str) -> EvidenceOutcome:
    with tempfile.TemporaryDirectory(prefix="pdd-checker-runner-") as directory:
        root = Path(directory)
        _git_fixture(root)
        (root / "tests").mkdir()
        (root / "tests/test_widget.py").write_text(content)
        head = _commit(root, "runner fixture")
        unit = UnitId(
            "checker-fixture", PurePosixPath("prompts/widget_python.prompt"), "python"
        )
        profile = _profile(unit)
        _envelope, executions = run_profile(
            root,
            profile,
            RunBinding("snapshot", head, head),
            AttestationIssue(
                AttestationSigner("runner-fixture", b"r" * 32),
                "runner-attestation",
                "runner-nonce",
                datetime.now(timezone.utc),
            ),
            RunnerConfig(timeout_seconds=30),
        )
        return executions[0].outcome


def _trusted_runner_outcomes(_arguments: argparse.Namespace) -> ScenarioResult:
    expected = {
        "def test_widget(): assert True\n": EvidenceOutcome.PASS,
        "import pytest\n@pytest.mark.skip(reason='required')\n"
        "def test_widget(): pass\n": EvidenceOutcome.SKIP,
        "import pytest\n@pytest.mark.xfail(reason='known')\n"
        "def test_widget(): assert True\n": EvidenceOutcome.XFAIL,
        "value = 1\n": EvidenceOutcome.NOT_COLLECTED,
    }
    for content, outcome in expected.items():
        observed = _run_fixture_profile(content)
        if observed is not outcome:
            raise AssertionError(f"runner normalized {observed.value}, expected {outcome.value}")
    return ScenarioResult("trusted-runner-outcomes", "PASS")


def _merge_base_movement(_arguments: argparse.Namespace) -> ScenarioResult:
    with tempfile.TemporaryDirectory(prefix="pdd-checker-merge-") as directory:
        root = Path(directory)
        _git_fixture(root)
        (root / "src").mkdir()
        target = root / "src/widget.py"
        target.write_text("base = True\n")
        _commit(root, "base")
        writes = (
            PlannedWrite(PurePosixPath("src/widget.py"), b"repair = True\n", "100644"),
        )
        stale = TransactionManager(root)
        stale.prepare("stale-repair", writes)
        target.write_text("merged = True\n")
        _commit(root, "merge group moved")
        try:
            stale.commit("stale-repair")
        except TransactionConflict:
            pass
        else:
            raise AssertionError("stale repair survived merge-group movement")
        fresh = TransactionManager(root)
        fresh.prepare("fresh-repair", writes)
        fresh.commit("fresh-repair")
        before = _git(root, "status", "--porcelain", "--untracked-files=all")
        second = fresh.prepare("post-merge-second", writes)
        after = _git(root, "status", "--porcelain", "--untracked-files=all")
        changes = int(before != after) + len(second.changed_paths)
        if changes:
            raise AssertionError("post-merge immediate rerun changed the tree")
    return ScenarioResult(
        "merge-group-base-movement-and-stale-repair",
        "PASS",
        post_merge_tree_changes=0,
    )


def _transactional_report(_arguments: argparse.Namespace) -> ScenarioResult:
    with tempfile.TemporaryDirectory(prefix="pdd-checker-noop-") as directory:
        root = Path(directory)
        writes = (
            PlannedWrite(PurePosixPath("src/widget.py"), b"value = 1\n", "100644"),
            PlannedWrite(PurePosixPath(".pdd/evidence/widget.json"), b"{}\n", "100644"),
            PlannedWrite(PurePosixPath(".pdd/meta/v2/widget.json"), b"{}\n", "100644"),
        )
        manager = TransactionManager(root)
        manager.prepare("first", writes)
        manager.commit("first")
        second = manager.prepare("second", writes)
        if not second.no_op or second.changed_paths:
            raise AssertionError("immediate transaction rerun was not a no-op")
    return ScenarioResult(
        "transactional-canonical-report",
        "PASS",
    )


def _built_wheel(arguments: argparse.Namespace) -> ScenarioResult:
    if "site-packages" not in Path(__file__).resolve().parts:
        raise AssertionError("scenario harness is not running from an installed wheel")
    probe = subprocess.run(
        [
            arguments.candidate_python,
            "-I",
            "-c",
            "import pathlib,pdd; print(pathlib.Path(pdd.__file__).resolve())",
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    candidate_environment = Path(arguments.candidate_python).absolute().parents[1].resolve()
    try:
        Path(probe.stdout.strip()).resolve().relative_to(candidate_environment)
    except ValueError as exc:
        raise AssertionError("candidate package was not imported from its wheel venv") from exc
    if probe.returncode != 0 or "site-packages" not in probe.stdout:
        raise AssertionError("candidate wheel import probe failed")
    return ScenarioResult("built-wheel-clean-environment", "PASS")


def _candidate_public_report(arguments: argparse.Namespace) -> ScenarioResult:
    with tempfile.TemporaryDirectory(prefix="pdd-candidate-report-") as directory:
        root = Path(directory)
        _git_fixture(root)
        initialize_repository_identity(
            root, "3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0"
        )
        (root / "prompts").mkdir()
        (root / "src").mkdir()
        (root / "tests").mkdir()
        (root / "prompts/widget_python.prompt").write_text("REQ-1: widget\n")
        (root / "src/widget.py").write_text("value = 1\n")
        (root / "tests/test_widget.py").write_text("def test_widget(): assert True\n")
        (root / "architecture.json").write_text(
            '[{"filename":"widget_python.prompt","filepath":"src/widget.py"}]\n'
        )
        (root / ".pdd/verification-profiles.json").write_text(
            json.dumps(
                {
                    "profiles": [
                        {
                            "prompt_path": "prompts/widget_python.prompt",
                            "language_id": "python",
                            "required_requirement_ids": ["REQ-1"],
                            "obligations": [
                                {
                                    "obligation_id": "pytest",
                                    "kind": "test",
                                    "validator_id": "pytest",
                                    "validator_config_digest": (
                                        "e3b0c44298fc1c149afbf4c8996fb924"
                                        "27ae41e4649b934ca495991b7852b855"
                                    ),
                                    "requirement_ids": ["REQ-1"],
                                    "artifact_paths": ["tests/test_widget.py"],
                                }
                            ],
                        }
                    ]
                }
            )
        )
        commit = _commit(root, "candidate report fixture")
        output = root / "candidate-report.json"
        result = _candidate(
            arguments,
            root,
            "sync",
            "certify",
            "--base-ref",
            commit,
            "--head-ref",
            commit,
            "--replay-ledger",
            str(root.parent / "candidate-replay.json"),
            "--output",
            str(output),
        )
        report = json.loads(output.read_text(encoding="utf-8"))
        if result.returncode != 1:
            raise AssertionError("unbaselined candidate report did not fail closed")
        if report.get("counts", {}).get("unbaselined") != 1:
            raise AssertionError("candidate report omitted unbaselined managed unit")
    return ScenarioResult("candidate-wheel-public-report", "PASS")


def _candidate_transaction_recovery(arguments: argparse.Namespace) -> ScenarioResult:
    writes = (
        PlannedWrite(PurePosixPath("src/widget.py"), b"new\n", "100644"),
        PlannedWrite(PurePosixPath(".pdd/evidence/widget.json"), b"{}\n", "100644"),
    )
    with tempfile.TemporaryDirectory(prefix="pdd-candidate-recovery-") as directory:
        root = Path(directory)
        (root / "src").mkdir()
        (root / "src/widget.py").write_text("old\n")
        manager = TransactionManager(root)
        manager.prepare("candidate-recovery", writes)

        def crash(event: str) -> None:
            if event == "after_install:0":
                raise SystemExit("injected process death")

        try:
            manager.commit("candidate-recovery", crash_hook=crash)
        except SystemExit:
            pass
        result = _candidate(
            arguments,
            root,
            "recover",
            "--transaction",
            "candidate-recovery",
        )
        if result.returncode != 0:
            raise AssertionError("candidate public recovery command failed")
        json_start = result.stdout.find("{")
        if json_start < 0:
            raise AssertionError("candidate recovery emitted no machine result")
        payload, _end = json.JSONDecoder().raw_decode(result.stdout[json_start:])
        if payload.get("phase") != "COMMITTED":
            raise AssertionError("candidate recovery did not commit the journal")
        if (root / "src/widget.py").read_text() != "new\n":
            raise AssertionError("candidate recovery left old artifact bytes")
        if (root / ".pdd/evidence/widget.json").read_text() != "{}\n":
            raise AssertionError("candidate recovery left partial evidence state")
    return ScenarioResult("candidate-wheel-transaction-recovery", "PASS")


def _cloud_canary(arguments: argparse.Namespace) -> ScenarioResult:
    cloud = Path(arguments.cloud_root).resolve()
    count = count_vendored_sync_semantics(
        cloud, base_ref=arguments.cloud_base_ref, head_ref=arguments.cloud_head_ref
    )
    if count:
        raise AssertionError(f"pdd_cloud retains {count} vendored sync semantics")
    before = _git(cloud, "status", "--porcelain", "--untracked-files=all")
    with tempfile.TemporaryDirectory(prefix="pdd-cloud-canary-") as directory:
        temporary = Path(directory)
        output = temporary / "report.json"
        candidate = _candidate(
            arguments,
            cloud,
            "sync",
            "certify",
            "--base-ref",
            arguments.cloud_base_ref,
            "--head-ref",
            arguments.cloud_head_ref,
            "--replay-ledger",
            str(temporary / "replay.json"),
            "--output",
            str(output),
        )
        report = json.loads(output.read_text(encoding="utf-8"))
    after = _git(cloud, "status", "--porcelain", "--untracked-files=all")
    if candidate.returncode != 0:
        counts = report.get("counts", {})
        raise AssertionError(
            "pdd_cloud candidate command is red: "
            + json.dumps(counts, sort_keys=True, separators=(",", ":"))
        )
    if before != after:
        raise AssertionError("pdd_cloud candidate canary mutated the checkout")
    if report.get("ok") is not True:
        counts = report.get("counts", {})
        raise AssertionError(
            "pdd_cloud canonical report is red: "
            + json.dumps(counts, sort_keys=True, separators=(",", ":"))
        )
    return ScenarioResult("pdd-cloud-real-consumer-canary", "PASS")


def _owned_harness(_arguments: argparse.Namespace) -> ScenarioResult:
    if any(
        marker in key.upper()
        for key in os.environ
        for marker in ("SIGNING_KEY", "CERTIFICATE_SIGNING", "ATTESTATION_SIGNING")
    ):
        raise AssertionError("scenario child received signing material")
    return ScenarioResult("released-checker-owned-scenario-harness", "PASS")


SCENARIOS: dict[str, Callable[[argparse.Namespace], ScenarioResult]] = {
    "source-edit-matrix": _source_edit_matrix,
    "missing-corrupt-delete-mode": _missing_corrupt_delete_mode,
    "transaction-crash-race-recovery": _transaction_crash_race,
    "forged-stale-replayed-revoked-evidence": _evidence_guards,
    "complete-base-head-inventory": _complete_inventory,
    "trusted-runner-outcomes": _trusted_runner_outcomes,
    "transactional-canonical-report": _transactional_report,
    "merge-group-base-movement-and-stale-repair": _merge_base_movement,
    "built-wheel-clean-environment": _built_wheel,
    "candidate-wheel-public-report": _candidate_public_report,
    "candidate-wheel-transaction-recovery": _candidate_transaction_recovery,
    "pdd-cloud-real-consumer-canary": _cloud_canary,
    "released-checker-owned-scenario-harness": _owned_harness,
}


def run_scenarios(arguments: argparse.Namespace) -> tuple[ScenarioResult, ...]:
    # pylint: disable=broad-exception-caught
    """Run every checker-owned scenario and normalize exceptions as failures."""
    results: list[ScenarioResult] = []
    for scenario_id in sorted(REQUIRED_SCENARIOS):
        scenario = SCENARIOS.get(scenario_id)
        if scenario is None:
            results.append(ScenarioResult(scenario_id, "MISSING", "scenario is absent"))
            continue
        try:
            result = scenario(arguments)
        except (Exception, SystemExit) as exc:
            result = ScenarioResult(scenario_id, "FAIL", f"{type(exc).__name__}: {exc}")
        results.append(result)
    return tuple(results)


def main() -> None:
    """Run the complete harness and write a normalized machine result."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cloud-root", required=True)
    parser.add_argument("--cloud-base-ref", required=True)
    parser.add_argument("--cloud-head-ref", required=True)
    parser.add_argument("--candidate-python", required=True)
    arguments = parser.parse_args()
    results = run_scenarios(arguments)
    payload = {
        "schema_version": 1,
        "results": [asdict(result) for result in results],
    }
    arguments.output.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")
    if any(result.status != "PASS" for result in results):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
