"""Strict tests for protected candidate-wheel build provenance."""
# pylint: disable=missing-function-docstring,line-too-long,too-many-arguments

import base64
import hashlib
import json
import subprocess
import sys
import threading
import zipfile
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest
import yaml

from pdd.sync_core import AttestationSigner
from pdd.sync_core.artifact_provenance import (
    CandidateArtifactPolicy,
    CandidateArtifactProvenanceError,
    TARGET_BASE_IMAGE,
    TARGET_RESOLVER,
    TARGET_RUNTIME,
    TargetRuntimeLockError,
    generate_target_runtime_lock,
    load_candidate_artifact_provenance,
    parse_target_runtime_lock,
    validate_installed_target_runtime,
    validate_target_wheelhouse,
)


SOURCE_SHA = "a" * 40
LOCK_SHA256 = "b" * 64
WORKFLOW = "promptdriven/pdd/.github/workflows/candidate-wheel.yml@refs/heads/main"
ROOT = Path(__file__).resolve().parents[1]
TARGET = {
    "implementation": "CPython",
    "version": "3.12.3",
    "abi": "cp312",
    "platform": "manylinux_2_17_x86_64",
}


def _policy(authority: AttestationSigner) -> CandidateArtifactPolicy:
    return CandidateArtifactPolicy(
        authority.issuer,
        authority.public_key_bytes(),
        WORKFLOW,
        LOCK_SHA256,
        TARGET["implementation"],
        TARGET["version"],
        TARGET["abi"],
        TARGET["platform"],
    )


def _policy_with_replay_ledger(authority: AttestationSigner, replay_ledger) -> CandidateArtifactPolicy:
    policy = _policy(authority)
    policy.replay_ledger_path = replay_ledger
    return policy


def _attestation(
    wheel,
    authority: AttestationSigner,
    **overrides,
) -> dict:
    now = datetime.now(timezone.utc)
    payload = {
        "schema_version": 1,
        "issuer": authority.issuer,
        "attestation_id": "candidate-build-123",
        "nonce": "candidate-build-nonce-123",
        "issued_at": now.isoformat(),
        "expires_at": (now + timedelta(minutes=10)).isoformat(),
        "wheel_sha256": hashlib.sha256(wheel.read_bytes()).hexdigest(),
        "source_sha": SOURCE_SHA,
        "dependency_lock_sha256": LOCK_SHA256,
        "python": TARGET,
        "builder_workflow_identity": WORKFLOW,
    }
    payload.update(overrides)
    payload["signature"] = {
        "algorithm": "Ed25519",
        "value": authority.sign_bytes(
            json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
        ),
    }
    return payload


def _load(tmp_path, wheel, authority, **overrides):
    path = tmp_path / "candidate-build-attestation.json"
    path.write_text(json.dumps(_attestation(wheel, authority, **overrides)))
    return load_candidate_artifact_provenance(path, wheel, _policy(authority))


def test_unrelated_wheel_cannot_use_another_wheels_attestation(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    certified = tmp_path / "certified.whl"
    unrelated = tmp_path / "unrelated.whl"
    certified.write_bytes(b"certified candidate wheel")
    unrelated.write_bytes(b"unrelated candidate wheel")
    with pytest.raises(CandidateArtifactProvenanceError, match="digest"):
        _load(tmp_path, unrelated, authority, wheel_sha256=hashlib.sha256(certified.read_bytes()).hexdigest())


def test_correct_wheel_with_wrong_certified_source_sha_is_rejected(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    with pytest.raises(CandidateArtifactProvenanceError, match="source SHA"):
        _load(tmp_path, wheel, authority, source_sha="c" * 40).verify(
            _policy(authority), expected_source_sha=SOURCE_SHA
        )


def test_forged_build_attestation_is_rejected(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    path = tmp_path / "candidate-build-attestation.json"
    forged = _attestation(wheel, authority)
    forged["source_sha"] = "c" * 40
    path.write_text(json.dumps(forged))
    with pytest.raises(CandidateArtifactProvenanceError, match="signature"):
        load_candidate_artifact_provenance(path, wheel, _policy(authority))


def test_stale_or_replayed_build_attestation_is_rejected(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    with pytest.raises(CandidateArtifactProvenanceError, match="expired"):
        _load(
            tmp_path,
            wheel,
            authority,
            issued_at=(datetime.now(timezone.utc) - timedelta(hours=2)).isoformat(),
            expires_at=(datetime.now(timezone.utc) - timedelta(hours=1)).isoformat(),
        )
    policy = _policy(authority)
    provenance = _load(tmp_path, wheel, authority)
    provenance.verify(policy, expected_source_sha=SOURCE_SHA)
    with pytest.raises(CandidateArtifactProvenanceError, match="replayed"):
        provenance.verify(policy, expected_source_sha=SOURCE_SHA)


def test_overlong_build_attestation_is_rejected(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    issued = datetime.now(timezone.utc)
    with pytest.raises(CandidateArtifactProvenanceError, match="lifetime"):
        _load(
            tmp_path,
            wheel,
            authority,
            issued_at=issued.isoformat(),
            expires_at=(issued + timedelta(days=1)).isoformat(),
        )


@pytest.mark.parametrize("link_parent", [False, True])
def test_durable_replay_ledger_rejects_symlink_components(tmp_path, link_parent) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    outside = tmp_path / "outside"
    outside.mkdir()
    if link_parent:
        linked = tmp_path / "linked"
        linked.symlink_to(outside, target_is_directory=True)
        replay_ledger = linked / "replay.json"
    else:
        target = outside / "replay.json"
        target.write_text("[]")
        replay_ledger = tmp_path / "replay.json"
        replay_ledger.symlink_to(target)
    provenance = _load(tmp_path, wheel, authority)
    with pytest.raises(CandidateArtifactProvenanceError, match="unsafe"):
        provenance.verify(
            _policy_with_replay_ledger(authority, replay_ledger),
            expected_source_sha=SOURCE_SHA,
        )


def test_replayed_build_attestation_is_rejected_across_policy_instances(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    replay_ledger = tmp_path / "external-candidate-replay.json"
    provenance = _load(tmp_path, wheel, authority)
    provenance.verify(
        _policy_with_replay_ledger(authority, replay_ledger),
        expected_source_sha=SOURCE_SHA,
    )
    with pytest.raises(CandidateArtifactProvenanceError, match="replayed"):
        provenance.verify(
            _policy_with_replay_ledger(authority, replay_ledger),
            expected_source_sha=SOURCE_SHA,
        )


def test_concurrent_durable_replay_consumers_are_atomic(tmp_path, monkeypatch) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    replay_ledger = tmp_path / "external-candidate-replay.json"
    provenance = _load(tmp_path, wheel, authority)
    write_barrier = threading.Barrier(2)
    original_write_text = type(replay_ledger).write_text

    def synchronized_ledger_write(path, *args, **kwargs):
        if path == replay_ledger:
            write_barrier.wait(timeout=5)
        return original_write_text(path, *args, **kwargs)

    monkeypatch.setattr(type(replay_ledger), "write_text", synchronized_ledger_write)
    results: list[str] = []
    lock = threading.Lock()

    def consume() -> None:
        try:
            provenance.verify(
                _policy_with_replay_ledger(authority, replay_ledger),
                expected_source_sha=SOURCE_SHA,
            )
            outcome = "accepted"
        except CandidateArtifactProvenanceError as exc:
            outcome = str(exc)
        with lock:
            results.append(outcome)

    threads = [threading.Thread(target=consume) for _ in range(2)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join(timeout=10)

    assert sorted(results) == ["accepted", "candidate attestation is replayed"]


@pytest.mark.parametrize(
    ("field", "value", "error"),
    [
        ("builder_workflow_identity", "attacker/workflow@main", "builder workflow"),
        ("dependency_lock_sha256", "c" * 64, "dependency lock"),
        ("python", {**TARGET, "abi": "cp313"}, "interpreter"),
    ],
)
def test_wrong_protected_build_environment_is_rejected(tmp_path, field, value, error) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    with pytest.raises(CandidateArtifactProvenanceError, match=error):
        _load(tmp_path, wheel, authority, **{field: value}).verify(
            _policy(authority), expected_source_sha=SOURCE_SHA
        )


def test_source_checkout_is_not_a_candidate_artifact(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    checkout = tmp_path / "pdd"
    checkout.mkdir()
    path = tmp_path / "candidate-build-attestation.json"
    path.write_text(json.dumps(_attestation(wheel, authority)))
    with pytest.raises(CandidateArtifactProvenanceError, match="wheel path"):
        load_candidate_artifact_provenance(path, checkout, _policy(authority))


def test_valid_exact_sha_artifact_is_accepted(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    provenance = _load(tmp_path, wheel, authority)
    provenance.verify(_policy(authority), expected_source_sha=SOURCE_SHA)
    assert provenance.source_sha == SOURCE_SHA
    assert provenance.wheel_sha256 == hashlib.sha256(wheel.read_bytes()).hexdigest()


def test_durable_replay_ledger_rejects_symlink_lock(tmp_path) -> None:
    authority = AttestationSigner("candidate-builder", b"a" * 32)
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"exact wheel")
    replay_ledger = tmp_path / "replay.json"
    outside = tmp_path / "outside.lock"
    outside.write_text("do not touch")
    replay_ledger.with_name("replay.json.lock").symlink_to(outside)
    provenance = _load(tmp_path, wheel, authority)
    with pytest.raises(CandidateArtifactProvenanceError, match="unsafe"):
        provenance.verify(
            _policy_with_replay_ledger(authority, replay_ledger),
            expected_source_sha=SOURCE_SHA,
        )


def _record_hash(content: bytes) -> str:
    return base64.urlsafe_b64encode(hashlib.sha256(content).digest()).rstrip(b"=").decode()


def _wheel(
    root,
    name: str,
    version: str = "1.0",
    *,
    tags: str = "py3-none-any",
    metadata_name: str | None = None,
    extra: dict[str, bytes] | None = None,
) -> Path:
    """Make a minimal regular wheel with a valid, deterministic RECORD."""
    filename = f"{name.replace('-', '_')}-{version}-{tags}.whl"
    path = root / filename
    distribution = f"{name.replace('-', '_')}-{version}.dist-info"
    files = {
        f"{name.replace('-', '_')}/__init__.py": b"VALUE = 1\n",
        f"{distribution}/METADATA": (
            f"Metadata-Version: 2.1\nName: {metadata_name or name}\nVersion: {version}\n"
        ).encode(),
        f"{distribution}/WHEEL": b"Wheel-Version: 1.0\nGenerator: test\nRoot-Is-Purelib: true\n",
    }
    files.update(extra or {})
    record = "".join(
        f"{entry},sha256={_record_hash(content)},{len(content)}\n"
        for entry, content in sorted(files.items())
    ) + f"{distribution}/RECORD,,\n"
    with zipfile.ZipFile(path, "w") as archive:
        for entry, content in files.items():
            archive.writestr(entry, content)
        archive.writestr(f"{distribution}/RECORD", record)
    return path


def _install_wheel(wheel, target) -> None:
    """Materialize the exact --target-style contents expected by the validator."""
    with zipfile.ZipFile(wheel) as archive:
        files = {
            name: archive.read(name)
            for name in archive.namelist()
            if not name.endswith("/") and not name.endswith(".dist-info/RECORD")
        }
    dist_info_name = next(
        Path(name).parent.name for name in files if name.endswith(".dist-info/METADATA")
    )
    for relative, content in files.items():
        destination = target / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(content)
    rows = []
    for relative, content in sorted(files.items()):
        rows.append(f"{relative},sha256={_record_hash(content)},{len(content)}\n")
    (target / dist_info_name / "RECORD").write_text(
        "".join(rows) + f"{dist_info_name}/RECORD,,\n", encoding="utf-8"
    )


def _runtime_fixture(tmp_path):
    wheelhouse = tmp_path / "wheelhouse"
    wheelhouse.mkdir()
    dependency = _wheel(wheelhouse, "demo-dependency")
    project = _wheel(tmp_path, "pdd-cli", "2.0")
    lock = generate_target_runtime_lock(wheelhouse)
    installed = tmp_path / "installed"
    installed.mkdir()
    _install_wheel(dependency, installed)
    _install_wheel(project, installed)
    return lock, wheelhouse, installed, project


def test_target_lock_round_trip_has_fixed_target_bindings(tmp_path) -> None:
    wheelhouse = tmp_path / "wheelhouse"
    wheelhouse.mkdir()
    _wheel(wheelhouse, "zeta")
    _wheel(wheelhouse, "alpha", "2.0")

    lock = generate_target_runtime_lock(wheelhouse)

    assert parse_target_runtime_lock(lock.bytes()) == lock
    assert lock.bytes().decode().splitlines()[:4] == [
        "# pdd-runtime-lock-format: 1",
        f"# target: {TARGET_RUNTIME}",
        f"# resolver: {TARGET_RESOLVER}",
        f"# base-image: {TARGET_BASE_IMAGE}",
    ]
    assert [entry.name for entry in lock.entries] == ["alpha", "zeta"]


@pytest.mark.parametrize(
    "mutation",
    [
        b"# pdd-runtime-lock-format: 1\n# target: linux_x86_64-cp312\n# resolver: pip==25.1.1\n# base-image: fake\n",
        b"# pdd-runtime-lock-format: 1\n# target: linux_x86_64-cp312\n# resolver: pip==25.1.1\n# base-image: python:3.12.13-slim-bookworm@sha256:72d3d75f2639ab82b34b29390ad3d6e0827c775befee94edda8e9976818f488d\n# comment\n",
        b"# pdd-runtime-lock-format: 1\n# target: linux_x86_64-cp312\n# resolver: pip==25.1.1\n# base-image: python:3.12.13-slim-bookworm@sha256:72d3d75f2639ab82b34b29390ad3d6e0827c775befee94edda8e9976818f488d\ndemo_dependency==1.0 --hash=sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n",
        b"# pdd-runtime-lock-format: 1\n# target: linux_x86_64-cp312\n# resolver: pip==25.1.1\n# base-image: python:3.12.13-slim-bookworm@sha256:72d3d75f2639ab82b34b29390ad3d6e0827c775befee94edda8e9976818f488d\npdd-cli==1.0 --hash=sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n",
        b"# pdd-runtime-lock-format: 1\n# target: linux_x86_64-cp312\n# resolver: pip==25.1.1\n# base-image: python:3.12.13-slim-bookworm@sha256:72d3d75f2639ab82b34b29390ad3d6e0827c775befee94edda8e9976818f488d\ndemo==1.0; python_version > '3' --hash=sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n",
    ],
)
def test_target_lock_rejects_noncanonical_or_unsafe_rows(mutation) -> None:
    with pytest.raises(TargetRuntimeLockError):
        parse_target_runtime_lock(mutation)


@pytest.mark.parametrize(
    ("tags", "metadata_name"),
    [
        ("cp312-cp312-macosx_11_0_x86_64", None),
        ("cp312-cp312-win_amd64", None),
        ("cp312-cp312-manylinux_2_17_aarch64", None),
        ("cp312-cp312-manylinux_2_99_x86_64", None),
        ("py3-none-any", "different"),
    ],
)
def test_target_wheelhouse_rejects_incompatible_or_misidentified_wheel(
    tmp_path, tags, metadata_name
) -> None:
    wheelhouse = tmp_path / "wheelhouse"
    wheelhouse.mkdir()
    _wheel(wheelhouse, "demo", tags=tags, metadata_name=metadata_name)

    with pytest.raises(TargetRuntimeLockError):
        generate_target_runtime_lock(wheelhouse)


def test_target_wheelhouse_accepts_bookworm_compatible_legacy_manylinux_tag(tmp_path) -> None:
    wheelhouse = tmp_path / "wheelhouse"
    wheelhouse.mkdir()
    _wheel(wheelhouse, "demo", tags="cp312-cp312-manylinux2014_x86_64")

    assert generate_target_runtime_lock(wheelhouse).entries[0].name == "demo"


def test_target_wheelhouse_requires_exact_bijection_and_regular_members(tmp_path) -> None:
    wheelhouse = tmp_path / "wheelhouse"
    wheelhouse.mkdir()
    _wheel(wheelhouse, "demo")
    lock = generate_target_runtime_lock(wheelhouse)
    _wheel(wheelhouse, "extra")
    with pytest.raises(TargetRuntimeLockError, match="extra"):
        validate_target_wheelhouse(lock, wheelhouse)

    (wheelhouse / "README.txt").write_text("not a wheel", encoding="utf-8")
    with pytest.raises(TargetRuntimeLockError, match="non-wheel"):
        validate_target_wheelhouse(lock, wheelhouse)


def test_target_wheelhouse_rejects_archive_escape_links_and_ambiguous_names(tmp_path) -> None:
    wheelhouse = tmp_path / "wheelhouse"
    wheelhouse.mkdir()
    malicious = _wheel(wheelhouse, "demo")
    with zipfile.ZipFile(malicious, "a") as archive:
        link = zipfile.ZipInfo("demo/link")
        link.external_attr = 0o120777 << 16
        archive.writestr(link, b"outside")
    with pytest.raises(TargetRuntimeLockError, match="unsafe"):
        generate_target_runtime_lock(wheelhouse)

    malicious.unlink()
    _wheel(wheelhouse, "demo", tags="py3-none-any")
    _wheel(wheelhouse, "demo", tags="cp312-cp312-manylinux_2_17_x86_64")
    with pytest.raises(TargetRuntimeLockError, match="duplicate"):
        generate_target_runtime_lock(wheelhouse)


@pytest.mark.parametrize("tamper", ["hash", "nohash", "extra", "overlap", "project", "base"])
def test_installed_target_runtime_fails_closed_on_tampering(tmp_path, tamper) -> None:
    lock, wheelhouse, installed, project = _runtime_fixture(tmp_path)
    demo_record = next(installed.glob("demo_dependency-*.dist-info/RECORD"))
    if tamper == "hash":
        demo_record.write_text(
            demo_record.read_text(encoding="utf-8").replace("sha256=", "sha256=x", 1),
            encoding="utf-8",
        )
    elif tamper == "nohash":
        demo_record.write_text(
            demo_record.read_text(encoding="utf-8").replace("sha256=", "", 1),
            encoding="utf-8",
        )
    elif tamper == "extra":
        (installed / "unexpected.py").write_text("x = 1\n", encoding="utf-8")
    elif tamper == "overlap":
        project_record = next(installed.glob("pdd_cli-*.dist-info/RECORD"))
        project_record.write_text(
            project_record.read_text(encoding="utf-8")
            + demo_record.read_text(encoding="utf-8").splitlines()[0]
            + "\n",
            encoding="utf-8",
        )
    elif tamper == "base":
        base = installed / "base-1.0.dist-info"
        base.mkdir()
        (base / "METADATA").write_text(
            "Metadata-Version: 2.1\nName: base\nVersion: 1.0\n", encoding="utf-8"
        )
        (base / "RECORD").write_text("base-1.0.dist-info/RECORD,,\n", encoding="utf-8")
    else:
        (installed / "pdd_cli/__init__.py").write_text("VALUE = 2\n", encoding="utf-8")
    with pytest.raises(TargetRuntimeLockError):
        validate_installed_target_runtime(lock, wheelhouse, installed, project)


def test_installed_target_runtime_accepts_exact_wheel_closure(tmp_path) -> None:
    lock, wheelhouse, installed, project = _runtime_fixture(tmp_path)

    validate_installed_target_runtime(lock, wheelhouse, installed, project)


def test_real_pip_target_install_closes_console_scripts_under_target_root(tmp_path) -> None:
    wheelhouse = tmp_path / "wheelhouse"
    project_directory = tmp_path / "project"
    wheelhouse.mkdir()
    project_directory.mkdir()
    _wheel(wheelhouse, "demo-dependency")
    project = _wheel(
        project_directory,
        "pdd-cli",
        "2.0",
        extra={
            "pdd_cli-2.0.dist-info/entry_points.txt": b"[console_scripts]\npdd = pdd_cli:main\n"
        },
    )
    lock = generate_target_runtime_lock(wheelhouse)
    requirements = tmp_path / "requirements.lock"
    requirements.write_bytes(
        lock.bytes()
        + f"pdd-cli==2.0 --hash=sha256:{hashlib.sha256(project.read_bytes()).hexdigest()}\n".encode()
    )
    installed = tmp_path / "installed"
    subprocess.run(
        [
            sys.executable,
            "-m",
            "pip",
            "install",
            "--no-index",
            "--no-compile",
            "--only-binary=:all:",
            "--require-hashes",
            "--find-links",
            str(wheelhouse),
            "--find-links",
            str(project_directory),
            "--target",
            str(installed),
            "-r",
            str(requirements),
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    validate_installed_target_runtime(
        lock, wheelhouse, installed, project, Path(sys.executable)
    )
    record = next(installed.glob("pdd_cli-*.dist-info/RECORD")).read_text(encoding="utf-8")
    assert "../../bin/pdd," in record
    assert (installed / "bin/pdd").is_file()


def test_isolated_runtime_bootstrap_does_not_execute_candidate_sitecustomize(tmp_path) -> None:
    candidate = tmp_path / "candidate"
    candidate.mkdir()
    marker = tmp_path / "sitecustomize-ran"
    (candidate / "sitecustomize.py").write_text(
        f"from pathlib import Path\nPath({str(marker)!r}).write_text('ran')\n", encoding="utf-8"
    )
    bootstrap = "import sys; sys.path.insert(0, sys.argv[1])"

    subprocess.run(
        [
            sys.executable,
            "-I",
            "-S",
            "-c",
            bootstrap,
            str(candidate),
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    assert not marker.exists()


def test_target_runtime_lock_cli_generates_and_validates(tmp_path) -> None:
    wheelhouse = tmp_path / "wheelhouse"
    wheelhouse.mkdir()
    _wheel(wheelhouse, "demo")
    lock_path = tmp_path / "runtime.lock"
    inventory = tmp_path / "inventory.json"
    command = [sys.executable, "-m", "pdd.sync_core.artifact_provenance"]

    subprocess.run(
        command
        + [
            "generate",
            "--wheelhouse",
            str(wheelhouse),
            "--output",
            str(lock_path),
            "--inventory",
            str(inventory),
        ],
        cwd=ROOT,
        check=True,
    )
    subprocess.run(
        command + ["validate-wheelhouse", "--lock", str(lock_path), "--wheelhouse", str(wheelhouse)],
        cwd=ROOT,
        check=True,
    )
    assert parse_target_runtime_lock(lock_path.read_bytes()).entries[0].name == "demo"
    assert json.loads(inventory.read_text(encoding="ascii"))[0]["filename"].endswith(".whl")


def test_target_runtime_workflow_is_offline_validated_before_artifact_upload() -> None:
    workflow_path = ROOT / ".github/workflows/unit-tests.yml"
    workflow = workflow_path.read_text(encoding="utf-8")
    payload = yaml.safe_load(workflow)
    job = payload["jobs"]["target-runtime-lock"]
    steps = job["steps"]
    names = [step["name"] for step in steps]
    generation = workflow.index("Generate Linux CPython 3.12 candidate lock online")
    validation = workflow.index("Validate candidate in fresh network-none container")
    upload = workflow.index("Upload target runtime lock candidate")

    assert job["runs-on"] == "ubuntu-latest"
    assert job["timeout-minutes"] == 30
    assert generation < validation < upload
    assert "python:3.12.13-slim-bookworm@sha256:72d3d75f2639ab82b34b29390ad3d6e0827c775befee94edda8e9976818f488d" in workflow
    assert "docker run --rm --network bridge" in workflow
    assert "docker run --rm --network none" in workflow
    assert "--only-binary=:all:" in workflow
    assert "--no-compile" in workflow
    assert "--require-hashes" in workflow
    assert "--find-links /runtime/project" in workflow
    assert "pip==25.1.1 build==1.2.2.post1" in workflow
    assert "actions/checkout@df4cb1c069e1874edd31b4311f1884172cec0e10" in workflow
    assert "actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02" in workflow
    assert "release.yml" not in workflow[workflow.index("  target-runtime-lock:") :]
    assert "Gate 2" not in workflow
    assert "Certificate" not in workflow
    assert names[-1] == "Upload target runtime lock candidate"
    target_job = workflow[workflow.index("  target-runtime-lock:") :]
    build_step = next(
        step["run"]
        for step in steps
        if step["name"] == "Generate Linux CPython 3.12 candidate lock online"
    )
    synthetic_build = (
        "SETUPTOOLS_SCM_PRETEND_VERSION_FOR_PDD_CLI=0.0.0 "
        "python -m build --wheel --outdir /runtime/project"
    )
    assert target_job.count("SETUPTOOLS_SCM_PRETEND_VERSION_FOR_PDD_CLI") == 1
    assert synthetic_build in build_step
    assert "export SETUPTOOLS_SCM_PRETEND_VERSION_FOR_PDD_CLI" not in build_step
    assert not any(
        line.strip().startswith(("git ", "apt-get ", "sudo apt-get "))
        for line in target_job.splitlines()
    )
    assert "PYTHONPATH" not in target_job
    assert target_job.count("-I -S -c") == 3
    removed_project_wheel = (
        'find /runtime/wheelhouse -maxdepth 1 -type f -name "pdd_cli-*.whl" -delete'
    )
    assert removed_project_wheel in target_job
    assert (
        target_job.index(synthetic_build)
        < target_job.index(removed_project_wheel)
        < target_job.index("generate --wheelhouse /runtime/wheelhouse")
    )
    assert "--find-links /runtime/wheelhouse --find-links /runtime/project" in target_job
    for step in steps:
        if "run" in step:
            checked = subprocess.run(
                ["bash", "-n"], input=step["run"], text=True, capture_output=True, check=False
            )
            assert checked.returncode == 0, checked.stderr
    assert subprocess.run(
        ["git", "diff", "--quiet", "HEAD", "--", ".github/workflows/release.yml"],
        cwd=ROOT,
        check=False,
    ).returncode == 0
