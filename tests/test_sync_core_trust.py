"""Adversarial tests for trusted semantic evidence issuance."""

import base64
import json
import os
import shutil
from pathlib import Path
import subprocess
import sys
import time
from dataclasses import replace
from datetime import datetime, timedelta, timezone
from pathlib import PurePosixPath

import pytest

from pdd.sync_core import (
    AttestationError,
    AttestationBinding,
    AttestationRequest,
    AttestationSigner,
    AttestationTrustPolicy,
    EvidenceOutcome,
    FileReplayStore,
    RemoteAttestationSigner,
    UnitId,
)
from pdd.sync_core.trust import ValidationEvidence
from pdd.sync_core.finalize import attestation_signer_from_environment
from pdd.sync_core.signer_process import run_signer
import pdd.sync_core.signer_process as signer_process_module
from pdd.sync_core.certificate import RemoteCertificateSigner
import pdd.sync_core.certificate as certificate_module
import pdd.sync_core.trust as trust_module
from pdd.sync_core.types import ObligationEvidence


PRIVATE_KEY = b"t" * 32
SIGNER = AttestationSigner("trusted-ci", PRIVATE_KEY)
PUBLIC_KEY = SIGNER.public_key_bytes()
NOW = datetime(2026, 7, 10, 12, 0, tzinfo=timezone.utc)
UNIT = UnitId("repository-1", PurePosixPath("prompts/widget_python.prompt"), "python")


def _envelope(*, nonce="nonce-1", issued_at=NOW, lifetime=timedelta(hours=1)):
    return SIGNER.issue(
        AttestationRequest(
            "attestation-1",
            _binding(),
            (ObligationEvidence("test", EvidenceOutcome.PASS),),
            nonce,
            issued_at,
            lifetime,
        )
    )


def _binding(**overrides):
    values = {
        "subject": UNIT,
        "snapshot_digest": "snapshot-1",
        "profile_digest": "profile-1",
        "runner_digest": "runner-1",
        "tool_version": "pdd-test",
        "base_sha": "base-1",
        "checked_sha": "head-1",
    }
    values.update(overrides)
    return AttestationBinding(**values)


def _verify(policy, envelope, **overrides):
    now = overrides.pop("now", NOW)
    return policy.verify(envelope, _binding(**overrides), now=now)


def test_valid_attestation_produces_sealed_evidence() -> None:
    evidence = _verify(AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY}), _envelope())
    assert isinstance(evidence, ValidationEvidence)
    assert evidence.attestation_id == "attestation-1"


def test_remote_attestation_authority_signature_is_verified(monkeypatch) -> None:
    request = AttestationRequest(
        "remote-attestation",
        _binding(),
        (ObligationEvidence("test", EvidenceOutcome.PASS),),
        "remote-nonce",
        NOW,
    )

    def remote_sign(command, input, *, timeout):
        assert command == ("protected-attestation-sign",)
        assert timeout > 0
        return subprocess.CompletedProcess(
            command,
            0,
            stdout=SIGNER.sign_bytes(input).encode("ascii"),
            stderr=b"",
        )

    monkeypatch.setattr("pdd.sync_core.trust.run_signer", remote_sign)
    signer = RemoteAttestationSigner(
        SIGNER.issuer, SIGNER.public_key_bytes(), ("protected-attestation-sign",)
    )
    envelope = signer.issue(request)
    evidence = AttestationTrustPolicy(
        {SIGNER.issuer: SIGNER.public_key_bytes()}
    ).verify(envelope, request.binding, now=NOW)
    assert evidence.attestation_id == request.attestation_id


def test_remote_attestation_signer_has_protected_timeout(monkeypatch) -> None:
    def stalled(_command, _payload, **kwargs):
        assert kwargs["timeout"] > 0
        raise subprocess.TimeoutExpired("protected-attestation-sign", kwargs["timeout"])

    monkeypatch.setattr("pdd.sync_core.trust.run_signer", stalled)
    signer = RemoteAttestationSigner(
        SIGNER.issuer, SIGNER.public_key_bytes(), ("protected-attestation-sign",)
    )
    with pytest.raises(AttestationError, match="timed out"):
        signer.issue(
            AttestationRequest(
                "remote-attestation", _binding(),
                (ObligationEvidence("test", EvidenceOutcome.PASS),),
                "remote-nonce", NOW,
            )
        )


def test_signer_timeout_is_bounded_with_detached_pipe_holder() -> None:
    script = (
        "import subprocess,sys,time; "
        "subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(30)'], "
        "start_new_session=True); time.sleep(30)"
    )
    started = time.monotonic()
    with pytest.raises(subprocess.TimeoutExpired):
        run_signer((sys.executable, "-c", script), b"", timeout=0.1)
    assert time.monotonic() - started < 1.5


def test_linux_signer_containment_binds_only_ready_root_writable(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(
        signer_process_module.shutil,
        "which",
        lambda name: "/usr/bin/bwrap" if name == "bwrap" else None,
    )

    command = signer_process_module._linux_contained_command(("signer",), tmp_path)

    assert command[command.index("--ro-bind") + 1:command.index("--ro-bind") + 3] == (
        "/", "/"
    )
    bind_index = command.index("--bind")
    assert command[bind_index + 1:bind_index + 3] == (str(tmp_path), str(tmp_path))
    assert command.index("--tmpfs") < bind_index
    assert "stdout=sys.stdout.buffer" in signer_process_module._LINUX_CONTAINMENT


@pytest.mark.skipif(
    not sys.platform.startswith("linux"), reason="requires Linux stable process identity"
)
@pytest.mark.parametrize("adapter", ["attestation", "certificate"])
def test_remote_signer_timeout_reaps_env_cleared_detached_descendant(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, adapter: str
) -> None:
    marker = tmp_path / f"{adapter}.survived"
    detached = (
        "import os,sys,time; "
        "time.sleep(1); open(sys.argv[1], 'w').write('survived'); time.sleep(30)"
    )
    parent = (
        "import os,subprocess,sys,time; env=dict(os.environ); "
        "env.pop('PDD_SIGNER_PROCESS_TOKEN', None); "
        "child=subprocess.Popen([sys.executable, '-c', sys.argv[1], sys.argv[2]], "
        "env=env, start_new_session=True, stdout=subprocess.DEVNULL, "
        "stderr=subprocess.DEVNULL); print('started', flush=True); time.sleep(30)"
    )
    command = (sys.executable, "-c", parent, detached, str(marker))
    actual_run_signer = run_signer
    timed_out: list[subprocess.TimeoutExpired] = []

    def short_run(command_value, payload, *, timeout):
        del timeout
        try:
            return actual_run_signer(command_value, payload, timeout=0.5)
        except subprocess.TimeoutExpired as exc:
            timed_out.append(exc)
            raise

    if adapter == "attestation":
        monkeypatch.setattr(trust_module, "run_signer", short_run)
        signer = RemoteAttestationSigner(SIGNER.issuer, PUBLIC_KEY, command)
        with pytest.raises(AttestationError, match="timed out"):
            signer.issue(
                AttestationRequest(
                    "remote-attestation", _binding(),
                    (ObligationEvidence("test", EvidenceOutcome.PASS),),
                    "remote-nonce", NOW,
                )
            )
    else:
        monkeypatch.setattr(certificate_module, "run_signer", short_run)
        signer = RemoteCertificateSigner(SIGNER.issuer, PUBLIC_KEY, command)
        with pytest.raises(ValueError, match="timed out"):
            signer.sign_bytes(b"payload")

    assert timed_out and timed_out[0].output, (
        timed_out[0].stderr if timed_out else "signer did not time out"
    )
    assert timed_out[0].output.strip() == b"started"
    marker_bytes = str(marker).encode()
    escaped = []
    for process in Path("/proc").iterdir():
        if not process.name.isdigit():
            continue
        try:
            command_line = (process / "cmdline").read_bytes()
        except (OSError, PermissionError):
            continue
        if marker_bytes in command_line:
            escaped.append(process.name)
    assert not escaped
    time.sleep(1.1)
    assert not marker.exists()


@pytest.mark.skipif(
    not sys.platform.startswith("linux") or not shutil.which("bwrap"),
    reason="requires Linux PID namespace containment",
)
@pytest.mark.parametrize("adapter", ["attestation", "certificate"])
def test_remote_signer_normal_return_reaps_detached_descendant(
    tmp_path: Path, adapter: str
) -> None:
    marker = tmp_path / f"{adapter}.normal-return-leak"
    child = (
        "import os,sys,time; os.setsid(); time.sleep(.5); "
        "open(sys.argv[1], 'w').write('leaked')"
    )
    parent = (
        "import os,subprocess,sys; env=dict(os.environ); "
        "env.pop('PDD_SIGNER_PROCESS_TOKEN', None); "
        "subprocess.Popen([sys.executable, '-c', sys.argv[1], sys.argv[2]], "
        "env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL); "
        "sys.stdout.buffer.write(b'not-a-signature')"
    )
    command = (sys.executable, "-c", parent, child, str(marker))
    if adapter == "attestation":
        signer = RemoteAttestationSigner(SIGNER.issuer, PUBLIC_KEY, command)
        with pytest.raises(AttestationError):
            signer.issue(AttestationRequest("remote", _binding(), (), "nonce", NOW))
    else:
        signer = RemoteCertificateSigner(SIGNER.issuer, PUBLIC_KEY, command)
        with pytest.raises(ValueError):
            signer.sign_bytes(b"payload")
    time.sleep(.6)
    assert not marker.exists()


@pytest.mark.skipif(
    not sys.platform.startswith("linux") or not shutil.which("bwrap"),
    reason="requires Linux PID namespace containment",
)
@pytest.mark.parametrize("adapter", ["attestation", "certificate"])
@pytest.mark.parametrize("leader_signal", ["SIGSTOP", "SIGKILL"])
def test_remote_signer_leader_loss_reaps_detached_descendant(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    adapter: str,
    leader_signal: str,
) -> None:
    marker = tmp_path / f"{adapter}-{leader_signal}.leader-leak"
    child = (
        "import os,sys,time; os.setsid(); time.sleep(.5); "
        "open(sys.argv[1], 'w').write('leaked')"
    )
    parent = (
        "import os,signal,subprocess,sys,time; env=dict(os.environ); "
        "env.pop('PDD_SIGNER_PROCESS_TOKEN', None); "
        "subprocess.Popen([sys.executable, '-c', sys.argv[1], sys.argv[2]], "
        "env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL); "
        "os.kill(os.getppid(), getattr(signal, sys.argv[3])); time.sleep(30)"
    )
    command = (sys.executable, "-c", parent, child, str(marker), leader_signal)
    actual_run_signer = run_signer

    def short_run(command_value, payload, *, timeout):
        del timeout
        return actual_run_signer(command_value, payload, timeout=0.1)

    started = time.monotonic()
    if adapter == "attestation":
        monkeypatch.setattr(trust_module, "run_signer", short_run)
        signer = RemoteAttestationSigner(SIGNER.issuer, PUBLIC_KEY, command)
        with pytest.raises(AttestationError):
            signer.issue(AttestationRequest("remote", _binding(), (), "nonce", NOW))
    else:
        monkeypatch.setattr(certificate_module, "run_signer", short_run)
        signer = RemoteCertificateSigner(SIGNER.issuer, PUBLIC_KEY, command)
        with pytest.raises(ValueError):
            signer.sign_bytes(b"payload")
    assert time.monotonic() - started < 1.5
    time.sleep(.6)
    assert not marker.exists()


def test_attestation_environment_forbids_local_private_key(monkeypatch) -> None:
    monkeypatch.setenv("PDD_ATTESTATION_SIGNING_KEY", "candidate-secret")
    with pytest.raises(ValueError, match="local attestation signing keys are forbidden"):
        attestation_signer_from_environment()


def test_attestation_environment_builds_remote_authority(monkeypatch) -> None:
    monkeypatch.setenv("PDD_ATTESTATION_ISSUER", SIGNER.issuer)
    monkeypatch.setenv(
        "PDD_ATTESTATION_PUBLIC_KEY",
        base64.b64encode(SIGNER.public_key_bytes()).decode("ascii"),
    )
    monkeypatch.setenv(
        "PDD_ATTESTATION_SIGNER_COMMAND",
        json.dumps(["protected-attestation-sign"]),
    )
    assert isinstance(attestation_signer_from_environment(), RemoteAttestationSigner)


def test_evidence_cannot_be_caller_asserted() -> None:
    with pytest.raises(TypeError, match="AttestationTrustPolicy"):
        ValidationEvidence(
            object(),
            _seal=object(),
        )


def test_forged_signature_is_rejected() -> None:
    envelope = replace(_envelope(), binding=_binding(checked_sha="candidate-head"))
    with pytest.raises(AttestationError, match="signature"):
        _verify(AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY}), envelope)


def test_unknown_issuer_is_rejected() -> None:
    with pytest.raises(AttestationError, match="not trusted"):
        _verify(AttestationTrustPolicy({}), _envelope())


def test_expired_attestation_is_rejected() -> None:
    envelope = _envelope(issued_at=NOW - timedelta(hours=2), lifetime=timedelta(minutes=1))
    with pytest.raises(AttestationError, match="expired"):
        _verify(AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY}), envelope)


def test_overlong_attestation_lifetime_is_rejected() -> None:
    envelope = _envelope(nonce="nonce-long", lifetime=timedelta(days=9))
    with pytest.raises(AttestationError, match="exceeds policy"):
        _verify(AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY}), envelope)


@pytest.mark.parametrize(
    ("policy", "message"),
    [
        (AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY}, revoked_issuers=frozenset({"trusted-ci"})), "issuer is revoked"),
        (AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY}, revoked_attestations=frozenset({"attestation-1"})), "attestation is revoked"),
    ],
)
def test_revocation_is_enforced(policy, message) -> None:
    with pytest.raises(AttestationError, match=message):
        _verify(policy, _envelope())


def test_nonce_reuse_by_different_attestation_is_rejected() -> None:
    policy = AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY})
    first = _envelope()
    _verify(policy, first)
    second = SIGNER.issue(
        AttestationRequest(
            "attestation-2",
            _binding(),
            first.results,
            "nonce-1",
            NOW,
        )
    )
    with pytest.raises(AttestationError, match="replayed"):
        _verify(policy, second)


def test_exact_signed_statement_recheck_is_idempotent() -> None:
    policy = AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY})
    envelope = _envelope()
    first = _verify(policy, envelope)
    second = _verify(policy, envelope)
    assert first.attestation_id == second.attestation_id == "attestation-1"


def test_durable_nonce_collision_is_rejected_across_policy_instances(tmp_path) -> None:
    path = tmp_path / "external/replay.json"
    envelope = _envelope()
    first = AttestationTrustPolicy(
        {"trusted-ci": PUBLIC_KEY}, replay_store=FileReplayStore(path)
    )
    second = AttestationTrustPolicy(
        {"trusted-ci": PUBLIC_KEY}, replay_store=FileReplayStore(path)
    )
    _verify(first, envelope)
    conflicting = SIGNER.issue(
        AttestationRequest(
            "attestation-conflict",
            _binding(),
            envelope.results,
            "nonce-1",
            NOW,
        )
    )
    with pytest.raises(AttestationError, match="replayed"):
        _verify(second, conflicting)
    assert path.stat().st_mode & 0o777 == 0o600


def test_durable_exact_statement_recheck_is_idempotent(tmp_path) -> None:
    path = tmp_path / "external/replay.json"
    envelope = _envelope()
    first = AttestationTrustPolicy(
        {"trusted-ci": PUBLIC_KEY}, replay_store=FileReplayStore(path)
    )
    second = AttestationTrustPolicy(
        {"trusted-ci": PUBLIC_KEY}, replay_store=FileReplayStore(path)
    )
    _verify(first, envelope)
    assert _verify(second, envelope).attestation_id == envelope.attestation_id


@pytest.mark.parametrize(
    "override",
    [
        {"snapshot_digest": "snapshot-2"},
        {"profile_digest": "profile-2"},
        {"base_sha": "base-2"},
        {"checked_sha": "head-2"},
    ],
)
def test_wrong_closure_binding_is_rejected(override) -> None:
    with pytest.raises(AttestationError, match="checked closure"):
        _verify(
            AttestationTrustPolicy({"trusted-ci": PUBLIC_KEY}),
            _envelope(),
            **override,
        )


def test_file_replay_store_rejects_symlink_lock(tmp_path) -> None:
    path = tmp_path / "replay.json"
    outside = tmp_path / "outside.lock"
    outside.write_text("do not touch")
    path.with_name("replay.json.lock").symlink_to(outside)
    store = FileReplayStore(path)
    with pytest.raises(AttestationError, match="unsafe"):
        store.consume("trusted-ci", "nonce", "attestation")


def test_file_replay_store_rejects_symlinked_ancestor(tmp_path) -> None:
    protected = tmp_path / "protected"
    protected.mkdir(mode=0o700)
    outside = tmp_path / "outside"
    outside.mkdir(mode=0o700)
    (protected / "linked").symlink_to(outside, target_is_directory=True)
    store = FileReplayStore(protected / "linked" / "nested" / "replay.json")
    with pytest.raises(AttestationError, match="unsafe"):
        store.consume("trusted-ci", "nonce", "attestation")
