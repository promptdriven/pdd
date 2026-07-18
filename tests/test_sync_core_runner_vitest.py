"""Contract tests for the fail-closed trusted Vitest adapter."""

import base64
import hashlib
import json
import os
import errno as errno_module
import signal
import shutil
import stat
import subprocess
import sys
from types import SimpleNamespace
import time
import tomllib
import zipfile
from contextlib import contextmanager, nullcontext
from dataclasses import replace
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

import pytest
import yaml

import pdd.sync_core.runner as runner_module
import pdd.sync_core.supervisor as supervisor_module
from pdd.sync_core import (
    AttestationIssue,
    AttestationSigner,
    EvidenceOutcome,
    RunBinding,
    RunnerConfig,
    RunnerExecution,
    UnitId,
    VerificationObligation,
    VerificationProfile,
    run_profile,
)
from pdd.sync_core.runner import (
    _copy_vitest_dependencies,
    _local_javascript_imports,
    _collect_vitest_at_base,
    _load_vitest_toolchain_descriptor,
    _prepare_vitest_toolchain,
    _run_vitest,
    _validator_tree_identity,
    _vitest_command_error,
    _vitest_environment,
    _vitest_reporter_source,
    _vitest_result,
    _vitest_worker_preload_source,
    jest_validator_config_digest,
    runner_identity_digest,
    vitest_validator_config_digest,
)
from pdd.sync_core.evidence_store import attestation_payload, decode_attestation
from pdd.sync_core.supervisor import (
    CgroupResourceTelemetry,
    SupervisedCompletedProcess,
    SupervisorLimits,
    SupervisorTermination,
    TerminationKind,
)


_VITEST_FAILURE_BASELINE_SHA = "b09b6bef2c8c4bee762965be463527cd0b050154"
_VITEST_PROTECTED_BASE_SHA = "cc97ef23a478fa123a7b9ffc5d7450b4d55b70e7"
_VITEST_RUNNER_IMAGE = "ubuntu-24.04/20260714.240.1"
_VITEST_RUNNER_PROVISIONER = "20260707.563"
_VITEST_PYTHON_VERSION = "3.12.13"
_VITEST_NODE_VERSION = "22.23.1"
_VITEST_PACKAGE_SHA256 = (
    "63b0ce64263ea3acaed934e5fb5fbbb98d7fcd7673acd40e164dea2a648f2da5"
)
_VITEST_LOCK_SHA256 = (
    "bfc69a55d08997f553a0901c2ec0b7830cb01d6c6cc81257d150dcc79d20783c"
)
_VITEST_DIAGNOSTIC_TEST_NODE = (
    "tests/test_sync_core_runner_vitest.py::"
    "test_real_vitest_runs_copied_entrypoint_without_candidate_result_access"
)
def _repository_head() -> str:
    """Return the exact test checkout HEAD used by ancestry verification."""
    repository = Path(__file__).resolve().parents[1]
    return subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repository,
        capture_output=True, text=True, check=True,
    ).stdout.strip()


def _configure_vitest_diagnostic(
    monkeypatch: pytest.MonkeyPatch, output: Path,
) -> dict[str, str]:
    """Install one complete protected diagnostic configuration."""
    runner_path = Path(runner_module.__file__).resolve(strict=True)
    verifier_path = (
        Path(__file__).parents[1]
        / "scripts"
        / "verify_vitest_termination_evidence.py"
    )
    values = {
        "PDD_VITEST_DIAGNOSTIC_OUTPUT": str(output),
        "PDD_VITEST_FAILURE_BASELINE_SHA": _VITEST_FAILURE_BASELINE_SHA,
        "PDD_VITEST_PROTECTED_BASE_SHA": _VITEST_PROTECTED_BASE_SHA,
        "PDD_VITEST_DIAGNOSTIC_HEAD_SHA": _repository_head(),
        "PDD_VITEST_DIAGNOSTIC_PRODUCER_SHA256": hashlib.sha256(
            runner_path.read_bytes()
        ).hexdigest(),
        "PDD_VITEST_DIAGNOSTIC_VERIFIER_SHA256": hashlib.sha256(
            verifier_path.read_bytes()
        ).hexdigest(),
        "PDD_VITEST_RUNNER_IMAGE": _VITEST_RUNNER_IMAGE,
        "PDD_VITEST_RUNNER_PROVISIONER": _VITEST_RUNNER_PROVISIONER,
        "PDD_VITEST_PYTHON_VERSION": _VITEST_PYTHON_VERSION,
        "PDD_VITEST_NODE_VERSION": _VITEST_NODE_VERSION,
        "PDD_VITEST_PACKAGE_SHA256": _VITEST_PACKAGE_SHA256,
        "PDD_VITEST_LOCK_SHA256": _VITEST_LOCK_SHA256,
        "PDD_VITEST_TEST_NODE": _VITEST_DIAGNOSTIC_TEST_NODE,
    }
    for name, value in values.items():
        monkeypatch.setenv(name, value)
    return values


def _write_vitest_review_evidence(
    path: Path, configured: dict[str, str],
) -> str:
    """Write independently supplied review evidence for verifier integration."""
    verifier = Path(__file__).parents[1] / "scripts/verify_vitest_termination_evidence.py"
    payload = {
        "schema": "vitest-diagnostic-review-v1",
        "failure_baseline_sha": _VITEST_FAILURE_BASELINE_SHA,
        "protected_base_sha": _VITEST_PROTECTED_BASE_SHA,
        "diagnostic_head_sha": configured["PDD_VITEST_DIAGNOSTIC_HEAD_SHA"],
        "producer_sha256": configured["PDD_VITEST_DIAGNOSTIC_PRODUCER_SHA256"],
        "verifier_sha256": hashlib.sha256(verifier.read_bytes()).hexdigest(),
        "verdict": "APPROVE",
        "behavioral_verdict": "NO_BEHAVIORAL_FIX",
    }
    encoded = (
        json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("ascii")
    path.write_bytes(encoded)
    path.chmod(0o600)
    return hashlib.sha256(encoded).hexdigest()


def _diagnostic_exit_result(diagnostic: str) -> SupervisedCompletedProcess:
    """Return the hosted no-reporter exit signature with trusted telemetry."""
    return SupervisedCompletedProcess(
        ["vitest"], 1, "", diagnostic,
        termination=SupervisorTermination(
            TerminationKind.EXIT,
            exit_code=1,
            resource_telemetry=CgroupResourceTelemetry(0, 0, 0),
        ),
    )


def _diagnostic_progress() -> tuple[runner_module.VitestProgressStage, ...]:
    """Return a concrete coordinator failure after the live hosted prefix."""
    return (
        runner_module.VitestProgressStage.POST_DROP_PROBES,
        runner_module.VitestProgressStage.CANDIDATE_EXEC,
        runner_module.VitestProgressStage.COORDINATOR_BOOTSTRAP,
        runner_module.VitestProgressStage.REPORTER_MODULE_START,
        runner_module.VitestProgressStage.REPORTER_ADDON_LOAD_START,
        runner_module.VitestProgressStage.REPORTER_ADDON_LOAD_FAILED,
        runner_module.VitestProgressStage.COORDINATOR_EXPLICIT_EXIT,
        runner_module.VitestProgressStage.COORDINATOR_EXIT,
    )


def _diagnostic_before_exit_progress() -> tuple[runner_module.VitestProgressStage, ...]:
    """Return the natural coordinator exit path before reporter evaluation."""
    return (
        runner_module.VitestProgressStage.POST_DROP_PROBES,
        runner_module.VitestProgressStage.CANDIDATE_EXEC,
        runner_module.VitestProgressStage.COORDINATOR_BOOTSTRAP,
        runner_module.VitestProgressStage.COORDINATOR_BEFORE_EXIT,
        runner_module.VitestProgressStage.COORDINATOR_EXIT,
    )


def test_vitest_termination_diagnostic_is_opt_in(tmp_path: Path) -> None:
    """Ordinary Vitest execution never creates a diagnostic artifact."""
    output = tmp_path / "vitest-termination-v1.json"

    observed = runner_module._write_vitest_termination_evidence(
        tmp_path / "candidate", _diagnostic_exit_result("diagnostic"),
        _diagnostic_progress(),
    )

    assert observed is None
    assert not output.exists()


def test_vitest_termination_diagnostic_writes_canonical_protected_evidence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The live signature becomes fixed-schema evidence without raw prose."""
    root = tmp_path / "candidate"
    root.mkdir()
    output = tmp_path / "protected" / "vitest-termination-v1.json"
    output.parent.mkdir(mode=0o700)
    configured = _configure_vitest_diagnostic(monkeypatch, output)
    diagnostic = "candidate secret and /candidate/path must remain unpublished"

    observed = runner_module._write_vitest_termination_evidence(
        root, _diagnostic_exit_result(diagnostic), _diagnostic_progress(),
    )

    assert observed == output
    encoded = output.read_bytes()
    payload = json.loads(encoded)
    assert encoded == (
        json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("ascii")
    assert stat.S_IMODE(output.stat().st_mode) == 0o600
    digest_sidecar = Path(str(output) + ".sha256")
    assert stat.S_IMODE(digest_sidecar.stat().st_mode) == 0o600
    assert digest_sidecar.read_text(encoding="ascii") == hashlib.sha256(
        encoded
    ).hexdigest() + "\n"
    assert set(payload) == {
        "schema",
        "failure_baseline_sha",
        "protected_base_sha",
        "diagnostic_head_sha",
        "producer_sha256",
        "verifier_sha256",
        "runner_image",
        "runner_provisioner",
        "python",
        "node",
        "vitest_package_sha256",
        "vitest_lock_sha256",
        "test_node",
        "process_role",
        "failure_stage",
        "cause_code",
        "exit_code",
        "cgroup_memory_oom_delta",
        "cgroup_memory_oom_kill_delta",
        "cgroup_pids_max_delta",
        "diagnostic_sha256",
        "cause_red_status",
    }
    assert payload == {
        "schema": "vitest-termination-v1",
        "failure_baseline_sha": _VITEST_FAILURE_BASELINE_SHA,
        "protected_base_sha": _VITEST_PROTECTED_BASE_SHA,
        "diagnostic_head_sha": configured["PDD_VITEST_DIAGNOSTIC_HEAD_SHA"],
        "producer_sha256": configured[
            "PDD_VITEST_DIAGNOSTIC_PRODUCER_SHA256"
        ],
        "verifier_sha256": configured[
            "PDD_VITEST_DIAGNOSTIC_VERIFIER_SHA256"
        ],
        "runner_image": _VITEST_RUNNER_IMAGE,
        "runner_provisioner": _VITEST_RUNNER_PROVISIONER,
        "python": _VITEST_PYTHON_VERSION,
        "node": _VITEST_NODE_VERSION,
        "vitest_package_sha256": _VITEST_PACKAGE_SHA256,
        "vitest_lock_sha256": _VITEST_LOCK_SHA256,
        "test_node": _VITEST_DIAGNOSTIC_TEST_NODE,
        "process_role": "vitest-coordinator",
        "failure_stage": "reporter-addon-load",
        "cause_code": "reporter-addon-load-failed",
        "exit_code": 1,
        "cgroup_memory_oom_delta": 0,
        "cgroup_memory_oom_kill_delta": 0,
        "cgroup_pids_max_delta": 0,
        "diagnostic_sha256": hashlib.sha256(diagnostic.encode()).hexdigest(),
        "cause_red_status": "pending",
    }
    assert diagnostic not in encoded.decode("ascii")
    assert str(root) not in encoded.decode("ascii")


def test_vitest_termination_diagnostic_verifies_against_current_producer(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The writer's canonical artifact satisfies the independent verifier."""
    root = tmp_path / "candidate"
    root.mkdir()
    output = tmp_path / "protected" / "vitest-termination-v1.json"
    output.parent.mkdir(mode=0o700)
    configured = _configure_vitest_diagnostic(monkeypatch, output)
    observed = runner_module._write_vitest_termination_evidence(
        root, _diagnostic_exit_result("diagnostic"), _diagnostic_progress(),
    )
    assert observed == output
    repository = Path(__file__).parents[1]
    verifier = repository / "scripts" / "verify_vitest_termination_evidence.py"
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    review_evidence = tmp_path / "vitest-diagnostic-review-v1.json"
    review_digest = _write_vitest_review_evidence(review_evidence, configured)

    completed = subprocess.run(
        [
            sys.executable, str(verifier),
            "--evidence", str(output),
            "--evidence-sha256", digest,
            "--repository", str(repository),
            "--failure-baseline-sha", _VITEST_FAILURE_BASELINE_SHA,
            "--protected-base-sha", _VITEST_PROTECTED_BASE_SHA,
            "--diagnostic-head-sha", configured["PDD_VITEST_DIAGNOSTIC_HEAD_SHA"],
            "--producer-sha256", configured["PDD_VITEST_DIAGNOSTIC_PRODUCER_SHA256"],
            "--verifier-sha256", configured["PDD_VITEST_DIAGNOSTIC_VERIFIER_SHA256"],
            "--runner-image", _VITEST_RUNNER_IMAGE,
            "--runner-provisioner", _VITEST_RUNNER_PROVISIONER,
            "--python", _VITEST_PYTHON_VERSION,
            "--node", _VITEST_NODE_VERSION,
            "--vitest-package-sha256", _VITEST_PACKAGE_SHA256,
            "--vitest-lock-sha256", _VITEST_LOCK_SHA256,
            "--test-node", _VITEST_DIAGNOSTIC_TEST_NODE,
            "--review-evidence", str(review_evidence),
            "--review-evidence-sha256", review_digest,
        ],
        capture_output=True,
        text=True,
        check=False,
    )

    assert completed.returncode == 0, completed.stderr


def test_vitest_termination_diagnostic_rejects_natural_coordinator_exit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A natural coordinator shutdown is a symptom, not a protected cause."""
    root = tmp_path / "candidate"
    root.mkdir()
    output = tmp_path / "protected" / "vitest-termination-v1.json"
    output.parent.mkdir(mode=0o700)
    _configure_vitest_diagnostic(monkeypatch, output)

    observed = runner_module._write_vitest_termination_evidence(
        root, _diagnostic_exit_result("diagnostic"),
        _diagnostic_before_exit_progress(),
    )

    assert observed is None
    assert not output.exists()


@pytest.mark.parametrize(
    "generic_stage",
    (
        runner_module.VitestProgressStage.COORDINATOR_UNCAUGHT_EXCEPTION,
        runner_module.VitestProgressStage.COORDINATOR_EXPLICIT_EXIT,
    ),
)
def test_vitest_termination_diagnostic_rejects_generic_lifecycle_symptoms(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    generic_stage: runner_module.VitestProgressStage,
) -> None:
    """Generic uncaught and explicit-exit events remain cause-ineligible."""
    root = tmp_path / "candidate"
    root.mkdir()
    output = tmp_path / "protected" / "vitest-termination-v1.json"
    output.parent.mkdir(mode=0o700)
    _configure_vitest_diagnostic(monkeypatch, output)
    progress = (
        runner_module.VitestProgressStage.POST_DROP_PROBES,
        runner_module.VitestProgressStage.CANDIDATE_EXEC,
        runner_module.VitestProgressStage.COORDINATOR_BOOTSTRAP,
        generic_stage,
        runner_module.VitestProgressStage.COORDINATOR_EXIT,
    )

    observed = runner_module._write_vitest_termination_evidence(
        root, _diagnostic_exit_result("diagnostic"), progress,
    )

    assert observed is None
    assert not output.exists()


def test_vitest_termination_diagnostic_rejects_broad_no_reporter_signature(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A bare exit after the old prefix cannot be relabeled as a cause."""
    root = tmp_path / "candidate"
    root.mkdir()
    output = tmp_path / "protected" / "vitest-termination-v1.json"
    output.parent.mkdir(mode=0o700)
    _configure_vitest_diagnostic(monkeypatch, output)
    broad_progress = (
        runner_module.VitestProgressStage.POST_DROP_PROBES,
        runner_module.VitestProgressStage.CANDIDATE_EXEC,
        runner_module.VitestProgressStage.COORDINATOR_BOOTSTRAP,
        runner_module.VitestProgressStage.COORDINATOR_EXIT,
    )

    observed = runner_module._write_vitest_termination_evidence(
        root, _diagnostic_exit_result("diagnostic"), broad_progress,
    )

    assert observed is None
    assert not output.exists()


def test_vitest_termination_diagnostic_rejects_candidate_checkout_output(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Protected evidence cannot be redirected into candidate-controlled storage."""
    root = tmp_path / "candidate"
    root.mkdir()
    output = root / "vitest-termination-v1.json"
    _configure_vitest_diagnostic(monkeypatch, output)

    with pytest.raises(ValueError, match="outside candidate checkout"):
        runner_module._write_vitest_termination_evidence(
            root, _diagnostic_exit_result("diagnostic"), _diagnostic_progress(),
        )

    assert not output.exists()


def test_vitest_diagnostic_sources_emit_only_fixed_coordinator_boundaries(
    tmp_path: Path,
) -> None:
    """Protected bootstrap and reporter code expose categories, never exception text."""
    addon = tmp_path / "checker-authority.node"
    addon.write_bytes(b"checker-owned authority")
    coordinator = runner_module._vitest_coordinator_diagnostic_source(198, 1, 2)
    reporter = runner_module._vitest_reporter_source(
        198, 1, 2, addon, diagnostic=True,
    )

    for stage in (
        "coordinator-bootstrap",
        "coordinator-uncaught-exception",
        "coordinator-explicit-exit",
        "coordinator-before-exit",
        "coordinator-exit",
    ):
        assert stage in coordinator
    assert "uncaughtExceptionMonitor" in coordinator
    assert "unhandledRejection" not in coordinator
    assert "error.message" not in coordinator
    assert "error.stack" not in coordinator
    assert "process.env" not in coordinator
    for stage in (
        "reporter-module-start",
        "reporter-addon-load-start",
        "reporter-addon-load-failed",
        "reporter-addon-load-succeeded",
        "reporter-authority-seal-start",
        "reporter-authority-seal-failed",
        "reporter-authority-seal-succeeded",
        "reporter-constructor-start",
        "reporter-constructor-failed",
        "reporter-constructor-succeeded",
    ):
        assert stage in reporter
    assert reporter.index("reporter-module-start") < reporter.index(
        "reporter-addon-load-start"
    ) < reporter.index("reporter-addon-load-succeeded") < reporter.index(
        "reporter-authority-seal-start"
    ) < reporter.index("reporter-authority-seal-succeeded") < reporter.index(
        "reporter-constructor-start"
    ) < reporter.index(
        "coordinator-start"
    ) < reporter.index(
        "reporter-constructor-succeeded"
    )
    assert "error.message" not in reporter
    assert "error.stack" not in reporter


def test_generated_diagnostic_reporter_attributes_real_addon_load_failure(
    tmp_path: Path,
) -> None:
    """Real generated source emits an authenticated concrete operation failure."""
    node = shutil.which("node")
    if node is None:
        pytest.skip("requires Node.js")
    read_fd, write_fd = os.pipe()
    identity = os.fstat(write_fd)
    invalid_addon = tmp_path / "trusted-addon.node"
    invalid_addon.write_bytes(b"not a native addon")
    reporter = tmp_path / "diagnostic-reporter.mjs"
    reporter.write_text(
        runner_module._vitest_reporter_source(
            write_fd, identity.st_dev, identity.st_ino, invalid_addon,
            diagnostic=True,
        ),
        encoding="utf-8",
    )
    try:
        completed = subprocess.run(
            [node, str(reporter)], pass_fds=(write_fd,), capture_output=True,
            text=True, timeout=2, check=False,
        )
    finally:
        os.close(write_fd)
    try:
        emitted = bytearray()
        while chunk := os.read(read_fd, 4096):
            emitted.extend(chunk)
    finally:
        os.close(read_fd)
    transport = b"".join((
        runner_module._vitest_progress_frame(
            runner_module.VitestProgressStage.POST_DROP_PROBES
        ),
        runner_module._vitest_progress_frame(
            runner_module.VitestProgressStage.CANDIDATE_EXEC
        ),
        runner_module._vitest_progress_frame(
            runner_module.VitestProgressStage.COORDINATOR_BOOTSTRAP
        ),
        bytes(emitted),
        runner_module._vitest_progress_frame(
            runner_module.VitestProgressStage.COORDINATOR_EXIT
        ),
    ))
    _result, progress = runner_module._parse_vitest_transport(transport)

    classification = runner_module._vitest_termination_classification(
        _diagnostic_exit_result("diagnostic"), progress,
    )

    assert completed.returncode != 0
    assert classification is not None
    assert classification.failure_stage.value == "reporter-addon-load"
    assert classification.cause_code.value == "reporter-addon-load-failed"


def test_vitest_diagnostic_launch_binds_coordinator_source_and_artifact(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Only complete host pins add the coordinator bootstrap to the real argv."""
    root, _commit = _repository(tmp_path)
    output = tmp_path / "protected" / "vitest-termination-v1.json"
    output.parent.mkdir(mode=0o700)
    _configure_vitest_diagnostic(monkeypatch, output)
    observed: dict[str, object] = {}

    def capture(command, *, result_write_fd, env, **kwargs):
        observed["command"] = command
        observed["environment"] = env
        observed["readable_roots"] = kwargs["readable_roots"]
        endpoint = os.fstat(result_write_fd)
        kwargs["anonymous_observation_ready"](endpoint.st_dev, endpoint.st_ino)
        coordinator_argument = next(
            value for value in command if value.startswith("--import=")
        )
        coordinator = Path(coordinator_argument.removeprefix("--import="))
        observed["coordinator_source"] = coordinator.read_text(encoding="utf-8")
        observed["coordinator_mode"] = stat.S_IMODE(coordinator.stat().st_mode)
        for stage in _diagnostic_progress():
            os.write(result_write_fd, runner_module._vitest_progress_frame(stage))
        return _diagnostic_exit_result("coordinator diagnostic"), False

    monkeypatch.setattr(runner_module, "run_supervised", capture)
    execution, identities = _run_vitest(
        root, (PurePosixPath("tests/widget.test.ts"),), 2,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert identities == ()
    command = observed["command"]
    assert isinstance(command, list)
    coordinator_argument = next(
        value for value in command if value.startswith("--import=")
    )
    coordinator = Path(coordinator_argument.removeprefix("--import="))
    assert coordinator.name == "coordinator-diagnostic.mjs"
    assert observed["coordinator_mode"] == 0o444
    assert "coordinator-bootstrap" in observed["coordinator_source"]
    readable_roots = observed["readable_roots"]
    assert isinstance(readable_roots, tuple)
    assert coordinator in readable_roots
    environment = observed["environment"]
    assert isinstance(environment, dict)
    assert "PDD_VITEST_DIAGNOSTIC_OUTPUT" not in environment
    payload = json.loads(output.read_text(encoding="ascii"))
    assert payload["cause_code"] == "reporter-addon-load-failed"
    assert payload["diagnostic_sha256"] == hashlib.sha256(
        b"coordinator diagnostic"
    ).hexdigest()


def test_framework_observation_fifo_eof_waits_for_late_writer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class Completion:
        def __init__(self) -> None:
            self.checks = 0
            self.waits = []

        def is_set(self) -> bool:
            self.checks += 1
            return self.checks > 3

        def wait(self, timeout: float) -> bool:
            self.waits.append(timeout)
            return False

    completion = Completion()
    result: dict[str, object] = {}
    monkeypatch.setattr(
        runner_module.select, "select", lambda *_args: ([17], [], [])
    )
    monkeypatch.setattr(runner_module.os, "read", lambda *_args: b"")

    runner_module._drain_result_pipe(17, completion, result)

    assert completion.waits
    assert all(wait == .01 for wait in completion.waits)
    assert result["data"] == b""


def test_vitest_progress_transport_localizes_each_trusted_boundary() -> None:
    """A partial reporter stream exposes only exact bounded progress stages."""
    stages = (
        runner_module.VitestProgressStage.POST_DROP_PROBES,
        runner_module.VitestProgressStage.CANDIDATE_EXEC,
        runner_module.VitestProgressStage.COORDINATOR_START,
        runner_module.VitestProgressStage.WORKER_START,
        runner_module.VitestProgressStage.COLLECTION_COMPLETE,
        runner_module.VitestProgressStage.RESULT_PUBLISHED,
    )
    payload = json.dumps(
        {"tests": [{"identity": IDENTITY, "status": "passed"}]},
        separators=(",", ":"),
    ).encode("utf-8")
    transport = b"".join(
        runner_module._vitest_progress_frame(stage) for stage in stages
    ) + runner_module._vitest_result_frame(payload)

    observed_payload, observed_stages = runner_module._parse_vitest_transport(
        transport
    )

    assert observed_payload == payload
    assert observed_stages == stages

@pytest.mark.skipif(
    not sys.platform.startswith("linux"),
    reason="the production coordinator authority addon is Linux-only",
)
@pytest.mark.parametrize(
    "transport",
    [
        b"PDD-VITEST-PROGRESS-V1 candidate-controlled-secret\n",
        b"PDD-VITEST-PROGRESS-V1 worker-start\n",
        (
            b"PDD-VITEST-PROGRESS-V1 post-drop-probes\n"
            b"PDD-VITEST-PROGRESS-V1 coordinator-start\n"
        ),
        b"PDD-VITEST-RESULT-V1 {}\ntrailing",
        b"PDD-VITEST-PROGRESS-V1 post-drop-probes",
    ],
)
def test_vitest_progress_transport_rejects_untrusted_shapes(
    transport: bytes,
) -> None:
    """Unknown, out-of-order, partial, and trailing records fail closed."""
    with pytest.raises(ValueError, match="Vitest progress transport"):
        runner_module._parse_vitest_transport(transport)


def test_vitest_progress_transport_reports_typed_out_of_order_stages() -> None:
    """Concurrent stage rejection retains only bounded allowlisted evidence."""
    transport = (
        b"PDD-VITEST-PROGRESS-V1 post-drop-probes\n"
        b"PDD-VITEST-PROGRESS-V1 coordinator-start\n"
    )

    with pytest.raises(ValueError) as error:
        runner_module._parse_vitest_transport(transport)

    assert str(error.value) == (
        "Vitest progress transport stage is out of order "
        "(observed=post-drop-probes; failing=coordinator-start)"
    )


def test_vitest_progress_transport_accepts_worker_reporter_race() -> None:
    """A fork preload may publish before the coordinator reporter is created."""
    stages = (
        runner_module.VitestProgressStage.POST_DROP_PROBES,
        runner_module.VitestProgressStage.CANDIDATE_EXEC,
        runner_module.VitestProgressStage.WORKER_START,
        runner_module.VitestProgressStage.COORDINATOR_START,
        runner_module.VitestProgressStage.RESULT_PUBLISHED,
    )
    payload = b'{"tests":[]}'
    transport = b"".join(
        runner_module._vitest_progress_frame(stage) for stage in stages
    ) + runner_module._vitest_result_frame(payload)

    observed_payload, observed_stages = runner_module._parse_vitest_transport(
        transport
    )

    assert observed_payload == payload
    assert observed_stages == stages


def test_vitest_progress_transport_accepts_optional_stage_gaps() -> None:
    """Reporter publication need not observe worker or collection callbacks."""
    stages = (
        runner_module.VitestProgressStage.POST_DROP_PROBES,
        runner_module.VitestProgressStage.CANDIDATE_EXEC,
        runner_module.VitestProgressStage.COORDINATOR_START,
        runner_module.VitestProgressStage.RESULT_PUBLISHED,
    )
    payload = b'{"tests":[]}'
    transport = b"".join(
        runner_module._vitest_progress_frame(stage) for stage in stages
    ) + runner_module._vitest_result_frame(payload)

    observed_payload, observed_stages = runner_module._parse_vitest_transport(
        transport
    )

    assert observed_payload == payload
    assert observed_stages == stages


@pytest.mark.parametrize(
    ("transport", "message"),
    [
        (
            b"PDD-VITEST-PROGRESS-V1 post-drop-probes\n"
            b"PDD-VITEST-PROGRESS-V1 post-drop-probes\n",
            "Vitest progress transport stage is duplicated",
        ),
        (
            b"PDD-VITEST-PROGRESS-V1 post-drop-probes\n"
            b"PDD-VITEST-PROGRESS-V1 candidate-exec\n"
            b"PDD-VITEST-PROGRESS-V1 coordinator-start\n"
            b"PDD-VITEST-PROGRESS-V1 result-published\n"
            b"PDD-VITEST-PROGRESS-V1 collection-complete\n",
            (
                "Vitest progress transport stage is out of order "
                "(observed=post-drop-probes,candidate-exec,coordinator-start,"
                "result-published; failing=collection-complete)"
            ),
        ),
    ],
)
def test_vitest_progress_transport_rejects_duplicate_and_regressive_stages(
    transport: bytes, message: str,
) -> None:
    """A concurrent topology still rejects duplicates and post-result writes."""
    with pytest.raises(ValueError) as error:
        runner_module._parse_vitest_transport(transport)

    assert str(error.value) == message


def test_vitest_progress_sources_cover_post_ready_noncompletion_boundaries(
    tmp_path: Path,
) -> None:
    """Checker-owned launch, reporter, and preload sources emit exact stages."""
    addon = tmp_path / "checker-authority.node"
    addon.write_bytes(b"checker-owned authority")
    reporter = runner_module._vitest_reporter_source(198, 1, 2, addon)
    preload = runner_module._vitest_worker_preload_source(198, 1, 2)
    wrapper = supervisor_module._anonymous_framework_observation_command(
        ["/bin/true"], 198, seal_cross_process=True,
    )
    wrapper_source = wrapper[2]

    assert "post-drop-probes" in wrapper_source
    assert "candidate-exec" in wrapper_source
    assert wrapper_source.index("post-drop-probes") < wrapper_source.index(
        "candidate-exec"
    ) < wrapper_source.index("os.execvpe")
    assert "coordinator-start" in reporter
    assert "collection-complete" in reporter
    assert "result-published" in reporter
    assert "worker-start" in preload
    assert preload.index("worker-start") < preload.index("fs.closeSync")


def test_vitest_timeout_reports_only_allowlisted_progress() -> None:
    """Candidate prose cannot become trusted hosted-stage telemetry."""
    result = SupervisedCompletedProcess(
        ["vitest"], 124, "", "secret candidate diagnostic",
        termination=SupervisorTermination(
            TerminationKind.TIMEOUT,
            timeout_seconds=30,
            resource_telemetry=CgroupResourceTelemetry(0, 0, 0),
        ),
    )

    _outcome, detail = runner_module._vitest_infrastructure_termination(
        result,
        30,
        progress=(
            runner_module.VitestProgressStage.POST_DROP_PROBES,
            "candidate-controlled-secret",
        ),
    )

    assert "trusted_vitest_progress=post-drop-probes" in detail
    assert "candidate-controlled-secret" not in detail
    assert "secret candidate diagnostic" not in detail


UNIT = UnitId("repository-1", PurePosixPath("prompts/widget_ts.prompt"), "typescript")
IDENTITY = "tests/widget.test.ts::widget works"
_REQUIRED_NAPI_HEADERS = (
    "node_api.h",
    "node_api_types.h",
    "js_native_api.h",
    "js_native_api_types.h",
)

# This is deliberately candidate-side code used only by the real Linux
# lifecycle regression.  It never writes, replays, or opens the reporter
# authority for writing: a successful observation is itself the failure.
_SAFE_VITEST_AUTHORITY_PROBE = """const authorityFailure = (category) => {
  throw new Error('PDD_VITEST_AUTHORITY_EXPOSURE=' + category);
};
const trustedDecimal = (value) => {
  if (typeof value !== 'string' || !/^(0|[1-9][0-9]*)$/.test(value)) {
    authorityFailure('identity-environment');
  }
  return BigInt(value);
};
const expectedDevice = trustedDecimal(process.env.PDD_FRAMEWORK_OBSERVATION_DEVICE);
const expectedInode = trustedDecimal(process.env.PDD_FRAMEWORK_OBSERVATION_INODE);
const isTrustedObservation = (metadata) => (
  metadata.isFIFO()
  && metadata.dev === expectedDevice
  && metadata.ino === expectedInode
);
const rejectTrustedObservation = (inspect, category) => {
  try {
    if (isTrustedObservation(inspect())) authorityFailure(category);
  } catch (error) {
    if (error instanceof Error && error.message.startsWith('PDD_VITEST_AUTHORITY_EXPOSURE=')) {
      throw error;
    }
  }
};
rejectTrustedObservation(() => fs.fstatSync(198, { bigint: true }), 'direct-fd');
for (const name of fs.readdirSync('/proc/self/fd')) {
  const descriptor = Number(name);
  if (Number.isSafeInteger(descriptor) && descriptor >= 3 && descriptor !== 198) {
    rejectTrustedObservation(() => fs.fstatSync(descriptor, { bigint: true }), 'self-alias');
  }
}
let parentDescriptor;
try {
  parentDescriptor = fs.openSync(
    '/proc/' + process.ppid + '/fd/198', fs.constants.O_RDONLY | fs.constants.O_CLOEXEC,
  );
  if (isTrustedObservation(fs.fstatSync(parentDescriptor, { bigint: true }))) authorityFailure('parent-reopen');
} catch (error) {
  if (error instanceof Error && error.message.startsWith('PDD_VITEST_AUTHORITY_EXPOSURE=')) {
    throw error;
  }
} finally {
  if (typeof parentDescriptor === 'number') try { fs.closeSync(parentDescriptor); } catch (_) {}
}
"""


def test_real_vitest_authority_probe_is_observation_only() -> None:
    """Forge regression observes authority routes without corrupting framing."""
    assert "writeSync" not in _SAFE_VITEST_AUTHORITY_PROBE
    assert "direct-fd" in _SAFE_VITEST_AUTHORITY_PROBE
    assert "self-alias" in _SAFE_VITEST_AUTHORITY_PROBE
    assert "parent-reopen" in _SAFE_VITEST_AUTHORITY_PROBE
    assert "PDD_FRAMEWORK_OBSERVATION_DEVICE" in _SAFE_VITEST_AUTHORITY_PROBE
    assert "PDD_FRAMEWORK_OBSERVATION_INODE" in _SAFE_VITEST_AUTHORITY_PROBE
    assert "metadata.isFIFO()\n  && metadata.dev === expectedDevice" in (
        _SAFE_VITEST_AUTHORITY_PROBE
    )
    assert "BigInt(metadata.dev)" not in _SAFE_VITEST_AUTHORITY_PROBE
    assert "BigInt(metadata.ino)" not in _SAFE_VITEST_AUTHORITY_PROBE
    assert "fs.fstatSync(198, { bigint: true })" in _SAFE_VITEST_AUTHORITY_PROBE
    assert "fs.fstatSync(descriptor, { bigint: true })" in _SAFE_VITEST_AUTHORITY_PROBE
    assert "fs.fstatSync(parentDescriptor, { bigint: true })" in _SAFE_VITEST_AUTHORITY_PROBE
    assert "if (fs.fstatSync(descriptor).isFIFO())" not in _SAFE_VITEST_AUTHORITY_PROBE


@pytest.mark.skipif(
    not sys.platform.startswith("linux") or shutil.which("node") is None,
    reason="requires Linux /proc and Node.js",
)
@pytest.mark.parametrize("matches_expected", (False, True))
def test_real_vitest_authority_probe_allows_unrelated_fifo_and_rejects_exact_identity(
    matches_expected: bool,
) -> None:
    """Only the checker-measured FIFO identity is an authority exposure."""
    node = shutil.which("node")
    assert node is not None
    authority_read, authority_write = os.pipe()
    unrelated_read, unrelated_write = os.pipe()
    saved_descriptor = None
    try:
        try:
            saved_descriptor = os.dup(198)
        except OSError:
            pass
        selected = authority_write if matches_expected else unrelated_write
        os.dup2(selected, 198)
        expected = os.fstat(authority_write)
        script = (
            "import fs from 'node:fs';\n"
            "const openSync = fs.openSync.bind(fs);\n"
            "fs.openSync = (path, ...arguments_) => {\n"
            "  if (typeof path === 'string' && path.startsWith('/proc/')) {\n"
            "    const error = new Error('nondumpable coordinator');\n"
            "    error.code = 'EACCES'; throw error;\n"
            "  }\n"
            "  return openSync(path, ...arguments_);\n"
            "};\n"
            + _SAFE_VITEST_AUTHORITY_PROBE
            + "\nconsole.log('probe-complete');\n"
        )
        completed = subprocess.run(
            [node, "--input-type=module", "--eval", script],
            pass_fds=(198,),
            env=os.environ | {
                "PDD_FRAMEWORK_OBSERVATION_DEVICE": str(expected.st_dev),
                "PDD_FRAMEWORK_OBSERVATION_INODE": str(expected.st_ino),
            },
            capture_output=True,
            text=True,
            timeout=5,
            check=False,
        )
        if matches_expected:
            assert completed.returncode != 0
            assert "PDD_VITEST_AUTHORITY_EXPOSURE=direct-fd" in completed.stderr
        else:
            assert completed.returncode == 0, completed.stderr
            assert completed.stdout.strip() == "probe-complete"
    finally:
        if saved_descriptor is None:
            try:
                os.close(198)
            except OSError:
                pass
        else:
            os.dup2(saved_descriptor, 198)
            os.close(saved_descriptor)
        os.close(authority_read)
        os.close(authority_write)
        os.close(unrelated_read)
        os.close(unrelated_write)


@pytest.mark.skipif(shutil.which("node") is None, reason="requires Node.js")
def test_real_vitest_authority_probe_uses_bigint_stat_for_high_value_identity() -> None:
    """The identity comparison remains exact beyond JavaScript Number precision."""
    node = shutil.which("node")
    assert node is not None
    script = (
        "import fs from 'node:fs';\n"
        "fs.fstatSync = (descriptor, options) => {\n"
        "  if (descriptor !== 198 || options?.bigint !== true) {\n"
        "    throw new Error('expected bigint direct observation');\n"
        "  }\n"
        "  return { isFIFO: () => true, dev: 9007199254740993n, ino: 9007199254740995n };\n"
        "};\n"
        + _SAFE_VITEST_AUTHORITY_PROBE
    )
    completed = subprocess.run(
        [node, "--input-type=module", "--eval", script],
        env=os.environ
        | {
            "PDD_FRAMEWORK_OBSERVATION_DEVICE": "9007199254740993",
            "PDD_FRAMEWORK_OBSERVATION_INODE": "9007199254740995",
        },
        capture_output=True,
        text=True,
        timeout=5,
        check=False,
    )

    assert completed.returncode != 0
    assert "PDD_VITEST_AUTHORITY_EXPOSURE=direct-fd" in completed.stderr


def test_packaged_vitest_authority_probe_uses_exact_observation_identity() -> None:
    """The installed-wheel real-worker fixture uses the same exact binding."""
    workflow = (Path(__file__).parents[1] / ".github/workflows/unit-tests.yml").read_text(
        encoding="utf-8"
    )

    assert "PDD_FRAMEWORK_OBSERVATION_DEVICE" in workflow
    assert "PDD_FRAMEWORK_OBSERVATION_INODE" in workflow
    assert "metadata.dev === expectedDevice" in workflow
    assert "metadata.ino === expectedInode" in workflow
    assert "BigInt(metadata.dev)" not in workflow
    assert "BigInt(metadata.ino)" not in workflow
    assert "fs.fstatSync(198, { bigint: true })" in workflow
    assert "fs.fstatSync(descriptor, { bigint: true })" in workflow
    assert "fs.fstatSync(parentDescriptor, { bigint: true })" in workflow
    assert "if (fs.fstatSync(descriptor).isFIFO())" not in workflow


@pytest.fixture(autouse=True)
def _controlled_supervisor(
    monkeypatch: pytest.MonkeyPatch, request: pytest.FixtureRequest
) -> None:
    """Exercise adapter logic portably without weakening production policy."""
    test_name = request.node.originalname
    if test_name is None:
        test_name = request.node.name.split("[", 1)[0]
    if test_name.startswith("test_real_vitest_"):
        return

    native_authority_tests = (
        "test_vitest_reporter_exits_after_publishing_terminal_result",
        "test_vitest_reporter_completes_partial_result_writes",
        "test_vitest_reporter_rejects_result_write_without_progress",
        "test_vitest_coordinator_addon_staging_identity_is_rechecked",
        "test_vitest_coordinator_addon_failures_publish_no_result",
        "test_vitest_coordinator_addon_rejects_unsupported_platform",
        "test_vitest_coordinator_precompile_rejects_candidate_header_aliases",
        "test_vitest_coordinator_precompile_requires_phase_bound_header_attestation",
        "test_vitest_coordinator_precompile_rechecks_phase_attestation_without_rehash",
    )
    if test_name not in native_authority_tests:
        # The production authority deliberately rejects unsupported platforms
        # and requires a real Node distribution. Most adapter contracts use a
        # fake launcher and replace the supervisor, so give only those tests a
        # checker-only inert stand-in rather than weakening production policy.
        def portable_test_addon(
            staging_directory: Path,
            _selected_node: Path,
            _candidate_root=None,
            **_ignored,
        ) -> runner_module.VitestCoordinatorAddon:
            source = Path(runner_module.__file__).resolve().parent / "native/vitest_fd_cloexec.c"
            staged = staging_directory / runner_module.COORDINATOR_ADDON_NAME
            staged.write_bytes(b"portable test authority")
            staged.chmod(0o555)
            source_member = runner_module._capture_vitest_member(
                source, "coordinator_addon", PurePosixPath(".")
            )
            staged_member = runner_module._capture_vitest_member(
                staged, "coordinator_addon", PurePosixPath(".")
            )
            return runner_module.VitestCoordinatorAddon(
                source, staged, source_member, staged_member, "portable-test-authority"
            )

        monkeypatch.setattr(
            runner_module, "_load_vitest_coordinator_addon", portable_test_addon
        )

    def execute(
        command, *, cwd, timeout, env, result_fifo=None,
        result_write_fd=None, result_fd=198, **_limits,
    ):
        child_env = dict(env)
        opened_fd = os.open(result_fifo, os.O_WRONLY) if result_fifo else None
        observation_fd = result_write_fd if result_write_fd is not None else opened_fd
        if observation_fd is not None:
            observed = os.fstat(observation_fd)
            child_env.update({
                "PDD_FRAMEWORK_OBSERVATION_DEVICE": str(observed.st_dev),
                "PDD_FRAMEWORK_OBSERVATION_INODE": str(observed.st_ino),
            })
            os.dup2(observation_fd, result_fd)
            if opened_fd is not None and opened_fd != result_fd:
                os.close(opened_fd)
        try:
            result = subprocess.run(
                command,
                cwd=cwd,
                timeout=timeout,
                env=child_env,
                pass_fds=((result_fd,) if observation_fd is not None else ()),
                capture_output=True,
                text=True,
                check=False,
            )
        except subprocess.TimeoutExpired:
            result = subprocess.CompletedProcess(command, 124, "", "timeout")
        finally:
            if observation_fd is not None:
                os.close(result_fd)
        return result, False

    monkeypatch.setattr("pdd.sync_core.runner.run_supervised", execute)


def _run_trusted_reporter_source(
    tmp_path: Path, driver_source: str,
) -> tuple[subprocess.CompletedProcess[str], bytes]:
    """Run the generated reporter with one real inherited observation pipe."""
    node = shutil.which("node")
    if node is None:
        pytest.skip("requires Node.js")
    read_fd, write_fd = os.pipe()
    reporter = tmp_path / "trusted-reporter.mjs"
    driver = tmp_path / "reporter-driver.mjs"
    identity = os.fstat(write_fd)
    phase = _prepared_vitest_phase(tmp_path, use_system_node_headers=True)
    addon = runner_module._load_vitest_coordinator_addon(
        tmp_path, phase.headers, phase_toolchain=phase
    )
    reporter.write_text(
        _vitest_reporter_source(
            write_fd, identity.st_dev, identity.st_ino, addon.staged_path
        ),
        encoding="utf-8",
    )
    driver.write_text(driver_source, encoding="utf-8")
    try:
        try:
            completed = subprocess.run(
                [node, str(driver), str(reporter)],
                pass_fds=(write_fd,),
                capture_output=True,
                text=True,
                timeout=2,
                check=False,
            )
        finally:
            os.close(write_fd)
        result = bytearray()
        while chunk := os.read(read_fd, 4096):
            result.extend(chunk)
    finally:
        os.close(read_fd)
    return completed, bytes(result)


def _node_headers(node: Path) -> Path:
    """Return the N-API include role paired with a resolved Node launcher."""
    return node.resolve(strict=True).parents[1] / "include" / "node"


def _prepared_vitest_phase(
    tmp_path: Path, *, use_system_node_headers: bool = False,
) -> runner_module.VitestPhaseToolchain:
    """Materialize one phase-bound header attestation for native-addon tests."""
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    if use_system_node_headers:
        node = shutil.which("node")
        if node is None:
            pytest.skip("requires Node.js")
        manifest = config.vitest_toolchain_manifest
        assert manifest is not None
        payload = json.loads(manifest.read_text(encoding="utf-8"))
        launcher = Path(node).resolve(strict=True)
        payload["roles"]["launcher"] = str(launcher)
        payload["roles"]["headers"] = str(_node_headers(launcher))
        manifest.write_text(json.dumps(payload), encoding="utf-8")
        config = replace(
            config, vitest_command=(str(launcher), str(runner.resolve()))
        )
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "candidate", config)
    phase_root = tmp_path / "phase-toolchain"
    phase_root.mkdir()
    return _prepare_vitest_toolchain(phase_root, descriptor)


def _test_compiler_closure(
    compiler: Path, *_args,
) -> tuple[runner_module.VitestCompilerMember, ...]:
    """Return a path-independent compiler record for mocked precompile tests."""
    return (
        runner_module.VitestCompilerMember(
            "compiler",
            compiler,
            stat.S_IMODE(compiler.stat().st_mode),
            runner_module._member_content_digest(compiler),
        ),
    )


def _write_test_elf(path: Path, *, dynamic: bool) -> None:
    """Write one minimal ELF64 program table for closure-discovery tests."""
    header = bytearray(64)
    header[:7] = b"\x7fELF\x02\x01\x01"
    header[16:18] = (2).to_bytes(2, "little")
    header[32:40] = (64).to_bytes(8, "little")
    header[52:54] = (64).to_bytes(2, "little")
    header[54:56] = (56).to_bytes(2, "little")
    header[56:58] = (1).to_bytes(2, "little")
    program = bytearray(56)
    program[:4] = (3 if dynamic else 1).to_bytes(4, "little")
    path.write_bytes(header + program)
    path.chmod(0o555)


def test_vitest_compiler_plan_accepts_clang_integrated_topology(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Clang may use one driver/frontend/assembler binary plus one linker."""
    compiler = tmp_path / "clang"
    linker = tmp_path / "ld.lld"
    for executable in (compiler, linker):
        executable.write_bytes(b"tool")
        executable.chmod(0o555)

    def compiler_query(command, **_kwargs):
        if "-###" in command:
            return subprocess.CompletedProcess(
                command, 0, "", f' "{compiler}" "-cc1" "source.c"\n'
            )
        assert command[-1] == "-print-prog-name=ld"
        return subprocess.CompletedProcess(command, 0, f"{linker}\n", "")

    monkeypatch.setattr(runner_module.subprocess, "run", compiler_query)

    programs = runner_module._checker_compiler_programs(
        compiler,
        tmp_path / "source.c",
        tmp_path / "headers",
        tmp_path / "output.node",
    )

    assert programs == tuple(sorted((compiler.resolve(), linker.resolve())))


def test_vitest_compiler_runtime_accepts_verified_static_tool(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A structurally verified static ELF has no dynamic library closure."""
    compiler = tmp_path / "static-compiler"
    _write_test_elf(compiler, dynamic=False)
    monkeypatch.setattr(
        runner_module.subprocess,
        "run",
        lambda *_args, **_kwargs: pytest.fail("ldd must not run for static ELF"),
    )

    assert runner_module._checker_compiler_libraries((compiler,)) == ()


def test_vitest_compiler_runtime_allows_dynamic_tools_with_shared_libraries(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Each dynamic compiler program may have the same complete runtime closure."""
    compiler = tmp_path / "compiler"
    linker = tmp_path / "linker"
    library = tmp_path / "libshared.so"
    resolver = tmp_path / "ldd"
    for path in (compiler, linker):
        _write_test_elf(path, dynamic=True)
    library.write_bytes(b"shared library")
    resolver.write_bytes(b"resolver")
    monkeypatch.setattr(runner_module, "_CHECKER_LDD", resolver)

    def resolve_libraries(command, **_kwargs):
        assert command[1] in {str(compiler), str(linker)}
        return subprocess.CompletedProcess(
            command, 0, f"libshared.so => {library} (0x00000000)\\n", ""
        )

    monkeypatch.setattr(runner_module.subprocess, "run", resolve_libraries)

    assert runner_module._checker_compiler_libraries((compiler, linker)) == (
        library.resolve(),
    )


@pytest.mark.skipif(
    not sys.platform.startswith("linux"),
    reason="the production coordinator authority addon is Linux-only",
)
def test_vitest_reporter_exits_after_publishing_terminal_result(
    tmp_path: Path,
) -> None:
    """Awaited module completion survives a terminal callback with no modules."""
    completed, result = _run_trusted_reporter_source(
        tmp_path,
        """import path from 'node:path';
import { pathToFileURL } from 'node:url';
const { default: Reporter } = await import(pathToFileURL(process.argv[2]).href);
setInterval(() => {}, 1000);
process.exitCode = 7;
const reporter = new Reporter();
const testCase = {
  fullName: 'widget > works',
  result: () => ({state: 'passed', errors: []}),
};
const testModule = {
  id: 'project:widget',
  moduleId: path.join(process.cwd(), 'tests', 'widget.test.ts'),
  errors: () => [],
  children: { *allTests() { yield testCase; } },
};
reporter.onTestModuleEnd(testModule);
reporter.onTestRunEnd([], [], 'passed');
""",
    )

    assert completed.returncode == 0, completed.stderr
    assert result == (
        b"PDD-VITEST-PROGRESS-V1 coordinator-start\n"
        b"PDD-VITEST-PROGRESS-V1 result-published\n"
        b'PDD-VITEST-RESULT-V1 {"tests":['
        b'{"identity":"tests/widget.test.ts::widget > works",'
        b'"status":"passed","failureMessages":[]}],'
        b'"moduleErrors":0,"unhandledErrors":0}\n'
    )

@pytest.mark.skipif(
    not sys.platform.startswith("linux"),
    reason="the production coordinator authority addon is Linux-only",
)
@pytest.mark.parametrize(
    "mode", ("malformed-children", "malformed-module-errors", "malformed-terminal")
)
def test_vitest_reporter_rejects_invalid_completed_module_callbacks(
    tmp_path: Path, mode: str,
) -> None:
    """Callback-shape faults fail before canonical result publication."""
    completed, result = _run_trusted_reporter_source(
        tmp_path,
        f"""import path from 'node:path';
import {{ pathToFileURL }} from 'node:url';
const {{ default: Reporter }} = await import(pathToFileURL(process.argv[2]).href);
const reporter = new Reporter();
const testModule = {{
  id: 'project:widget',
  moduleId: path.join(process.cwd(), 'tests', 'widget.test.ts'),
  errors: () => [],
  children: {{ *allTests() {{ yield {{
    fullName: 'widget works',
    result: () => ({{state: 'passed', errors: []}}),
  }}; }} }},
}};
if ({json.dumps(mode)} === 'malformed-children') testModule.children = null;
if ({json.dumps(mode)} === 'malformed-module-errors') testModule.errors = () => null;
reporter.onTestModuleEnd(testModule);
reporter.onTestRunEnd(
  [], {json.dumps(mode)} === 'malformed-terminal' ? null : [], 'passed'
);
""",
    )

    assert completed.returncode != 0
    assert result == b"PDD-VITEST-PROGRESS-V1 coordinator-start\n"

@pytest.mark.skipif(
    not sys.platform.startswith("linux"),
    reason="the production coordinator authority addon is Linux-only",
)
def test_vitest_reporter_replaces_modules_and_sorts_canonical_tests(
    tmp_path: Path,
) -> None:
    """Repeated module snapshots replace stale state in deterministic order."""
    completed, result = _run_trusted_reporter_source(
        tmp_path,
        """import path from 'node:path';
import { pathToFileURL } from 'node:url';
const { default: Reporter } = await import(pathToFileURL(process.argv[2]).href);
const reporter = new Reporter();
const makeModule = (id, filename, names, errors = []) => ({
  id,
  moduleId: path.join(process.cwd(), 'tests', filename),
  errors: () => errors,
  children: { *allTests() {
    for (const name of names) yield {
      fullName: name,
      result: () => ({state: 'passed', errors: []}),
    };
  } },
});
reporter.onTestModuleEnd(makeModule('z-project', 'z.test.ts', ['old']));
reporter.onTestModuleEnd(makeModule('a-project', 'a.test.ts', ['z', 'a'], [{}]));
reporter.onTestModuleEnd(makeModule('z-project', 'z.test.ts', ['new']));
reporter.onTestRunEnd([], [{message: 'terminal'}], 'failed');
""",
    )

    assert completed.returncode == 1, completed.stderr
    records = result.splitlines()
    assert records[:2] == [
        b"PDD-VITEST-PROGRESS-V1 coordinator-start",
        b"PDD-VITEST-PROGRESS-V1 result-published",
    ]
    payload = records[2].removeprefix(b"PDD-VITEST-RESULT-V1 ")
    assert json.loads(payload) == {
        "tests": [
            {
                "identity": "tests/a.test.ts::a",
                "status": "passed",
                "failureMessages": [],
            },
            {
                "identity": "tests/a.test.ts::z",
                "status": "passed",
                "failureMessages": [],
            },
            {
                "identity": "tests/z.test.ts::new",
                "status": "passed",
                "failureMessages": [],
            },
        ],
        "moduleErrors": 1,
        "unhandledErrors": 1,
    }

@pytest.mark.skipif(
    not sys.platform.startswith("linux"),
    reason="the production coordinator authority addon is Linux-only",
)
@pytest.mark.parametrize(
    ("case", "status", "module_errors", "unhandled_errors", "terminal_exit", "expected"),
    (
        ("pass-spurious-terminal", "passed", 0, 0, 1, 0),
        ("failed-test", "failed", 0, 0, 0, 1),
        ("zero-identities", None, 0, 0, 0, 1),
        ("module-error", "passed", 1, 0, 0, 1),
        ("unhandled-error", "passed", 0, 1, 0, 1),
    ),
)
def test_vitest_reporter_exit_is_derived_from_canonical_evidence(
    tmp_path: Path,
    case: str,
    status: str | None,
    module_errors: int,
    unhandled_errors: int,
    terminal_exit: int,
    expected: int,
) -> None:
    """Only authenticated canonical evidence determines coordinator success."""
    completed, result = _run_trusted_reporter_source(
        tmp_path,
        f"""import path from 'node:path';
import {{ pathToFileURL }} from 'node:url';
const {{ default: Reporter }} = await import(pathToFileURL(process.argv[2]).href);
const reporter = new Reporter();
process.exitCode = {terminal_exit};
const status = {json.dumps(status)};
if (status !== null) reporter.onTestModuleEnd({{
  id: 'project:widget',
  moduleId: path.join(process.cwd(), 'tests', 'widget.test.ts'),
  errors: () => Array.from({{length: {module_errors}}}, () => ({{message: 'module'}})),
  children: {{ *allTests() {{ yield {{
    fullName: 'widget works',
    result: () => ({{state: status, errors: status === 'failed' ? [{{message: 'failed'}}] : []}}),
  }}; }} }},
}});
reporter.onTestRunEnd(
  [], Array.from({{length: {unhandled_errors}}}, () => ({{message: 'terminal'}})),
  'ignored'
);
""",
    )

    assert completed.returncode == expected, (case, completed.stderr)
    payload = json.loads(result.splitlines()[-1].removeprefix(b"PDD-VITEST-RESULT-V1 "))
    assert len(payload["tests"]) == (0 if status is None else 1)
    assert payload["moduleErrors"] == module_errors
    assert payload["unhandledErrors"] == unhandled_errors


@pytest.mark.skipif(
    not sys.platform.startswith("linux"),
    reason="the production coordinator authority addon is Linux-only",
)
def test_vitest_reporter_completes_partial_result_writes(tmp_path: Path) -> None:
    """Short writes cannot truncate canonical signed terminal evidence."""
    completed, result = _run_trusted_reporter_source(
        tmp_path,
        """import fs from 'node:fs';
import path from 'node:path';
import { pathToFileURL } from 'node:url';
const originalWriteSync = fs.writeSync.bind(fs);
fs.writeSync = (fd, value, offset = 0, length) => {
  const buffer = Buffer.isBuffer(value) ? value : Buffer.from(value);
  const requested = length ?? buffer.length - offset;
  return originalWriteSync(fd, buffer, offset, Math.min(requested, 3));
};
const { default: Reporter } = await import(pathToFileURL(process.argv[2]).href);
const reporter = new Reporter();
reporter.onTestModuleEnd({
  id: 'project:widget', moduleId: path.join(process.cwd(), 'tests', 'widget.test.ts'),
  errors: () => [], children: { *allTests() { yield {
    fullName: 'widget works', result: () => ({state: 'passed', errors: []}),
  }; } },
});
reporter.onTestRunEnd([], [], 'ignored');
""",
    )

    assert completed.returncode == 0, completed.stderr
    assert result.startswith(b"PDD-VITEST-PROGRESS-V1 coordinator-start\n")
    assert result.endswith(b'"moduleErrors":0,"unhandledErrors":0}\n')


@pytest.mark.skipif(
    not sys.platform.startswith("linux"),
    reason="the production coordinator authority addon is Linux-only",
)
def test_vitest_reporter_rejects_result_write_without_progress(
    tmp_path: Path,
) -> None:
    """A non-advancing canonical write fails before publication or exit."""
    completed, result = _run_trusted_reporter_source(
        tmp_path,
        """import fs from 'node:fs';
fs.writeSync = () => 0;
import { pathToFileURL } from 'node:url';
const { default: Reporter } = await import(pathToFileURL(process.argv[2]).href);
new Reporter().onTestRunEnd([], [], 'ignored');
""",
    )

    assert completed.returncode != 0
    assert result == b""

@pytest.mark.skipif(
    not sys.platform.startswith("linux"),
    reason="the production coordinator authority addon is Linux-only",
)
@pytest.mark.parametrize("duplicate", (False, True), ids=("idempotent", "duplicate"))
def test_vitest_reporter_module_identity_is_idempotent_but_globally_unique(
    tmp_path: Path, duplicate: bool,
) -> None:
    """A repeated module replaces itself; distinct modules cannot forge one identity."""
    completed, result = _run_trusted_reporter_source(
        tmp_path,
        f"""import path from 'node:path';
import {{ pathToFileURL }} from 'node:url';
const {{ default: Reporter }} = await import(pathToFileURL(process.argv[2]).href);
const reporter = new Reporter();
const moduleFor = (id) => ({{
  id, moduleId: path.join(process.cwd(), 'tests', 'widget.test.ts'), errors: () => [],
  children: {{ *allTests() {{ yield {{
    fullName: 'widget works', result: () => ({{state: 'passed', errors: []}}),
  }}; }} }},
}});
reporter.onTestModuleEnd(moduleFor('project:widget'));
reporter.onTestModuleEnd(moduleFor({json.dumps('project:other' if duplicate else 'project:widget')}));
reporter.onTestRunEnd([], [], 'ignored');
""",
    )

    assert (completed.returncode != 0) is duplicate
    assert result.endswith(b"\n")
    assert (b"PDD-VITEST-RESULT-V1 " in result) is not duplicate


def test_vitest_reporter_seals_checker_addon_before_worker_lifecycle(
    tmp_path: Path,
) -> None:
    """The checker seals before Vitest can create a worker lifecycle."""
    addon = tmp_path / "checker-authority.node"
    addon.write_bytes(b"checker-owned test addon")
    source = _vitest_reporter_source(198, 1, 2, addon)
    seal_call = "sealResultAuthority(RESULT_FD, EXPECTED_DEVICE, EXPECTED_INODE)"
    marker = "process.env.PDD_FRAMEWORK_COORDINATOR_NONDUMPABLE = '1';"
    valid_count = "if (!Number.isSafeInteger(SEALED_DESCRIPTOR_COUNT)"

    assert "const SEALED_DESCRIPTOR_COUNT" in source
    assert "constructor()" in source
    assert "onTestModuleEnd" in source
    assert seal_call in source
    assert source.index(seal_call) < source.index("export default class")
    assert source.index(seal_call) < source.index(valid_count) < source.index(marker)
    assert source.index(marker) < source.index("export default class")
    assert source.count(seal_call) == 1
    assert source.count(marker) == 1
    assert "authoritySealed" not in source
    assert "--require" not in source
    assert "execArgv" not in source


def test_vitest_environment_rejects_ambient_coordinator_nondumpable_marker(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Candidate code cannot receive a pre-seal coordinator-policy marker."""
    monkeypatch.setenv("PDD_FRAMEWORK_COORDINATOR_NONDUMPABLE", "forged")

    assert "PDD_FRAMEWORK_COORDINATOR_NONDUMPABLE" not in _vitest_environment(tmp_path)


def test_dev_extra_covers_no_isolation_build_requirements() -> None:
    """The CI dev environment can build the wheel without network isolation."""
    repository = Path(__file__).resolve().parents[1]
    pyproject = tomllib.loads((repository / "pyproject.toml").read_text(encoding="utf-8"))
    build_requirements = set(pyproject["build-system"]["requires"])
    dev_requirements = set(pyproject["project"]["optional-dependencies"]["dev"])

    missing = build_requirements - dev_requirements
    assert not missing, f"dev extra is missing build requirements: {sorted(missing)}"


def test_vitest_authority_wheel_is_source_only(tmp_path: Path) -> None:
    """The universal checker wheel carries C source, never a host native addon."""
    repository = Path(__file__).resolve().parents[1]
    source = tmp_path / "source"
    shutil.copytree(
        repository,
        source,
        ignore=shutil.ignore_patterns(
            ".git", ".pytest_cache", "__pycache__", "build", "dist",
            "*.egg-info", "*.node",
        ),
    )
    output = tmp_path / "dist"
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "build",
            "--no-isolation",
            "--wheel",
            "--outdir",
            str(output),
        ],
        cwd=source,
        check=False,
        env=os.environ
        | {
            "PIP_NO_INDEX": "1",
            "SETUPTOOLS_SCM_PRETEND_VERSION_FOR_PDD_CLI": "0.0.0",
        },
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 0, (
        f"source-only wheel build failed (exit {completed.returncode})\n"
        f"stdout:\n{completed.stdout}\n"
        f"stderr:\n{completed.stderr}"
    )
    wheels = tuple(output.glob("*.whl"))
    assert len(wheels) == 1
    with zipfile.ZipFile(wheels[0]) as archive:
        names = archive.namelist()
    assert "pdd/sync_core/native/vitest_fd_cloexec.c" in names
    assert not any(name.endswith(".node") for name in names)

    installed = tmp_path / "installed"
    subprocess.run(
        [
            sys.executable,
            "-m",
            "pip",
            "install",
            "--no-deps",
            "--no-index",
            "--target",
            str(installed),
            str(wheels[0]),
        ],
        cwd=tmp_path,
        check=True,
        capture_output=True,
        text=True,
    )
    measured = subprocess.run(
        [
            sys.executable,
            "-P",
            "-c",
            "import json; from pathlib import Path; "
            "import pdd.sync_core.runner as runner; "
            "native=Path(runner.__file__).resolve().parent/'native/vitest_fd_cloexec.c'; "
            "print(json.dumps({'module': runner.__file__, "
            "'native_sha256': runner._member_content_digest(native), "
            "'checker_digest': runner._checker_artifact_digest()}))",
        ],
        cwd=tmp_path,
        env=os.environ | {"PYTHONPATH": str(installed), "PDD_PATH": ""},
        check=True,
        capture_output=True,
        text=True,
    )
    installed_identity = json.loads(measured.stdout)
    packaged_source = (
        Path(runner_module.__file__).resolve().parent
        / "native"
        / runner_module.COORDINATOR_ADDON_SOURCE_NAME
    )
    assert Path(installed_identity["module"]).is_relative_to(installed)
    assert installed_identity["native_sha256"] == runner_module._member_content_digest(
        packaged_source
    )
    assert installed_identity["checker_digest"] == runner_module._checker_artifact_digest()


def test_vitest_coordinator_addon_rejects_unsupported_platform(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The Linux-only source authority has no unsafe portable fallback."""
    monkeypatch.setattr(runner_module.sys, "platform", "darwin")
    phase = _prepared_vitest_phase(tmp_path)

    with pytest.raises(
        ValueError, match=r"Linux.*?/usr/bin/cc.*?matching regular Node headers"
    ):
        runner_module._load_vitest_coordinator_addon(
            tmp_path, phase.headers, phase_toolchain=phase
        )


@pytest.mark.skipif(
    not sys.platform.startswith("linux"),
    reason="the production coordinator authority addon is Linux-only",
)
def test_vitest_coordinator_addon_staging_identity_is_rechecked(
    tmp_path: Path,
) -> None:
    """A substituted checker addon cannot be accepted after candidate execution."""
    node = shutil.which("node")
    if node is None:
        pytest.skip("requires Node.js")
    phase = _prepared_vitest_phase(tmp_path, use_system_node_headers=True)
    addon = runner_module._load_vitest_coordinator_addon(
        tmp_path, phase.headers, phase_toolchain=phase
    )
    addon.staged_path.chmod(0o755)
    addon.staged_path.write_bytes(b"substituted authority")

    with pytest.raises(ValueError, match="identity changed"):
        runner_module._verify_vitest_coordinator_addon(addon)


def test_vitest_native_binding_is_path_independent_and_complete(tmp_path: Path) -> None:
    """Source, compiler, exact headers, and generated output define one digest."""
    first_root = tmp_path / "first"
    second_root = tmp_path / "second"
    first_root.mkdir()
    second_root.mkdir()
    for root in (first_root, second_root):
        (root / "source.c").write_bytes(b"int authority(void) { return 1; }\n")
        (root / "source.c").chmod(0o444)
        (root / "compiler").write_bytes(b"compiler")
        (root / "compiler").chmod(0o555)
        (root / "compiler-runtime").write_bytes(b"compiler runtime")
        (root / "compiler-runtime").chmod(0o444)
        (root / "addon.node").write_bytes(b"native addon")
        (root / "addon.node").chmod(0o555)

    source = runner_module._capture_vitest_member(
        first_root / "source.c", "coordinator_addon", PurePosixPath(".")
    )
    output = runner_module._capture_vitest_member(
        first_root / "addon.node", "coordinator_addon", PurePosixPath(".")
    )
    compiler = (
        runner_module.VitestCompilerMember(
            "compiler",
            first_root / "compiler",
            0o555,
            runner_module._member_content_digest(first_root / "compiler"),
        ),
        runner_module.VitestCompilerMember(
            "runtime/0",
            first_root / "compiler-runtime",
            0o444,
            runner_module._member_content_digest(first_root / "compiler-runtime"),
        ),
    )
    headers = (
        runner_module.VitestToolchainMember(
            "headers", PurePosixPath("."), "directory", 0o555
        ),
        runner_module.VitestToolchainMember(
            "headers",
            PurePosixPath("node_api.h"),
            "file",
            0o444,
            content_digest="1" * 64,
        ),
    )
    identity = runner_module._vitest_coordinator_identity(
        source, compiler, headers, output
    )
    relocated = runner_module._vitest_coordinator_identity(
        runner_module._capture_vitest_member(
            second_root / "source.c", "coordinator_addon", PurePosixPath(".")
        ),
        tuple(
            replace(
                member,
                path=second_root / (
                    "compiler" if member.role == "compiler" else "compiler-runtime"
                ),
            )
            for member in compiler
        ),
        headers,
        runner_module._capture_vitest_member(
            second_root / "addon.node", "coordinator_addon", PurePosixPath(".")
        ),
    )

    assert relocated == identity
    changed_bindings = (
        (replace(source, content_digest="2" * 64), compiler, headers, output),
        (
            source,
            (replace(compiler[0], content_digest="3" * 64), compiler[1]),
            headers,
            output,
        ),
        (
            source,
            (compiler[0], replace(compiler[1], content_digest="6" * 64)),
            headers,
            output,
        ),
        (
            source,
            (replace(compiler[0], mode=0o500), compiler[1]),
            headers,
            output,
        ),
        (
            source,
            compiler,
            (headers[0], replace(headers[1], content_digest="4" * 64)),
            output,
        ),
        (
            source,
            compiler,
            (headers[0], replace(headers[1], mode=0o400)),
            output,
        ),
        (source, compiler, headers, replace(output, content_digest="5" * 64)),
        (replace(source, mode=0o400), compiler, headers, output),
        (source, compiler, headers, replace(output, mode=0o500)),
    )
    assert all(
        runner_module._vitest_coordinator_identity(*binding) != identity
        for binding in changed_bindings
    )


@pytest.mark.skipif(
    not sys.platform.startswith("linux"),
    reason="requires the Linux /proc descriptor table used by the production addon",
)
def test_vitest_coordinator_addon_seals_all_aliases_across_real_exec(
    tmp_path: Path,
) -> None:
    """A real fork+exec loses fd198 and its alias while the parent can report."""
    node = shutil.which("node")
    if node is None:
        pytest.skip("requires Node.js")
    addon_path = tmp_path / "exec-probe.node"
    subprocess.run(
        [sys.executable, "scripts/build_vitest_fd_cloexec_addon.py",
         "--output", str(addon_path), "--headers", str(_node_headers(Path(node))),
         "--exec-probe"],
        cwd=Path(__file__).parents[1], check=True,
    )
    read_fd, write_fd = os.pipe()
    alias_fd = os.dup(write_fd)
    saved_fd = None
    try:
        try:
            saved_fd = os.dup(198)
        except OSError:
            saved_fd = None
        os.dup2(write_fd, 198)
        identity = os.fstat(198)
        program = (
            "const fs=require('node:fs');"
            "const addon=require(process.argv[1]);"
            "const fd=198, alias=Number(process.argv[2]);"
            "addon.sealResultAuthority(fd,BigInt(process.argv[3]),BigInt(process.argv[4]));"
            "const status=addon.probeExec(process.execPath,fd,alias,"
            "BigInt(process.argv[3]),BigInt(process.argv[4]));"
            "if(status!==0)throw new Error('fork+exec retained authority');"
            "fs.writeSync(fd,Buffer.from('PDD-FRAME-V1 complete\\n'));"
        )
        completed = subprocess.run(
            [node, "-e", program, str(addon_path), str(alias_fd),
             str(identity.st_dev), str(identity.st_ino)],
            pass_fds=(198, alias_fd), capture_output=True, text=True,
            timeout=5, check=False,
        )
        assert completed.returncode == 0, completed.stderr
        assert os.read(read_fd, 4096) == b"PDD-FRAME-V1 complete\n"
    finally:
        if saved_fd is None:
            try:
                os.close(198)
            except OSError:
                pass
        else:
            os.dup2(saved_fd, 198)
            os.close(saved_fd)
        os.close(alias_fd)
        os.close(write_fd)
        os.close(read_fd)


@pytest.mark.skipif(
    not sys.platform.startswith("linux"),
    reason="requires the Linux /proc descriptor table used by the production addon",
)
def test_vitest_coordinator_addon_denies_cross_process_reopen_after_seal(
    tmp_path: Path,
) -> None:
    """A post-seal worker cannot reopen the coordinator's FIFO through procfs."""
    node = shutil.which("node")
    if node is None:
        pytest.skip("requires Node.js")
    addon_path = tmp_path / "cross-process-probe.node"
    subprocess.run(
        [sys.executable, "scripts/build_vitest_fd_cloexec_addon.py",
         "--output", str(addon_path), "--headers", str(_node_headers(Path(node)))],
        cwd=Path(__file__).parents[1], check=True,
    )
    read_fd, write_fd = os.pipe()
    saved_fd = None
    try:
        try:
            saved_fd = os.dup(198)
        except OSError:
            pass
        os.dup2(write_fd, 198)
        identity = os.fstat(198)
        child_program = (
            "const fs=require('node:fs');"
            "let reopened;"
            "try { reopened=fs.openSync('/proc/'+process.argv[1]+'/fd/'+process.argv[2],"
            "fs.constants.O_RDONLY|fs.constants.O_CLOEXEC);"
            "fs.closeSync(reopened); process.exit(process.argv[3]==='deny' ? 7 : 0); }"
            "catch (error) { process.exit(process.argv[3]==='deny' && error && "
            "(error.code==='EACCES'||error.code==='EPERM') ? 0 : 8); }"
        )
        program = (
            "const fs=require('node:fs'); const {spawnSync}=require('node:child_process');"
            "const addon=require(process.argv[1]); const fd=198;"
            f"const probe={json.dumps(child_program)};"
            "const before=spawnSync(process.execPath,['-e',probe,String(process.pid),String(fd),'allow']);"
            "if(before.status!==0)throw new Error('pre-seal procfs reopen control failed');"
            "addon.sealResultAuthority(fd,BigInt(process.argv[2]),BigInt(process.argv[3]));"
            "const after=spawnSync(process.execPath,['-e',probe,String(process.pid),String(fd),'deny']);"
            "if(after.status!==0)throw new Error("
            "'cross-process procfs authority reopen was not denied');"
            "fs.writeSync(fd,Buffer.from('PDD-FRAME-V1 complete\\n'));"
        )
        completed = subprocess.run(
            [node, "-e", program, str(addon_path), str(identity.st_dev), str(identity.st_ino)],
            pass_fds=(198,), capture_output=True, text=True,
            timeout=5, check=False,
        )
        assert completed.returncode == 0, completed.stderr
        assert os.read(read_fd, 4096) == b"PDD-FRAME-V1 complete\n"
    finally:
        if saved_fd is None:
            try:
                os.close(198)
            except OSError:
                pass
        else:
            os.dup2(saved_fd, 198)
            os.close(saved_fd)
        os.close(write_fd)
        os.close(read_fd)


@pytest.mark.skipif(
    not sys.platform.startswith("linux"),
    reason="requires the Linux production addon",
)
@pytest.mark.parametrize(
    "mode", ("wrong-identity", "non-fifo", "fcntl-error", "prctl-error"),
)
def test_vitest_coordinator_addon_failures_publish_no_result(
    tmp_path: Path, mode: str
) -> None:
    """Identity/type/sealing failures fail before the reporter can publish."""
    node = shutil.which("node")
    if node is None:
        pytest.skip("requires Node.js")
    phase = _prepared_vitest_phase(tmp_path, use_system_node_headers=True)
    addon = runner_module._load_vitest_coordinator_addon(
        tmp_path, phase.headers, phase_toolchain=phase
    )
    if mode in {"fcntl-error", "prctl-error"}:
        addon_path = tmp_path / f"forced-{mode}.node"
        option = "--force-fcntl-error" if mode == "fcntl-error" else "--force-prctl-error"
        subprocess.run(
            [sys.executable, "scripts/build_vitest_fd_cloexec_addon.py",
             "--output", str(addon_path), "--headers", str(_node_headers(Path(node))),
             option],
            cwd=Path(__file__).parents[1], check=True,
        )
    else:
        addon_path = addon.staged_path
    read_fd, write_fd = os.pipe()
    descriptor = write_fd
    regular = None
    try:
        if mode == "non-fifo":
            regular = tmp_path / "not-a-fifo"
            descriptor = os.open(regular, os.O_WRONLY | os.O_CREAT, 0o600)
        identity = os.fstat(descriptor)
        expected_inode = identity.st_ino + (1 if mode == "wrong-identity" else 0)
        program = (
            "const fs=require('node:fs'); const addon=require(process.argv[1]);"
            "try { addon.sealResultAuthority(Number(process.argv[2]),BigInt(process.argv[3]),BigInt(process.argv[4])); }"
            "catch (_) { process.exit(41); } process.exit(0);"
        )
        completed = subprocess.run(
            [node, "-e", program, str(addon_path), str(descriptor),
             str(identity.st_dev), str(expected_inode)],
            pass_fds=(descriptor,), capture_output=True, text=True,
            timeout=5, check=False,
        )
        assert completed.returncode == 41, completed.stderr
        os.set_blocking(read_fd, False)
        with pytest.raises(BlockingIOError):
            os.read(read_fd, 1)
    finally:
        if descriptor != write_fd:
            os.close(descriptor)
        os.close(write_fd)
        os.close(read_fd)


@pytest.mark.parametrize(
    "test_config",
    ({"reporters": ["default"]}, {"coverage": {"enabled": True}}),
    ids=("reporters", "coverage"),
)
def test_vitest_config_cannot_replace_or_extend_trusted_reporter(
    tmp_path: Path, test_config: dict[str, object]
) -> None:
    """Candidate config cannot add a reporter or enable coverage hooks."""
    root, commit = _repository(
        tmp_path, config=json.dumps({"test": test_config})
    )

    with pytest.raises(ValueError, match="not bound by this adapter"):
        vitest_validator_config_digest(
            root, commit, (PurePosixPath("tests/widget.test.ts"),)
        )


@pytest.mark.parametrize(
    "control",
    [
        "--testNamePattern=smoke",
        "--project=unit",
        "--shard=1/2",
        "--related=src/widget.ts",
        "--retry=3",
        "--repeat=2",
        "--update",
    ],
)
def test_vitest_command_schema_rejects_non_launcher_controls(
    tmp_path: Path, control: str
) -> None:
    launcher = tmp_path / "node"
    launcher.write_text("#!/bin/sh\n", encoding="utf-8")
    launcher.chmod(0o755)
    entrypoint = tmp_path / "vitest.mjs"
    entrypoint.write_text("", encoding="utf-8")

    assert _vitest_command_error(
        tmp_path, (str(launcher), str(entrypoint), control)
    ) is not None


def test_vitest_prior_retry_failure_cannot_normalize_to_pass(tmp_path: Path) -> None:
    output = tmp_path / "results.json"
    output.write_text(
        json.dumps(
            {
                "testResults": [
                    {
                        "name": str(tmp_path / "tests/widget.test.ts"),
                        "assertionResults": [
                            {
                                "title": "widget works",
                                "fullName": "widget works",
                                "status": "passed",
                                "failureMessages": ["first attempt failed"],
                            }
                        ],
                    }
                ]
            }
        ),
        encoding="utf-8",
    )

    outcome, _detail, _identities = _vitest_result(tmp_path, output, 0, None)
    assert outcome is not EvidenceOutcome.PASS


def test_vitest_present_malformed_canonical_schema_cannot_fallback_to_legacy(
    tmp_path: Path,
) -> None:
    """A present canonical schema never downgrades to compatible legacy data."""
    output = tmp_path / "results.json"
    output.write_text(
        json.dumps(
            {
                "tests": None,
                "moduleErrors": 0,
                "unhandledErrors": 0,
                "testResults": [
                    {
                        "name": str(tmp_path / "tests/widget.test.ts"),
                        "assertionResults": [
                            {
                                "title": "widget works",
                                "fullName": "widget works",
                                "status": "passed",
                                "failureMessages": [],
                            }
                        ],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )

    outcome, _detail, identities = _vitest_result(tmp_path, output, 0, None)

    assert outcome is EvidenceOutcome.COLLECTION_ERROR
    assert identities == ()


@pytest.mark.parametrize(
    ("field", "value"),
    (
        ("failureMessages", ["prior failure"]),
        ("moduleErrors", 1),
        ("unhandledErrors", 1),
    ),
)
def test_vitest_canonical_failure_evidence_cannot_normalize_to_pass(
    tmp_path: Path, field: str, value: object,
) -> None:
    """Terminal graph and error evidence adjudicate even with exit status zero."""
    item = {
        "identity": IDENTITY,
        "status": "passed",
        "failureMessages": [],
    }
    payload = {"tests": [item], "moduleErrors": 0, "unhandledErrors": 0}
    if field == "failureMessages":
        item[field] = value
    else:
        payload[field] = value
    output = tmp_path / "results.json"
    output.write_text(json.dumps(payload), encoding="utf-8")

    outcome, _detail, identities = _vitest_result(tmp_path, output, 0, None)

    assert outcome is EvidenceOutcome.FAIL
    assert identities == (IDENTITY,)


@pytest.mark.parametrize(
    "payload",
    (
        {"tests": [], "moduleErrors": 0},
        {"tests": [], "moduleErrors": False, "unhandledErrors": 0},
        {"tests": [], "moduleErrors": -1, "unhandledErrors": 0},
        {"tests": [], "moduleErrors": 0, "unhandledErrors": "1"},
        {
            "tests": [{
                "identity": IDENTITY,
                "status": "passed",
                "failureMessages": None,
            }],
            "moduleErrors": 0,
            "unhandledErrors": 0,
        },
        {
            "tests": [{
                "identity": IDENTITY,
                "status": "passed",
                "failureMessages": [1],
            }],
            "moduleErrors": 0,
            "unhandledErrors": 0,
        },
    ),
)
def test_vitest_canonical_error_schema_fails_closed(
    tmp_path: Path, payload: object,
) -> None:
    """Canonical tests and bounded error counts have one strict schema."""
    output = tmp_path / "results.json"
    output.write_text(json.dumps(payload), encoding="utf-8")

    outcome, _detail, identities = _vitest_result(tmp_path, output, 0, None)

    assert outcome is EvidenceOutcome.COLLECTION_ERROR
    assert identities == ()


def test_vitest_forged_pass_cannot_normalize_failed_execution(
    tmp_path: Path,
) -> None:
    """Worker-authored PASS bytes cannot erase a failing process outcome."""
    output = tmp_path / "results.json"
    output.write_text(
        json.dumps({
            "tests": [{
                "identity": IDENTITY,
                "status": "passed",
                "failureMessages": [],
            }],
            "moduleErrors": 0,
            "unhandledErrors": 0,
        }),
        encoding="utf-8",
    )

    outcome, _detail, identities = _vitest_result(tmp_path, output, 1, None)

    assert outcome is EvidenceOutcome.FAIL
    assert identities == (IDENTITY,)


@pytest.mark.skipif(
    not sys.platform.startswith("linux"),
    reason="requires Linux pipe descriptor identity",
)
def test_vitest_worker_preload_closes_helper_identity_without_worker_environment(
    tmp_path: Path,
) -> None:
    """A helper-bound descriptor closes even when fork workers drop PDD env."""
    node = shutil.which("node")
    if node is None:
        pytest.skip("requires Node")
    outer_read_fd, outer_write_fd = os.pipe()
    namespace_read_fd, namespace_write_fd = os.pipe()
    os.set_blocking(namespace_read_fd, False)
    try:
        outer = os.fstat(outer_write_fd)
        namespace = os.fstat(namespace_write_fd)
        assert (outer.st_dev, outer.st_ino) != (namespace.st_dev, namespace.st_ino)
        preload = tmp_path / "worker-preload.cjs"
        preload.write_text(
            _vitest_worker_preload_source(
                namespace_write_fd, namespace.st_dev, namespace.st_ino
            ),
            encoding="utf-8",
        )
        sealed = subprocess.run(
            [
                node,
                f"--require={preload}",
                "-e",
                (
                    "const fs=require('node:fs');"
                    f"const expected={namespace.st_dev}n+':'+{namespace.st_ino}n;"
                    "const matches=fs.readdirSync('/dev/fd').filter(x=>/^\\d+$/.test(x))"
                    ".map(Number).filter(fd=>{try{const s=fs.fstatSync(fd,{bigint:true});"
                    "return s.dev+':'+s.ino===expected}catch(e){return false}});"
                    "if(matches.length)process.exit(2)"
                ),
            ],
            pass_fds=(namespace_write_fd,),
            capture_output=True,
            text=True,
            env={"PATH": os.environ["PATH"]},
            check=False,
        )
        assert sealed.returncode == 0, sealed.stderr
        observation = os.read(namespace_read_fd, 4096)
    finally:
        os.close(namespace_write_fd)
        os.close(namespace_read_fd)
        os.close(outer_write_fd)
        os.close(outer_read_fd)

    assert observation == b"PDD-VITEST-PROGRESS-V1 worker-start\n"


def test_vitest_worker_preload_accepts_coordinator_cloexec_descriptor(
    tmp_path: Path,
) -> None:
    """A sealed coordinator may remove its result descriptor before worker exec."""
    node = shutil.which("node")
    if node is None:
        pytest.skip("requires Node")
    read_fd, write_fd = os.pipe()
    saved_fd = None
    result_fd_open = False
    try:
        try:
            saved_fd = os.dup(198)
        except OSError:
            saved_fd = None
        os.dup2(write_fd, 198, inheritable=False)
        result_fd_open = True
        os.close(write_fd)
        write_fd = -1
        identity = os.fstat(198)
        preload = tmp_path / "worker-preload.cjs"
        preload.write_text(
            _vitest_worker_preload_source(198, identity.st_dev, identity.st_ino),
            encoding="utf-8",
        )

        worker = subprocess.run(
            [
                node,
                f"--require={preload}",
                "-e",
                "process.stdout.write('worker-entrypoint')",
            ],
            close_fds=False,
            capture_output=True,
            text=True,
            env={"PATH": os.environ["PATH"]},
            check=False,
        )
        os.close(198)
        result_fd_open = False
        observation = os.read(read_fd, 4096)
    finally:
        if result_fd_open:
            os.close(198)
        if saved_fd is not None:
            os.dup2(saved_fd, 198)
            os.close(saved_fd)
        if write_fd >= 0:
            os.close(write_fd)
        os.close(read_fd)

    assert worker.returncode == 0, worker.stderr
    assert worker.stdout == "worker-entrypoint"
    assert observation == b""


@pytest.mark.skipif(
    not sys.platform.startswith("linux"),
    reason="requires Linux pipe descriptor identity",
)
def test_vitest_worker_preload_rejects_rebound_result_descriptor(
    tmp_path: Path,
) -> None:
    """A candidate cannot substitute a new pipe before the trusted preload."""
    node = shutil.which("node")
    if node is None:
        pytest.skip("requires Node")
    expected_read_fd, expected_write_fd = os.pipe()
    rebound_read_fd, rebound_write_fd = os.pipe()
    try:
        expected = os.fstat(expected_write_fd)
        preload = tmp_path / "worker-preload.cjs"
        preload.write_text(
            _vitest_worker_preload_source(
                rebound_write_fd, expected.st_dev, expected.st_ino
            ), encoding="utf-8"
        )
        rejected = subprocess.run(
            [node, f"--require={preload}", "-e", "process.exit(0)"],
            pass_fds=(rebound_write_fd,),
            capture_output=True,
            text=True,
            env={"PATH": os.environ["PATH"]},
            check=False,
        )
        assert rejected.returncode != 0
        assert "trusted Vitest result descriptor identity mismatch" in rejected.stderr
        os.set_blocking(rebound_read_fd, False)
        with pytest.raises(BlockingIOError):
            os.read(rebound_read_fd, 1)
    finally:
        os.close(expected_read_fd)
        os.close(expected_write_fd)
        os.close(rebound_read_fd)
        os.close(rebound_write_fd)


def test_vitest_declared_product_is_excluded_from_support_digest(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "src").mkdir()
    (root / "src/product.ts").write_text("export const value = 1;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import '../src/product';\nimport { test } from 'vitest';\ntest('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "import declared product")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    products = (PurePosixPath("src/product.ts"),)
    before = vitest_validator_config_digest(root, "HEAD", paths, products)
    (root / "src/product.ts").write_text("export const value = 2;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change product")
    assert vitest_validator_config_digest(root, "HEAD", paths, products) == before


def test_vitest_ast_binds_static_template_loader_and_rejects_runtime_config(
    tmp_path: Path,
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/resource.ts").write_text("export default 'base';\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import(`./resource`);\nimport { test } from 'vitest';\ntest('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add static template loader")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    before = vitest_validator_config_digest(root, "HEAD", paths)
    (root / "tests/resource.ts").write_text("export default 'changed';\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change loaded resource")
    assert vitest_validator_config_digest(root, "HEAD", paths) != before
    (root / "snapshot-environment.ts").write_text("export {};\n", encoding="utf-8")
    (root / "vitest.config.json").write_text(
        '{"test":{"snapshotEnvironment":"./snapshot-environment.ts"}}', encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "unsupported runtime config")
    with pytest.raises(ValueError, match="snapshotEnvironment"):
        vitest_validator_config_digest(root, "HEAD", paths)


@pytest.mark.parametrize(
    "loader",
    [
        "const p = './helper'; module.require(p);",
        "import.meta.glob('./helpers/*.ts');",
    ],
)
def test_vitest_rejects_unbound_alternate_local_loaders(
    tmp_path: Path, loader: str
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.test.ts").write_text(
        f"{loader}\nimport {{ test }} from 'vitest';\ntest('widget works', () => {{}});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add alternate loader")

    with pytest.raises(ValueError, match="loader|module loading|glob|createRequire"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


def test_vitest_rejects_unbound_alternate_loader_transitively(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/helper.ts").write_text(
        "import.meta.glob('./fixtures/*.ts');\n", encoding="utf-8"
    )
    (root / "tests/widget.test.ts").write_text(
        "import './helper';\nimport { test } from 'vitest';\n"
        "test('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add transitive alternate loader")

    with pytest.raises(ValueError, match="glob|loader"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


@pytest.mark.parametrize(
    "loader",
    [
        "const req = require; req('./helper.cjs');",
        (
            "import { createRequire } from 'node:module'; "
            "const req = createRequire(import.meta.url); req('./helper.cjs');"
        ),
        (
            "import { createRequire as makeRequire } from 'node:module'; "
            "const req = makeRequire(import.meta.url); req('./helper.cjs');"
        ),
        (
            "const { createRequire: makeRequire } = require('node:module'); "
            "const req = makeRequire(import.meta.url); req('./helper.cjs');"
        ),
        "let req; req = require; req('./helper.cjs');",
    ],
)
def test_vitest_binds_statically_proven_commonjs_loader_aliases(
    tmp_path: Path, loader: str
) -> None:
    root, _commit = _repository(tmp_path)
    helper = root / "tests/helper.cjs"
    helper.write_text("module.exports = 'trusted';\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        f"{loader}\nimport {{ test }} from 'vitest';\n"
        "test('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add static CommonJS alias")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    before = vitest_validator_config_digest(root, "HEAD", paths)
    helper.write_text("module.exports = 'changed';\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change CommonJS helper")

    assert vitest_validator_config_digest(root, "HEAD", paths) != before


@pytest.mark.parametrize(
    "loader",
    [
        "let req = require; req = unknown; req('./helper.cjs');",
        "const req = enabled ? require : unknown; req('./helper.cjs');",
        (
            "import { createRequire } from 'node:module'; "
            "const req = createRequire(runtimeUrl); req('./helper.cjs');"
        ),
        "const req = require; const box = { req }; box.req('./helper.cjs');",
        "const box = getLoader(); box.load('./helper.cjs');",
        "const p = './helper.cjs'; require.apply(null, [p]);",
        "const p = './helper.cjs'; Reflect.apply(require, null, [p]);",
        "const p = './helper.cjs'; const [load = require] = []; load(p);",
        "const p = './helper.cjs'; module.constructor._load(p, module);",
    ],
)
def test_vitest_rejects_dynamic_or_ambiguous_loader_aliases(
    tmp_path: Path, loader: str
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/helper.cjs").write_text("module.exports = 1;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        f"{loader}\nimport {{ test }} from 'vitest';\n"
        "test('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add ambiguous CommonJS alias")

    with pytest.raises(ValueError, match="alias|loader|dynamic|provenance"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


@pytest.mark.parametrize(
    "loader",
    [
        (
            "const p = './helper.cjs'; "
            "function invoke(loader, arg) { return loader(arg); } "
            "invoke(require, p);"
        ),
        (
            "const p = './helper.cjs'; const { apply } = Reflect; "
            "apply(require, null, [p]);"
        ),
        (
            "const p = './helper.cjs'; const invoke = Reflect.apply; "
            "invoke(require, null, [p]);"
        ),
        (
            "const p = './helper.cjs'; const invoke = Function.prototype.call; "
            "invoke(require, null, p);"
        ),
        "const p = './helper.cjs'; (0, require)(p);",
        "const p = './helper.cjs'; (require, require)(p);",
        (
            "import Module from 'node:module'; const p = './helper.cjs'; "
            "const load = Module._load; load(p);"
        ),
        (
            "const p = './helper.cjs'; "
            "const load = module.constructor._load; load(p, module);"
        ),
        (
            "import Module from 'node:module'; const p = './helper.cjs'; "
            "const { _load: load } = Module; load(p);"
        ),
        (
            "const key = '_load'; const p = './helper.cjs'; "
            "const load = module.constructor[key]; load(p, module);"
        ),
        "const p = './helper.cjs'; const box = { load: require }; box.load(p);",
        "const p = './helper.cjs'; function pass() { return require; } pass()(p);",
        "const req = require; { const req = unknown; req('./helper.cjs'); }",
        "const req = require; function shadow(req) { req('./helper.cjs'); } shadow(req);",
        "const req = require; req = unknown; req('./helper.cjs');",
        r"requ\u0069re(process.argv[2]);",
        r"const req = requ\u0069re; req(process.argv[2]);",
        (
            r"import { create\u0052equire as make } from 'node:module'; "
            "const req = make(import.meta.url); req(process.argv[2]);"
        ),
        "eval('require')(process.argv[2]);",
        "Function('return require')()(process.argv[2]);",
        (
            "const m = module; const req = Reflect.get(m, 'require'); "
            "req(process.argv[2]);"
        ),
        (
            "const m = module; const c = m.constructor; const key = '_lo' + 'ad'; "
            "const load = c[key]; load(process.argv[2], m);"
        ),
        (
            "const m = module; const c = m.constructor; "
            "const load = Reflect.get(c, '_lo' + 'ad'); load(process.argv[2], m);"
        ),
        (
            "const key = 'requ' + 'ire'; const req = globalThis[key]; "
            "req(process.argv[2]);"
        ),
        (
            "const key = '_lo' + 'ad'; const load = process.mainModule.constructor[key]; "
            "load(process.argv[2]);"
        ),
    ],
)
def test_vitest_positive_loader_capability_rejects_unproven_uses(
    tmp_path: Path, loader: str
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/helper.cjs").write_text("module.exports = 1;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        f"{loader}\nimport {{ test }} from 'vitest';\n"
        "test('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add uncertain loader capability")

    with pytest.raises(ValueError, match="capability|loader|provenance|internal"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


def test_vitest_rejects_loader_capability_forwarding_transitively(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/helper.cjs").write_text("module.exports = 1;\n", encoding="utf-8")
    (root / "tests/loader.cjs").write_text(
        "const p = './helper.cjs';\n"
        "function invoke(loader, arg) { return loader(arg); }\n"
        "module.exports = invoke(require, p);\n",
        encoding="utf-8",
    )
    (root / "tests/widget.test.ts").write_text(
        "import './loader.cjs';\nimport { test } from 'vitest';\n"
        "test('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "forward loader transitively")

    with pytest.raises(ValueError, match="capability|loader|provenance"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


def test_vitest_binds_transitive_create_require_helper_mutation(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    fixture = root / "tests/fixture.cjs"
    fixture.write_text("module.exports = 'trusted';\n", encoding="utf-8")
    (root / "tests/loader.cjs").write_text(
        "const { createRequire: makeRequire } = require('node:module');\n"
        "const req = makeRequire(import.meta.url);\n"
        "module.exports = req('./fixture.cjs');\n",
        encoding="utf-8",
    )
    (root / "tests/widget.test.ts").write_text(
        "import './loader.cjs';\nimport { test } from 'vitest';\n"
        "test('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add transitive createRequire helper")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    before = vitest_validator_config_digest(root, "HEAD", paths)
    fixture.write_text("module.exports = 'changed';\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate transitive createRequire helper")

    assert vitest_validator_config_digest(root, "HEAD", paths) != before


def test_vitest_grammar_dependencies_are_exactly_pinned() -> None:
    project = tomllib.loads(
        (Path(__file__).parents[1] / "pyproject.toml").read_text(encoding="utf-8")
    )
    dependencies = set(project["project"]["dependencies"])

    assert "tree-sitter==0.25.2" in dependencies
    assert "tree-sitter-javascript==0.25.0" in dependencies
    assert "tree-sitter-typescript==0.23.2" in dependencies
    assert not any(item.startswith("tree-sitter-language-pack") for item in dependencies)


def test_real_vitest_workflow_uses_checked_in_locked_toolchain() -> None:
    """Hosted protected Vitest must use one locked toolchain in a fresh worker."""
    root = Path(__file__).parents[1]
    toolchain = root / ".github/toolchains/vitest"
    package = json.loads((toolchain / "package.json").read_text(encoding="utf-8"))
    lock = json.loads((toolchain / "package-lock.json").read_text(encoding="utf-8"))
    workflow = (root / ".github/workflows/unit-tests.yml").read_text(encoding="utf-8")
    vitest_step = workflow[
        workflow.index("- name: Provision identity-bound Vitest toolchain"):
        workflow.index("- name: Provision identity-bound Playwright Chromium toolchain")
    ]

    assert package["private"] is True
    assert package["dependencies"] == {"vitest": "4.1.10"}
    assert lock["packages"][""]["dependencies"] == package["dependencies"]
    assert 'cp .github/toolchains/vitest/package.json "$toolchain/"' in workflow
    assert 'cp .github/toolchains/vitest/package-lock.json "$toolchain/"' in workflow
    assert 'npm ci --prefix "$toolchain" --ignore-scripts --no-audit --no-fund' in workflow
    assert 'npm install --prefix "$toolchain"' not in vitest_step
    real_vitest_test = (
        "tests/test_sync_core_runner_vitest.py::"
        "test_real_vitest_runs_copied_entrypoint_without_candidate_result_access"
    )
    sandbox_step = "- name: Provision and verify protected Linux sandbox"
    dedicated_step = "- name: Verify real Vitest sandbox isolation"
    focused_step = "- name: Run focused protected-runner tests"
    bulk_step = "- name: Run unit tests"
    sandbox_index = workflow.index(sandbox_step)
    dedicated_index = workflow.index(dedicated_step)
    focused_index = workflow.index(focused_step)
    bulk_index = workflow.index(bulk_step)
    dedicated_body = workflow[dedicated_index:focused_index]
    bulk_body = workflow[bulk_index:]
    target_deselect = f"--deselect={real_vitest_test}"

    assert sandbox_index < dedicated_index < focused_index < bulk_index
    assert dedicated_body.count(f"pytest -q {real_vitest_test} --timeout=180") == 1
    assert workflow.count(real_vitest_test) >= 2
    assert "pytest -q -n" not in dedicated_body
    assert "xdist" not in dedicated_body
    assert "--deselect" not in dedicated_body
    assert "continue-on-error" not in dedicated_body
    assert target_deselect not in workflow[:bulk_index]
    assert bulk_body.count(target_deselect) == 1


def test_vitest_diagnostic_workflow_preserves_red_probe_and_uploads_evidence(
    tmp_path: Path,
) -> None:
    """Stage-1 uses protected identity/provenance and preserves Unit RED."""
    repository = Path(__file__).parents[1]
    workflow = (repository / ".github/workflows/unit-tests.yml").read_text(
        encoding="utf-8"
    )
    workflow_payload = yaml.safe_load(workflow)
    provenance_script = next(
        step["run"]
        for step in workflow_payload["jobs"]["unit-tests"]["steps"]
        if step.get("name") == "Verify reviewed identity and runner provenance"
    )
    dedicated_step = "- name: Verify real Vitest sandbox isolation"
    upload_step = "- name: Upload Vitest termination evidence"
    focused_step = "- name: Run focused protected-runner tests"
    dedicated_body = workflow[
        workflow.index(dedicated_step):workflow.index(upload_step)
    ]
    upload_body = workflow[
        workflow.index(upload_step):workflow.index(focused_step)
    ]

    checkout_body = workflow[
        workflow.index("- name: Checkout"):workflow.index("- name: Set up Python")
    ]
    provenance_step = "- name: Verify reviewed identity and runner provenance"
    provision_step = "- name: Provision identity-bound Vitest toolchain"
    provenance_body = workflow[
        workflow.index(provenance_step):workflow.index(provision_step)
    ]
    assert "runs-on: ubuntu-24.04" in workflow[:workflow.index("steps:")]
    assert (
        "ref: ${{ vars.PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA }}" in checkout_body
    )
    assert "persist-credentials: false" in checkout_body
    assert "PDD_TRIGGER_EVENT_NAME: ${{ github.event_name }}" in workflow
    assert (
        "PDD_TRIGGER_PR_HEAD_SHA: ${{ github.event.pull_request.head.sha }}"
        in workflow
    )
    assert (
        'check_equal "trigger-event" "pull_request" "$PDD_TRIGGER_EVENT_NAME"'
        in provenance_body
    )
    assert "python-version: '3.12.13'" in workflow[
        :workflow.index(provision_step)
    ]
    assert (
        '"trigger-head-reviewed-head"'
        in provenance_body
    )
    assert 'capture_output checked_out_head "checkout-head-read"' in provenance_body
    assert (
        '"checkout-head-trigger-head"'
        in provenance_body
    )
    assert (
        '"checkout-head-reviewed-head"'
        in provenance_body
    )
    event_guard = provenance_script[:provenance_script.index("for required in")]
    marker = "candidate-pytest-would-run"
    for case_name, event_name, event_head, reviewed_head, predicate in (
        (
            "head-mismatch", "pull_request", "a" * 40, "b" * 40,
            "trigger-head-reviewed-head",
        ),
        ("non-pr", "push", "", "b" * 40, "trigger-event"),
    ):
        runner_temp = tmp_path / case_name
        runner_temp.mkdir()
        review_secret = "secret-review-evidence-must-not-appear"
        mismatch = subprocess.run(
            ["bash", "-c", event_guard + f"\nprintf '%s\\n' '{marker}'\n"],
            cwd=repository,
            env={
                **os.environ,
                "RUNNER_TEMP": str(runner_temp),
                "PDD_TRIGGER_EVENT_NAME": event_name,
                "PDD_TRIGGER_PR_HEAD_SHA": event_head,
                "PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA": reviewed_head,
                "PDD_REVIEW_EVIDENCE_B64": review_secret,
            },
            capture_output=True,
            text=True,
            check=False,
        )
        assert mismatch.returncode != 0
        assert marker not in mismatch.stdout
        assert f"predicate={predicate}" in mismatch.stderr
        artifact = (
            runner_temp / "pdd-vitest-preflight-evidence"
            / "vitest-preflight-v1.json"
        )
        encoded = artifact.read_bytes()
        payload = json.loads(encoded)
        assert encoded == (
            json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n"
        ).encode("ascii")
        assert payload["schema"] == "vitest-preflight-v1"
        assert payload["predicate"] == predicate
        assert payload["observation_base64"] == ""
        assert payload["observation_sha256"] == hashlib.sha256(b"").hexdigest()
        assert payload["observation_truncated"] is False
        assert review_secret not in encoded.decode("ascii")
        assert stat.S_IMODE(artifact.stat().st_mode) == 0o600
        assert Path(str(artifact) + ".sha256").read_text(encoding="ascii") == (
            hashlib.sha256(encoded).hexdigest() + "\n"
        )
    provisioner_temp = tmp_path / "provisioner-command"
    provisioner_temp.mkdir()
    provisioner_output = b"hosted-compute-agent rejected --version\n"
    function_prefix = provenance_script[
        :provenance_script.index('check_equal "trigger-event"')
    ]
    provisioner_failure = subprocess.run(
        [
            "bash", "-c", function_prefix + "\n"
            'observation="$RUNNER_TEMP/provisioner-output"\n'
            "printf '%s' 'hosted-compute-agent rejected --version\n' "
            '> "$observation"\n'
            "preflight_fail runner-provisioner-command exit=0 exit=64 "
            '64 "$observation" 64\n',
        ],
        cwd=repository,
        env={
            **os.environ,
            "RUNNER_TEMP": str(provisioner_temp),
            "PDD_REVIEW_EVIDENCE_B64": "secret-review-evidence",
        },
        capture_output=True,
        text=True,
        check=False,
    )
    assert provisioner_failure.returncode == 64
    provisioner_artifact = (
        provisioner_temp / "pdd-vitest-preflight-evidence"
        / "vitest-preflight-v1.json"
    )
    provisioner_payload = json.loads(provisioner_artifact.read_bytes())
    assert provisioner_payload["predicate"] == "runner-provisioner-command"
    assert provisioner_payload["command_exit_code"] == 64
    assert base64.b64decode(
        provisioner_payload["observation_base64"], validate=True
    ) == provisioner_output
    assert provisioner_payload["observation_sha256"] == hashlib.sha256(
        provisioner_output
    ).hexdigest()
    assert 'capture_output actual_python "python-version-command"' in provenance_body
    assert 'capture_output actual_node "node-version-command"' in provenance_body
    assert (
        'package_hash_line "vitest-package-sha256-read"' in provenance_body
    )
    assert (
        'lock_hash_line "vitest-lock-sha256-read"' in provenance_body
    )
    assert 'check_equal "runner-image-os" "ubuntu24" "${ImageOS:-}"' in (
        provenance_body
    )
    assert (
        'actual_runner_image="ubuntu-24.04/${ImageVersion}"' in provenance_body
    )
    assert "/opt/hca/hosted-compute-agent --version" in provenance_body
    assert '"runner-provisioner-command"' in provenance_body
    assert '"$provisioner_capture"' in provenance_body
    assert "observation_base64" in provenance_body
    assert "PDD_REVIEW_EVIDENCE_B64" not in upload_body
    assert "python scripts/verify_vitest_termination_evidence.py" in provenance_body
    assert "--review-only" in provenance_body
    assert workflow.index(
        'capture_output actual_python "python-version-command"'
    ) < workflow.index(provision_step)
    for protected_name in (
        "PDD_REVIEWED_FAILURE_BASELINE_SHA",
        "PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA",
        "PDD_REVIEWED_PRODUCER_SHA256",
        "PDD_REVIEWED_VERIFIER_SHA256",
        "PDD_REVIEW_EVIDENCE_B64",
        "PDD_REVIEW_EVIDENCE_SHA256",
    ):
        assert f"vars.{protected_name}" in workflow
    assert 'diagnostic_head="$PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA"' in dedicated_body
    for name in (
        "PDD_VITEST_DIAGNOSTIC_OUTPUT",
        "PDD_VITEST_FAILURE_BASELINE_SHA",
        "PDD_VITEST_PROTECTED_BASE_SHA",
        "PDD_VITEST_DIAGNOSTIC_HEAD_SHA",
        "PDD_VITEST_DIAGNOSTIC_PRODUCER_SHA256",
        "PDD_VITEST_DIAGNOSTIC_VERIFIER_SHA256",
        "PDD_VITEST_RUNNER_IMAGE",
        "PDD_VITEST_RUNNER_PROVISIONER",
        "PDD_VITEST_PYTHON_VERSION",
        "PDD_VITEST_NODE_VERSION",
        "PDD_VITEST_PACKAGE_SHA256",
        "PDD_VITEST_LOCK_SHA256",
        "PDD_VITEST_TEST_NODE",
    ):
        assert f"export {name}=" in dedicated_body
    assert "PDD_VITEST_CAUSE_RED" not in dedicated_body
    assert "cause_red_test_node" not in dedicated_body
    assert 'artifact_sha256="$(sha256sum "$artifact"' in dedicated_body
    assert '"$artifact.sha256"' in dedicated_body
    assert "python scripts/verify_vitest_termination_evidence.py" in dedicated_body
    assert "--evidence-sha256 \"$artifact_sha256\"" in dedicated_body
    assert "--review-evidence \"$PDD_REVIEW_EVIDENCE_PATH\"" in dedicated_body
    assert "--review-evidence-sha256 \"$PDD_REVIEW_EVIDENCE_SHA256\"" in dedicated_body
    assert "set +e" in dedicated_body
    assert "test_status=$?" in dedicated_body
    assert dedicated_body.rindex("exit \"$test_status\"") > dedicated_body.index(
        "python scripts/verify_vitest_termination_evidence.py"
    )
    assert dedicated_body.count(
        "pytest -q tests/test_sync_core_runner_vitest.py::"
        "test_real_vitest_runs_copied_entrypoint_without_candidate_result_access"
    ) == 1
    assert "continue-on-error" not in dedicated_body
    assert "if: always()" in upload_body
    assert "actions/upload-artifact@v4" in upload_body
    assert "pdd-vitest-termination-evidence" in upload_body
    assert "pdd-vitest-preflight-evidence" in upload_body
    assert "include-hidden-files: false" in upload_body
    assert "if-no-files-found: error" in upload_body

def test_vitest_uses_packaged_grammars_without_language_pack(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setitem(sys.modules, "tree_sitter_language_pack", None)
    javascript = runner_module._vitest_parser("javascript")
    typescript = runner_module._vitest_parser("typescript")

    assert not javascript.parse(b"const value = 1;").root_node.has_error
    assert not typescript.parse(b"const value: number = 1;").root_node.has_error


def test_vitest_binds_commonjs_alias_in_transitive_local_helper(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    helper = root / "tests/fixture.cjs"
    helper.write_text("module.exports = 'trusted';\n", encoding="utf-8")
    (root / "tests/loader.cjs").write_text(
        "const req = require; module.exports = req('./fixture.cjs');\n",
        encoding="utf-8",
    )
    (root / "tests/widget.test.ts").write_text(
        "import './loader.cjs';\nimport { test } from 'vitest';\n"
        "test('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add transitive CommonJS alias")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    before = vitest_validator_config_digest(root, "HEAD", paths)
    helper.write_text("module.exports = 'changed';\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change transitive CommonJS helper")

    assert vitest_validator_config_digest(root, "HEAD", paths) != before


def test_vitest_parser_initialization_failure_is_deterministic(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, _commit = _repository(tmp_path)
    monkeypatch.setattr(
        "pdd.sync_core.runner.importlib.metadata.version",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            runner_module.importlib.metadata.PackageNotFoundError("missing")
        ),
    )

    with pytest.raises(ValueError, match="parser is unavailable"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


def test_vitest_grammar_version_mismatch_is_deterministic(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, _commit = _repository(tmp_path)
    monkeypatch.setattr(
        "pdd.sync_core.runner.importlib.metadata.version", lambda _name: "unexpected"
    )

    with pytest.raises(ValueError, match="parser is unavailable"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


def test_vitest_rejects_nonregular_git_closure_members(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    target = tmp_path / "outside.ts"
    target.write_text("export {};\n", encoding="utf-8")
    (root / "setup.ts").symlink_to(target)
    (root / "vitest.config.json").write_text(
        '{"test":{"setupFiles":["./setup.ts"]}}', encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "symlink support")
    with pytest.raises(ValueError, match="regular|symlink"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


def test_vitest_environment_drops_protected_host_capabilities(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("PDD_ATTESTATION_SIGNER_COMMAND", "steal-me")
    monkeypatch.setenv("AWS_PROFILE", "production")
    monkeypatch.setenv("PDD_FRAMEWORK_OBSERVATION_DEVICE", "candidate-supplied")
    monkeypatch.setenv("PDD_FRAMEWORK_OBSERVATION_INODE", "candidate-supplied")
    environment = _vitest_environment(tmp_path)
    assert "PDD_ATTESTATION_SIGNER_COMMAND" not in environment
    assert "AWS_PROFILE" not in environment
    assert "PDD_FRAMEWORK_OBSERVATION_DEVICE" not in environment
    assert "PDD_FRAMEWORK_OBSERVATION_INODE" not in environment


def test_vitest_execution_uses_shared_supervisor(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, _commit = _repository(tmp_path)
    invoked = False
    observed: list[str] = []

    def supervised(command, **_kwargs):
        nonlocal invoked
        invoked = True
        observed.extend(
            part for part in command if part.startswith("--config")
        )
        return subprocess.CompletedProcess([], 1, "", ""), set()

    monkeypatch.setattr("pdd.sync_core.runner.run_supervised", supervised)
    original_run = subprocess.run

    def guarded_run(command, *args, **kwargs):
        if command and command[0] == "git":
            return original_run(command, *args, **kwargs)
        pytest.fail("Vitest bypassed shared supervision")

    monkeypatch.setattr(
        "pdd.sync_core.runner.subprocess.run",
        guarded_run,
    )
    _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        1,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )
    assert invoked
    assert observed == [
        f"--config={root / runner_module.VITEST_CONFIG_SHIM_PATH}",
        "--configLoader=runner",
    ]
    assert (root / runner_module.VITEST_CONFIG_SHIM_PATH).read_text(
        encoding="utf-8"
    ) == 'export default {"test":{}};\n'


def test_vitest_package_config_is_materialized_as_checker_shim(tmp_path: Path) -> None:
    """The supported package.json form uses the same trusted module boundary."""
    root, _commit = _repository(tmp_path)
    (root / "vitest.config.json").unlink()
    (root / "package.json").write_text(
        '{"name":"fixture","vitest":{"test":{"setupFiles":["setup.ts"]}}}',
        encoding="utf-8",
    )
    (root / "setup.ts").write_text("export {};\n", encoding="utf-8")
    _git(root, "add", "package.json", "setup.ts", "vitest.config.json")
    _git(root, "commit", "-q", "-m", "use package Vitest config")

    assert vitest_validator_config_digest(
        root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
    )
    shim = runner_module._write_vitest_config_shim(root, "HEAD")

    assert shim == root / runner_module.VITEST_CONFIG_SHIM_PATH
    assert shim.read_text(encoding="utf-8") == (
        'export default {"test":{"setupFiles":["setup.ts"]}};\n'
    )


def test_vitest_rejects_candidate_owned_checker_config_shim(tmp_path: Path) -> None:
    """A committed shim must never be mistaken for checker-owned configuration."""
    root, _commit = _repository(tmp_path)
    shim = root / runner_module.VITEST_CONFIG_SHIM_PATH
    shim.write_text("export default {};\n", encoding="utf-8")

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        1,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert "candidate-owned" in execution.detail
    assert identities == ()


def test_vitest_toolchain_descriptor_is_complete_typed_and_matches_command(
    tmp_path: Path,
) -> None:
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)

    assert descriptor.launcher.name == "node"
    assert descriptor.entrypoint == runner.resolve()
    assert descriptor.dependencies.name == "node_modules"
    assert descriptor.native_runtime[0].name == "runtime.bin"
    assert descriptor.headers.name == "node"
    assert any(member.role == "headers" for member in descriptor.members)

    wrong = tmp_path / "wrong.py"
    wrong.write_text("pass\n", encoding="utf-8")
    with pytest.raises(ValueError, match="entrypoint.*command"):
        _load_vitest_toolchain_descriptor(
            tmp_path / "repo",
            replace(config, vitest_command=(config.vitest_command[0], str(wrong))),
        )


@pytest.mark.parametrize("missing_role", [
    "launcher", "entrypoint", "dependencies", "native_runtime", "lockfile",
    "headers",
])
def test_vitest_toolchain_descriptor_rejects_missing_roles(
    tmp_path: Path, missing_role: str
) -> None:
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    payload = json.loads(config.vitest_toolchain_manifest.read_text(encoding="utf-8"))
    del payload["roles"][missing_role]
    config.vitest_toolchain_manifest.write_text(json.dumps(payload), encoding="utf-8")

    with pytest.raises(ValueError, match="roles"):
        _load_vitest_toolchain_descriptor(tmp_path / "repo", config)


def test_vitest_toolchain_headers_are_attested_and_staged_checker_owned(
    tmp_path: Path,
) -> None:
    """The C compiler receives only a copied, typed Node header closure."""
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    phase_root = tmp_path / "phase"
    phase_root.mkdir()

    phase = _prepare_vitest_toolchain(phase_root, descriptor)

    assert phase.headers != descriptor.headers
    assert phase.headers.parent == phase.controller
    assert (phase.headers / "node_api.h").read_text(encoding="utf-8") == (
        descriptor.headers / "node_api.h"
    ).read_text(encoding="utf-8")
    assert {path.name for path in phase.headers.iterdir()} == set(
        _REQUIRED_NAPI_HEADERS
    )
    assert {member.relative_path.as_posix() for member in phase.header_members} == {
        ".", *_REQUIRED_NAPI_HEADERS,
    }
    assert not phase.headers.is_symlink()
    assert all(not path.is_symlink() for path in phase.headers.rglob("*"))
    assert all(
        stat.S_IMODE(path.lstat().st_mode) == (0o555 if path.is_dir() else 0o444)
        for path in (phase.headers, *phase.headers.rglob("*"))
    )


def test_vitest_toolchain_hardens_only_required_group_writable_headers_in_staging(
    tmp_path: Path,
) -> None:
    """External Node package modes do not weaken checker-owned staged input."""
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    source_headers = tmp_path / "trusted-toolchain/include/node"
    source_headers.chmod(0o775)
    for header in source_headers.iterdir():
        header.chmod(0o664)
    nested = source_headers / "nested"
    nested.mkdir(mode=0o775)
    (nested / "extra.h").write_text("#define EXTRA_HEADER 1\n", encoding="utf-8")
    (nested / "extra.h").chmod(0o664)
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    phase_root = tmp_path / "phase"
    phase_root.mkdir()

    phase = _prepare_vitest_toolchain(phase_root, descriptor)

    assert stat.S_IMODE((descriptor.headers / "node_api.h").lstat().st_mode) == 0o664
    assert {path.name for path in phase.headers.iterdir()} == set(
        _REQUIRED_NAPI_HEADERS
    )
    assert not (phase.headers / "nested").exists()
    assert all(
        stat.S_IMODE(path.lstat().st_mode) == (0o555 if path.is_dir() else 0o444)
        for path in (phase.headers, *phase.headers.rglob("*"))
    )
    assert all(
        path.lstat().st_uid == os.getuid()
        for path in (phase.headers, *phase.headers.rglob("*"))
    )


@pytest.mark.parametrize("mutation", ("mode", "owner", "ancestor", "link", "extra"))
def test_vitest_toolchain_rejects_staged_header_tampering(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mutation: str,
) -> None:
    """Post-stage header substitution cannot survive the pre-execution recheck."""
    runner = _fake_vitest(tmp_path)
    descriptor = _load_vitest_toolchain_descriptor(
        tmp_path / "repo", _runner_config(tmp_path, runner)
    )
    phase_root = tmp_path / "phase"
    phase_root.mkdir()
    phase = _prepare_vitest_toolchain(phase_root, descriptor)
    header = phase.headers / "node_api.h"
    if mutation == "mode":
        header.chmod(0o644)
    elif mutation == "owner":
        actual_owner = os.getuid()
        monkeypatch.setattr(runner_module.os, "getuid", lambda: actual_owner + 1)
    elif mutation == "ancestor":
        phase.controller.chmod(0o720)
    elif mutation == "link":
        replacement = tmp_path / "replacement.h"
        replacement.write_text("#define PDD_INJECTED 1\n", encoding="utf-8")
        phase.headers.chmod(0o755)
        header.unlink()
        header.symlink_to(replacement)
    else:
        phase.headers.chmod(0o755)
        added = phase.headers / "pdd-added.h"
        added.write_text("#define PDD_ADDED 1\n", encoding="utf-8")
        added.chmod(0o444)
        phase.headers.chmod(0o555)

    with pytest.raises(ValueError, match="header|Vitest.*identity|provenance"):
        runner_module._verify_vitest_phase_toolchain(phase)


# pylint: disable=protected-access
@pytest.mark.skipif(sys.platform != "darwin", reason="uses the macOS /var resolver alias")
def test_vitest_staged_headers_accept_only_the_system_resolver_alias(
    tmp_path: Path,
) -> None:
    """A system resolver alias is valid only for the recorded controller inode."""
    canonical_root = tmp_path.resolve()
    private_root = Path("/private/var")
    if not canonical_root.is_relative_to(private_root):
        pytest.skip("pytest temporary directory is not behind the macOS /var alias")
    phase_root = canonical_root / "phase"
    runner = _fake_vitest(tmp_path)
    descriptor = _load_vitest_toolchain_descriptor(
        tmp_path / "repo", _runner_config(tmp_path, runner)
    )
    phase_root.mkdir()
    resolver_root = Path("/var") / phase_root.relative_to(private_root)
    phase = _prepare_vitest_toolchain(resolver_root, descriptor)
    resolver_controller = resolver_root / ".pdd-vitest-toolchain"
    resolver_headers = resolver_controller / "headers"

    assert resolver_headers != phase.headers
    assert resolver_headers.resolve() == phase.headers.resolve()
    assert resolver_controller.resolve() == phase.controller.resolve()
    runner_module._verify_staged_vitest_header_attestation(
        resolver_headers,
        resolver_controller,
        phase.header_members,
        phase.header_provenance,
        phase.header_ancestors,
    )


# pylint: enable=protected-access
# pylint: disable=too-many-locals,protected-access
def test_vitest_coordinator_precompile_requires_phase_bound_header_attestation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Only an immutable, exact phase header attestation may reach the compiler.

    The public compiler boundary has one secure model: a caller supplies the
    staged header directory with its phase record.  An otherwise valid external
    Node include directory is deliberately insufficient, so no legacy bare
    ``headers`` fallback can reintroduce an unbound compiler input.
    """
    monkeypatch.setattr(runner_module.sys, "platform", "linux")
    monkeypatch.setattr(runner_module, "released_runtime_closure_paths", lambda: ())
    runner = _fake_vitest(tmp_path)
    descriptor = _load_vitest_toolchain_descriptor(
        tmp_path / "repo", _runner_config(tmp_path, runner)
    )
    compiler = tmp_path / "trusted-cc"
    compiler.write_text("checker compiler\n", encoding="utf-8")
    compiler.chmod(0o555)
    compiler_commands: list[tuple[str, ...]] = []

    def compile_checker(command, **_kwargs):
        compiler_commands.append(tuple(command))
        output = Path(command[command.index("-o") + 1])
        output.write_bytes(b"checker authority")
        return subprocess.CompletedProcess(command, 0, b"", b"")

    monkeypatch.setattr(runner_module, "_checker_c_compiler", lambda: compiler)
    monkeypatch.setattr(
        runner_module, "_checker_compiler_closure", _test_compiler_closure
    )
    monkeypatch.setattr(runner_module.subprocess, "run", compile_checker)

    unbound_staging = tmp_path / "unbound-addon"
    unbound_staging.mkdir()
    with pytest.raises(ValueError, match="phase.*header.*attestation"):
        runner_module._load_vitest_coordinator_addon(
            unbound_staging, descriptor.headers, tmp_path / "candidate"
        )
    assert not compiler_commands

    phase_root = tmp_path / "phase"
    phase_root.mkdir()
    phase = _prepare_vitest_toolchain(phase_root, descriptor)
    candidate_headers = tmp_path / "candidate-headers"
    candidate_headers.symlink_to(phase.headers, target_is_directory=True)
    rejected_staging = tmp_path / "rejected-addon"
    rejected_staging.mkdir()
    with pytest.raises(ValueError, match="phase.*header.*attestation"):
        runner_module._load_vitest_coordinator_addon(
            rejected_staging,
            candidate_headers,
            phase_root,
            phase_toolchain=phase,
        )
    assert not compiler_commands

    bound_staging = tmp_path / "bound-addon"
    bound_staging.mkdir()
    addon = runner_module._load_vitest_coordinator_addon(
        bound_staging,
        phase.headers,
        phase_root,
        phase_toolchain=phase,
    )

    assert addon.staged_path.is_file()
    assert len(compiler_commands) == 1
    assert compiler_commands[0][compiler_commands[0].index("-I") + 1] == str(
        phase.headers
    )


def test_vitest_coordinator_precompile_rejects_candidate_header_aliases(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A candidate-controlled intermediate alias cannot select compiler input."""
    monkeypatch.setattr(runner_module.sys, "platform", "linux")
    monkeypatch.setattr(runner_module, "released_runtime_closure_paths", lambda: ())
    runner = _fake_vitest(tmp_path)
    descriptor = _load_vitest_toolchain_descriptor(
        tmp_path / "repo", _runner_config(tmp_path, runner)
    )
    phase_root = tmp_path / "phase"
    phase_root.mkdir()
    phase = _prepare_vitest_toolchain(phase_root, descriptor)
    compiler = tmp_path / "trusted-cc"
    compiler.write_text("checker compiler\n", encoding="utf-8")
    compiler.chmod(0o555)
    compiler_commands: list[tuple[str, ...]] = []

    def compile_checker(command, **_kwargs):
        compiler_commands.append(tuple(command))
        output = Path(command[command.index("-o") + 1])
        output.write_bytes(b"checker authority")
        return subprocess.CompletedProcess(command, 0, b"", b"")

    candidate_alias = tmp_path / "candidate-alias"
    candidate_alias.symlink_to(phase_root, target_is_directory=True)
    aliased_headers = candidate_alias / ".pdd-vitest-toolchain" / "headers"
    assert aliased_headers.resolve() == phase.headers.resolve()
    staging = tmp_path / "alias-addon"
    staging.mkdir()
    monkeypatch.setattr(runner_module, "_checker_c_compiler", lambda: compiler)
    monkeypatch.setattr(
        runner_module, "_checker_compiler_closure", _test_compiler_closure
    )
    monkeypatch.setattr(runner_module.subprocess, "run", compile_checker)

    with pytest.raises(ValueError, match="phase.*header.*attestation"):
        runner_module._load_vitest_coordinator_addon(
            staging,
            aliased_headers,
            phase_root,
            phase_toolchain=phase,
        )

    assert not compiler_commands


# pylint: enable=too-many-locals,protected-access
# pylint: disable=too-many-locals,protected-access
def test_vitest_coordinator_precompile_rechecks_phase_attestation_without_rehash(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Precompile checks the staged phase identity without rereading its bytes.

    The checker must carry the private phase attestation from staging to the
    compiler boundary. It may make a fresh no-follow structural pass there,
    but must not turn the four already-attested header bytes into another
    content-hash operation.
    """
    monkeypatch.setattr(runner_module.sys, "platform", "linux")
    monkeypatch.setattr(runner_module, "released_runtime_closure_paths", lambda: ())
    runner = _fake_vitest(tmp_path)
    descriptor = _load_vitest_toolchain_descriptor(
        tmp_path / "repo", _runner_config(tmp_path, runner)
    )
    compiler = tmp_path / "trusted-cc"
    compiler.write_text("checker compiler\n", encoding="utf-8")
    compiler.chmod(0o555)
    staged_headers: Path | None = None
    compiler_commands: list[tuple[str, ...]] = []
    capture_headers = runner_module._capture_vitest_headers

    def reject_redundant_staged_header_capture(headers: Path):
        if headers == staged_headers:
            pytest.fail("precompile rehashed the already-attested staged headers")
        return capture_headers(headers)

    def compile_checker(command, **_kwargs):
        compiler_commands.append(tuple(command))
        output = Path(command[command.index("-o") + 1])
        output.write_bytes(b"checker authority")
        return subprocess.CompletedProcess(command, 0, b"", b"")

    monkeypatch.setattr(runner_module, "_checker_c_compiler", lambda: compiler)
    monkeypatch.setattr(
        runner_module, "_checker_compiler_closure", _test_compiler_closure
    )
    monkeypatch.setattr(
        runner_module,
        "_capture_vitest_headers",
        reject_redundant_staged_header_capture,
    )
    monkeypatch.setattr(runner_module.subprocess, "run", compile_checker)

    mutations = (
        "baseline", "added", "deleted", "mode", "owner", "ancestor",
        "symlink", "inode",
    )
    for mutation in mutations:
        phase_root = tmp_path / f"phase-{mutation}"
        phase_root.mkdir()
        phase = _prepare_vitest_toolchain(phase_root, descriptor)
        staged_headers = phase.headers
        assert {member.relative_path.as_posix() for member in phase.header_members} == {
            ".", *_REQUIRED_NAPI_HEADERS,
        }
        staging = tmp_path / f"addon-{mutation}"
        staging.mkdir()
        compiler_calls_before = len(compiler_commands)
        header = phase.headers / "node_api.h"

        with monkeypatch.context():
            if mutation == "added":
                phase.headers.chmod(0o755)
                added = phase.headers / "pdd-injected.h"
                added.write_text("#define PDD_INJECTED 1\n", encoding="utf-8")
                added.chmod(0o444)
                phase.headers.chmod(0o555)
            elif mutation == "deleted":
                phase.headers.chmod(0o755)
                header.unlink()
                phase.headers.chmod(0o555)
            elif mutation == "mode":
                header.chmod(0o644)
            elif mutation == "owner":
                provenance = phase.header_provenance[0]
                phase = replace(
                    phase,
                    header_provenance=(
                        replace(provenance, owner=provenance.owner + 1),
                        *phase.header_provenance[1:],
                    ),
                )
            elif mutation == "ancestor":
                phase.controller.chmod(0o720)
            elif mutation == "symlink":
                replacement = tmp_path / "replacement.h"
                replacement.write_text("#define PDD_INJECTED 1\n", encoding="utf-8")
                phase.headers.chmod(0o755)
                header.unlink()
                header.symlink_to(replacement)
                phase.headers.chmod(0o555)
            elif mutation == "inode":
                original = header.read_bytes()
                original_inode = header.stat().st_ino
                phase.headers.chmod(0o755)
                replacement = phase.headers / "node_api.replacement"
                replacement.write_bytes(original)
                replacement.chmod(0o444)
                replacement_inode = replacement.stat().st_ino
                assert replacement_inode != original_inode
                os.replace(replacement, header)
                assert header.stat().st_ino == replacement_inode
                phase.headers.chmod(0o555)

            if mutation == "baseline":
                addon = runner_module._load_vitest_coordinator_addon(
                    staging,
                    phase.headers,
                    phase_root,
                    phase_toolchain=phase,
                )
                assert addon.staged_path.is_file()
                assert len(compiler_commands) == compiler_calls_before + 1
            else:
                with pytest.raises(ValueError):
                    runner_module._load_vitest_coordinator_addon(
                        staging,
                        phase.headers,
                        phase_root,
                        phase_toolchain=phase,
                    )
                assert len(compiler_commands) == compiler_calls_before


# pylint: enable=too-many-locals,protected-access
def test_vitest_execution_rechecks_minimal_staged_headers_without_generic_root_rehash(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Use the complete phase checks, not duplicate root hashing, for headers.

    The checker attests only the N-API files included by its C source. The
    phase verifier captures those files before and after execution, including
    bytes, type, mode, ownership, and controller ancestry. The generic
    protected-root digest must not traverse that independently checked scope.
    """
    root, _commit = _repository(tmp_path)
    config = _runner_config(tmp_path, _fake_vitest(tmp_path))
    descriptor = _load_vitest_toolchain_descriptor(root, config)
    unrelated_header = descriptor.headers / "nested" / "generated.h"
    unrelated_header.parent.mkdir()
    unrelated_header.write_text(
        "#define PDD_HEADER_WALK_REGRESSION 1\n", encoding="utf-8"
    )
    # A normal Node distribution has a much larger unrelated header tree.
    descriptor = _load_vitest_toolchain_descriptor(root, config)
    unrelated_header.write_text(
        "#define PDD_HEADER_WALK_REGRESSION 2\n", encoding="utf-8"
    )
    assert _load_vitest_toolchain_descriptor(root, config).identity == descriptor.identity
    phase = _prepare_vitest_toolchain(root, descriptor)
    assert not (phase.headers / "nested").exists()
    assert {member.relative_path.as_posix() for member in phase.header_members} == {
        ".", *_REQUIRED_NAPI_HEADERS,
    }

    staged_phase_checks: list[Path] = []
    generic_header_paths: list[Path] = []
    originals = (
        getattr(runner_module, "_capture_staged_vitest_headers"),
        getattr(runner_module, "_update_validator_path_identity"),
    )

    def capture_phase_check(headers: Path, controller: Path):
        staged_phase_checks.append(headers)
        return originals[0](headers, controller)

    def capture_generic_header_rehash(
        digest,
        path: Path,
        logical: str,
        active: set[Path],
        excluded: frozenset[Path],
    ) -> None:
        if (
            path.absolute() not in excluded
            and (path == phase.headers or path.is_relative_to(phase.headers))
        ):
            generic_header_paths.append(path)
        originals[1](digest, path, logical, active, excluded)

    monkeypatch.setattr(
        runner_module, "_capture_staged_vitest_headers", capture_phase_check
    )
    monkeypatch.setattr(
        runner_module, "_update_validator_path_identity", capture_generic_header_rehash
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        2,
        config,
        phase_toolchain=phase,
    )

    assert execution.outcome is EvidenceOutcome.PASS
    assert identities == (IDENTITY,)
    # Exact no-follow N-API capture still protects both execution boundaries.
    assert staged_phase_checks.count(phase.headers) >= 2
    # The generic root digest is not allowed to rehash checker-owned headers.
    assert not generic_header_paths


@pytest.mark.parametrize("mutation", ("missing", "symlink"))
@pytest.mark.parametrize("header_name", _REQUIRED_NAPI_HEADERS)
def test_vitest_toolchain_requires_each_regular_napi_header(
    tmp_path: Path, mutation: str, header_name: str,
) -> None:
    """Every compiler-input header is an exact no-link required member."""
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    header = tmp_path / "trusted-toolchain/include/node" / header_name
    if mutation == "missing":
        header.unlink()
    else:
        replacement = tmp_path / f"replacement-{header_name}"
        replacement.write_text("#define PDD_INJECTED 1\n", encoding="utf-8")
        header.unlink()
        header.symlink_to(replacement)

    with pytest.raises(ValueError, match=header_name):
        _load_vitest_toolchain_descriptor(tmp_path / "repo", config)


def test_vitest_toolchain_rejects_manifest_injected_header_path(tmp_path: Path) -> None:
    """The candidate-facing manifest cannot select compiler include input."""
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    payload = json.loads(config.vitest_toolchain_manifest.read_text(encoding="utf-8"))
    injected = tmp_path / "injected-headers"
    injected.mkdir()
    payload["roles"]["headers"] = str(injected)
    config.vitest_toolchain_manifest.write_text(json.dumps(payload), encoding="utf-8")

    with pytest.raises(ValueError, match="headers.*selected Node launcher"):
        _load_vitest_toolchain_descriptor(tmp_path / "repo", config)


@pytest.mark.parametrize("mutation", ("header-bytes", "header-symlink", "ancestor-mode"))
def test_vitest_toolchain_headers_fail_closed_when_provenance_changes(
    tmp_path: Path, mutation: str,
) -> None:
    """A candidate cannot route checker C compilation through mutable headers."""
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    header = descriptor.headers / "node_api.h"
    if mutation == "header-bytes":
        header.write_text("#define PDD_INJECTED 1\n", encoding="utf-8")
    elif mutation == "header-symlink":
        replacement = tmp_path / "replacement.h"
        replacement.write_text("#define PDD_INJECTED 1\n", encoding="utf-8")
        header.unlink()
        header.symlink_to(replacement)
    else:
        descriptor.headers.chmod(0o775)
    phase_root = tmp_path / "phase"
    phase_root.mkdir()

    with pytest.raises(ValueError, match="header|Vitest.*identity|provenance"):
        _prepare_vitest_toolchain(phase_root, descriptor)


def test_vitest_toolchain_identity_binds_all_roles_modes_symlinks_and_ignores_cache(
    tmp_path: Path,
) -> None:
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    baseline = descriptor.identity

    launcher = descriptor.launcher
    launcher.write_bytes(launcher.read_bytes() + b"changed")
    assert _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity != baseline
    launcher.write_bytes(launcher.read_bytes().removesuffix(b"changed"))
    baseline = _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity

    runner.write_text(runner.read_text(encoding="utf-8") + "\n# changed\n", encoding="utf-8")
    assert _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity != baseline
    runner.write_text(runner.read_text(encoding="utf-8").removesuffix("\n# changed\n"), encoding="utf-8")
    baseline = _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity

    native = descriptor.native_runtime[0]
    native.write_bytes(b"changed-native")
    assert _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity != baseline
    native.write_bytes(b"native")
    baseline = _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity

    header = descriptor.headers / "node_api.h"
    header.write_text("#define PDD_CHANGED 1\n", encoding="utf-8")
    assert _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity != baseline
    header.write_text("#include <js_native_api.h>\n", encoding="utf-8")
    baseline = _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity

    descriptor.lockfile.write_text('{"changed":true}\n', encoding="utf-8")
    assert _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity != baseline
    descriptor.lockfile.write_text("{}\n", encoding="utf-8")

    dependency = descriptor.dependencies / "vitest/dependency.js"
    dependency.write_text("export default 1;\n", encoding="utf-8")
    dependency.chmod(0o600)
    mode_identity = _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity
    dependency.chmod(0o644)
    assert _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity != mode_identity

    target = descriptor.dependencies / "linked-target"
    target.mkdir()
    (target / "native.bin").write_bytes(b"one")
    link = descriptor.dependencies / "linked-native"
    link.symlink_to("linked-target", target_is_directory=True)
    linked_identity = _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity
    (target / "native.bin").write_bytes(b"two")
    assert _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity != linked_identity

    cache = descriptor.dependencies / ".vite"
    cache.mkdir()
    before_cache = _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity
    (cache / "mutable.json").write_text("changed", encoding="utf-8")
    assert _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity == before_cache


def test_vitest_toolchain_identity_is_stable_after_relocation(tmp_path: Path) -> None:
    first = tmp_path / "first"
    second = tmp_path / "second"
    runner = _fake_vitest(first)
    first_config = _runner_config(first, runner)
    shutil.copytree(first / "trusted-toolchain", second / "trusted-toolchain")
    relocated_runner = second / "trusted-toolchain/node_modules/vitest/fake_vitest.py"
    second_config = _runner_config(second, relocated_runner)

    assert _load_vitest_toolchain_descriptor(
        tmp_path / "repo", first_config
    ).identity == _load_vitest_toolchain_descriptor(
        tmp_path / "repo", second_config
    ).identity


def test_validator_tree_identity_is_uniquely_mode_and_symlink_sensitive(
    tmp_path: Path,
) -> None:
    root = tmp_path / "tree"
    root.mkdir()
    file_path = root / "file"
    file_path.write_bytes(b"content")
    first = _validator_tree_identity(root)
    file_path.chmod(0o600)
    assert _validator_tree_identity(root) != first


def test_vitest_toolchain_entrypoint_is_copied_into_phase_tree(
    tmp_path: Path,
) -> None:
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    phase_root = tmp_path / "phase"
    phase_root.mkdir()

    phase = _prepare_vitest_toolchain(phase_root, descriptor)

    assert phase.entrypoint != descriptor.entrypoint
    assert phase.entrypoint.read_bytes() == descriptor.entrypoint.read_bytes()
    assert (phase_root / "node_modules/.vite-temp").is_dir()
    assert (phase_root / "node_modules/.vite").is_dir()


def test_vitest_phase_native_runtime_proof_is_bound_to_descriptor(
    tmp_path: Path,
) -> None:
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    phase_root = tmp_path / "phase"
    phase_root.mkdir()

    phase = _prepare_vitest_toolchain(phase_root, descriptor)

    member = next(
        item for item in descriptor.members if item.role == "native_runtime"
    )
    proof = phase.immutable_binding_proofs[0]
    assert proof.copied_source == phase.native_runtime[0]
    assert proof.protected_source == descriptor.native_runtime[0]
    assert proof.destination == descriptor.native_runtime[0]
    assert proof.descriptor_identity == descriptor.identity
    assert proof.member_role == "native_runtime"
    assert proof.member_path == "0"
    assert proof.collision_category == "vitest_inferred_runtime"
    attestation = json.loads(proof.descriptor_attestation)
    attested_member = next(
        item for item in attestation["members"]
        if item["role"] == "native_runtime" and item["path"] == "0"
    )
    assert attested_member["digest"] == member.content_digest
    assert attested_member["mode"] == member.mode
    assert set(attestation) == {
        "adapter", "launch_policy", "members", "native_runtime", "schema"
    }
    assert attestation["native_runtime"] == [str(descriptor.native_runtime[0])]


def test_vitest_phase_does_not_replace_supervisor_owned_native_runtime(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A released runtime destination must retain one supervisor authority."""
    monkeypatch.setattr(runner_module.sys, "platform", "linux")
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    protected_runtime = descriptor.native_runtime[0]
    monkeypatch.setattr(
        runner_module,
        "released_runtime_closure_paths",
        lambda: (("native/dynamic-loader", protected_runtime),),
    )
    phase_root = tmp_path / "phase"
    phase_root.mkdir()

    phase = _prepare_vitest_toolchain(phase_root, descriptor)

    assert phase.native_runtime[0].read_bytes() == protected_runtime.read_bytes()
    assert phase.readable_bindings == ()
    assert phase.immutable_binding_proofs == ()


def test_vitest_rejects_phase_with_mismatched_native_runtime_proof(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, _commit = _repository(tmp_path)
    config = _runner_config(tmp_path, _fake_vitest(tmp_path))
    descriptor = _load_vitest_toolchain_descriptor(root, config)
    phase = _prepare_vitest_toolchain(root, descriptor)
    phase = replace(
        phase,
        immutable_binding_proofs=(replace(
            phase.immutable_binding_proofs[0], descriptor_identity="0" * 64,
        ),),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: pytest.fail("mismatched proof reached execution"),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        2,
        config,
        phase_toolchain=phase,
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert "proof mismatch" in execution.detail
    assert not identities


def test_vitest_phase_rejects_dependency_mutated_during_copy(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    dependency = descriptor.dependencies / "vitest/dependency.js"
    dependency.write_text("module.exports = 'trusted';\n", encoding="utf-8")
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    phase_root = tmp_path / "phase"
    phase_root.mkdir()

    def corrupt_copy(source: Path, destination: Path) -> None:
        _copy_vitest_dependencies(source, destination)
        (destination / "vitest/dependency.js").write_text(
            "module.exports = 'attacker';\n", encoding="utf-8"
        )

    monkeypatch.setattr(
        "pdd.sync_core.runner._copy_vitest_dependencies", corrupt_copy
    )
    with pytest.raises(ValueError, match="identity|member|copied"):
        _prepare_vitest_toolchain(phase_root, descriptor)


def test_vitest_phase_rejects_source_mutated_after_descriptor_capture(
    tmp_path: Path,
) -> None:
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    dependency = runner.parent / "dependency.js"
    dependency.write_text("module.exports = 'trusted';\n", encoding="utf-8")
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    dependency.write_text("module.exports = 'attacker';\n", encoding="utf-8")
    phase_root = tmp_path / "phase"
    phase_root.mkdir()

    with pytest.raises(ValueError, match="identity|changed|member"):
        _prepare_vitest_toolchain(phase_root, descriptor)


@pytest.mark.parametrize(
    "mutation",
    [
        "dependency-bytes",
        "dependency-mode",
        "dependency-symlink",
        "dependency-missing",
        "dependency-extra",
        "launcher-bytes",
        "lockfile-bytes",
        "native-bytes",
    ],
)
def test_vitest_rechecks_exact_staged_descriptor_before_execution(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    mutation: str,
) -> None:
    root, _commit = _repository(tmp_path)
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    dependency = runner.parent / "dependency.js"
    dependency.write_text("module.exports = 'trusted';\n", encoding="utf-8")
    descriptor = _load_vitest_toolchain_descriptor(root, config)
    phase = _prepare_vitest_toolchain(root, descriptor)
    copied_dependency = phase.entrypoint.parent / "dependency.js"
    if mutation == "dependency-bytes":
        copied_dependency.write_text("attacker\n", encoding="utf-8")
    elif mutation == "dependency-mode":
        copied_dependency.chmod(0o600)
    elif mutation == "dependency-symlink":
        copied_dependency.unlink()
        copied_dependency.symlink_to(tmp_path / "outside")
    elif mutation == "dependency-missing":
        copied_dependency.unlink()
    elif mutation == "dependency-extra":
        (phase.entrypoint.parent / "extra.js").write_text("attacker\n", encoding="utf-8")
    elif mutation == "launcher-bytes":
        phase.launcher.write_bytes(b"attacker")
    elif mutation == "lockfile-bytes":
        phase.lockfile.write_bytes(b"attacker")
    else:
        phase.native_runtime[0].write_bytes(b"attacker")

    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: pytest.fail("mutated phase reached execution"),
    )
    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        2,
        config,
        phase_toolchain=phase,
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert "identity" in execution.detail.lower() or "member" in execution.detail.lower()
    assert not identities


@pytest.mark.parametrize("mutation", ("changed", "deleted", "added"))
def test_vitest_postrun_staged_header_mutation_fails_phase_recheck(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    mutation: str,
) -> None:
    """Header-tree exclusion from generic hashing still fails closed post-run."""
    root, _commit = _repository(tmp_path)
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    descriptor = _load_vitest_toolchain_descriptor(root, config)
    phase = _prepare_vitest_toolchain(root, descriptor)
    header = phase.headers / "node_api.h"

    def mutate_after_run(command, *, result_write_fd, **_kwargs):
        if mutation == "changed":
            header.chmod(0o644)
            header.write_text("#define PDD_CHANGED 1\n", encoding="utf-8")
            header.chmod(0o444)
        elif mutation == "deleted":
            phase.headers.chmod(0o755)
            header.unlink()
            phase.headers.chmod(0o555)
        else:
            phase.headers.chmod(0o755)
            added = phase.headers / "pdd-added.h"
            added.write_text("#define PDD_ADDED 1\n", encoding="utf-8")
            added.chmod(0o444)
            phase.headers.chmod(0o555)
        os.write(
            result_write_fd,
            json.dumps({"tests": [{"identity": IDENTITY, "status": "passed"}]}).encode(),
        )
        return subprocess.CompletedProcess(command, 0, "", ""), False

    monkeypatch.setattr("pdd.sync_core.runner.run_supervised", mutate_after_run)
    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        2,
        config,
        phase_toolchain=phase,
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert execution.detail.startswith("Vitest toolchain recheck failed:")
    assert not identities


def test_vitest_postrun_candidate_mutation_stays_quarantined(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The header-only exemption cannot hide a candidate-tree modification."""
    root, _commit = _repository(tmp_path)
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    descriptor = _load_vitest_toolchain_descriptor(root, config)
    phase = _prepare_vitest_toolchain(root, descriptor)

    def mutate_after_run(command, *, result_write_fd, **_kwargs):
        (root / "tests/widget.test.ts").write_text("// replaced\n", encoding="utf-8")
        os.write(
            result_write_fd,
            json.dumps({"tests": [{"identity": IDENTITY, "status": "passed"}]}).encode(),
        )
        return subprocess.CompletedProcess(command, 0, "", ""), False

    monkeypatch.setattr("pdd.sync_core.runner.run_supervised", mutate_after_run)
    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        2,
        config,
        phase_toolchain=phase,
    )

    assert execution.outcome is EvidenceOutcome.QUARANTINED
    assert execution.detail == "Vitest phase modified its protected execution tree"
    assert not identities


def test_vitest_result_channel_is_not_disclosed_to_candidate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, commit = _repository(tmp_path, mode="forge")
    observed: list[dict[str, object]] = []

    def inspect(command, **kwargs):
        observed.append({"command": command, **kwargs})
        return _controlled_run(command, **kwargs)

    monkeypatch.setattr("pdd.sync_core.runner.run_supervised", inspect)
    _envelope, executions = _run(root, commit, commit, _fake_vitest(tmp_path))

    assert executions[0].outcome is EvidenceOutcome.FAIL
    assert observed
    for call in observed:
        assert "PDD_TRUSTED_VITEST_OUTPUT" not in call["env"]
        assert "--outputFile" not in " ".join(call["command"])
        assert isinstance(call["result_write_fd"], int)
        assert "result_fifo" not in call
        assert "/run/pdd-framework-observation" not in " ".join(call["command"])


def test_vitest_phase_tree_mutation_cannot_pass(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    runner = tmp_path / "mutating_vitest.py"
    runner.write_text(
        "import json, os, pathlib\n"
        "root = pathlib.Path.cwd()\n"
        "(root / 'tests/widget.test.ts').write_text('// replaced')\n"
        "pathlib.Path(os.environ['PDD_TRUSTED_VITEST_OUTPUT']).write_text("
        "json.dumps({'tests':[{'identity':'tests/widget.test.ts::widget works','status':'passed'}]}))\n",
        encoding="utf-8",
    )
    _envelope, executions = _run(root, commit, commit, runner)
    assert executions[0].outcome is not EvidenceOutcome.PASS


@pytest.mark.parametrize("payload", [[], {"tests": [None]}, {"testResults": None}])
def test_vitest_malformed_json_shapes_fail_closed(tmp_path: Path, payload: object) -> None:
    output = tmp_path / "results.json"
    output.write_text(json.dumps(payload), encoding="utf-8")
    outcome, _detail, identities = _vitest_result(tmp_path, output, 0, None)
    assert outcome is EvidenceOutcome.COLLECTION_ERROR
    assert identities == ()


def test_vitest_missing_launcher_is_normalized(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        1,
        RunnerConfig(vitest_command=(str(tmp_path / "missing-node"),)),
    )
    assert execution.outcome is EvidenceOutcome.ERROR
    assert identities == ()


@pytest.mark.parametrize("failure", ["setup-oserror", "setup-valueerror"])
def test_vitest_phase_setup_failures_are_normalized(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    failure: str,
) -> None:
    root, commit = _repository(tmp_path)
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)

    def fail_setup(*_args, **_kwargs):
        if failure == "setup-oserror":
            raise OSError("copy denied")
        raise ValueError("malformed descriptor")

    monkeypatch.setattr("pdd.sync_core.runner._prepare_vitest_toolchain", fail_setup)
    execution, identities = _collect_vitest_at_base(
        root,
        commit,
        (PurePosixPath("tests/widget.test.ts"),),
        config,
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert "setup" in execution.detail.lower()
    assert not identities


def test_vitest_post_phase_toolchain_deletion_is_normalized(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, _commit = _repository(tmp_path)
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    original = _load_vitest_toolchain_descriptor
    calls = 0

    def disappear(*args, **kwargs):
        nonlocal calls
        calls += 1
        if calls > 1:
            raise OSError("toolchain disappeared")
        return original(*args, **kwargs)

    monkeypatch.setattr(
        "pdd.sync_core.runner._load_vitest_toolchain_descriptor", disappear
    )
    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        2,
        config,
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert "toolchain" in execution.detail.lower()
    assert not identities


def test_profile_does_not_execute_after_failed_initial_vitest_capture(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, commit = _repository(tmp_path)
    config = _runner_config(tmp_path, _fake_vitest(tmp_path))
    paths = (PurePosixPath("tests/widget.test.ts"),)
    obligation = VerificationObligation(
        "vitest", "test", "vitest",
        vitest_validator_config_digest(root, commit, paths),
        ("REQ-1",), paths,
    )
    profile = VerificationProfile(UNIT, (obligation,), ("REQ-1",), "profile-v1")
    original = _load_vitest_toolchain_descriptor
    calls = 0

    def fail_once(*args, **kwargs):
        nonlocal calls
        calls += 1
        if calls == 1:
            raise OSError("capture race")
        return original(*args, **kwargs)

    monkeypatch.setattr(
        "pdd.sync_core.runner._load_vitest_toolchain_descriptor", fail_once
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_obligation",
        lambda *_args, **_kwargs: pytest.fail("Vitest ran after failed capture"),
    )

    envelope, executions = run_profile(
        root,
        profile,
        RunBinding("snapshot-v1", commit, commit),
        AttestationIssue(
            AttestationSigner("trusted-ci", b"v" * 32),
            "id", "nonce", datetime(2026, 7, 13, tzinfo=timezone.utc),
        ),
        config,
    )

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "initial capture failed" in executions[0].detail
    assert envelope.binding.vitest_toolchain_identity is None
    assert calls == 1


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()


def _fake_vitest(tmp_path: Path) -> Path:
    runner = tmp_path / "trusted-toolchain/node_modules/vitest/fake_vitest.py"
    runner.parent.mkdir(parents=True, exist_ok=True)
    runner.write_text(
        "import json, os, pathlib, re, sys, time\n"
        "root = pathlib.Path.cwd()\n"
        "mode = (root / 'source.ts').read_text().strip()\n"
        "if mode == 'timeout': time.sleep(5)\n"
        "reporter_arg = next(x for x in sys.argv if x.startswith('--reporter='))\n"
        "reporter = pathlib.Path(reporter_arg.split('=', 1)[1]).read_text()\n"
        "fd = int(re.search(r'RESULT_FD = (\\d+)', reporter).group(1))\n"
        "if mode == 'forge':\n"
        "  forged = os.environ.get('PDD_TRUSTED_VITEST_OUTPUT')\n"
        "  if forged: pathlib.Path(forged).write_text(json.dumps({'tests':[{'identity':'forged','status':'passed'}]}))\n"
        "if mode == 'malformed': os.write(fd, b'{')\n"
        "else:\n"
        "  tests = [] if mode == 'zero' else [{'identity': 'tests/widget.test.ts::widget works', 'status': {'fail': 'failed', 'skip': 'skipped', 'todo': 'todo'}.get(mode, 'passed'), 'failureMessages': []}]\n"
        "  if mode == 'forge': tests[0]['status'] = 'failed'\n"
        "  if mode == 'mismatch': tests = [{'identity': 'tests/widget.test.ts::other', 'status': 'passed', 'failureMessages': []}]\n"
        "  if mode == 'candidate': tests.append({'identity': 'tests/widget.test.ts::candidate only', 'status': 'passed', 'failureMessages': []})\n"
        "  os.write(fd, json.dumps({'tests': tests, 'moduleErrors': 0, 'unhandledErrors': 0}).encode())\n",
        encoding="utf-8",
    )
    return runner


def _toolchain_manifest(
    tmp_path: Path, entrypoint: Path, *, linux_wasm_guard: bool | None = None,
) -> Path:
    """Build a strict, platform-specific stand-in for the trusted Node launcher."""
    toolchain = tmp_path / "trusted-toolchain"
    native = toolchain / "native"
    native.mkdir(parents=True, exist_ok=True)
    native_file = native / "runtime.bin"
    native_file.write_bytes(b"native")
    launcher = toolchain / "bin/node"
    launcher.parent.mkdir(parents=True, exist_ok=True)
    if linux_wasm_guard is None:
        linux_wasm_guard = sys.platform.startswith("linux")
    if not launcher.exists():
        wasm_guard = (
            "[ \"$1\" = \"--disable-wasm-trap-handler\" ] || exit 64\n"
            "shift\n"
            if linux_wasm_guard else
            "[ \"$1\" != \"--disable-wasm-trap-handler\" ] || exit 64\n"
        )
        launcher.write_text(
            "#!/bin/sh\n"
            + wasm_guard
            + "entrypoint=$1\n"
            "shift\n"
            "case \" $* \" in *\" --disable-wasm-trap-handler \"*) exit 64;; esac\n"
            + f"exec {sys.executable!s} \"$entrypoint\" \"$@\"\n",
            encoding="utf-8",
        )
        launcher.chmod(0o755)
    lockfile = toolchain / "package-lock.json"
    lockfile.write_text("{}\n", encoding="utf-8")
    headers = toolchain / "include/node"
    headers.mkdir(parents=True, exist_ok=True)
    # The descriptor test double does not compile the authority, but it must
    # still model the complete no-link N-API role required before compilation.
    (headers / "node_api.h").write_text(
        "#include <js_native_api.h>\n", encoding="utf-8"
    )
    (headers / "js_native_api.h").write_text(
        "#include <js_native_api_types.h>\n", encoding="utf-8"
    )
    (headers / "js_native_api_types.h").write_text("\n", encoding="utf-8")
    (headers / "node_api_types.h").write_text("\n", encoding="utf-8")
    manifest = toolchain / "vitest-toolchain.json"
    manifest.write_text(
        json.dumps(
            {
                "version": 1,
                "roles": {
                    "launcher": str(launcher.resolve()),
                    "entrypoint": str(entrypoint.resolve()),
                    "dependencies": str((toolchain / "node_modules").resolve()),
                    "native_runtime": [str(native_file.resolve())],
                    "lockfile": str(lockfile.resolve()),
                    "headers": str(headers.resolve()),
                },
            }
        ),
        encoding="utf-8",
    )
    return manifest


def _runner_config(tmp_path: Path, entrypoint: Path, timeout: int = 2) -> RunnerConfig:
    manifest = _toolchain_manifest(tmp_path, entrypoint)
    roles = json.loads(manifest.read_text(encoding="utf-8"))["roles"]
    return RunnerConfig(
        timeout_seconds=timeout,
        vitest_command=(roles["launcher"], str(entrypoint)),
        vitest_toolchain_manifest=manifest,
    )


def _real_vitest_4_command() -> tuple[Path, Path]:
    """Return the CI-provisioned exact Vitest 4.1.10 launcher and entrypoint."""
    manifest_name = os.environ.get("PDD_REAL_VITEST_TOOLCHAIN_MANIFEST")
    if not manifest_name:
        pytest.skip("requires the CI-provisioned exact Vitest 4.1.10 toolchain")
    roles = json.loads(Path(manifest_name).read_text(encoding="utf-8"))["roles"]
    entrypoint = Path(roles["entrypoint"])
    package = json.loads(
        (Path(roles["dependencies"]) / "vitest/package.json").read_text(encoding="utf-8")
    )
    assert package["version"] == "4.1.10"
    return Path(roles["launcher"]), entrypoint


def _real_vitest_worker_source(label: str) -> str:
    """Return one exact-Vitest worker probe for parser and pool ownership tests."""
    return (
        "import fs from 'node:fs';\n"
        "import { expect, test } from 'vitest';\n"
        "test('records checker-owned worker controls', () => {\n"
        "  fs.appendFileSync(process.env.PDD_VITEST_MARKER, JSON.stringify({\n"
        f"    label: {label!r}, pool: process.env.VITEST_POOL_ID,\n"
        "    uv: process.env.UV_THREADPOOL_SIZE, nodeOptions: process.env.NODE_OPTIONS,\n"
        "  }) + '\\n');\n"
        "  expect(process.env.UV_THREADPOOL_SIZE).toBe('1');\n"
        "  expect(process.env.NODE_OPTIONS).toBe('--v8-pool-size=1');\n"
        "});\n"
    )


def _controlled_run(
    command, *, cwd, timeout, env, result_write_fd=None, result_fd=198,
    **_limits,
):
    child_env = dict(env)
    if result_write_fd is not None:
        observed = os.fstat(result_write_fd)
        child_env.update({
            "PDD_FRAMEWORK_OBSERVATION_DEVICE": str(observed.st_dev),
            "PDD_FRAMEWORK_OBSERVATION_INODE": str(observed.st_ino),
        })
        os.dup2(result_write_fd, result_fd)
    try:
        result = subprocess.run(
            command,
            cwd=cwd,
            timeout=timeout,
            env=child_env,
            pass_fds=((result_fd,) if result_write_fd is not None else ()),
            capture_output=True,
            text=True,
            check=False,
        )
    except subprocess.TimeoutExpired:
        result = subprocess.CompletedProcess(command, 124, "", "timeout")
    finally:
        if result_write_fd is not None:
            os.close(result_fd)
    return result, False


def _repository(
    tmp_path: Path, *, mode: str = "pass", config: str = '{"test":{}}'
) -> tuple[Path, str]:
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "runner@example.com")
    _git(root, "config", "user.name", "Runner Test")
    (root / "tests").mkdir()
    (root / "tests/widget.test.ts").write_text(
        "import { expect, test } from 'vitest';\ntest('widget works', () => expect(true).toBe(true));\n",
        encoding="utf-8",
    )
    (root / "vitest.config.json").write_text(config, encoding="utf-8")
    (root / "source.ts").write_text(mode, encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "protected Vitest tests")
    return root, _git(root, "rev-parse", "HEAD")


def _run(root: Path, base: str, head: str, fake_vitest: Path, timeout: int = 2):
    paths = (PurePosixPath("tests/widget.test.ts"),)
    try:
        config_digest = vitest_validator_config_digest(root, base, paths)
    except ValueError:
        config_digest = "invalid-vitest-config"
    obligation = VerificationObligation(
        "vitest", "test", "vitest", config_digest, ("REQ-1",), paths
    )
    profile = VerificationProfile(UNIT, (obligation,), ("REQ-1",), "profile-v1")
    return run_profile(
        root,
        profile,
        RunBinding("snapshot-v1", base, head),
        AttestationIssue(
            AttestationSigner("trusted-ci", b"v" * 32),
            "id",
            "nonce",
            datetime(2026, 7, 10, tzinfo=timezone.utc),
        ),
        config=_runner_config(fake_vitest.parents[3], fake_vitest, timeout),
    )


def _run_default_vitest(root: Path, base: str, head: str, timeout: int = 2):
    paths = (PurePosixPath("tests/widget.test.ts"),)
    obligation = VerificationObligation(
        "vitest",
        "test",
        "vitest",
        vitest_validator_config_digest(root, base, paths),
        ("REQ-1",),
        paths,
    )
    profile = VerificationProfile(UNIT, (obligation,), ("REQ-1",), "profile-v1")
    return run_profile(
        root,
        profile,
        RunBinding("snapshot-v1", base, head),
        AttestationIssue(
            AttestationSigner("trusted-ci", b"v" * 32),
            "id",
            "nonce",
            datetime(2026, 7, 10, tzinfo=timezone.utc),
        ),
        config=RunnerConfig(timeout_seconds=timeout),
    )


def test_vitest_passing_collected_test_is_pass(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    _envelope, executions = _run(root, commit, commit, _fake_vitest(tmp_path))
    assert executions[0].outcome is EvidenceOutcome.PASS


def test_vitest_phase_canonicalizes_trusted_temporary_root(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Platform temp aliases are resolved before trusted Vitest staging."""
    temporary_directory = runner_module.tempfile.TemporaryDirectory
    aliased_prefixes = {
        "pdd-vitest-protected-base-",
        "pdd-vitest-checked-head-",
        "pdd-trusted-vitest-",
        "pdd-vitest-signing-binding-",
    }
    aliases_created = 0

    @contextmanager
    def aliased_temporary_directory(*args, **kwargs):
        nonlocal aliases_created
        with temporary_directory(*args, **kwargs) as directory:
            prefix = kwargs.get("prefix", args[0] if args else None)
            if prefix not in aliased_prefixes:
                yield directory
                return
            alias = tmp_path / f"temporary-alias-{aliases_created}"
            aliases_created += 1
            alias.symlink_to(directory, target_is_directory=True)
            try:
                yield str(alias)
            finally:
                alias.unlink()

    monkeypatch.setattr(
        runner_module.tempfile, "TemporaryDirectory", aliased_temporary_directory
    )
    load_addon = runner_module._load_vitest_coordinator_addon

    def load_addon_from_canonical_staging(staging_directory: Path, *args, **kwargs):
        assert not staging_directory.is_symlink()
        return load_addon(staging_directory, *args, **kwargs)

    monkeypatch.setattr(
        runner_module,
        "_load_vitest_coordinator_addon",
        load_addon_from_canonical_staging,
    )
    root, commit = _repository(tmp_path)

    _envelope, executions = _run(root, commit, commit, _fake_vitest(tmp_path))

    assert executions[0].outcome is EvidenceOutcome.PASS
    assert aliases_created == 5


def test_vitest_native_authority_identity_changes_signed_binding(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The exact native authority measured by a PASS must reach signed bytes."""
    authority_identity = ["a" * 64]
    paths = (PurePosixPath("tests/widget.test.ts"),)
    profile = VerificationProfile(
        UNIT,
        (
            VerificationObligation(
                "vitest", "test", "vitest", "config", ("REQ-1",), paths
            ),
        ),
        ("REQ-1",),
        "profile-v1",
    )
    issuance = AttestationIssue(
        AttestationSigner("trusted-ci", b"v" * 32),
        "id",
        "nonce",
        datetime(2026, 7, 10, tzinfo=timezone.utc),
    )
    monkeypatch.setattr(
        runner_module,
        "_capture_adapter_identities",
        lambda _root, _config: ((("vitest", "adapter"),), {}),
    )
    monkeypatch.setattr(
        runner_module, "_verify_adapter_identities", lambda _root, _config: None
    )
    monkeypatch.setattr(
        runner_module,
        "runner_identity_digest",
        lambda *_args, **_kwargs: "runner-identity",
    )
    monkeypatch.setattr(
        runner_module,
        "run_obligation",
        lambda *_args, **_kwargs: runner_module.RunnerExecution(
            "vitest",
            EvidenceOutcome.PASS,
            authority_identity[0],
            "passed",
            native_binding_digest=runner_module._vitest_protocol_native_digest(
                authority_identity[0], authority_identity[0]
            ),
        ),
    )
    monkeypatch.setattr(
        runner_module,
        "_vitest_signing_addon",
        lambda _root, _config, _required: nullcontext(
            SimpleNamespace(identity=authority_identity[0])
        ),
    )
    monkeypatch.setattr(
        runner_module,
        "_verify_vitest_signing_addon",
        lambda _root, _config, _addon: None,
    )

    first, first_executions = run_profile(
        tmp_path,
        profile,
        RunBinding("snapshot-v1", "base", "head"),
        issuance,
        RunnerConfig(vitest_command=("trusted-vitest",)),
    )
    authority_identity[0] = "b" * 64
    second, second_executions = run_profile(
        tmp_path,
        profile,
        RunBinding("snapshot-v1", "base", "head"),
        issuance,
        RunnerConfig(vitest_command=("trusted-vitest",)),
    )

    assert first_executions[0].outcome is EvidenceOutcome.PASS
    assert second_executions[0].outcome is EvidenceOutcome.PASS
    assert first.binding.runner_digest == second.binding.runner_digest
    assert first.payload() != second.payload()


def test_vitest_native_authority_tampering_at_signing_is_rejected(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A live addon mutation after execution cannot receive a PASS signature."""
    source = tmp_path / "authority.c"
    source.write_bytes(b"int authority(void) { return 1; }\n")
    source.chmod(0o444)
    staged = tmp_path / "authority.node"
    staged.write_bytes(b"native authority")
    staged.chmod(0o555)
    source_member = runner_module._capture_vitest_member(
        source, "coordinator_addon", PurePosixPath(".")
    )
    staged_member = runner_module._capture_vitest_member(
        staged, "coordinator_addon", PurePosixPath(".")
    )
    addon = runner_module.VitestCoordinatorAddon(
        source,
        staged,
        source_member,
        staged_member,
        runner_module._vitest_coordinator_identity(
            source_member, (), (), staged_member
        ),
    )
    native_binding = runner_module._vitest_protocol_native_digest(
        addon.identity, addon.identity
    )
    profile = VerificationProfile(
        UNIT,
        (
            VerificationObligation(
                "vitest",
                "test",
                "vitest",
                "config",
                ("REQ-1",),
                (PurePosixPath("tests/widget.test.ts"),),
            ),
        ),
        ("REQ-1",),
        "profile-v1",
    )

    class TamperingSigner(AttestationSigner):
        def issue(self, request):
            staged.chmod(0o755)
            staged.write_bytes(b"substituted native authority")
            return super().issue(request)

    monkeypatch.setattr(
        runner_module,
        "_capture_adapter_identities",
        lambda _root, _config: ((("vitest", "adapter"),), {}),
    )
    monkeypatch.setattr(
        runner_module, "_verify_adapter_identities", lambda _root, _config: None
    )
    monkeypatch.setattr(
        runner_module,
        "runner_identity_digest",
        lambda *_args, **_kwargs: "runner-identity",
    )
    monkeypatch.setattr(
        runner_module,
        "run_obligation",
        lambda *_args, **_kwargs: runner_module.RunnerExecution(
            "vitest",
            EvidenceOutcome.PASS,
            "command",
            "passed",
            native_binding_digest=native_binding,
        ),
    )
    monkeypatch.setattr(
        runner_module,
        "_vitest_signing_addon",
        lambda _root, _config, _required: nullcontext(addon),
    )
    monkeypatch.setattr(
        runner_module,
        "_verify_vitest_signing_addon",
        lambda _root, _config, value: (
            runner_module._verify_vitest_coordinator_addon(value)
        ),
    )

    with pytest.raises(ValueError, match="identity changed"):
        run_profile(
            tmp_path,
            profile,
            RunBinding("snapshot-v1", "base", "head"),
            AttestationIssue(
                TamperingSigner("trusted-ci", b"v" * 32),
                "id",
                "nonce",
                datetime(2026, 7, 10, tzinfo=timezone.utc),
            ),
            RunnerConfig(vitest_command=("trusted-vitest",)),
        )


@pytest.mark.parametrize(
    ("mode", "outcome"),
    [
        ("fail", EvidenceOutcome.FAIL),
        ("skip", EvidenceOutcome.SKIP),
        ("todo", EvidenceOutcome.SKIP),
        ("zero", EvidenceOutcome.NOT_COLLECTED),
        ("timeout", EvidenceOutcome.TIMEOUT),
        ("malformed", EvidenceOutcome.COLLECTION_ERROR),
    ],
)
def test_vitest_normalizes_non_pass_outcomes(
    tmp_path: Path, mode: str, outcome: EvidenceOutcome
) -> None:
    root, commit = _repository(tmp_path, mode=mode)
    _envelope, executions = _run(root, commit, commit, _fake_vitest(tmp_path), timeout=1)
    assert executions[0].outcome is outcome


@pytest.mark.parametrize("mode", ["mismatch", "candidate"])
def test_vitest_collection_identity_mismatch_cannot_pass(
    tmp_path: Path, mode: str
) -> None:
    root, base = _repository(tmp_path)
    (root / "source.ts").write_text(mode, encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change application behavior")
    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_vitest(tmp_path)
    )
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED


def test_vitest_removed_protected_test_cannot_pass(tmp_path: Path) -> None:
    root, base = _repository(tmp_path)
    (root / "tests/widget.test.ts").write_text("// removed\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "remove protected test")
    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_vitest(tmp_path)
    )
    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


@pytest.mark.parametrize("path", ["vitest.config.json", "setup.ts", "transform.ts"])
def test_vitest_config_and_support_mutation_cannot_pass(
    tmp_path: Path, path: str
) -> None:
    config = '{"test":{"setupFiles":["setup.ts"]},"transform":{"^.+\\\\.ts$":"transform.ts"}}'
    root, base = _repository(tmp_path, config=config)
    (root / "setup.ts").write_text("export {};\n", encoding="utf-8")
    (root / "transform.ts").write_text("export {};\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add protected support")
    base = _git(root, "rev-parse", "HEAD")
    (root / path).write_text("changed\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate protected Vitest support")
    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_vitest(tmp_path)
    )
    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_vitest_dirty_support_cannot_influence_run(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    (root / "setup.ts").write_text("export {};\n", encoding="utf-8")
    _envelope, executions = _run(root, commit, commit, _fake_vitest(tmp_path))
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED


def test_vitest_imported_test_helper_mutation_cannot_pass(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/helper.ts").write_text("export const expected = true;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import { expect, test } from 'vitest';\n"
        "import { expected } from './helper';\n"
        "test('widget works', () => expect(expected).toBe(true));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add protected Vitest helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "tests/helper.ts").write_text("export const expected = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate imported Vitest helper")

    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_vitest(tmp_path)
    )

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_vitest_side_effect_import_helper_mutation_cannot_pass(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/helper.ts").write_text("globalThis.expected = true;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import { expect, test } from 'vitest';\n"
        "import './helper';\n"
        "test('widget works', () => expect(globalThis.expected).toBe(true));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add protected side effect helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "tests/helper.ts").write_text("globalThis.expected = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate side effect helper")

    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_vitest(tmp_path)
    )

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_vitest_parent_directory_import_helper_mutation_cannot_pass(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "shared").mkdir()
    (root / "shared/helper.ts").write_text("export const expected = true;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import { expect, test } from 'vitest';\n"
        "import { expected } from '../shared/helper';\n"
        "test('widget works', () => expect(expected).toBe(true));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add parent import helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "shared/helper.ts").write_text("export const expected = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate parent import helper")

    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_vitest(tmp_path)
    )

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_vitest_parent_directory_side_effect_import_mutation_cannot_pass(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "shared").mkdir()
    (root / "shared/setup.ts").write_text("globalThis.expected = true;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import { expect, test } from 'vitest';\n"
        "import '../shared/setup';\n"
        "test('widget works', () => expect(globalThis.expected).toBe(true));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add parent side effect helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "shared/setup.ts").write_text("globalThis.expected = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate parent side effect helper")

    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_vitest(tmp_path)
    )

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_vitest_parent_directory_imports_change_validator_digest(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    paths = (PurePosixPath("tests/widget.test.ts"),)
    (root / "shared/helpers").mkdir(parents=True)
    (root / "shared/helpers/index.ts").write_text(
        "export const expected = true;\n", encoding="utf-8"
    )
    (root / "shared/setup.ts").write_text("globalThis.expected = true;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import { expect, test } from 'vitest';\n"
        "import { expected } from '../shared/helpers';\n"
        "import '../shared/setup';\n"
        "test('widget works', () => expect(expected && globalThis.expected).toBe(true));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add parent import helpers")
    base = _git(root, "rev-parse", "HEAD")
    base_digest = vitest_validator_config_digest(root, base, paths)

    (root / "shared/helpers/index.ts").write_text(
        "export const expected = false;\n", encoding="utf-8"
    )
    (root / "shared/setup.ts").write_text("globalThis.expected = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate parent import helpers")
    head_digest = vitest_validator_config_digest(root, _git(root, "rev-parse", "HEAD"), paths)

    assert head_digest != base_digest


def test_vitest_config_reference_index_candidate_changes_validator_digest(tmp_path: Path) -> None:
    config = '{"test":{"setupFiles":["support/setup"]}}'
    root, _commit = _repository(tmp_path, config=config)
    paths = (PurePosixPath("tests/widget.test.ts"),)
    (root / "support/setup").mkdir(parents=True)
    (root / "support/setup/index.ts").write_text(
        "globalThis.expected = true;\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add extensionless setup index")
    base = _git(root, "rev-parse", "HEAD")
    base_digest = vitest_validator_config_digest(root, base, paths)

    (root / "support/setup/index.ts").write_text(
        "globalThis.expected = false;\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate extensionless setup index")
    head_digest = vitest_validator_config_digest(root, _git(root, "rev-parse", "HEAD"), paths)

    assert head_digest != base_digest


def test_vitest_repository_escape_import_fails_clearly(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    with pytest.raises(ValueError, match="escapes repository"):
        _local_javascript_imports(
            root,
            commit,
            PurePosixPath("tests/widget.test.ts"),
            b"import '../../outside.js';\n",
        )


def test_vitest_local_alias_config_fails_closed(tmp_path: Path) -> None:
    config = '{"resolve":{"alias":{"@":"./src"}}}'
    root, commit = _repository(tmp_path, config=config)
    (root / "src").mkdir()
    (root / "src/helper.ts").write_text("export const expected = true;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import { expect, test } from 'vitest';\n"
        "import { expected } from '@/helper';\n"
        "test('widget works', () => expect(expected).toBe(true));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add aliased protected helper")
    commit = _git(root, "rev-parse", "HEAD")

    _envelope, executions = _run(root, commit, commit, _fake_vitest(tmp_path))

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "alias" in executions[0].detail


def test_default_candidate_node_modules_vitest_is_not_trusted(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    (root / ".gitignore").write_text("node_modules/\n", encoding="utf-8")
    _git(root, "add", ".gitignore")
    _git(root, "commit", "-q", "-m", "ignore local node modules")
    commit = _git(root, "rev-parse", "HEAD")
    binary = root / "node_modules" / "vitest" / "vitest.mjs"
    binary.parent.mkdir(parents=True)
    binary.write_text(
        "import fs from 'fs';\n"
        "const output = process.argv.find((arg) => arg.startsWith('--outputFile='))"
        "?.slice('--outputFile='.length);\n"
        "fs.writeFileSync(output, JSON.stringify({tests:[{identity:"
        "'tests/widget.test.ts::widget works',status:'passed'}]}));\n",
        encoding="utf-8",
    )

    _envelope, executions = _run_default_vitest(root, commit, commit)

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "candidate node_modules" in executions[0].detail


def test_explicit_candidate_local_vitest_command_is_not_trusted(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    runner = root / "tools" / "vitest.py"
    runner.parent.mkdir()
    runner.write_text(_fake_vitest(tmp_path).read_text(encoding="utf-8"), encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add candidate-local Vitest command")
    commit = _git(root, "rev-parse", "HEAD")

    _envelope, executions = _run(root, commit, commit, runner)

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "candidate checkout" in executions[0].detail


def test_pathless_vitest_script_operand_is_not_resolved_from_candidate(
    tmp_path: Path,
) -> None:
    root, base = _repository(tmp_path)
    (root / "fake_vitest.py").write_text(
        _fake_vitest(tmp_path).read_text(encoding="utf-8"), encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add pathless candidate Vitest command")
    base = _git(root, "rev-parse", "HEAD")
    (root / "fake_vitest.py").write_text(
        _fake_vitest(tmp_path).read_text(encoding="utf-8") + "\n# changed\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate pathless Vitest command")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    obligation = VerificationObligation(
        "vitest",
        "test",
        "vitest",
        vitest_validator_config_digest(root, base, paths),
        ("REQ-1",),
        paths,
    )
    profile = VerificationProfile(UNIT, (obligation,), ("REQ-1",), "profile-v1")

    _envelope, executions = run_profile(
        root,
        profile,
        RunBinding("snapshot-v1", base, _git(root, "rev-parse", "HEAD")),
        AttestationIssue(
            AttestationSigner("trusted-ci", b"v" * 32),
            "id",
            "nonce",
            datetime(2026, 7, 10, tzinfo=timezone.utc),
        ),
        config=RunnerConfig(
            timeout_seconds=2,
            vitest_command=(sys.executable, "fake_vitest.py"),
        ),
    )

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "pathless" in executions[0].detail


def test_vitest_subprocess_cannot_read_secret(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, commit = _repository(tmp_path)
    fake = _fake_vitest(tmp_path)
    fake.write_text(
        fake.read_text(encoding="utf-8")
        + "\nassert 'PDD_ATTESTATION_SIGNING_KEY' not in os.environ\n",
        encoding="utf-8",
    )
    monkeypatch.setenv("PDD_ATTESTATION_SIGNING_KEY", "must-not-leak")
    _envelope, executions = _run(root, commit, commit, fake)
    assert executions[0].outcome is EvidenceOutcome.PASS


def test_vitest_rejects_dynamic_config(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    (root / "vitest.config.json").unlink()
    (root / "vitest.config.ts").write_text("export default {};\n", encoding="utf-8")
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", "dynamic config")
    commit = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, commit, commit, _fake_vitest(tmp_path))
    assert executions[0].outcome is EvidenceOutcome.ERROR


@pytest.mark.parametrize(
    "config",
    [
        '{"test":{"watch":true}}',
        '{"test":{"shard":"1/2"}}',
        '{"projects":["unit"]}',
        '{"plugins":["local-plugin"]}',
        '{"test":{"env":{"UV_THREADPOOL_SIZE":"64"}}}',
        '{"test":{"env":{"NODE_OPTIONS":"--v8-pool-size=64"}}}',
        '{"test":{"execArgv":["--v8-pool-size=64"]}}',
        '{"test":{"execArgv":["--require","./unbound-preload.cjs"]}}',
        '{"env":{"UV_THREADPOOL_SIZE":"64"}}',
        '{"env":{"NODE_OPTIONS":"--v8-pool-size=64"}}',
        '{"execArgv":["--require","./unbound-preload.cjs"]}',
        '{"workspace":[]}',
        '{"projects":[]}',
        '{"test":{"execArgv":["--require","./candidate-preload.cjs"]}}',
        '{"test":{"env":{"NODE_OPTIONS":"--require=./candidate-preload.cjs"}}}',
        '{"test":{"poolOptions":{"forks":{"execArgv":["--require","./candidate-preload.cjs"]}}}}',
        '{"execArgv":["--require","./candidate-preload.cjs"]}',
        '{"env":{"NODE_OPTIONS":"--require=./candidate-preload.cjs"}}',
        '{"poolOptions":{"forks":{"execArgv":["--require","./candidate-preload.cjs"]}}}',
        '{"test":{"browser":false}}',
        '{"test":{"browser":{}}}',
        '{"test":{"browser":{"enabled":true}}}',
        '{"browser":false}',
        '{"browser":{}}',
        '{"browser":{"enabled":true}}',
    ],
)
def test_vitest_rejects_unbound_execution_controls(
    tmp_path: Path, config: str
) -> None:
    root, commit = _repository(tmp_path, config=config)
    _envelope, executions = _run(root, commit, commit, _fake_vitest(tmp_path))
    assert executions[0].outcome is EvidenceOutcome.ERROR


def _real_vitest_execution(tmp_path: Path, source: str) -> RunnerExecution:
    """Run one exact real-toolchain protected Vitest source."""
    if os.environ.get("PDD_REQUIRE_INSTALLED_WHEEL"):
        import pdd  # pylint: disable=import-outside-toplevel
        assert "site-packages" in str(Path(pdd.__file__).resolve())
        assert "site-packages" in str(Path(runner_module.__file__).resolve())
    manifest = Path(os.environ["PDD_REAL_VITEST_TOOLCHAIN_MANIFEST"])
    roles = json.loads(manifest.read_text(encoding="utf-8"))["roles"]
    root = tmp_path / "real-vitest-repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "runner@example.com")
    _git(root, "config", "user.name", "Runner Test")
    (root / "tests").mkdir()
    (root / "tests/widget.test.ts").write_text(source, encoding="utf-8")
    (root / "vitest.config.json").write_text('{"test":{}}\n', encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "protected real Vitest test")
    commit = _git(root, "rev-parse", "HEAD")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    obligation = VerificationObligation(
        "vitest-real", "test", "vitest",
        vitest_validator_config_digest(root, commit, paths),
        ("REQ-1",), paths,
    )
    profile = VerificationProfile(
        UnitId("repo", PurePosixPath("prompts/widget_ts.prompt"), "typescript"),
        (obligation,), ("REQ-1",), "profile-v1",
    )
    _real_vitest_concurrency_barrier()
    _envelope, executions = run_profile(
        root, profile, RunBinding("snapshot", commit, commit),
        AttestationIssue(
            AttestationSigner("trusted-ci", b"v" * 32), "id", "nonce",
            datetime(2026, 7, 13, tzinfo=timezone.utc),
        ),
        RunnerConfig(
            timeout_seconds=30,
            vitest_command=(roles["launcher"], roles["entrypoint"]),
            vitest_toolchain_manifest=manifest,
        ),
    )
    return executions[0]


def _real_vitest_direct(
    tmp_path: Path, source: str,
) -> tuple[RunnerExecution, tuple[str, ...]]:
    """Run one real protected process and return its trusted identities."""
    return _real_vitest_direct_files(
        tmp_path, {PurePosixPath("tests/widget.test.ts"): source}
    )


def _real_vitest_direct_files(
    tmp_path: Path, sources: dict[PurePosixPath, str],
) -> tuple[RunnerExecution, tuple[str, ...]]:
    """Run exact real protected modules and return canonical identities."""
    manifest = Path(os.environ["PDD_REAL_VITEST_TOOLCHAIN_MANIFEST"])
    roles = json.loads(manifest.read_text(encoding="utf-8"))["roles"]
    root = tmp_path / "real-vitest-repo"
    root.mkdir(parents=True)
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "runner@example.com")
    _git(root, "config", "user.name", "Runner Test")
    for relative, source in sources.items():
        destination = root / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(source, encoding="utf-8")
    (root / "vitest.config.json").write_text('{"test":{}}\n', encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "protected real Vitest test")
    _real_vitest_concurrency_barrier()
    return _run_vitest(
        root, tuple(sources), 30,
        RunnerConfig(
            timeout_seconds=30,
            vitest_command=(roles["launcher"], roles["entrypoint"]),
            vitest_toolchain_manifest=manifest,
        ),
    )


def _real_vitest_concurrency_barrier() -> None:
    """Release hosted child processes only after every exact case is ready."""
    barrier_value = os.environ.get("PDD_REAL_VITEST_CONCURRENCY_BARRIER")
    if not barrier_value:
        return
    barrier = Path(barrier_value)
    participants = int(os.environ["PDD_REAL_VITEST_CONCURRENCY_PARTICIPANTS"])
    os.environ.pop("PDD_REAL_VITEST_CONCURRENCY_BARRIER", None)
    os.environ.pop("PDD_REAL_VITEST_CONCURRENCY_PARTICIPANTS", None)
    if not 2 <= participants <= 8:
        raise RuntimeError("invalid real Vitest concurrency participant count")
    (barrier / f"ready-{os.getpid()}").touch(exist_ok=False)
    deadline = time.monotonic() + 30
    while time.monotonic() < deadline:
        if len(tuple(barrier.glob("ready-*"))) == participants:
            return
        time.sleep(.01)
    raise RuntimeError("real Vitest concurrency barrier timed out")


def test_real_vitest_concurrency_barrier_releases_once_per_process(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A repeated-process case joins the outer barrier only on its first run."""
    (tmp_path / "ready-peer").touch()
    monkeypatch.setenv("PDD_REAL_VITEST_CONCURRENCY_BARRIER", str(tmp_path))
    monkeypatch.setenv("PDD_REAL_VITEST_CONCURRENCY_PARTICIPANTS", "2")

    _real_vitest_concurrency_barrier()
    _real_vitest_concurrency_barrier()

    assert len(tuple(tmp_path.glob("ready-*"))) == 2


def _cross_process_descriptor_probe(test_name: str) -> str:
    """Return a worker that probes every visible non-self proc descriptor."""
    return (
        "import fs from 'node:fs';\n"
        "import { expect, test } from 'vitest';\n"
        "const preloadSource = fs.readFileSync(process.execArgv.find((value) =>\n"
        "  value.startsWith('--require=')).slice('--require='.length), 'utf8');\n"
        "const expectedMatch = preloadSource.match(\n"
        "  /const EXPECTED_DEVICE = ([0-9]+)n;\\nconst EXPECTED_INODE = ([0-9]+)n;/);\n"
        "if (!expectedMatch) throw new Error('missing trusted worker identity');\n"
        "const expected = expectedMatch[1] + ':' + expectedMatch[2];\n"
        f"test({test_name!r} + ' ' + expected, () => {{\n"
        "  const forged = Buffer.from(JSON.stringify({\n"
        "    tests: [{identity: 'forged', status: 'passed'}]\n"
        "  }));\n"
        "  const denied = new Set(['EACCES', 'EPERM', 'ENOENT', 'ESRCH']);\n"
        "  const visible = fs.readdirSync('/proc').filter((value) =>\n"
        "    /^\\d+$/.test(value) && Number(value) !== process.pid);\n"
        "  expect(visible.map(Number)).toContain(process.ppid);\n"
        "  const exposed = [];\n"
        "  for (const pid of visible) {\n"
        "    let tids;\n"
        "    try { tids = fs.readdirSync('/proc/' + pid + '/task'); }\n"
        "    catch (error) { if (!denied.has(error?.code)) throw error; continue; }\n"
        "    const directories = ['/proc/' + pid + '/fd', ...tids.map((tid) =>\n"
        "      '/proc/' + pid + '/task/' + tid + '/fd')];\n"
        "    for (const directory of directories) {\n"
        "      let entries;\n"
        "      try { entries = fs.readdirSync(directory); }\n"
        "      catch (error) { if (!denied.has(error?.code)) throw error; continue; }\n"
        "      for (const fd of entries) {\n"
        "        const path = directory + '/' + fd;\n"
        "        let observed;\n"
        "        try { observed = fs.statSync(path, {bigint: true}); }\n"
        "        catch (error) { if (!denied.has(error?.code)) throw error; continue; }\n"
        "        if (observed.dev + ':' + observed.ino !== expected) continue;\n"
        "        let writer;\n"
        "        try { writer = fs.openSync(path, 'w'); fs.writeSync(writer, forged); }\n"
        "        catch (error) { if (!denied.has(error?.code)) throw error; }\n"
        "        finally { if (writer !== undefined) fs.closeSync(writer); }\n"
        "        exposed.push(path);\n"
        "      }\n"
        "    }\n"
        "  }\n"
        "  expect(exposed).toEqual([]);\n"
        "});\n"
    )


def test_package_preprocess_smoke_vitest_manifest_matches_runner_schema() -> None:
    """The first package manifest carries the complete installed-wheel schema."""
    repository = Path(__file__).resolve().parents[1]
    workflow = (repository / ".github/workflows/unit-tests.yml").read_text(
        encoding="utf-8"
    )
    package_job = workflow.split("  package-preprocess-smoke:", 1)[1].split(
        "  repo-bloat-docker-e2e:", 1
    )[0]
    provision = package_job.split(
        "      - name: Provision identity-bound Vitest toolchain", 1
    )[1].split("      - name:", 1)[0]
    roles = provision.split('"roles": {', 1)[1].split("              },", 1)[0]
    role_names = {
        line.split('"', 2)[1]
        for line in roles.splitlines()
        if line.lstrip().startswith('"')
    }
    assert role_names == {
        "launcher",
        "entrypoint",
        "dependencies",
        "native_runtime",
        "lockfile",
        "headers",
    }
    assert 'headers = launcher.parents[1] / "include/node"' in provision
    for header in (
        "node_api.h",
        "node_api_types.h",
        "js_native_api.h",
        "js_native_api_types.h",
    ):
        assert f'headers / "{header}"' in provision


def test_vitest_hosted_workflow_pins_and_runs_the_installed_wheel() -> None:
    """The hosted lanes execute the exact source and installed-wheel boundary."""
    repository = Path(__file__).resolve().parents[1]
    workflow = (repository / ".github/workflows/unit-tests.yml").read_text(
        encoding="utf-8"
    )
    package_job = workflow.split("  package-preprocess-smoke:", 1)[1].split(
        "  repo-bloat-docker-e2e:", 1
    )[0]
    package = json.loads(
        (repository / ".github/toolchains/vitest/package.json").read_text(
            encoding="utf-8"
        )
    )

    assert workflow.count("node-version: '22.23.1'") >= 2
    assert "node-version: '22'" not in workflow
    assert package["dependencies"] == {"vitest": "4.1.10"}
    assert "Provision identity-bound Vitest toolchain" in package_job
    assert "PDD_REQUIRE_INSTALLED_WHEEL: '1'" in package_job
    assert (
        "test_sync_core_runner_vitest.py::"
        "test_real_vitest_runs_copied_entrypoint_without_candidate_result_access"
    ) in package_job
    assert (
        "test_sync_core_runner_vitest.py::"
        "test_real_vitest_concurrent_scope_setup_is_independent_and_leak_free"
    ) in workflow


@pytest.mark.skipif(
    not sys.platform.startswith("linux")
    or not shutil.which("bwrap")
    or not os.environ.get("PDD_REAL_VITEST_TOOLCHAIN_MANIFEST"),
    reason="requires Linux sandbox and provisioned real Vitest toolchain",
)
def test_real_vitest_runs_copied_entrypoint_without_candidate_result_access(
    tmp_path: Path,
) -> None:
    execution = _real_vitest_execution(
        tmp_path,
        "import fs from 'node:fs';\n"
        "import { expect, test } from 'vitest';\n"
        "test('observation environment is absent', () => {\n"
        "  expect(process.env.PDD_TRUSTED_VITEST_OUTPUT).toBeUndefined();\n"
        "  expect(() => fs.fstatSync(198)).toThrow();\n"
        "  expect(() => fs.writeSync(198, Buffer.from('forged'))).toThrow();\n"
        "  expect(() => fs.openSync('/proc/self/fd/198', 'w')).toThrow();\n"
        "  expect(() => fs.openSync('/run/pdd-framework-observation', 'w')).toThrow();\n"
        "  const preloadSource = fs.readFileSync(process.execArgv.find((value) =>\n"
        "    value.startsWith('--require=')).slice('--require='.length), 'utf8');\n"
        "  const expectedMatch = preloadSource.match(\n"
        "    /const EXPECTED_DEVICE = ([0-9]+)n;\\nconst EXPECTED_INODE = ([0-9]+)n;/);\n"
        "  if (!expectedMatch) throw new Error('missing trusted worker identity');\n"
        "  const expected = expectedMatch[1] + ':' + expectedMatch[2];\n"
        "  const matches = fs.readdirSync('/proc/self/fd')\n"
        "    .filter((value) => /^\\d+$/.test(value)).map(Number).filter((fd) => {\n"
        "      try { const item = fs.fstatSync(fd, { bigint: true });\n"
        "        return item.dev + ':' + item.ino === expected;\n"
        "      } catch (error) { return false; }\n"
        "    });\n"
        "  expect(matches).toEqual([]);\n"
        "  const preload = process.execArgv.find((value) => value.startsWith('--require='))\n"
        "    ?.slice('--require='.length);\n"
        "  expect(preload).toBeTruthy();\n"
        "  expect(() => fs.writeFileSync(preload, 'replaced')).toThrow();\n"
        "  expect(() => fs.renameSync(preload, preload + '.moved')).toThrow();\n"
        "  expect(() => fs.unlinkSync(preload)).toThrow();\n"
        "});\n",
    )
    assert execution.outcome is EvidenceOutcome.PASS, execution.detail


@pytest.mark.skipif(
    not sys.platform.startswith("linux")
    or not shutil.which("bwrap")
    or not os.environ.get("PDD_REAL_VITEST_TOOLCHAIN_MANIFEST"),
    reason="requires Linux sandbox and provisioned real Vitest toolchain",
)
def test_real_vitest_repeated_processes_use_fresh_denied_authorities(
    tmp_path: Path,
) -> None:
    """Real workers complete with fresh identities and no cross-process writer."""
    authorities = []
    for attempt in range(3):
        execution, identities = _real_vitest_direct(
            tmp_path / str(attempt),
            _cross_process_descriptor_probe("fresh authority"),
        )
        assert execution.outcome is EvidenceOutcome.PASS, execution.detail
        assert len(identities) == 1
        authorities.append(identities[0].rsplit("fresh authority ", 1)[1])

    assert len(set(authorities)) == 3


@pytest.mark.skipif(
    not sys.platform.startswith("linux")
    or not shutil.which("bwrap")
    or not os.environ.get("PDD_REAL_VITEST_TOOLCHAIN_MANIFEST"),
    reason="requires Linux sandbox and provisioned real Vitest toolchain",
)
def test_real_vitest_valid_forge_cannot_hide_actual_failure(tmp_path: Path) -> None:
    execution = _real_vitest_execution(
        tmp_path,
        "import fs from 'node:fs';\nimport { expect, test } from 'vitest';\n"
        "test('actual failure remains failed', () => {\n"
        "  const preloadSource = fs.readFileSync(process.execArgv.find((value) =>\n"
        "    value.startsWith('--require=')).slice('--require='.length), 'utf8');\n"
        "  const expectedMatch = preloadSource.match(\n"
        "    /const EXPECTED_DEVICE = ([0-9]+)n;\\nconst EXPECTED_INODE = ([0-9]+)n;/);\n"
        "  if (!expectedMatch) throw new Error('missing trusted worker identity');\n"
        "  const expected = expectedMatch[1] + ':' + expectedMatch[2];\n"
        "  for (const value of fs.readdirSync('/proc/self/fd')) {\n"
        "    try { const fd = Number(value); const item = fs.fstatSync(fd, { bigint: true });\n"
        "      if (item.dev + ':' + item.ino === expected) fs.writeSync(fd,\n"
        "        JSON.stringify({tests:[{identity:'forged',status:'passed'}]}));\n"
        "    } catch (error) { if (!['EBADF','ENOENT'].includes(error.code)) throw error; }\n"
        "  }\n"
        "  expect(false).toBe(true);\n"
        "});\n",
    )
    assert execution.outcome is EvidenceOutcome.FAIL, execution.detail


@pytest.mark.skipif(
    not sys.platform.startswith("linux")
    or not shutil.which("bwrap")
    or not os.environ.get("PDD_REAL_VITEST_TOOLCHAIN_MANIFEST"),
    reason="requires Linux sandbox and provisioned real Vitest toolchain",
)
def test_real_vitest_module_end_graph_has_stable_identities(tmp_path: Path) -> None:
    """Two completed modules survive empty terminal modules in canonical order."""
    execution, identities = _real_vitest_direct_files(
        tmp_path,
        {
            PurePosixPath("tests/z.test.ts"): (
                "import { test } from 'vitest';\n"
                "test('z works', () => {});\n"
            ),
            PurePosixPath("tests/a.test.ts"): (
                "import { test } from 'vitest';\n"
                "test('a works', () => {});\n"
            ),
        },
    )

    assert execution.outcome is EvidenceOutcome.PASS, execution.detail
    assert identities == (
        "tests/a.test.ts::a works",
        "tests/z.test.ts::z works",
    )


@pytest.mark.skipif(
    not sys.platform.startswith("linux")
    or not shutil.which("bwrap")
    or not os.environ.get("PDD_REAL_VITEST_TOOLCHAIN_MANIFEST"),
    reason="requires Linux sandbox and provisioned real Vitest toolchain",
)
def test_real_vitest_concurrent_scope_setup_is_independent_and_leak_free(
    tmp_path: Path,
) -> None:
    """The exact three hosted cases may construct and clean scopes concurrently."""
    repository = Path(__file__).resolve().parents[1]
    barrier = tmp_path / "barrier"
    barrier.mkdir()
    child_temp = tmp_path / "child-tmp"
    child_temp.mkdir()
    selectors = (
        "test_real_vitest_runs_copied_entrypoint_without_candidate_result_access",
        "test_real_vitest_repeated_processes_use_fresh_denied_authorities",
        "test_real_vitest_valid_forge_cannot_hide_actual_failure",
        "test_real_vitest_module_end_graph_has_stable_identities",
    )
    environment = dict(os.environ)
    environment.update({
        "PDD_REAL_VITEST_CONCURRENCY_BARRIER": str(barrier),
        "PDD_REAL_VITEST_CONCURRENCY_PARTICIPANTS": str(len(selectors)),
        "TMPDIR": str(child_temp),
    })
    processes = []
    for index, selector in enumerate(selectors):
        processes.append((selector, subprocess.Popen(
            [
                sys.executable, "-m", "pytest", "-q",
                f"tests/test_sync_core_runner_vitest.py::{selector}",
                f"--basetemp={tmp_path / f'pytest-{index}'}", "--timeout=120",
            ],
            cwd=repository, env=environment, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, text=True,
        )))
    completed = []
    try:
        for selector, process in processes:
            stdout, stderr = process.communicate(timeout=240)
            completed.append((selector, process.returncode, stdout, stderr))
    finally:
        for _, process in processes:
            if process.poll() is None:
                process.kill()
                process.wait(timeout=10)

    failures = [
        (selector, returncode, stdout[-4096:], stderr[-4096:])
        for selector, returncode, stdout, stderr in completed if returncode != 0
    ]
    assert not failures
    assert not tuple(child_temp.glob("pdd-scope-*"))
    mountinfo = Path("/proc/self/mountinfo").read_text(encoding="utf-8")
    assert str(child_temp) not in mountinfo


@pytest.mark.skipif(
    not sys.platform.startswith("linux")
    or not shutil.which("bwrap")
    or not os.environ.get("PDD_REAL_VITEST_TOOLCHAIN_MANIFEST"),
    reason="requires Linux sandbox and provisioned real Vitest toolchain",
)
def test_real_vitest_forge_with_missing_reporter_cannot_pass(tmp_path: Path) -> None:
    execution = _real_vitest_execution(
        tmp_path,
        "import fs from 'node:fs';\nimport { test } from 'vitest';\n"
        "test('missing reporter cannot admit forge', async () => {\n"
        "  const preloadSource = fs.readFileSync(process.execArgv.find((value) =>\n"
        "    value.startsWith('--require=')).slice('--require='.length), 'utf8');\n"
        "  const expectedMatch = preloadSource.match(\n"
        "    /const EXPECTED_DEVICE = ([0-9]+)n;\\nconst EXPECTED_INODE = ([0-9]+)n;/);\n"
        "  if (!expectedMatch) throw new Error('missing trusted worker identity');\n"
        "  const expected = expectedMatch[1] + ':' + expectedMatch[2];\n"
        "  for (const value of fs.readdirSync('/proc/self/fd')) {\n"
        "    try { const fd = Number(value); const item = fs.fstatSync(fd, { bigint: true });\n"
        "      if (item.dev + ':' + item.ino === expected) fs.writeSync(fd,\n"
        "        JSON.stringify({tests:[{identity:'forged',status:'passed'}]}));\n"
        "    } catch (error) { if (!['EBADF','ENOENT'].includes(error.code)) throw error; }\n"
        "  }\n"
        "  process.kill(process.ppid, 'SIGKILL');\n"
        "  await new Promise((resolve) => setTimeout(resolve, 1000));\n"
        "});\n",
    )
    assert execution.outcome is not EvidenceOutcome.PASS, execution.detail


@pytest.mark.parametrize(
    ("specifier", "mapping"),
    [
        ("#fixture-helper", {"imports": {"#fixture-helper": "./tests/mapped.ts"}}),
        ("fixture-self/helper", {"name": "fixture-self", "exports": {"./helper": "./tests/mapped.ts"}}),
    ],
)
def test_vitest_package_mappings_bind_transitive_local_helpers(
    tmp_path: Path, specifier: str, mapping: dict[str, object]
) -> None:
    """Self-package and imports mappings are support, not ambient packages."""
    root, _commit = _repository(tmp_path)
    (root / "package.json").write_text(json.dumps(mapping), encoding="utf-8")
    (root / "tests/mapped.ts").write_text("export const trusted = true;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        f"import {{ trusted }} from {specifier!r};\n"
        "import { test } from 'vitest';\n"
        "test('widget works', () => { if (!trusted) throw new Error('bad'); });\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add static package mapping")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    before = vitest_validator_config_digest(root, "HEAD", paths)

    (root / "tests/mapped.ts").write_text("export const trusted = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate mapped support")

    assert vitest_validator_config_digest(root, "HEAD", paths) != before


@pytest.mark.parametrize(("validator", "suffix"), [("jest", "js"), ("vitest", "ts")])
@pytest.mark.parametrize(
    ("specifier", "root_mapping", "nested_mapping"),
    [
        (
            "#fixture-helper",
            {"imports": {"#fixture-helper": "./tests/root-helper.{suffix}"}},
            {"imports": {"#fixture-helper": "./tests/nested-helper.{suffix}"}},
        ),
        (
            "fixture-self/helper",
            {"name": "fixture-self", "exports": {"./helper": "./tests/root-helper.{suffix}"}},
            {"name": "fixture-self", "exports": {"./helper": "./tests/nested-helper.{suffix}"}},
        ),
    ],
)
def test_javascript_package_mappings_use_nearest_committed_scope(
    tmp_path: Path,
    validator: str,
    suffix: str,
    specifier: str,
    root_mapping: dict[str, object],
    nested_mapping: dict[str, object],
) -> None:
    """Nested imports and self-exports must not bind a root package helper."""
    root, _commit = _repository(tmp_path)
    package = root / "packages/widget"
    tests = package / "tests"
    tests.mkdir(parents=True)
    (root / "package.json").write_text(
        json.dumps(root_mapping).replace("{suffix}", suffix), encoding="utf-8"
    )
    (root / f"tests/root-helper.{suffix}").write_text(
        "export const trusted = 'root';\n", encoding="utf-8"
    )
    (package / "package.json").write_text(
        json.dumps(nested_mapping).replace("{suffix}", suffix), encoding="utf-8"
    )
    (tests / f"nested-helper.{suffix}").write_text(
        "export const trusted = 'nested';\n", encoding="utf-8"
    )
    test_path = PurePosixPath(f"packages/widget/tests/widget.test.{suffix}")
    test_source = f"import {{ trusted }} from {specifier!r};\n"
    test_source += (
        "test('widget works', () => expect(trusted).toBe('nested'));\n"
        if validator == "jest"
        else "import { test } from 'vitest';\ntest('widget works', () => { if (trusted !== 'nested') throw new Error('bad'); });\n"
    )
    (root / test_path).write_text(test_source, encoding="utf-8")
    if validator == "jest":
        (root / "jest.config.json").write_text("{}\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add conflicting nested package maps")
    digest_function = (
        jest_validator_config_digest if validator == "jest"
        else vitest_validator_config_digest
    )
    digest = digest_function(root, "HEAD", (test_path,))

    (root / f"tests/root-helper.{suffix}").write_text(
        "export const trusted = 'changed-root';\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate root mapped helper")
    assert digest_function(root, "HEAD", (test_path,)) == digest

    (tests / f"nested-helper.{suffix}").write_text(
        "export const trusted = 'changed-nested';\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate nested mapped helper")
    assert digest_function(root, "HEAD", (test_path,)) != digest


@pytest.mark.parametrize(
    "target",
    [
        {"node": "./tests/a.ts", "default": "./tests/b.ts"},
        {"default": "./tests/a.ts"},
    ],
)
def test_vitest_rejects_unsupported_package_mapping_conditions(
    tmp_path: Path, target: dict[str, str]
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "package.json").write_text(
        json.dumps({"imports": {"#fixture-helper": target}}),
        encoding="utf-8",
    )
    (root / "tests/a.ts").write_text("export {};\n", encoding="utf-8")
    (root / "tests/b.ts").write_text("export {};\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import '#fixture-helper';\nimport { test } from 'vitest';\ntest('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add ambiguous package mapping")

    with pytest.raises(ValueError, match="package mapping|condition"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


def test_jest_package_import_mapping_binds_exact_helper(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "package.json").write_text(
        json.dumps({"imports": {"#fixture-helper": "./tests/mapped.js"}}),
        encoding="utf-8",
    )
    (root / "jest.config.json").write_text("{}\n", encoding="utf-8")
    (root / "tests/mapped.js").write_text("export const trusted = true;\n", encoding="utf-8")
    (root / "tests/widget.test.js").write_text(
        "import { trusted } from '#fixture-helper';\n"
        "test('widget works', () => { expect(trusted).toBe(true); });\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add Jest package mapping")
    paths = (PurePosixPath("tests/widget.test.js"),)
    before = jest_validator_config_digest(root, "HEAD", paths)
    (root / "tests/mapped.js").write_text("export const trusted = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate Jest mapped support")

    assert jest_validator_config_digest(root, "HEAD", paths) != before


def test_vitest_result_fifo_drains_large_success_while_child_runs(
    tmp_path: Path,
) -> None:
    """A reporter larger than the kernel FIFO capacity still certifies."""
    root, commit = _repository(tmp_path)
    runner = _fake_vitest(tmp_path)
    runner.write_text(
        "import json, os\n"
        "payload = {'tests': [{'identity': 'tests/widget.test.ts::widget works', 'status': 'passed', 'failureMessages': []}], 'moduleErrors': 0, 'unhandledErrors': 0}\n"
        "os.write(198, json.dumps(payload).encode() + b' ' * (2 * 1024 * 1024))\n",
        encoding="utf-8",
    )

    _envelope, executions = _run(root, commit, commit, runner, timeout=3)

    assert executions[0].outcome is EvidenceOutcome.PASS


def test_vitest_result_fifo_overflow_fails_deterministically(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    runner = _fake_vitest(tmp_path)
    runner.write_text(
        "import os\nos.write(198, b'x' * (17 * 1024 * 1024))\n",
        encoding="utf-8",
    )

    _envelope, executions = _run(root, commit, commit, runner, timeout=3)

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "result transport exceeded" in executions[0].detail


def test_vitest_result_fifo_without_writer_is_distinct_collection_error(
    tmp_path: Path,
) -> None:
    root, commit = _repository(tmp_path)
    runner = _fake_vitest(tmp_path)
    runner.write_text("pass\n", encoding="utf-8")

    _envelope, executions = _run(root, commit, commit, runner)

    assert executions[0].outcome is EvidenceOutcome.COLLECTION_ERROR
    assert executions[0].detail == "Vitest reporter produced no result"


def test_vitest_sigabrt_reports_only_trusted_zero_cgroup_deltas(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A generic abort stays fail-closed and is not mislabeled as a limit breach."""
    root, _commit = _repository(tmp_path)
    result = SupervisedCompletedProcess(
        ["vitest"],
        -signal.SIGABRT,
        "candidate stdout must not be exposed",
        "candidate stderr must not be exposed",
        termination=SupervisorTermination(
            TerminationKind.SIGNAL,
            signal_number=signal.SIGABRT,
            resource_telemetry=CgroupResourceTelemetry(0, 0, 0),
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert execution.detail == (
        "Vitest infrastructure termination: reporter=missing; kind=signal; "
        "signal=SIGABRT; signal_number=6; cgroup_memory_oom_delta=0; "
        "cgroup_memory_oom_kill_delta=0; cgroup_pids_max_delta=0; "
        "diagnostic_sha256=a56506d06ba82ba55af2e5593dab5a2044555b5f75d8389f"
        "c90dd9679fe43f20"
    )
    assert "candidate stdout" not in execution.detail
    assert "candidate stderr" not in execution.detail
    assert identities == ()


def test_vitest_sandbox_error_reports_only_trusted_phases_and_hashed_diagnostic(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Candidate diagnostics cannot spoof structured infrastructure evidence."""
    root, _commit = _repository(tmp_path)
    diagnostic = "secret=candidate-value; trusted_failure_phases=result-handoff"
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "candidate says trusted_failure_phases=construction",
        diagnostic,
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(
                supervisor_module.InfrastructureFailurePhase.SCOPE_CLEANUP,
                supervisor_module.InfrastructureFailurePhase.MOUNT_CLEANUP,
            ),
            resource_telemetry=CgroupResourceTelemetry(0, 0, 0),
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert execution.detail == (
        "Vitest infrastructure termination: reporter=missing; kind=sandbox-error; "
        "exit_code=125; trusted_failure_phases=scope-cleanup,mount-cleanup; "
        "cgroup_memory_oom_delta=0; cgroup_memory_oom_kill_delta=0; "
        "cgroup_pids_max_delta=0; diagnostic_sha256="
        + hashlib.sha256(diagnostic.encode("utf-8")).hexdigest()
    )
    assert "candidate-value" not in execution.detail
    assert "trusted_failure_phases=construction" not in execution.detail
    assert "trusted_failure_phases=result-handoff" not in execution.detail
    assert not identities


def test_vitest_reports_typed_construction_reason_without_diagnostic_prose(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Trusted construction attribution supplements, never replaces, the hash."""
    root, _commit = _repository(tmp_path)
    diagnostic = "[Errno 24] Too many open files: /host/private/secret"
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        diagnostic,
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(supervisor_module.InfrastructureFailurePhase.CONSTRUCTION,),
            construction_substage=supervisor_module.ConstructionSubstage.STAGING,
            construction_reason=supervisor_module.ConstructionFailureReason.OS_ERROR,
            construction_errno=errno_module.EMFILE,
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.detail == (
        "Vitest infrastructure termination: reporter=missing; kind=sandbox-error; "
        "exit_code=125; trusted_failure_phases=construction; "
        "trusted_construction_substage=staging; "
        "trusted_construction_reason=os-error; trusted_construction_errno=EMFILE; "
        "diagnostic_sha256=" + hashlib.sha256(diagnostic.encode("utf-8")).hexdigest()
    )
    assert "Too many open files" not in execution.detail
    assert "/host/private/secret" not in execution.detail
    assert identities == ()


def test_vitest_formats_plan_os_error_without_code_or_path(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Plan-time filesystem faults expose only typed OS-error attribution."""
    root, _commit = _repository(tmp_path)
    diagnostic = "[Errno 24] proof read failed: /host/private/proof-token"
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        diagnostic,
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(supervisor_module.InfrastructureFailurePhase.CONSTRUCTION,),
            construction_substage=supervisor_module.ConstructionSubstage.PLAN,
            construction_reason=supervisor_module.ConstructionFailureReason.OS_ERROR,
            construction_errno=errno_module.EMFILE,
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert "trusted_construction_substage=plan" in execution.detail
    assert "trusted_construction_reason=os-error" in execution.detail
    assert "trusted_construction_errno=EMFILE" in execution.detail
    assert "trusted_plan_failure_code=" not in execution.detail
    assert "/host/private/proof-token" not in execution.detail
    assert identities == ()


def test_vitest_reports_exact_trusted_plan_validation_code_without_paths(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A plan code identifies a dynamic collision without exposing its target."""
    root, _commit = _repository(tmp_path)
    diagnostic = "protected sandbox has conflicting bindings for /host/private/node"
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        diagnostic,
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(supervisor_module.InfrastructureFailurePhase.CONSTRUCTION,),
            construction_substage=supervisor_module.ConstructionSubstage.PLAN,
            construction_reason=supervisor_module.ConstructionFailureReason.VALIDATION,
            plan_failure_code=supervisor_module.SandboxPlanFailureCode.BINDING_RESOLUTION,
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.detail == (
        "Vitest infrastructure termination: reporter=missing; kind=sandbox-error; "
        "exit_code=125; trusted_failure_phases=construction; "
        "trusted_construction_substage=plan; "
        "trusted_construction_reason=validation; "
        "trusted_plan_failure_code=binding-resolution; diagnostic_sha256="
        + hashlib.sha256(diagnostic.encode("utf-8")).hexdigest()
    )
    assert "/host/private/node" not in execution.detail
    assert identities == ()


def test_vitest_rejects_untyped_construction_attribution_from_untrusted_strings(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Only enum-backed supervisor fields can become structured runner detail."""
    root, _commit = _repository(tmp_path)
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        "candidate says staging EMFILE",
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(supervisor_module.InfrastructureFailurePhase.CONSTRUCTION,),
            construction_substage="staging",  # type: ignore[arg-type]
            construction_reason="os-error",  # type: ignore[arg-type]
            construction_errno="EMFILE",
            plan_failure_code=SimpleNamespace(value="binding-resolution"),
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert "trusted_construction_substage=unknown" in execution.detail
    assert "trusted_construction_reason=unknown" in execution.detail
    assert "trusted_construction_errno=" not in execution.detail
    assert "trusted_plan_failure_code=" not in execution.detail
    assert "candidate says staging EMFILE" not in execution.detail
    assert identities == ()


def test_vitest_rejects_forged_or_contradictory_construction_errno(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Runner details retain an errno only for exact trusted OS-error evidence."""
    class ForgedInt(int):
        """Integer subclass that must not render as trusted errno evidence."""

        pass

    root, _commit = _repository(tmp_path)
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        "candidate diagnostic",
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(supervisor_module.InfrastructureFailurePhase.CONSTRUCTION,),
            construction_substage=supervisor_module.ConstructionSubstage.PLAN,
            construction_reason=supervisor_module.ConstructionFailureReason.VALIDATION,
            construction_errno=ForgedInt(errno_module.EMFILE),
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert "trusted_construction_reason=validation" in execution.detail
    assert "trusted_construction_errno=" not in execution.detail
    assert identities == ()


def test_vitest_sandbox_error_defaults_malformed_phase_to_unknown(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Malformed fake termination data cannot become trusted runner detail."""
    root, _commit = _repository(tmp_path)
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        "trusted_failure_phases=candidate-spoofed",
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=("candidate-spoofed",),  # type: ignore[arg-type]
            scope_setup_subreason="cgroup-configure",  # type: ignore[arg-type]
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert "trusted_failure_phases=unknown" in execution.detail
    assert "candidate-spoofed" not in execution.detail
    assert "trusted_scope_setup_subreason" not in execution.detail
    assert not identities


def test_vitest_scope_setup_subreason_is_trusted_and_allowlisted(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Hosted diagnostics expose a bounded trusted setup category, never prose."""
    root, _commit = _repository(tmp_path)
    result = SupervisedCompletedProcess(
        ["vitest"], 125, "", "secret path=/run/private",
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(
                supervisor_module.InfrastructureFailurePhase.SCOPE_SETUP,
            ),
            scope_setup_subreason=(
                supervisor_module.ScopeSetupFailureReason.CGROUP_CONFIGURE
            ),
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root, (PurePosixPath("tests/widget.test.ts"),), 30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert "trusted_scope_setup_subreason=cgroup-configure" in execution.detail
    assert "private" not in execution.detail
    assert not identities


def test_vitest_valid_reporter_cannot_hide_cleanup_sandbox_error(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A valid candidate report cannot outrank trusted late-cleanup evidence."""
    root, _commit = _repository(tmp_path)
    diagnostic = "candidate-controlled cleanup diagnostic"
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        diagnostic,
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(
                supervisor_module.InfrastructureFailurePhase.SCOPE_CLEANUP,
                supervisor_module.InfrastructureFailurePhase.MOUNT_CLEANUP,
            ),
        ),
    )

    def supervised(_command, *, result_write_fd, **_kwargs):
        os.write(
            result_write_fd,
            json.dumps({
                "tests": [{"identity": IDENTITY, "status": "passed"}],
            }).encode("utf-8"),
        )
        return result, False

    monkeypatch.setattr("pdd.sync_core.runner.run_supervised", supervised)

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert execution.detail == (
        "Vitest infrastructure termination: reporter=missing; kind=sandbox-error; "
        "exit_code=125; trusted_failure_phases=scope-cleanup,mount-cleanup; "
        "diagnostic_sha256="
        + hashlib.sha256(diagnostic.encode("utf-8")).hexdigest()
    )
    assert diagnostic not in execution.detail
    assert "Vitest reported failed protected tests" not in execution.detail
    assert not identities


def test_vitest_survivor_cannot_hide_process_cleanup_sandbox_error(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Survivor telemetry cannot replace its trusted sandbox failure phase."""
    root, _commit = _repository(tmp_path)
    diagnostic = "candidate-controlled process cleanup diagnostic"
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        diagnostic,
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(
                supervisor_module.InfrastructureFailurePhase.PROCESS_CLEANUP,
            ),
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, True),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert execution.detail == (
        "Vitest infrastructure termination: reporter=missing; kind=sandbox-error; "
        "exit_code=125; trusted_failure_phases=process-cleanup; diagnostic_sha256="
        + hashlib.sha256(diagnostic.encode("utf-8")).hexdigest()
    )
    assert diagnostic not in execution.detail
    assert "surviving process-group descendant" not in execution.detail
    assert not identities


def test_vitest_transport_overflow_cannot_hide_output_drain_sandbox_error(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Transport overflow cannot replace trusted sandbox termination evidence."""
    root, _commit = _repository(tmp_path)
    diagnostic = "candidate-controlled output drain diagnostic"
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        diagnostic,
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(
                supervisor_module.InfrastructureFailurePhase.OUTPUT_DRAIN,
            ),
        ),
    )

    def overflow(_read_fd, _finished, drained):
        drained.update({"overflow": True, "data": b""})

    monkeypatch.setattr(runner_module, "_drain_result_pipe", overflow)
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert execution.detail == (
        "Vitest infrastructure termination: reporter=missing; kind=sandbox-error; "
        "exit_code=125; trusted_failure_phases=output-drain; diagnostic_sha256="
        + hashlib.sha256(diagnostic.encode("utf-8")).hexdigest()
    )
    assert diagnostic not in execution.detail
    assert "result transport exceeded byte limit" not in execution.detail
    assert not identities


@pytest.mark.parametrize(
    ("returncode", "outcome"),
    [(126, EvidenceOutcome.ERROR), (127, EvidenceOutcome.ERROR), (1, EvidenceOutcome.ERROR)],
)
def test_vitest_exit_failure_precedes_empty_fifo_collection_error(
    tmp_path: Path, returncode: int, outcome: EvidenceOutcome
) -> None:
    root, commit = _repository(tmp_path)
    runner = _fake_vitest(tmp_path)
    runner.write_text(f"import sys\nsys.exit({returncode})\n", encoding="utf-8")

    _envelope, executions = _run(root, commit, commit, runner)

    assert executions[0].outcome is outcome
    if returncode == 1:
        assert executions[0].detail == (
            "Vitest infrastructure termination: reporter=missing; kind=exit; "
            "exit_code=1"
        )


@pytest.mark.parametrize(
    ("platform", "worker_wasm_guard"),
    [("linux", "--execArgv=--disable-wasm-trap-handler"), ("darwin", None)],
)
def test_vitest_omits_unproven_worker_caps_without_relaxing_limits(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    platform: str,
    worker_wasm_guard: str | None,
) -> None:
    """Discredited worker caps must not weaken the protected Vitest boundary."""
    root, _commit = _repository(tmp_path)
    config = _runner_config(tmp_path, _fake_vitest(tmp_path))
    observed: list[list[str]] = []
    observed_environments: list[dict[str, str]] = []
    proofs = []
    readable_roots = []
    preload_sources: list[str] = []
    reporter_sources: list[str] = []
    helper_identities: list[tuple[int, int]] = []
    observed_limits: list[SupervisorLimits] = []
    observed_timeouts: list[int] = []
    observed_result_fds: list[int] = []

    def capture(
        command, *, result_write_fd, result_fd, env, limits, timeout, **kwargs
    ):
        observed.append(command)
        observed_environments.append(env)
        proofs.append(kwargs["immutable_binding_proofs"])
        readable_roots.append(kwargs["readable_roots"])
        preload = next(
            Path(item.removeprefix("--execArgv=--require="))
            for item in command
            if item.startswith("--execArgv=--require=")
        )
        helper_read_fd, helper_write_fd = os.pipe()
        try:
            helper = os.fstat(helper_write_fd)
            kwargs["anonymous_observation_ready"](
                helper.st_dev, helper.st_ino
            )
            helper_identities.append((helper.st_dev, helper.st_ino))
        finally:
            os.close(helper_read_fd)
            os.close(helper_write_fd)
        preload_sources.append(preload.read_text(encoding="utf-8"))
        reporter = next(
            Path(item.removeprefix("--reporter="))
            for item in command
            if item.startswith("--reporter=")
        )
        reporter_sources.append(reporter.read_text(encoding="utf-8"))
        observed_limits.append(limits)
        observed_timeouts.append(timeout)
        observed_result_fds.append(result_fd)
        assert stat.S_ISFIFO(os.fstat(result_write_fd).st_mode)
        os.write(
            result_write_fd,
            json.dumps({
                "tests": [{
                    "identity": IDENTITY,
                    "status": "passed",
                    "failureMessages": [],
                }],
                "moduleErrors": 0,
                "unhandledErrors": 0,
            }).encode(),
        )
        return subprocess.CompletedProcess(command, 0, "", ""), False

    monkeypatch.setenv("UV_THREADPOOL_SIZE", "64")
    monkeypatch.setattr(runner_module.sys, "platform", platform)
    monkeypatch.setattr("pdd.sync_core.runner.run_supervised", capture)
    monkeypatch.setattr(
        "pdd.sync_core.runner.released_runtime_closure_paths", lambda: ()
    )
    execution, _identities = _run_vitest(
        root,
        (
            PurePosixPath("tests/widget.test.ts"),
            PurePosixPath("--maxWorkers=64"),
            PurePosixPath("--"),
            PurePosixPath("--testNamePattern=escape"),
        ),
        2,
        config,
    )

    assert execution.outcome is EvidenceOutcome.PASS
    allowed_vitest_constants = {
        "_VITEST_SUPERVISOR_LIMITS",
        "_VITEST_PROGRESS_MAX_RECORDS",
        "_VITEST_PROGRESS_PREFIX",
        "_VITEST_RESULT_PREFIX",
    }
    assert "--pool=forks" in observed[0]
    if worker_wasm_guard is None:
        assert "--execArgv=--disable-wasm-trap-handler" not in observed[0]
    else:
        assert worker_wasm_guard in observed[0]
    assert not {
        name
        for name in vars(runner_module)
        if name.startswith("_VITEST_") and name not in allowed_vitest_constants
    }
    assert not any(
        value.startswith(("--maxWorkers", "--retry", "--v8-pool-size"))
        for command in observed
        for value in command
    )
    assert all("UV_THREADPOOL_SIZE" not in environment for environment in observed_environments)
    assert all(any(value.startswith("--reporter=") for value in command) for command in observed)
    assert len(observed) == 1
    assert observed_result_fds == [198]
    assert observed_timeouts == [2]
    assert observed_limits == [
        SupervisorLimits(max_memory_bytes=4 * 1024 * 1024 * 1024),
    ]
    command = observed[0]
    if platform == "linux":
        assert command[1] == "--disable-wasm-trap-handler"
    run_index = command.index("run")
    assert command[run_index:run_index + 4] == [
        "run",
        f"--config={root / '.pdd-vitest.config.mjs'}",
        "--configLoader=runner",
        next(value for value in command if value.startswith("--reporter=")),
    ]
    assert command[-4:] == [
        "./tests/widget.test.ts",
        "./--maxWorkers=64",
        "./--",
        "./--testNamePattern=escape",
    ]
    assert "UV_THREADPOOL_SIZE" not in runner_module._playwright_environment(tmp_path, None)
    assert "--pool=forks" in command
    if worker_wasm_guard is not None:
        worker_wasm_index = command.index(worker_wasm_guard)
    worker_preload = next(
        item.removeprefix("--execArgv=--require=") for item in command
        if item.startswith("--execArgv=--require=")
    )
    if worker_wasm_guard is not None:
        assert command[worker_wasm_index + 1] == f"--execArgv=--require={worker_preload}"
    assert Path(worker_preload).name == "worker-preload.cjs"
    preload_source = preload_sources[0]
    observation_device, observation_inode = helper_identities[0]
    assert "const RESULT_FD = 198" in preload_source
    assert f"const EXPECTED_DEVICE = {observation_device}n" in preload_source
    assert f"const EXPECTED_INODE = {observation_inode}n" in preload_source
    assert "process.env.PDD_FRAMEWORK_OBSERVATION_DEVICE" not in preload_source
    assert "process.env.PDD_FRAMEWORK_OBSERVATION_INODE" not in preload_source
    assert "const EXPECTED_DEVICE = primary.dev" not in preload_source
    assert "const EXPECTED_INODE = primary.ino" not in preload_source
    assert "trusted Vitest result descriptor identity mismatch" in preload_source
    assert "fs.closeSync(fd)" in preload_source
    assert "new Set(descriptorTable())" in preload_source
    reporter_source = reporter_sources[0]
    assert f"const EXPECTED_DEVICE = {observation_device}n" in reporter_source
    assert f"const EXPECTED_INODE = {observation_inode}n" in reporter_source
    assert "sealResultAuthority(RESULT_FD, EXPECTED_DEVICE, EXPECTED_INODE)" in (
        reporter_source
    )
    assert "PDD_FRAMEWORK_COORDINATOR_NONDUMPABLE = '1'" in reporter_source
    assert Path(worker_preload) in readable_roots[0]
    assert any(path.name == runner_module.COORDINATOR_ADDON_NAME for path in readable_roots[0])
    assert proofs[0][0].descriptor_identity == _load_vitest_toolchain_descriptor(
        root, config
    ).identity
    assert observed_limits == [
        SupervisorLimits(
            max_memory_bytes=4 * 1024 * 1024 * 1024,
        )
    ]
    assert observed_timeouts == [2]
    assert any(value.startswith("--reporter=") for value in observed[0])
    assert observed_limits[0].max_processes == SupervisorLimits().max_processes
    assert observed_limits[0].max_output_bytes == SupervisorLimits().max_output_bytes
    assert observed_limits[0].max_cpu_seconds == SupervisorLimits().max_cpu_seconds
    assert observed_limits[0].max_writable_bytes == SupervisorLimits().max_writable_bytes
    assert SupervisorLimits().max_memory_bytes == 2 * 1024 * 1024 * 1024
    assert (
        observed_limits[0].max_virtual_memory_bytes
        == SupervisorLimits().max_virtual_memory_bytes
    )


def test_vitest_linux_wasm_guard_remains_fake_launcher_compatible(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The portable fake launcher accepts the retained Linux wasm guard."""
    root, _commit = _repository(tmp_path)
    monkeypatch.setattr(runner_module.sys, "platform", "linux")
    monkeypatch.setattr(
        "pdd.sync_core.runner.released_runtime_closure_paths", lambda: ()
    )
    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        2,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.outcome is EvidenceOutcome.PASS
    assert identities == (IDENTITY,)


def test_mixed_adapter_identities_survive_manifest_removal_and_round_trip(
    tmp_path: Path,
) -> None:
    """Signed adapter content identities are independent of temporary manifests."""
    root, commit = _repository(tmp_path)
    (root / "tests/widget.test.js").write_text("test('widget works', () => {});\n", encoding="utf-8")
    (root / "jest.config.json").write_text("{}\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add mixed protected adapters")
    commit = _git(root, "rev-parse", "HEAD")
    fake_jest = tmp_path / "fake_jest.py"
    fake_jest.write_text(
        "import json, os\n"
        "os.write(198, json.dumps({'tests':[{'identity':'tests/widget.test.js::widget works','status':'passed'}]}).encode())\n",
        encoding="utf-8",
    )
    vitest = _fake_vitest(tmp_path)
    config = replace(
        _runner_config(tmp_path, vitest),
        jest_command=(sys.executable, str(fake_jest)),
    )
    vitest_paths = (PurePosixPath("tests/widget.test.ts"),)
    jest_paths = (PurePosixPath("tests/widget.test.js"),)
    profile = VerificationProfile(
        UNIT,
        (
            VerificationObligation(
                "jest", "test", "jest", jest_validator_config_digest(root, commit, jest_paths),
                ("REQ-1",), jest_paths,
            ),
            VerificationObligation(
                "vitest", "test", "vitest", vitest_validator_config_digest(root, commit, vitest_paths),
                ("REQ-1",), vitest_paths,
            ),
        ),
        ("REQ-1",),
        "mixed-profile",
    )
    envelope, executions = run_profile(
        root, profile, RunBinding("snapshot-v1", commit, commit),
        AttestationIssue(AttestationSigner("trusted-ci", b"v" * 32), "id", "nonce", datetime(2026, 7, 10, tzinfo=timezone.utc)),
        config=config,
    )

    assert all(item.outcome is EvidenceOutcome.PASS for item in executions)
    assert {name for name, _identity in envelope.binding.adapter_identities} == {"jest", "vitest"}
    config.vitest_toolchain_manifest.unlink()
    restored = decode_attestation(attestation_payload(envelope))
    assert restored.binding.adapter_identities == envelope.binding.adapter_identities
    decoded = subprocess.run(
        [
            sys.executable,
            "-c",
            "import json,sys; from pdd.sync_core.evidence_store import decode_attestation; "
            "print(json.dumps(decode_attestation(json.load(sys.stdin)).binding.adapter_identities))",
        ],
        input=json.dumps(attestation_payload(envelope)),
        capture_output=True,
        text=True,
        check=True,
    )
    assert json.loads(decoded.stdout) == [list(item) for item in envelope.binding.adapter_identities]
    assert runner_identity_digest(
        profile,
        root=root,
        ref=commit,
        config=RunnerConfig(adapter_identities=restored.binding.adapter_identities),
    ) == envelope.binding.runner_digest
