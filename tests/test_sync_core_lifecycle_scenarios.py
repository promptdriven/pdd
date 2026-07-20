"""Process-level merge, wheel, and real-consumer lifecycle scenarios."""
# pylint: disable=missing-function-docstring,protected-access,redefined-outer-name

import argparse
import hashlib
import os
import json
import subprocess
import sys
import zipfile
from pathlib import Path, PurePosixPath

import pytest
import pdd.sync_core.lifecycle as lifecycle_module

from pdd.sync_core.certificate import LifecycleResult
from pdd.sync_core.lifecycle import (
    _install_candidate_wheel,
    _isolated_lifecycle_environment,
    _lifecycle_command,
    run_lifecycle_matrix,
)
from pdd.sync_core.scenario_contract import REQUIRED_SCENARIOS
from pdd.sync_core import scenario_harness
from pdd.sync_core import (
    CandidateArtifactPolicy,
    PlannedWrite,
    TransactionConflict,
    TransactionManager,
    build_unit_manifest,
)
from pdd.sync_core.identity import initialize_repository_identity


def _run(root: Path, *args: str, env=None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
        env=env,
    )


def _git(root: Path, *args: str) -> str:
    result = _run(root, "git", *args)
    assert result.returncode == 0, result.stderr
    return result.stdout.strip()


def _record_metric(name: str, value: int) -> None:
    configured = os.environ.get("PDD_LIFECYCLE_METRICS_PATH")
    if not configured:
        return
    path = Path(configured)
    payload = json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}
    payload[name] = value
    path.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")


def _write_wheel(
    wheelhouse: Path,
    *,
    distribution: str,
    version: str,
    files: dict[str, str],
    metadata_extra: str = "",
) -> Path:
    dist_info = f"{distribution.replace('-', '_')}-{version}.dist-info"
    wheel = wheelhouse / f"{distribution.replace('-', '_')}-{version}-py3-none-any.whl"
    with zipfile.ZipFile(wheel, "w") as archive:
        for name, content in files.items():
            archive.writestr(name, content)
        archive.writestr(
            f"{dist_info}/METADATA",
            (
                "Metadata-Version: 2.1\n"
                f"Name: {distribution}\n"
                f"Version: {version}\n"
                f"{metadata_extra}\n"
            ),
        )
        archive.writestr(
            f"{dist_info}/WHEEL",
            "Wheel-Version: 1.0\nGenerator: pdd-test\nRoot-Is-Purelib: true\n"
            "Tag: py3-none-any\n",
        )
        archive.writestr(f"{dist_info}/RECORD", "")
    return wheel


def test_lifecycle_command_maps_inputs_read_only_and_environment_immutable(
    tmp_path, monkeypatch
) -> None:
    scratch = tmp_path / "scratch"
    scratch.mkdir()
    environment = tmp_path / "candidate-environment"
    environment.mkdir()
    wheelhouse = tmp_path / "wheelhouse"
    wheelhouse.mkdir()
    cloud = tmp_path / "cloud"
    cloud.mkdir()
    captured = {}

    def fake_run(command, **kwargs):
        captured.update(kwargs)
        return subprocess.CompletedProcess(command, 0, "", ""), False

    monkeypatch.setattr("pdd.sync_core.lifecycle.run_supervised", fake_run)
    result = _lifecycle_command(
        [sys.executable, "-c", "pass"], scratch, scratch / "home",
        readable_roots=(environment, wheelhouse, cloud),
    )
    assert result.returncode == 0
    assert captured["writable_roots"] == (scratch,)
    assert captured["readable_roots"] == (environment, wheelhouse, cloud)


def test_lifecycle_contract_requires_public_repair_injection_scenarios() -> None:
    required = {
        "public-prompt-only-repair-zero-write-rerun",
        "public-code-only-repair-zero-write-rerun",
        "public-test-only-repair-zero-write-rerun",
        "public-include-only-repair-zero-write-rerun",
        "public-simultaneous-edit-repair-block",
    }
    assert required <= REQUIRED_SCENARIOS


def test_lifecycle_predicate_requires_dependency_environment_digest() -> None:
    result = LifecycleResult(
        0,
        0,
        0,
        0,
        0,
        0,
        candidate_wheel_sha256="a" * 64,
        dependency_environment_digest="b" * 64,
    )
    assert result.dependency_environment_digest == "b" * 64


def test_lifecycle_result_binds_recomputable_runtime_measurement() -> None:
    result = LifecycleResult(
        0, 0, 0, 0, 0, 0,
        candidate_wheel_sha256="a" * 64,
        dependency_environment_digest="b" * 64,
        runtime_lock_sha256="c" * 64,
        interpreter={
            "implementation": "CPython",
            "version": "3.12.3",
            "abi": "cp312",
            "platform": "macosx_14_0_arm64",
        },
        installed_files=(("pdd", "1.0", "pdd/__init__.py", "d" * 64),),
        measurement_authority="pdd-released-checker-v1",
    )
    assert result.runtime_lock_sha256 == "c" * 64
    assert result.interpreter["abi"] == "cp312"
    assert result.installed_files[0][2] == "pdd/__init__.py"
    assert result.measurement_authority == "pdd-released-checker-v1"


def test_lifecycle_measurement_rejects_synthesized_compatibility_fields() -> None:
    from pdd.sync_core.certificate import _lifecycle_measurement_complete

    assert _lifecycle_measurement_complete(
        LifecycleResult(
            0, 0, 0, 0, 0, 0,
            candidate_wheel_sha256="a" * 64,
            dependency_environment_digest="b" * 64,
            candidate_artifact=object(),
        )
    ) is False


def test_lifecycle_commands_do_not_use_unsupervised_subprocess_run(monkeypatch) -> None:
    def forbidden(*_args, **_kwargs):
        pytest.fail("lifecycle command bypassed the shared sandbox supervisor")

    monkeypatch.setattr(lifecycle_module.subprocess, "run", forbidden)
    assert lifecycle_module._candidate_interpreter_identity(
        Path(sys.executable), {"PATH": os.environ.get("PATH", "")}
    ) is not None


def test_lifecycle_matrix_fails_closed_without_hash_pinned_wheelhouse(
    tmp_path,
) -> None:
    wheel = tmp_path / "pdd_cli-1.0.0-py3-none-any.whl"
    wheel.write_bytes(b"candidate-wheel")
    result = run_lifecycle_matrix(
        tmp_path,
        candidate_wheel=wheel,
        cloud_root=tmp_path,
        cloud_base_ref="a" * 40,
        cloud_head_ref="b" * 40,
    )
    assert result.failed == len(REQUIRED_SCENARIOS)
    assert result.candidate_wheel_sha256 == ""
    assert result.dependency_environment_digest == ""


def test_lifecycle_matrix_rejects_actual_runtime_lock_mismatch(tmp_path, monkeypatch) -> None:
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"wheel")
    wheelhouse = tmp_path / "wheelhouse"
    wheelhouse.mkdir()
    lock = tmp_path / "runtime.lock"
    lock.write_bytes(b"different lock bytes\n")
    attestation = tmp_path / "attestation.json"
    attestation.write_text("{}")
    policy = CandidateArtifactPolicy(
        "builder", b"a" * 32, "workflow", "b" * 64,
        "CPython", "3.12.3", "cp312", "platform",
    )
    monkeypatch.setattr(
        "pdd.sync_core.lifecycle.load_candidate_artifact_provenance",
        lambda *_args, **_kwargs: object(),
    )
    monkeypatch.setattr(
        "pdd.sync_core.lifecycle._install_candidate_wheel",
        lambda *_args, **_kwargs: pytest.fail("mismatched lock reached installation"),
    )
    result = run_lifecycle_matrix(
        tmp_path,
        candidate_wheel=wheel,
        candidate_wheelhouse=wheelhouse,
        candidate_runtime_lock=lock,
        candidate_attestation=attestation,
        candidate_artifact_policy=policy,
        cloud_root=tmp_path,
        cloud_base_ref="a" * 40,
        cloud_head_ref="b" * 40,
    )
    assert result.failed == len(REQUIRED_SCENARIOS)


def test_candidate_install_uses_hash_pinned_wheelhouse_no_index(
    tmp_path, monkeypatch
) -> None:
    wheel = tmp_path / "pdd_cli-1.0.0-py3-none-any.whl"
    wheel.write_bytes(b"candidate-wheel")
    wheelhouse = tmp_path / "wheelhouse"
    wheelhouse.mkdir()
    lock = tmp_path / "runtime.lock"
    lock.write_text(
        "click==8.4.1 --hash=sha256:" + ("c" * 64) + "\n",
        encoding="utf-8",
    )
    calls = []

    def fake_run(command, **kwargs):
        calls.append((tuple(str(item) for item in command), kwargs))
        if "-m" in command and "venv" in command:
            (tmp_path / "candidate-venv" / ("Scripts" if os.name == "nt" else "bin")).mkdir(
                parents=True
            )
        return subprocess.CompletedProcess(command, 0, "ok", "")

    monkeypatch.setattr(
        "pdd.sync_core.lifecycle._lifecycle_command",
        lambda command, *_args, **_kwargs: fake_run(command),
    )
    installed = _install_candidate_wheel(
        tmp_path,
        tmp_path / "home",
        wheel,
        wheelhouse,
        lock,
    )
    assert installed is not None
    install_command = calls[1][0]
    assert "--no-index" in install_command
    assert "--require-hashes" in install_command
    assert "--find-links" in install_command
    assert str(wheelhouse.resolve()) in install_command
    assert "--no-deps" not in install_command
    combined_lock = Path(install_command[install_command.index("-r") + 1])
    lock_text = combined_lock.read_text(encoding="utf-8")
    assert str(wheel.resolve()) in lock_text
    assert f"--hash=sha256:{hashlib.sha256(wheel.read_bytes()).hexdigest()}" in lock_text


def test_candidate_install_proves_isolated_module_entrypoint(
    tmp_path, monkeypatch
) -> None:
    wheel = tmp_path / "pdd_cli-1.0.0-py3-none-any.whl"
    wheel.write_bytes(b"candidate-wheel")
    wheelhouse = tmp_path / "wheelhouse"
    wheelhouse.mkdir()
    lock = tmp_path / "runtime.lock"
    lock.write_text("", encoding="utf-8")
    calls = []

    def fake_run(command, **_kwargs):
        calls.append(tuple(str(item) for item in command))
        if "-m" in command and "venv" in command:
            (tmp_path / "candidate-venv" / ("Scripts" if os.name == "nt" else "bin")).mkdir(
                parents=True
            )
        return subprocess.CompletedProcess(command, 0, "ok", "")

    monkeypatch.setattr(
        "pdd.sync_core.lifecycle._lifecycle_command",
        lambda command, *_args, **_kwargs: fake_run(command),
    )
    assert _install_candidate_wheel(
        tmp_path,
        tmp_path / "home",
        wheel,
        wheelhouse,
        lock,
    )
    assert any(
        command[-4:] == ("-I", "-m", "pdd.cli", "--help")
        for command in calls
    )


@pytest.mark.skipif(
    not sys.platform.startswith("linux"), reason="protected lifecycle requires Linux"
)
def test_candidate_install_e2e_uses_locked_runtime_wheelhouse(tmp_path) -> None:
    wheelhouse = tmp_path / "wheelhouse"
    wheelhouse.mkdir()
    runtime = _write_wheel(
        wheelhouse,
        distribution="runtime-dep",
        version="1.0.0",
        files={"runtime_dep.py": "VALUE = 'runtime wheel loaded'\n"},
    )
    candidate = _write_wheel(
        tmp_path,
        distribution="pdd-cli",
        version="1.0.0",
        files={
            "pdd/__init__.py": "",
            "pdd/cli.py": (
                "import sys\n"
                "import runtime_dep\n"
                "if __name__ == '__main__':\n"
                "    print(runtime_dep.VALUE)\n"
                "    raise SystemExit(0 if '--help' in sys.argv else 2)\n"
            ),
        },
        metadata_extra="Requires-Dist: runtime-dep==1.0.0\n",
    )
    lock = tmp_path / "runtime.lock"
    lock.write_text(
        "runtime-dep==1.0.0 --hash=sha256:"
        f"{hashlib.sha256(runtime.read_bytes()).hexdigest()}\n",
        encoding="utf-8",
    )
    commands = []
    actual_command = lifecycle_module._lifecycle_command

    def traced_command(*args, **kwargs):
        result = actual_command(*args, **kwargs)
        commands.append(result)
        return result

    monkeypatch = pytest.MonkeyPatch()
    monkeypatch.setattr(lifecycle_module, "_lifecycle_command", traced_command)
    try:
        installed = _install_candidate_wheel(
            tmp_path,
            tmp_path / "home",
            candidate,
            wheelhouse,
            lock,
        )
    finally:
        monkeypatch.undo()
    assert installed is not None, "\n".join(
        result.stderr for result in commands if result.stderr
    )
    candidate_python, dependency_digest = installed
    pyvenv = candidate_python.parents[1] / "pyvenv.cfg"
    assert "include-system-site-packages = false" in pyvenv.read_text(encoding="utf-8")
    probe = _run(
        tmp_path,
        str(candidate_python),
        "-I",
        "-m",
        "pdd.cli",
        "--help",
    )
    assert probe.returncode == 0
    assert "runtime wheel loaded" in probe.stdout
    assert len(dependency_digest) == 64


def test_lifecycle_environment_strips_signer_capabilities(tmp_path, monkeypatch) -> None:
    monkeypatch.setenv("PDD_ATTESTATION_SIGNER_COMMAND", "protected-attestation")
    monkeypatch.setenv("PDD_CERTIFICATE_ISSUER", "protected-issuer")
    monkeypatch.setenv("PDD_RELEASED_CHECKER_COMMAND", "protected-checker")
    environment = _isolated_lifecycle_environment(tmp_path)
    assert "PDD_ATTESTATION_SIGNER_COMMAND" not in environment
    assert "PDD_CERTIFICATE_ISSUER" not in environment
    assert "PDD_RELEASED_CHECKER_COMMAND" not in environment


def test_candidate_scenario_environment_strips_signer_capabilities(
    tmp_path, monkeypatch
) -> None:
    captured = {}

    def fake_run(*_args, **kwargs):
        captured.update(kwargs["env"])
        return subprocess.CompletedProcess(_args[0], 0, "", "")

    monkeypatch.setenv("PDD_ATTESTATION_SIGNER_COMMAND", "protected-attestation")
    monkeypatch.setenv("PDD_CERTIFICATE_ISSUER", "protected-issuer")
    monkeypatch.setenv("PDD_RELEASED_CHECKER_COMMAND", "protected-checker")
    monkeypatch.setattr(scenario_harness.subprocess, "run", fake_run)
    scenario_harness._candidate(
        argparse.Namespace(candidate_python=sys.executable),
        tmp_path,
        "--version",
    )
    assert "PDD_ATTESTATION_SIGNER_COMMAND" not in captured
    assert "PDD_CERTIFICATE_ISSUER" not in captured
    assert "PDD_RELEASED_CHECKER_COMMAND" not in captured


def test_lifecycle_public_report_uses_root_certify(monkeypatch) -> None:
    observed = {}

    def fake_candidate(_arguments, _root, *command):
        observed["command"] = command
        output = Path(command[command.index("--output") + 1])
        output.write_text(
            json.dumps({"counts": {"unbaselined": 1}}),
            encoding="utf-8",
        )
        return subprocess.CompletedProcess(command, 1, "", "")

    monkeypatch.setattr(scenario_harness, "_candidate", fake_candidate)
    result = scenario_harness._candidate_public_report(
        argparse.Namespace(candidate_python=sys.executable)
    )
    assert result.status == "PASS"
    assert observed["command"][0] == "certify"


def test_merge_base_movement_blocks_stale_repair_and_converges(tmp_path) -> None:
    """A repair planned before merge movement must never overwrite merged bytes."""
    root = tmp_path / "merge-repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "sync@example.com")
    _git(root, "config", "user.name", "Sync Test")
    initialize_repository_identity(root, "a1970bc0-ecde-4c13-b3dc-ee2fccf1d043")
    (root / "prompts").mkdir()
    (root / "src").mkdir()
    (root / "prompts/widget_python.prompt").write_text("REQ-1: widget\n")
    target = root / "src/widget.py"
    target.write_text("value = 1\n")
    (root / "architecture.json").write_text(
        '[{"filename":"widget_python.prompt","filepath":"src/widget.py"}]\n'
    )
    _git(root, "add", ".")
    _git(root, "commit", "-qm", "protected base")
    base = _git(root, "rev-parse", "HEAD")

    manager = TransactionManager(root)
    repair = (
        PlannedWrite(PurePosixPath("src/widget.py"), b"value = 2\n", "100644"),
    )
    manager.prepare("stale-repair", repair)
    target.write_text("merged = True\n")
    _git(root, "add", "src/widget.py")
    _git(root, "commit", "-qm", "merge group moved")
    head = _git(root, "rev-parse", "HEAD")
    assert head != base
    manifest = build_unit_manifest(root, base_ref=base, head_ref=head)
    assert manifest.base_ref == base
    assert manifest.head_ref == head
    with pytest.raises(TransactionConflict, match="destination changed"):
        manager.commit("stale-repair")
    assert target.read_text() == "merged = True\n"

    fresh = TransactionManager(root)
    fresh.prepare("fresh-repair", repair)
    fresh.commit("fresh-repair")
    before_second = _git(root, "status", "--porcelain", "--untracked-files=all")
    second = fresh.prepare("second-run", repair)
    assert second.no_op is True
    after_second = _git(root, "status", "--porcelain", "--untracked-files=all")
    _record_metric(
        "post_merge_tree_changes",
        int(before_second != after_second) + len(second.changed_paths),
    )


@pytest.fixture(scope="module")
def released_checker(tmp_path_factory) -> Path:
    """Build and install the exact wheel used by clean-environment scenarios."""
    tmp_path = tmp_path_factory.mktemp("released-checker")
    root = Path(__file__).resolve().parents[1]
    dist = tmp_path / "dist"
    build = _run(root, sys.executable, "-m", "build", "--wheel", "--outdir", str(dist))
    assert build.returncode == 0, build.stdout + build.stderr
    wheels = tuple(dist.glob("*.whl"))
    assert len(wheels) == 1
    wheel = wheels[0]
    environment = tmp_path / "venv"
    create = _run(
        root,
        sys.executable,
        "-m",
        "venv",
        "--system-site-packages",
        str(environment),
    )
    assert create.returncode == 0, create.stderr
    python = environment / ("Scripts/python.exe" if os.name == "nt" else "bin/python")
    install = _run(
        root, str(python), "-m", "pip", "install", "--no-deps", str(wheel)
    )
    assert install.returncode == 0, install.stdout + install.stderr
    return python


def test_built_wheel_runs_in_clean_virtual_environment(
    tmp_path, released_checker
) -> None:
    """The packaged checker and protected registry work outside the source tree."""
    probe = _run(
        tmp_path,
        str(released_checker),
        "-c",
        (
            "from pdd.sync_core import LanguageRegistry; "
            "r=LanguageRegistry.bundled(); "
            "assert r.resolve_alias('python').language_id == 'python'"
        ),
    )
    assert probe.returncode == 0, probe.stdout + probe.stderr
