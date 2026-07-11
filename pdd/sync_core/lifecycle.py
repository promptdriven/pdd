"""Credential-free execution of checker-owned packaged lifecycle scenarios."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

from .artifact_provenance import (
    CandidateArtifactPolicy,
    CandidateArtifactProvenanceError,
    load_candidate_artifact_provenance,
)
from .certificate import LifecycleResult
from .isolation import untrusted_child_environment
from .scenario_contract import REQUIRED_SCENARIOS


def _isolated_lifecycle_environment(home: Path) -> dict[str, str]:
    """Build a credential-free environment with no source import overrides."""
    return untrusted_child_environment(
        home=home,
        extra={"PYTHONNOUSERSITE": "1"},
        drop={"PYTHONPATH", "PYTHONHOME", "PDD_PATH"},
    )


def _failed_result(*, timeout: bool = False) -> LifecycleResult:
    return LifecycleResult(
        len(REQUIRED_SCENARIOS),
        0,
        0,
        int(timeout),
        1,
        1,
        tuple(sorted(REQUIRED_SCENARIOS)),
        "",
        "",
        None,
    )


def _required_paths_available(
    path_inputs: tuple[tuple[Path | None, str], ...],
) -> bool:
    """Return whether all required filesystem inputs satisfy their path predicate."""
    predicates = {"file": Path.is_file, "directory": Path.is_dir}
    return all(
        path is not None and predicates[predicate](Path(path))
        for path, predicate in path_inputs
    )


def _normalized_results(payload: Any) -> dict[str, dict[str, Any]]:
    if not isinstance(payload, dict) or payload.get("schema_version") != 1:
        raise ValueError("released lifecycle result schema is invalid")
    rows = payload.get("results")
    if not isinstance(rows, list):
        raise ValueError("released lifecycle results are absent")
    results: dict[str, dict[str, Any]] = {}
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError("released lifecycle result is malformed")
        scenario_id = row.get("scenario_id")
        status = row.get("status")
        if (
            not isinstance(scenario_id, str)
            or scenario_id in results
            or status not in {"PASS", "FAIL", "MISSING"}
        ):
            raise ValueError("released lifecycle result identity is invalid")
        for metric in (
            "required_tests_skipped_or_xfailed",
            "collection_errors",
            "timeouts",
            "post_repair_second_run_writes",
            "post_merge_tree_changes",
        ):
            value = row.get(metric)
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                raise ValueError("released lifecycle metric is invalid")
        results[scenario_id] = row
    if set(results) != set(REQUIRED_SCENARIOS):
        raise ValueError("released lifecycle scenario set is incomplete")
    return results


def _dependency_environment_digest(candidate_python: Path, isolated: dict[str, str]) -> str:
    """Hash the installed distribution set visible to the candidate wheel."""
    probe = subprocess.run(
        [
            str(candidate_python),
            "-c",
            (
                "import importlib.metadata as m, json;"
                "rows=[];"
                "\nfor d in m.distributions():"
                "\n rows.append({"
                "'name': d.metadata.get('Name', ''),"
                "'version': d.version,"
                "'files': sorted("
                "(str(f), getattr(getattr(f, 'hash', None), 'value', ''), f.size or 0)"
                " for f in (d.files or ()))"
                "})"
                "\nprint(json.dumps(sorted(rows, key=lambda r: (r['name'].lower(), r['version'])),"
                " sort_keys=True, separators=(',', ':')))"
            ),
        ],
        capture_output=True,
        text=True,
        check=False,
        env=isolated,
    )
    if probe.returncode != 0:
        return ""
    return hashlib.sha256(probe.stdout.encode()).hexdigest()


def _candidate_interpreter_identity(
    candidate_python: Path, isolated: dict[str, str]
) -> dict[str, str] | None:
    """Measure the interpreter and first compatible wheel tag actually executed."""
    probe = subprocess.run(
        [
            str(candidate_python),
            "-I",
            "-c",
            (
                "import json, platform; from packaging.tags import sys_tags;"
                "tag=next(sys_tags()); print(json.dumps({"
                "'implementation':platform.python_implementation(),"
                "'version':platform.python_version(),'abi':tag.abi,"
                "'platform':tag.platform},sort_keys=True))"
            ),
        ],
        capture_output=True,
        text=True,
        check=False,
        env=isolated,
    )
    if probe.returncode != 0:
        return None
    try:
        measured = json.loads(probe.stdout)
    except json.JSONDecodeError:
        return None
    return measured if isinstance(measured, dict) else None


def _combined_candidate_lock(temporary: Path, runtime_lock: Path, wheel: Path) -> Path | None:
    """Return a requirements file that pins the exact candidate wheel by hash."""
    try:
        runtime_text = runtime_lock.read_text(encoding="utf-8")
        wheel_hash = hashlib.sha256(wheel.read_bytes()).hexdigest()
    except OSError:
        return None
    combined = temporary / "candidate-install.lock"
    combined.write_text(
        (
            runtime_text.rstrip()
            + "\n"
            + f"{wheel.resolve().as_posix()} --hash=sha256:{wheel_hash}\n"
        ).lstrip(),
        encoding="utf-8",
    )
    return combined


def _install_candidate_wheel(
    temporary: Path,
    home: Path,
    wheel: Path,
    wheelhouse: Path,
    runtime_lock: Path,
) -> tuple[Path, str] | None:
    # pylint: disable=too-many-return-statements
    """Install the exact candidate wheel and runtime deps from a pinned wheelhouse."""
    if not wheelhouse.is_dir() or not runtime_lock.is_file():
        return None
    combined_lock = _combined_candidate_lock(temporary, runtime_lock, wheel)
    if combined_lock is None:
        return None
    environment = temporary / "candidate-venv"
    isolated = _isolated_lifecycle_environment(home)
    created = subprocess.run(
        [sys.executable, "-m", "venv", str(environment)],
        capture_output=True,
        text=True,
        check=False,
        env=isolated,
    )
    candidate_python = environment / (
        "Scripts/python.exe" if os.name == "nt" else "bin/python"
    )
    if created.returncode != 0:
        return None
    installed = subprocess.run(
        [
            str(candidate_python),
            "-m",
            "pip",
            "install",
            "--no-index",
            "--find-links",
            str(wheelhouse.resolve()),
            "--require-hashes",
            "--only-binary=:all:",
            "--disable-pip-version-check",
            "--force-reinstall",
            "-r",
            str(combined_lock),
        ],
        capture_output=True,
        text=True,
        check=False,
        env=isolated,
    )
    if installed.returncode != 0:
        return None
    proved = subprocess.run(
        [str(candidate_python), "-I", "-m", "pdd.cli", "--help"],
        capture_output=True,
        text=True,
        check=False,
        env=isolated,
    )
    if proved.returncode != 0:
        return None
    dependency_digest = _dependency_environment_digest(candidate_python, isolated)
    if len(dependency_digest) != 64:
        return None
    return candidate_python, dependency_digest


def run_lifecycle_matrix(
    root: Path,
    *,
    candidate_wheel: Path | None = None,
    candidate_wheelhouse: Path | None = None,
    candidate_runtime_lock: Path | None = None,
    candidate_attestation: Path | None = None,
    candidate_artifact_policy: CandidateArtifactPolicy | None = None,
    cloud_root: Path | None = None,
    cloud_base_ref: str | None = None,
    cloud_head_ref: str | None = None,
    timeout_seconds: int = 1200,
) -> LifecycleResult:
    # pylint: disable=too-many-arguments,too-many-locals,too-many-boolean-expressions
    # pylint: disable=too-many-return-statements
    """Run only the scenario harness installed with the released checker."""
    del root  # Candidate repository tests are never lifecycle evidence.
    required_paths = (
        (candidate_wheel, "file"),
        (candidate_wheelhouse, "directory"),
        (candidate_runtime_lock, "file"),
    )
    if (
        not _required_paths_available(required_paths)
        or candidate_attestation is None
        or candidate_artifact_policy is None
        or cloud_root is None
        or cloud_base_ref is None
        or cloud_head_ref is None
    ):
        return _failed_result()
    try:
        runtime_lock_digest = hashlib.sha256(
            Path(candidate_runtime_lock).read_bytes()
        ).hexdigest()
        if runtime_lock_digest != candidate_artifact_policy.dependency_lock_sha256:
            return _failed_result()
    except CandidateArtifactProvenanceError:
        return _failed_result()
    except OSError:
        return _failed_result()
    with tempfile.TemporaryDirectory(prefix="pdd-released-lifecycle-") as directory:
        temporary = Path(directory)
        protected = temporary / "protected-inputs"
        protected.mkdir(mode=0o700)
        protected_wheel = protected / Path(candidate_wheel).name
        protected_attestation = protected / "candidate-attestation.json"
        protected_lock = protected / "candidate-runtime.lock"
        try:
            shutil.copy2(candidate_wheel, protected_wheel)
            shutil.copy2(candidate_attestation, protected_attestation)
            shutil.copy2(candidate_runtime_lock, protected_lock)
            for path in (protected_wheel, protected_attestation, protected_lock):
                path.chmod(0o400)
            candidate_artifact = load_candidate_artifact_provenance(
                protected_attestation, protected_wheel, candidate_artifact_policy
            )
        except (OSError, CandidateArtifactProvenanceError):
            return _failed_result()
        output = temporary / "result.json"
        (temporary / "home").mkdir(mode=0o700)
        installed_candidate = _install_candidate_wheel(
            temporary,
            temporary / "home",
            protected_wheel,
            Path(candidate_wheelhouse),
            protected_lock,
        )
        if installed_candidate is None:
            return _failed_result()
        candidate_python, dependency_digest = installed_candidate
        measured_python = _candidate_interpreter_identity(
            candidate_python, _isolated_lifecycle_environment(temporary / "home")
        )
        expected_python = {
            "implementation": candidate_artifact_policy.python_implementation,
            "version": candidate_artifact_policy.python_version,
            "abi": candidate_artifact_policy.python_abi,
            "platform": candidate_artifact_policy.python_platform,
        }
        if measured_python != expected_python:
            return _failed_result()
        command = [
            sys.executable,
            "-I",
            "-m",
            "pdd.sync_core.scenario_harness",
            "--output",
            str(output),
            "--cloud-root",
            str(Path(cloud_root).resolve()),
            "--cloud-base-ref",
            cloud_base_ref,
            "--cloud-head-ref",
            cloud_head_ref,
            "--candidate-python",
            str(candidate_python),
        ]
        try:
            completed = subprocess.run(
                command,
                capture_output=True,
                text=True,
                check=False,
                timeout=timeout_seconds,
                env=_isolated_lifecycle_environment(temporary / "home"),
            )
        except subprocess.TimeoutExpired:
            return _failed_result(timeout=True)
        try:
            results = _normalized_results(json.loads(output.read_text(encoding="utf-8")))
        except (OSError, ValueError, json.JSONDecodeError):
            return _failed_result()
        missing = tuple(
            sorted(
                scenario_id
                for scenario_id, row in results.items()
                if row["status"] == "MISSING"
            )
        )
        failures = sum(row["status"] != "PASS" for row in results.values())
        if completed.returncode != 0 and failures == 0:
            failures = 1
        return LifecycleResult(
            failures,
            sum(
                int(row["required_tests_skipped_or_xfailed"])
                for row in results.values()
            ),
            sum(int(row["collection_errors"]) for row in results.values()),
            sum(int(row["timeouts"]) for row in results.values()),
            sum(
                int(row["post_repair_second_run_writes"])
                for row in results.values()
            ),
            sum(int(row["post_merge_tree_changes"]) for row in results.values()),
            missing,
            hashlib.sha256(protected_wheel.read_bytes()).hexdigest(),
            dependency_digest,
            candidate_artifact,
        )
