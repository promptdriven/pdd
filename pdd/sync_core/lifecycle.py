"""Credential-free execution of checker-owned packaged lifecycle scenarios."""

from __future__ import annotations

import hashlib
import json
import os
import stat
import subprocess
import sys
import tempfile
from dataclasses import dataclass
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
from .supervisor import run_supervised


_LIFECYCLE_RECEIPT_MAX_BYTES = 4 * 1024 * 1024
_CHILD_OUTPUT_MAX_BYTES = 1024 * 1024

_VENV_TREE_VALIDATOR_SOURCE = """
def _normalize_and_validate_environment(root):
    root = pathlib.Path(root)
    root_metadata = root.lstat()
    if not stat.S_ISDIR(root_metadata.st_mode) or stat.S_ISLNK(root_metadata.st_mode):
        raise RuntimeError('candidate environment root is not a real directory')
    alias = root / 'lib64'
    if os.path.lexists(alias):
        alias_metadata = alias.lstat()
        if not stat.S_ISLNK(alias_metadata.st_mode) or os.readlink(alias) != 'lib':
            raise RuntimeError('candidate environment lib64 alias is invalid')
        library = root / 'lib'
        library_metadata = library.lstat()
        if not stat.S_ISDIR(library_metadata.st_mode) or stat.S_ISLNK(
            library_metadata.st_mode
        ):
            raise RuntimeError('candidate environment lib directory is invalid')
        alias.unlink()

    def raise_walk_error(error):
        raise error

    for current, directories, files in os.walk(
        root, topdown=True, onerror=raise_walk_error, followlinks=False
    ):
        parent = pathlib.Path(current)
        for name in (*directories, *files):
            path = parent / name
            metadata = path.lstat()
            if stat.S_ISLNK(metadata.st_mode):
                raise RuntimeError('candidate environment contains a symlink')
            if not (
                stat.S_ISDIR(metadata.st_mode) or stat.S_ISREG(metadata.st_mode)
            ):
                raise RuntimeError('candidate environment contains a special file')
"""

_VENV_CREATION_SOURCE = "\n".join((
    "import os,pathlib,stat,sys,venv",
    _VENV_TREE_VALIDATOR_SOURCE.strip(),
    "if len(sys.argv) != 2: raise RuntimeError('invalid candidate environment argv')",
    "root=pathlib.Path(sys.argv[1])",
    "if not root.is_absolute(): raise RuntimeError('candidate environment is not absolute')",
    "parent_metadata=root.parent.lstat()",
    "if not stat.S_ISDIR(parent_metadata.st_mode) or "
    "stat.S_ISLNK(parent_metadata.st_mode): "
    "raise RuntimeError('candidate environment parent is invalid')",
    "if os.path.lexists(root): raise RuntimeError('candidate environment already exists')",
    "venv.EnvBuilder(symlinks=False,with_pip=True).create(root)",
    "_normalize_and_validate_environment(root)",
))

_CANDIDATE_TRANSACTION_SOURCE = "\n".join((
    "import hashlib,json,os,pathlib,signal,stat,subprocess,sys,time,venv",
    _VENV_TREE_VALIDATOR_SOURCE.strip(),
    "if len(sys.argv) != 6: raise RuntimeError('invalid lifecycle transaction argv')",
    "root=pathlib.Path(sys.argv[1])",
    "wheelhouse=pathlib.Path(sys.argv[2])",
    "requirements=pathlib.Path(sys.argv[3])",
    "timeout=float(sys.argv[4])",
    "scenario=json.loads(sys.argv[5])",
    "if not root.is_absolute(): raise RuntimeError('candidate environment is not absolute')",
    "parent_metadata=root.parent.lstat()",
    "if not stat.S_ISDIR(parent_metadata.st_mode) or stat.S_ISLNK(parent_metadata.st_mode): "
    "raise RuntimeError('candidate environment parent is invalid')",
    "if os.path.lexists(root): raise RuntimeError('candidate environment already exists')",
    "if type(timeout) is not float or not 0 < timeout <= 86400: "
    "raise RuntimeError('invalid lifecycle child timeout')",
    "if not isinstance(scenario,list) or not all(isinstance(item,str) for item in scenario): "
    "raise RuntimeError('invalid lifecycle scenario command')",
    f"output_limit={_CHILD_OUTPUT_MAX_BYTES}",
    "deadline=time.monotonic()+timeout",
    "def run_child(argv):",
    "    remaining=deadline-time.monotonic()",
    "    if remaining <= 0: raise RuntimeError('lifecycle child deadline expired')",
    "    child=subprocess.Popen(argv,stdout=subprocess.PIPE,stderr=subprocess.PIPE,"
    "text=False,start_new_session=True)",
    "    try:",
    "        stdout,stderr=child.communicate(timeout=remaining)",
    "    except subprocess.TimeoutExpired:",
    "        os.killpg(child.pid,signal.SIGKILL)",
    "        child.communicate()",
    "        raise RuntimeError('lifecycle child deadline expired') from None",
    "    try:",
    "        os.killpg(child.pid,0)",
    "    except ProcessLookupError:",
    "        pass",
    "    else:",
    "        os.killpg(child.pid,signal.SIGKILL)",
    "        raise RuntimeError('lifecycle child left surviving descendants')",
    "    if len(stdout)>output_limit or len(stderr)>output_limit: "
    "raise RuntimeError('lifecycle child output exceeded limit')",
    "    return child.returncode,stdout,stderr",
    "def closure():",
    "    rows=[]",
    "    for path in sorted(root.rglob('*')):",
    "        metadata=path.lstat()",
    "        if stat.S_ISLNK(metadata.st_mode): "
    "raise RuntimeError('candidate environment contains a symlink')",
    "        if stat.S_ISDIR(metadata.st_mode): continue",
    "        if not stat.S_ISREG(metadata.st_mode): "
    "raise RuntimeError('candidate environment contains a special file')",
    "        relative=path.relative_to(root).as_posix()",
    "        rows.append(('candidate-environment','1',relative,"
    "hashlib.sha256(path.read_bytes()).hexdigest()))",
    "    return tuple(rows)",
    "venv.EnvBuilder(symlinks=False,with_pip=True).create(root)",
    "_normalize_and_validate_environment(root)",
    "candidate_python=root/('Scripts/python.exe' if os.name=='nt' else 'bin/python')",
    "pip_command=[str(candidate_python),'-m','pip','install','--no-index','--find-links',"
    "str(wheelhouse),'--require-hashes','--only-binary=:all:',"
    "'--disable-pip-version-check','--force-reinstall','-r',str(requirements)]",
    "pip_status,_,_=run_child(pip_command)",
    "if pip_status != 0: raise RuntimeError('candidate installation failed')",
    "_normalize_and_validate_environment(root)",
    "installed=closure()",
    "proof_status,_,_=run_child([str(candidate_python),'-I','-m','pdd.cli','--help'])",
    "if proof_status != 0: raise RuntimeError('candidate proof failed')",
    "_normalize_and_validate_environment(root)",
    "if closure()!=installed: raise RuntimeError('candidate proof mutated environment')",
    "scenario_status=None",
    "scenario_stdout=None",
    "if scenario:",
    "    scenario_status,scenario_bytes,_=run_child(scenario)",
    "    scenario_stdout=scenario_bytes.decode('utf-8','strict')",
    "    _normalize_and_validate_environment(root)",
    "    if closure()!=installed: raise RuntimeError('candidate scenario mutated environment')",
    "digest=hashlib.sha256(json.dumps(installed,separators=(',',':')).encode()).hexdigest()",
    "receipt={'dependency_digest':digest,'installed_files':installed,"
    "'scenario_returncode':scenario_status,'scenario_stdout':scenario_stdout,"
    "'status':'ok','version':1}",
    "encoded=json.dumps(receipt,separators=(',',':'),sort_keys=True)",
    f"if len(encoded.encode())>{_LIFECYCLE_RECEIPT_MAX_BYTES}: "
    "raise RuntimeError('lifecycle receipt exceeded limit')",
    "sys.stdout.write(encoded)",
))


@dataclass(frozen=True)
class _CandidateTransactionReceipt:
    dependency_digest: str
    installed_files: tuple[tuple[str, str, str, str], ...]
    scenario_returncode: int | None
    scenario_stdout: str | None


def _lexical_real_directory(path: Path) -> Path:
    """Validate every lexical path component before canonicalizing it."""
    if not path.is_absolute():
        raise ValueError("candidate environment parent is not absolute")
    current = Path(path.anchor)
    try:
        for component in path.parts[1:]:
            current /= component
            metadata = current.lstat()
            if not stat.S_ISDIR(metadata.st_mode) or stat.S_ISLNK(metadata.st_mode):
                raise ValueError("candidate environment parent is invalid")
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise ValueError("candidate environment parent is unavailable") from exc
    if resolved != path:
        raise ValueError("candidate environment parent changed during validation")
    return resolved


def _candidate_venv_command(environment: Path) -> list[str]:
    """Build the exact isolated wrapper command for one checker-owned venv path."""
    parent = _lexical_real_directory(environment.parent)
    if os.path.lexists(environment):
        raise ValueError("candidate environment destination already exists")
    destination = parent / environment.name
    return [sys.executable, "-I", "-c", _VENV_CREATION_SOURCE, str(destination)]


def _candidate_transaction_command(
    environment: Path,
    wheelhouse: Path,
    requirements: Path,
    timeout_seconds: int,
    scenario_command: tuple[str, ...],
) -> list[str]:
    """Build one trusted wrapper command for create, install, proof, and scenario."""
    if (
        type(timeout_seconds) is not int  # pylint: disable=unidiomatic-typecheck
        or not 0 < timeout_seconds <= 86400
        or not isinstance(scenario_command, tuple)
        or not all(isinstance(item, str) for item in scenario_command)
    ):
        raise ValueError("candidate transaction arguments are invalid")
    parent = _lexical_real_directory(environment.parent)
    if os.path.lexists(environment):
        raise ValueError("candidate environment destination already exists")
    return [
        sys.executable,
        "-I",
        "-c",
        _CANDIDATE_TRANSACTION_SOURCE,
        str(parent / environment.name),
        str(wheelhouse.resolve(strict=True)),
        str(requirements.resolve(strict=True)),
        str(timeout_seconds),
        json.dumps(scenario_command, separators=(",", ":")),
    ]


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


def _copy_protected(source: Path, destination: Path) -> str:
    """Copy a regular input without following its final component and hash the copy."""
    descriptor = os.open(source, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            raise OSError("protected input is not regular")
        digest = hashlib.sha256()
        with os.fdopen(descriptor, "rb", closefd=False) as reader, destination.open("wb") as writer:
            while chunk := reader.read(1024 * 1024):
                digest.update(chunk)
                writer.write(chunk)
            writer.flush()
            os.fsync(writer.fileno())
        destination.chmod(0o400)
        if hashlib.sha256(destination.read_bytes()).hexdigest() != digest.hexdigest():
            raise OSError("protected copy changed")
        return digest.hexdigest()
    finally:
        os.close(descriptor)


def _installed_file_closure(candidate_python: Path) -> tuple[tuple[str, str, str, str], ...]:
    """Measure installed regular files from checker-owned filesystem traversal."""
    environment = candidate_python.parents[1]
    rows = []
    for path in sorted(environment.rglob("*")):
        if path.is_symlink() or not path.is_file():
            continue
        relative = path.relative_to(environment).as_posix()
        rows.append(("candidate-environment", "1", relative,
                     hashlib.sha256(path.read_bytes()).hexdigest()))
    return tuple(rows)


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


def _dependency_environment_digest(candidate_python: Path, _isolated: dict[str, str]) -> str:
    """Hash the checker-owned installed-file closure without candidate startup."""
    closure = _installed_file_closure(candidate_python)
    return hashlib.sha256(json.dumps(closure, separators=(",", ":")).encode()).hexdigest()


def _candidate_interpreter_identity(
    candidate_python: Path, isolated: dict[str, str]
) -> dict[str, str] | None:
    """Measure the checker interpreter used to create the venv, before site startup."""
    del candidate_python, isolated
    import platform  # pylint: disable=import-outside-toplevel
    from packaging.tags import sys_tags  # pylint: disable=import-outside-toplevel
    tag = next(sys_tags())
    return {"implementation": platform.python_implementation(),
            "version": platform.python_version(), "abi": tag.abi,
            "platform": tag.platform}


def _lifecycle_command(command: list[str], temporary: Path, home: Path,
                       timeout: int = 1200, *,
                       readable_roots: tuple[Path, ...] = (),
                       writable_roots: tuple[Path, ...] | None = None,
                       cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
    # pylint: disable=too-many-arguments
    """Route every lifecycle command through the shared fail-closed supervisor."""
    result, surviving = run_supervised(
        command, cwd=cwd or temporary, timeout=timeout,
        env=_isolated_lifecycle_environment(home),
        writable_roots=writable_roots or (temporary,),
        readable_roots=readable_roots,
    )
    if surviving:
        return subprocess.CompletedProcess(command, 125, result.stdout,
                                           result.stderr + "\nsurviving descendant")
    return result


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


def _parse_candidate_transaction_receipt(
    completed: subprocess.CompletedProcess[str],
) -> _CandidateTransactionReceipt | None:
    # pylint: disable=too-many-return-statements,too-many-boolean-expressions
    # pylint: disable=unidiomatic-typecheck
    """Parse the wrapper's exact canonical, bounded receipt fail closed."""
    stdout = completed.stdout
    if (
        completed.returncode != 0
        or not isinstance(stdout, str)
        or not isinstance(completed.stderr, str)
        or completed.stderr
        or len(stdout.encode("utf-8")) > _LIFECYCLE_RECEIPT_MAX_BYTES
    ):
        return None
    try:
        payload = json.loads(stdout)
    except (TypeError, ValueError, json.JSONDecodeError):
        return None
    expected_keys = {
        "dependency_digest",
        "installed_files",
        "scenario_returncode",
        "scenario_stdout",
        "status",
        "version",
    }
    if (
        not isinstance(payload, dict)
        or set(payload) != expected_keys
        or type(payload["version"]) is not int
        or payload["version"] != 1
        or payload["status"] != "ok"
        or not isinstance(payload["dependency_digest"], str)
        or len(payload["dependency_digest"]) != 64
        or any(character not in "0123456789abcdef" for character in payload["dependency_digest"])
        or json.dumps(payload, separators=(",", ":"), sort_keys=True) != stdout
    ):
        return None
    raw_files = payload["installed_files"]
    if not isinstance(raw_files, list):
        return None
    installed_files: list[tuple[str, str, str, str]] = []
    seen_paths: set[str] = set()
    for row in raw_files:
        if (
            not isinstance(row, list)
            or len(row) != 4
            or row[0:2] != ["candidate-environment", "1"]
            or not isinstance(row[2], str)
            or not row[2]
            or row[2] in seen_paths
            or Path(row[2]).is_absolute()
            or ".." in Path(row[2]).parts
            or not isinstance(row[3], str)
            or len(row[3]) != 64
            or any(character not in "0123456789abcdef" for character in row[3])
        ):
            return None
        seen_paths.add(row[2])
        installed_files.append(tuple(row))
    if installed_files != sorted(installed_files, key=lambda row: Path(row[2]).parts):
        return None
    expected_digest = hashlib.sha256(
        json.dumps(tuple(installed_files), separators=(",", ":")).encode()
    ).hexdigest()
    if payload["dependency_digest"] != expected_digest:
        return None
    scenario_returncode = payload["scenario_returncode"]
    scenario_stdout = payload["scenario_stdout"]
    scenario_absent = scenario_returncode is None and scenario_stdout is None
    scenario_present = (
        type(scenario_returncode) is int
        and -255 <= scenario_returncode <= 255
        and isinstance(scenario_stdout, str)
        and len(scenario_stdout.encode("utf-8")) <= _CHILD_OUTPUT_MAX_BYTES
    )
    if not scenario_absent and not scenario_present:
        return None
    return _CandidateTransactionReceipt(
        payload["dependency_digest"],
        tuple(installed_files),
        scenario_returncode,
        scenario_stdout,
    )


def _run_candidate_transaction(
    temporary: Path,
    home: Path,
    wheel: Path,
    wheelhouse: Path,
    runtime_lock: Path,
    *,
    timeout_seconds: int = 1200,
    scenario_command: tuple[str, ...] = (),
    scenario_readable_roots: tuple[Path, ...] = (),
) -> tuple[_CandidateTransactionReceipt | None, int]:
    # pylint: disable=too-many-arguments
    """Run the complete ephemeral candidate lifecycle in one supervised command."""
    if not wheelhouse.is_dir() or not runtime_lock.is_file():
        return None, 125
    combined_lock = _combined_candidate_lock(temporary, runtime_lock, wheel)
    if combined_lock is None:
        return None, 125
    environment = temporary / "candidate-venv"
    try:
        command = _candidate_transaction_command(
            environment, wheelhouse, combined_lock, timeout_seconds, scenario_command
        )
    except (OSError, ValueError):
        return None, 125
    completed = _lifecycle_command(
        command,
        temporary,
        home,
        timeout_seconds,
        readable_roots=(wheelhouse, wheel, runtime_lock, *scenario_readable_roots),
    )
    return _parse_candidate_transaction_receipt(completed), completed.returncode


def _install_candidate_wheel(
    temporary: Path,
    home: Path,
    wheel: Path,
    wheelhouse: Path,
    runtime_lock: Path,
) -> _CandidateTransactionReceipt | None:
    """Install and prove the candidate within one ephemeral transaction."""
    receipt, _returncode = _run_candidate_transaction(
        temporary, home, wheel, wheelhouse, runtime_lock
    )
    return receipt


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
            _copy_protected(Path(candidate_wheel), protected_wheel)
            _copy_protected(Path(candidate_attestation), protected_attestation)
            protected_lock_digest = _copy_protected(
                Path(candidate_runtime_lock), protected_lock
            )
            if protected_lock_digest != candidate_artifact_policy.dependency_lock_sha256:
                return _failed_result()
            candidate_artifact = load_candidate_artifact_provenance(
                protected_attestation, protected_wheel, candidate_artifact_policy
            )
        except (OSError, CandidateArtifactProvenanceError):
            return _failed_result()
        (temporary / "home").mkdir(mode=0o700)
        candidate_python = temporary / "candidate-venv" / (
            "Scripts/python.exe" if os.name == "nt" else "bin/python"
        )
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
            "-",
            "--cloud-root",
            str(Path(cloud_root).resolve()),
            "--cloud-base-ref",
            cloud_base_ref,
            "--cloud-head-ref",
            cloud_head_ref,
            "--candidate-python",
            str(candidate_python),
        ]
        receipt, transaction_returncode = _run_candidate_transaction(
            temporary,
            temporary / "home",
            protected_wheel,
            Path(candidate_wheelhouse),
            protected_lock,
            timeout_seconds=timeout_seconds,
            scenario_command=tuple(command),
            scenario_readable_roots=(Path(cloud_root).resolve(),),
        )
        if receipt is None:
            return _failed_result(timeout=transaction_returncode == 124)
        dependency_digest = receipt.dependency_digest
        installed_files = receipt.installed_files
        if receipt.scenario_returncode is None or receipt.scenario_stdout is None:
            return _failed_result()
        if receipt.scenario_returncode == 124:
            return _failed_result(timeout=True)
        try:
            lines = [line for line in receipt.scenario_stdout.splitlines() if line.strip()]
            results = _normalized_results(json.loads(lines[-1]))
        except (IndexError, OSError, ValueError, json.JSONDecodeError):
            return _failed_result()
        missing = tuple(
            sorted(
                scenario_id
                for scenario_id, row in results.items()
                if row["status"] == "MISSING"
            )
        )
        failures = sum(row["status"] != "PASS" for row in results.values())
        if receipt.scenario_returncode != 0 and failures == 0:
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
            protected_lock_digest,
            measured_python,
            installed_files,
            "pdd-released-checker-v1",
        )
