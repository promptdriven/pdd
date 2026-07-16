"""Run and seal the immutable, never-merge issue-2083 hosted diagnostic."""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path


SUBJECT_SHA = "bd4a250420c3b7aaa50bab6fd73aded271115c71"
EXACT_NODE = (
    "tests/test_sync_core_runner_vitest.py::"
    "test_real_vitest_runs_copied_entrypoint_without_candidate_result_access"
)
EXPECTED_VITEST_VERSION = "4.1.10"
SERIAL_REPETITIONS = 3
CONCURRENT_WIDTHS = (2, 4)
CONCURRENT_WAVES = 3
INVOCATION_TIMEOUT_SECONDS = 75
MEMINFO_FIELDS = {
    "MemTotal", "MemFree", "MemAvailable", "SwapTotal", "SwapFree",
}
CGROUP_FILES = (
    "memory.current", "memory.max", "memory.events",
    "pids.current", "pids.max", "pids.events",
)
HEX_DIGEST = re.compile(r"[0-9a-f]{64}")
SAFE_NAME = re.compile(r"[A-Za-z0-9._+-]+")
NODE_VERSION = re.compile(r"v\d+\.\d+\.\d+")
NPM_VERSION = re.compile(r"\d+\.\d+\.\d+")
SHA256 = re.compile(r"\bdiagnostic_sha256=([0-9a-f]{64})\b")
SIGNAL_RESULT = re.compile(r"\bkind=signal; signal=([A-Z0-9]+); signal_number=(\d+)")
SANDBOX_RESULT = re.compile(r"\bkind=sandbox-error; exit_code=(\d+)")
RESOURCE_RESULT = re.compile(r"\bkind=resource-limit; resource_limit=([a-z-]+)")
TRUSTED_FIELD = re.compile(
    r"\b(trusted_failure_phases|trusted_failure_reason|"
    r"trusted_descriptor_plan_stage)=([a-z0-9_,-]+)"
)
CGROUP_DELTA = re.compile(
    r"\b(cgroup_memory_oom_delta|cgroup_memory_oom_kill_delta|"
    r"cgroup_pids_max_delta)=(\d+)"
)


def _canonical(payload: object) -> str:
    return json.dumps(payload, separators=(",", ":"), sort_keys=True)


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _git(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True,
    )
    return result.stdout.strip()


def _exact_keys(value: object, expected: set[str], label: str) -> dict:
    if not isinstance(value, dict) or set(value) != expected:
        raise ValueError(f"toolchain {label} fields are invalid")
    return value


def _valid_digest(value: object) -> bool:
    return isinstance(value, str) and HEX_DIGEST.fullmatch(value) is not None


def _validate_artifact(value: object, label: str) -> dict[str, str]:
    artifact = _exact_keys(value, {"name", "sha256"}, label)
    name = artifact["name"]
    if not isinstance(name, str) or SAFE_NAME.fullmatch(name) is None:
        raise ValueError(f"toolchain {label} name is invalid")
    if not _valid_digest(artifact["sha256"]):
        raise ValueError(f"toolchain {label} digest is invalid")
    return artifact


def _validate_versions(value: object) -> None:
    versions = _exact_keys(value, {"node", "npm", "vitest"}, "version")
    if not isinstance(versions["node"], str) or not NODE_VERSION.fullmatch(
        versions["node"]
    ):
        raise ValueError("toolchain node version is invalid")
    if not isinstance(versions["npm"], str) or not NPM_VERSION.fullmatch(
        versions["npm"]
    ):
        raise ValueError("toolchain npm version is invalid")
    if versions["vitest"] != EXPECTED_VITEST_VERSION:
        raise ValueError("toolchain Vitest version is invalid")


def _validate_package(value: object) -> None:
    package = _exact_keys(
        value,
        {
            "package_json_sha256", "package_lock_sha256",
            "vitest_package_sha256",
        },
        "package",
    )
    if not all(_valid_digest(digest) for digest in package.values()):
        raise ValueError("toolchain package digest is invalid")


def _validate_closure(value: object) -> None:
    if not isinstance(value, list) or not value:
        raise ValueError("toolchain native closure is invalid")
    validated = [
        _validate_artifact(artifact, "native closure") for artifact in value
    ]
    if validated != sorted(validated, key=lambda item: (item["name"], item["sha256"])):
        raise ValueError("toolchain native closure is not canonical")
    if len({item["name"] for item in validated}) != len(validated):
        raise ValueError("toolchain native closure names are ambiguous")


def load_toolchain_identity(path: Path) -> tuple[dict[str, object], str]:
    """Load a canonical, complete, path-free toolchain attestation."""
    if path.is_symlink():
        raise ValueError("toolchain identity is unavailable")
    try:
        raw = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise ValueError("toolchain identity is unavailable") from exc
    try:
        payload = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ValueError("toolchain identity is malformed") from exc
    identity = _exact_keys(
        payload,
        {
            "schema", "versions", "package", "launcher", "entrypoint",
            "native_closure", "runtime_manifest_sha256",
        },
        "identity",
    )
    if raw != _canonical(identity):
        raise ValueError("toolchain identity is not canonical")
    if identity["schema"] != "pdd-vitest-toolchain-attestation-v1":
        raise ValueError("toolchain identity schema is invalid")
    _validate_versions(identity["versions"])
    _validate_package(identity["package"])
    _validate_artifact(identity["launcher"], "launcher")
    _validate_artifact(identity["entrypoint"], "entrypoint")
    _validate_closure(identity["native_closure"])
    if not _valid_digest(identity["runtime_manifest_sha256"]):
        raise ValueError("toolchain runtime manifest digest is invalid")
    return identity, hashlib.sha256(raw.encode("utf-8")).hexdigest()


def verify_runtime_manifest(identity: dict[str, object], path: Path) -> None:
    """Bind the path-bearing runtime manifest to its redacted identity."""
    if not path.is_file() or path.is_symlink():
        raise ValueError("toolchain runtime manifest is unavailable")
    if _digest(path) != identity["runtime_manifest_sha256"]:
        raise ValueError("toolchain runtime manifest changed after attestation")


def _version(command: list[str], pattern: re.Pattern[str], label: str) -> str:
    result = subprocess.run(
        command, capture_output=True, text=True, check=True, timeout=30,
    )
    value = result.stdout.strip()
    if pattern.fullmatch(value) is None:
        raise ValueError(f"toolchain {label} version is invalid")
    return value


def _native_identity(launcher: Path) -> list[dict[str, str]]:
    """Hash the launcher's native closure without retaining host paths."""
    linked = subprocess.run(
        ["ldd", str(launcher)],
        capture_output=True,
        text=True,
        check=True,
        timeout=30,
    ).stdout
    native_paths = sorted({
        Path(match.group(1)).resolve(strict=True)
        for line in linked.splitlines()
        if (match := re.search(r"(?:=>\s+)?(/[^ ]+)", line))
    })
    if not native_paths:
        raise ValueError("toolchain native closure is invalid")
    closure = sorted(
        (
            {"name": path.name, "sha256": _digest(path)}
            for path in native_paths
        ),
        key=lambda value: (value["name"], value["sha256"]),
    )
    if len({value["name"] for value in closure}) != len(closure):
        raise ValueError("toolchain native closure names are ambiguous")
    return closure


def attest_toolchain(root: Path, runtime_manifest: Path, output: Path) -> None:
    """Create redacted canonical identity for a provisioned Vitest toolchain."""
    root = root.resolve(strict=True)
    if runtime_manifest.is_symlink() or not runtime_manifest.is_file():
        raise ValueError("toolchain runtime manifest is unavailable")
    package_json = (root / "package.json").resolve(strict=True)
    package_lock = (root / "package-lock.json").resolve(strict=True)
    vitest_package = (root / "node_modules/vitest/package.json").resolve(strict=True)
    entrypoint = (root / "node_modules/vitest/vitest.mjs").resolve(strict=True)
    launcher_value = shutil.which("node")
    npm_value = shutil.which("npm")
    if not launcher_value or not npm_value:
        raise ValueError("toolchain launcher is unavailable")
    launcher = Path(launcher_value).resolve(strict=True)
    vitest_metadata = json.loads(vitest_package.read_text(encoding="utf-8"))
    vitest_version = vitest_metadata.get("version")
    if vitest_version != EXPECTED_VITEST_VERSION:
        raise ValueError("toolchain Vitest version is invalid")
    identity = {
        "schema": "pdd-vitest-toolchain-attestation-v1",
        "versions": {
            "node": _version([str(launcher), "--version"], NODE_VERSION, "node"),
            "npm": _version([npm_value, "--version"], NPM_VERSION, "npm"),
            "vitest": vitest_version,
        },
        "package": {
            "package_json_sha256": _digest(package_json),
            "package_lock_sha256": _digest(package_lock),
            "vitest_package_sha256": _digest(vitest_package),
        },
        "runtime_manifest_sha256": _digest(runtime_manifest),
        "launcher": {"name": launcher.name, "sha256": _digest(launcher)},
        "entrypoint": {"name": entrypoint.name, "sha256": _digest(entrypoint)},
        "native_closure": _native_identity(launcher),
    }
    output.write_text(_canonical(identity), encoding="utf-8")
    load_toolchain_identity(output)


def _selected_meminfo() -> dict[str, int]:
    values: dict[str, int] = {}
    try:
        lines = Path("/proc/meminfo").read_text(encoding="ascii").splitlines()
    except OSError:
        return values
    for line in lines:
        name, separator, rest = line.partition(":")
        if separator and name in MEMINFO_FIELDS:
            match = re.fullmatch(r"\s*(\d+)\s+kB\s*", rest)
            if match:
                values[name] = int(match.group(1))
    return values


def _safe_cgroup_value(path: Path) -> object:
    try:
        value = path.read_text(encoding="ascii").strip()
    except OSError:
        return None
    if re.fullmatch(r"\d+|max", value):
        return int(value) if value.isdigit() else value
    rows = {}
    for line in value.splitlines():
        match = re.fullmatch(r"([a-z_]+)\s+(\d+)", line)
        if not match:
            return None
        rows[match.group(1)] = int(match.group(2))
    return rows


def _job_cgroup() -> Path | None:
    try:
        lines = Path("/proc/self/cgroup").read_text(encoding="ascii").splitlines()
    except OSError:
        return None
    unified = next((line.partition("::")[2] for line in lines if "::" in line), "")
    relative = Path(unified.lstrip("/"))
    if not unified or ".." in relative.parts:
        return None
    candidate = Path("/sys/fs/cgroup") / relative
    return candidate if candidate.is_dir() else None


def _host_snapshot(phase: str) -> dict[str, object]:
    try:
        processes = [
            path for path in Path("/proc").iterdir()
            if path.name.isdigit() and path.is_dir()
        ]
    except OSError:
        processes = []
    thread_count = 0
    for process in processes:
        try:
            thread_count += sum(
                1 for path in (process / "task").iterdir() if path.name.isdigit()
            )
        except OSError:
            continue
    cgroup = _job_cgroup()
    cgroup_values = (
        {name: _safe_cgroup_value(cgroup / name) for name in CGROUP_FILES}
        if cgroup is not None
        else {}
    )
    try:
        load = Path("/proc/loadavg").read_text(encoding="ascii").split()[:3]
        load_average = [float(item) for item in load]
    except (OSError, ValueError):
        load_average = []
    return {
        "phase": phase,
        "timestamp": _utc_now(),
        "meminfo_kib": _selected_meminfo(),
        "process_count": len(processes),
        "thread_count": thread_count,
        "load_average": load_average,
        "job_cgroup": cgroup_values,
    }


def _classify(
    completed: subprocess.CompletedProcess[bytes], started: str,
) -> dict[str, object]:
    diagnostic = (completed.stdout or b"") + (completed.stderr or b"")
    text = diagnostic.decode("utf-8", errors="replace")
    outcome = "pass" if completed.returncode == 0 else "failure"
    signal_name = None
    signal_number = None
    resource_limit = None
    sandbox_exit = None
    if match := SIGNAL_RESULT.search(text):
        outcome = "signal"
        signal_name, signal_number = match.group(1), int(match.group(2))
    elif match := SANDBOX_RESULT.search(text):
        outcome = "sandbox-error"
        sandbox_exit = int(match.group(1))
    elif match := RESOURCE_RESULT.search(text):
        outcome = "resource-limit"
        resource_limit = match.group(1)
    elif completed.returncode == 124:
        outcome = "timeout"
    digest_match = SHA256.search(text)
    return {
        "started_at": started,
        "finished_at": _utc_now(),
        "returncode": completed.returncode,
        "classification": outcome,
        "reporter": "missing" if "reporter=missing" in text else "present-or-unknown",
        "signal_name": signal_name,
        "signal_number": signal_number,
        "sandbox_exit_code": sandbox_exit,
        "resource_limit": resource_limit,
        "diagnostic_sha256": digest_match.group(1) if digest_match else None,
        "trusted_fields": dict(TRUSTED_FIELD.findall(text)),
        "cgroup_deltas": {
            name: int(value) for name, value in CGROUP_DELTA.findall(text)
        },
        "pytest_output_sha256": hashlib.sha256(diagnostic).hexdigest(),
    }


def _terminate(process: subprocess.Popen[bytes]) -> None:
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()


def _invoke(root: Path, barrier: Path, width: int, index: int) -> dict[str, object]:
    environment = os.environ.copy()
    environment.update({
        "PDD_2083_BARRIER_DIRECTORY": str(barrier),
        "PDD_2083_BARRIER_PARTIES": str(width),
        "PDD_2083_BARRIER_TOKEN": f"p{index}",
        "PYTHONPATH": str(root / "scripts/ci"),
    })
    command = [
        sys.executable, "-m", "pytest", "-q", EXACT_NODE,
        "-p", "issue_2083_vitest_barrier", "--tb=short", "--timeout=60",
    ]
    started = _utc_now()
    with subprocess.Popen(
        command,
        cwd=root,
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    ) as process:
        try:
            output, diagnostic = process.communicate(
                timeout=INVOCATION_TIMEOUT_SECONDS
            )
        except subprocess.TimeoutExpired:
            _terminate(process)
            completed = subprocess.CompletedProcess(process.args, 124, b"", b"")
        else:
            completed = subprocess.CompletedProcess(
                process.args, process.returncode, output, diagnostic,
            )
    return _classify(completed, started)


def _wave(
    root: Path, barrier_root: Path, label: str, width: int,
) -> tuple[list[dict[str, object]], bool]:
    barrier = barrier_root / label
    barrier.mkdir(mode=0o700)
    with concurrent.futures.ThreadPoolExecutor(max_workers=width) as executor:
        rows = list(executor.map(
            lambda index: _invoke(root, barrier, width, index),
            range(width),
        ))
    return rows, any(row["classification"] != "pass" for row in rows)


def _execute_matrices(
    root: Path, barrier_root: Path,
) -> tuple[list[dict[str, object]], dict[str, list[dict[str, object]]], bool]:
    """Execute the bounded matrix and return snapshots, rows, and failure."""
    phases = [_host_snapshot("serial-before")]
    failed = False
    serial_rows = []
    for index in range(SERIAL_REPETITIONS):
        rows, wave_failed = _wave(root, barrier_root, f"serial-{index}", 1)
        serial_rows.extend(rows)
        failed |= wave_failed
    phases.append(_host_snapshot("serial-after"))
    matrices: dict[str, list[dict[str, object]]] = {"serial": serial_rows}
    for width in CONCURRENT_WIDTHS:
        concurrent_rows = []
        phases.append(_host_snapshot(f"concurrent-{width}-before"))
        for wave in range(CONCURRENT_WAVES):
            wave_rows, wave_failed = _wave(
                root, barrier_root, f"concurrent-{width}-{wave}", width,
            )
            concurrent_rows.extend(wave_rows)
            failed |= wave_failed
        phases.append(_host_snapshot(f"concurrent-{width}-after"))
        matrices[f"concurrent_{width}"] = concurrent_rows
    return phases, matrices, failed


def run_matrix(root: Path, output: Path, identity_path: Path) -> int:
    """Run serial controls followed by synchronized two- and four-way waves."""
    identity, identity_digest = load_toolchain_identity(identity_path)
    runtime_value = os.environ.get("PDD_REAL_VITEST_TOOLCHAIN_MANIFEST", "")
    verify_runtime_manifest(identity, Path(runtime_value))
    identity_output = output.parent / "toolchain-identity.json"
    identity_output.write_text(_canonical(identity), encoding="utf-8")
    with tempfile.TemporaryDirectory(
        prefix="pdd-issue-2083-barriers-"
    ) as barrier_directory:
        phases, matrices, failed = _execute_matrices(
            root, Path(barrier_directory),
        )
    payload = {
        "schema": "pdd-issue-2083-vitest-pressure-v1",
        "subject_sha": SUBJECT_SHA,
        "checked_head": _git(root, "rev-parse", "HEAD"),
        "exact_node": EXACT_NODE,
        "toolchain_attestation_sha256": identity_digest,
        "bounds": {
            "serial_repetitions": SERIAL_REPETITIONS,
            "concurrent_widths": list(CONCURRENT_WIDTHS),
            "concurrent_waves": CONCURRENT_WAVES,
            "invocation_timeout_seconds": INVOCATION_TIMEOUT_SECONDS,
        },
        "host_snapshots": phases,
        "matrices": matrices,
    }
    output.write_text(_canonical(payload), encoding="utf-8")
    return int(failed)


def _regular_files(root: Path) -> list[Path]:
    files = sorted(root.iterdir(), key=lambda path: path.name)
    if any(path.is_symlink() or not path.is_file() for path in files):
        raise ValueError("diagnostic evidence must be flat regular files")
    return files


def seal(source: Path, destination: Path, head: str, run_id: str, attempt: str) -> None:
    """Copy flat evidence and create a canonical SHA256 manifest."""
    if destination.exists():
        raise ValueError("sealed diagnostic destination already exists")
    if not (source / "toolchain-identity.json").is_file():
        raise ValueError("toolchain identity evidence is unavailable")
    load_toolchain_identity(source / "toolchain-identity.json")
    destination.mkdir(mode=0o700)
    for path in _regular_files(source):
        shutil.copyfile(path, destination / path.name)
    files = {
        path.name: {"sha256": _digest(path), "size": path.stat().st_size}
        for path in _regular_files(destination)
    }
    manifest = {
        "schema": "pdd-issue-2083-evidence-manifest-v1",
        "subject_sha": SUBJECT_SHA,
        "source_sha": head,
        "run_id": run_id,
        "run_attempt": attempt,
        "files": files,
    }
    (destination / "manifest.json").write_text(_canonical(manifest), encoding="utf-8")
    for path in _regular_files(destination):
        path.chmod(0o444)
    destination.chmod(0o555)


def verify_seal(root: Path) -> None:
    """Verify canonical sealed evidence and all recorded file digests."""
    manifest_path = root / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if _canonical(manifest) != manifest_path.read_text(encoding="utf-8"):
        raise ValueError("diagnostic manifest is not canonical")
    actual = {
        path.name: {"sha256": _digest(path), "size": path.stat().st_size}
        for path in _regular_files(root)
        if path.name != "manifest.json"
    }
    if manifest.get("files") != actual:
        raise ValueError("diagnostic SHA256 manifest mismatch")
    load_toolchain_identity(root / "toolchain-identity.json")


def main() -> int:
    """Dispatch toolchain attestation, diagnostic execution, and evidence seal."""
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="operation", required=True)
    attest = subparsers.add_parser("attest-toolchain")
    attest.add_argument("--toolchain-root", type=Path, required=True)
    attest.add_argument("--runtime-manifest", type=Path, required=True)
    attest.add_argument("--output", type=Path, required=True)
    run = subparsers.add_parser("run")
    run.add_argument("--root", type=Path, required=True)
    run.add_argument("--output", type=Path, required=True)
    run.add_argument("--toolchain-identity", type=Path, required=True)
    seal_parser = subparsers.add_parser("seal")
    seal_parser.add_argument("--source", type=Path, required=True)
    seal_parser.add_argument("--destination", type=Path, required=True)
    seal_parser.add_argument("--source-sha", required=True)
    seal_parser.add_argument("--run-id", required=True)
    seal_parser.add_argument("--attempt", required=True)
    verify_parser = subparsers.add_parser("verify-seal")
    verify_parser.add_argument("--root", type=Path, required=True)
    args = parser.parse_args()
    if args.operation == "attest-toolchain":
        attest_toolchain(args.toolchain_root, args.runtime_manifest, args.output)
        return 0
    if args.operation == "run":
        return run_matrix(
            args.root.resolve(), args.output, args.toolchain_identity,
        )
    if args.operation == "seal":
        seal(
            args.source,
            args.destination,
            args.source_sha,
            args.run_id,
            args.attempt,
        )
        return 0
    verify_seal(args.root)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
