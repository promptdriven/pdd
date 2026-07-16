"""Run and seal the immutable issue-2083 RLIMIT_AS A/B diagnostic."""
# pylint: disable=too-many-locals,too-many-branches,too-many-boolean-expressions

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path


SUBJECT_SHA = "f4cfa48036993d49332519b6ce0625470a1f14e4"
EXACT_NODE = (
    "tests/test_sync_core_runner_vitest.py::"
    "test_real_vitest_runs_copied_entrypoint_without_candidate_result_access"
)
EXPECTED_NODE_VERSION = "v22.23.1"
EXPECTED_NPM_VERSION = "10.9.8"
EXPECTED_VITEST_VERSION = "4.1.10"
EXPECTED_PACKAGE_JSON_SHA256 = (
    "63b0ce64263ea3acaed934e5fb5fbbb98d7fcd7673acd40e164dea2a648f2da5"
)
EXPECTED_PACKAGE_LOCK_SHA256 = (
    "bfc69a55d08997f553a0901c2ec0b7830cb01d6c6cc81257d150dcc79d20783c"
)
INVOCATION_TIMEOUT_SECONDS = 75
RESULTS_SCHEMA = "pdd-issue-2083-vitest-rlimit-ab-results-v1"
MANIFEST_SCHEMA = "pdd-issue-2083-vitest-rlimit-ab-manifest-v1"
EXIT_ACCEPTED = 0
EXIT_REJECTED = 20
EXIT_INCONCLUSIVE = 21
EXIT_INFRASTRUCTURE = 22
_ARMS = ("control-2g", "candidate-4g")
_PLUGIN = {
    "control-2g": "scripts.ci.issue_2083_vitest_rlimit_2g",
    "candidate-4g": "scripts.ci.issue_2083_vitest_rlimit_4g",
}
_BARRIER_PLUGIN = "scripts.ci.issue_2083_vitest_barrier"
_EXPECTED_SIGABRT_DETAIL = (
    "reporter=missing; kind=signal; signal=SIGABRT; signal_number=6; "
    "cgroup_memory_oom_delta=0; cgroup_memory_oom_kill_delta=0; "
    "cgroup_pids_max_delta=0; "
    "diagnostic_sha256="
    "bb513afd31fa58609832d821820622c8dbc8f357e8363c695add12000f5ad1c6"
)
_SIGABRT = re.compile(
    re.escape(_EXPECTED_SIGABRT_DETAIL) + r"(?=\r?\n|$)"
)
_SHA = re.compile(r"[0-9a-f]{40}")
_RUN_ID = re.compile(r"[A-Za-z0-9._-]{1,128}")
_HEX_DIGEST = re.compile(r"[0-9a-f]{64}")
_SOURCE_PATHS = {
    "scripts/ci/run_issue_2083_vitest_rlimit_ab.py",
    "scripts/ci/issue_2083_vitest_rlimit_2g.py",
    "scripts/ci/issue_2083_vitest_rlimit_4g.py",
    "scripts/ci/issue_2083_vitest_barrier.py",
    "tests/test_issue_2083_vitest_rlimit_ab.py",
}


@dataclass(frozen=True)
class Observation:
    """One immutable matrix position."""

    index: int
    arm: str
    stratum: str
    width: int
    wave: int
    position: int


@dataclass(frozen=True)
class ClassifiedResult:
    """Sanitized subprocess result retaining no raw process output."""

    status: str
    diagnostic_sha256: str


@dataclass(frozen=True)
class ObservationResult:
    """Sanitized result bound to one matrix position."""

    observation: int
    arm: str
    stratum: str
    status: str
    diagnostic_sha256: str


@dataclass(frozen=True)
class Decision:
    """Terminal statistical or infrastructure decision."""

    state: str
    exit_code: int
    candidate_sigabrt: int
    control_sigabrt: int
    control_sigabrt_strata: int
    fisher_one_sided_p: float


def canonical_json(payload: object) -> str:
    """Return the sole accepted JSON encoding."""
    return json.dumps(payload, separators=(",", ":"), sort_keys=True)


def _append_wave(
    schedule: list[Observation],
    *,
    arm: str,
    width: int,
    wave: int,
) -> None:
    stratum = f"width-{width}"
    for position in range(1, width + 1):
        schedule.append(
            Observation(
                index=len(schedule) + 1,
                arm=arm,
                stratum=stratum,
                width=width,
                wave=wave,
                position=position,
            )
        )


def build_schedule() -> tuple[Observation, ...]:
    """Build the fixed 60-observation serial and homogeneous-wave matrix."""
    schedule: list[Observation] = []
    for pair in range(12):
        order = _ARMS if pair % 2 == 0 else tuple(reversed(_ARMS))
        for position, arm in enumerate(order, start=1):
            schedule.append(
                Observation(
                    index=len(schedule) + 1,
                    arm=arm,
                    stratum="serial",
                    width=1,
                    wave=pair + 1,
                    position=position,
                )
            )
    wave_number = 13
    for width in (2, 4):
        for repetition in range(3):
            order = _ARMS if repetition % 2 == 0 else tuple(reversed(_ARMS))
            for arm in order:
                _append_wave(
                    schedule,
                    arm=arm,
                    width=width,
                    wave=wave_number,
                )
                wave_number += 1
    return tuple(schedule)


def fisher_exact_control_greater(
    candidate_sigabrt: int,
    control_sigabrt: int,
    sample_size: int = 30,
) -> float:
    """Compute the one-sided exact probability without optional dependencies."""
    values = (candidate_sigabrt, control_sigabrt, sample_size)
    if any(not isinstance(value, int) or isinstance(value, bool) for value in values):
        raise ValueError("Fisher inputs must be integers")
    if not 0 <= candidate_sigabrt <= sample_size:
        raise ValueError("candidate count is invalid")
    if not 0 <= control_sigabrt <= sample_size:
        raise ValueError("control count is invalid")
    total_success = candidate_sigabrt + control_sigabrt
    population = 2 * sample_size
    denominator = math.comb(population, sample_size)
    maximum_candidate = min(sample_size, total_success)
    minimum_candidate = max(0, total_success - sample_size)
    probability = 0.0
    for candidate_count in range(
        minimum_candidate,
        min(candidate_sigabrt, maximum_candidate) + 1,
    ):
        probability += (
            math.comb(total_success, candidate_count)
            * math.comb(population - total_success, sample_size - candidate_count)
            / denominator
        )
    return probability


def classify_completed(
    returncode: int,
    standard_output: str,
    standard_error: str,
) -> ClassifiedResult:
    """Classify exact SIGABRT evidence and immediately reduce output to a hash."""
    encoded = (standard_output + "\0" + standard_error).encode(
        "utf-8", errors="replace"
    )
    digest = hashlib.sha256(encoded).hexdigest()
    if returncode == 0:
        status = "pass"
    elif returncode == 1 and _SIGABRT.search(
        standard_output + "\n" + standard_error
    ):
        status = "sigabrt"
    else:
        status = "infrastructure"
    return ClassifiedResult(status=status, diagnostic_sha256=digest)


def evaluate(records: list[ObservationResult]) -> Decision:
    """Apply the fixed acceptance contract to exactly 60 observations."""
    expected = build_schedule()
    if len(records) != len(expected):
        return Decision("infrastructure", EXIT_INFRASTRUCTURE, 0, 0, 0, 1.0)
    for record, observation in zip(records, expected, strict=True):
        if (
            record.observation != observation.index
            or record.arm != observation.arm
            or record.stratum != observation.stratum
            or record.status not in {"pass", "sigabrt", "infrastructure"}
            or _HEX_DIGEST.fullmatch(record.diagnostic_sha256) is None
        ):
            return Decision("infrastructure", EXIT_INFRASTRUCTURE, 0, 0, 0, 1.0)
    candidate = sum(
        record.arm == "candidate-4g" and record.status == "sigabrt"
        for record in records
    )
    control = sum(
        record.arm == "control-2g" and record.status == "sigabrt"
        for record in records
    )
    strata = len(
        {
            record.stratum
            for record in records
            if record.arm == "control-2g" and record.status == "sigabrt"
        }
    )
    probability = fisher_exact_control_greater(candidate, control)
    if any(record.status == "infrastructure" for record in records):
        state, exit_code = "infrastructure", EXIT_INFRASTRUCTURE
    elif candidate:
        state, exit_code = "rejected", EXIT_REJECTED
    elif control >= 5 and strata >= 2 and probability < 0.05:
        state, exit_code = "accepted", EXIT_ACCEPTED
    else:
        state, exit_code = "inconclusive", EXIT_INCONCLUSIVE
    return Decision(state, exit_code, candidate, control, strata, probability)


def _run_command(
    root: Path,
    observation: Observation,
    barrier_directory: Path | None,
) -> ObservationResult:
    command = [
        sys.executable,
        "-m",
        "pytest",
        "-q",
        EXACT_NODE,
        "-p",
        _PLUGIN[observation.arm],
    ]
    environment = dict(os.environ)
    if barrier_directory is not None:
        command.extend(("-p", _BARRIER_PLUGIN))
        environment.update(
            {
                "PDD_2083_BARRIER_DIRECTORY": str(barrier_directory),
                "PDD_2083_BARRIER_PARTIES": str(observation.width),
                "PDD_2083_BARRIER_TOKEN": f"p{observation.position}",
            }
        )
    try:
        completed = subprocess.run(
            command,
            cwd=root,
            env=environment,
            capture_output=True,
            text=True,
            timeout=INVOCATION_TIMEOUT_SECONDS,
            check=False,
        )
        classified = classify_completed(
            completed.returncode,
            completed.stdout,
            completed.stderr,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        classified = ClassifiedResult(
            status="infrastructure",
            diagnostic_sha256=hashlib.sha256(
                type(exc).__name__.encode("ascii")
            ).hexdigest(),
        )
    return ObservationResult(
        observation=observation.index,
        arm=observation.arm,
        stratum=observation.stratum,
        status=classified.status,
        diagnostic_sha256=classified.diagnostic_sha256,
    )


def _exact_version(command: list[str], expected: str, label: str) -> None:
    result = subprocess.run(
        command,
        capture_output=True,
        text=True,
        check=True,
        timeout=30,
    )
    if result.stdout.strip() != expected:
        raise ValueError(f"issue-2083 {label} version changed")


def _exact_role(value: object, label: str, *, directory: bool = False) -> Path:
    if not isinstance(value, str):
        raise ValueError(f"issue-2083 {label} role is invalid")
    candidate = Path(value)
    try:
        resolved = candidate.resolve(strict=True)
    except OSError as exc:
        raise ValueError(f"issue-2083 {label} role is unavailable") from exc
    if candidate != resolved or candidate.is_symlink():
        raise ValueError(f"issue-2083 {label} role is not canonical")
    if directory != resolved.is_dir() or (not directory and not resolved.is_file()):
        raise ValueError(f"issue-2083 {label} role type is invalid")
    return resolved


def _runtime_identity(root: Path) -> dict[str, str]:
    manifest_value = os.environ.get("PDD_REAL_VITEST_TOOLCHAIN_MANIFEST")
    if not manifest_value:
        raise ValueError("issue-2083 Vitest toolchain manifest is unavailable")
    manifest = Path(manifest_value)
    if manifest.is_symlink() or not manifest.is_file():
        raise ValueError("issue-2083 Vitest toolchain manifest is unavailable")
    try:
        payload = json.loads(manifest.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ValueError("issue-2083 Vitest toolchain manifest is malformed") from exc
    if not isinstance(payload, dict) or set(payload) != {"version", "roles"}:
        raise ValueError("issue-2083 Vitest toolchain manifest fields changed")
    if payload["version"] != 1 or isinstance(payload["version"], bool):
        raise ValueError("issue-2083 Vitest toolchain manifest version changed")
    roles = payload["roles"]
    expected_roles = {
        "launcher", "entrypoint", "dependencies", "native_runtime", "lockfile"
    }
    if not isinstance(roles, dict) or set(roles) != expected_roles:
        raise ValueError("issue-2083 Vitest toolchain roles changed")
    launcher = _exact_role(roles["launcher"], "launcher")
    entrypoint = _exact_role(roles["entrypoint"], "entrypoint")
    dependencies = _exact_role(roles["dependencies"], "dependencies", directory=True)
    lockfile = _exact_role(roles["lockfile"], "lockfile")
    native_values = roles["native_runtime"]
    if not isinstance(native_values, list) or not native_values:
        raise ValueError("issue-2083 native runtime role changed")
    native = [_exact_role(value, "native runtime") for value in native_values]
    if native != sorted(native) or len(set(native)) != len(native):
        raise ValueError("issue-2083 native runtime role is not canonical")
    if entrypoint != dependencies / "vitest/vitest.mjs":
        raise ValueError("issue-2083 Vitest entrypoint changed")
    if lockfile.parent != dependencies.parent:
        raise ValueError("issue-2083 Vitest lockfile root changed")
    package = lockfile.with_name("package.json")
    vitest_package = dependencies / "vitest/package.json"
    if (
        _digest(package) != EXPECTED_PACKAGE_JSON_SHA256
        or _digest(lockfile) != EXPECTED_PACKAGE_LOCK_SHA256
        or _digest(root / ".github/toolchains/vitest/package.json")
        != EXPECTED_PACKAGE_JSON_SHA256
        or _digest(root / ".github/toolchains/vitest/package-lock.json")
        != EXPECTED_PACKAGE_LOCK_SHA256
    ):
        raise ValueError("issue-2083 Vitest package identity changed")
    try:
        version = json.loads(vitest_package.read_text(encoding="utf-8"))["version"]
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as exc:
        raise ValueError("issue-2083 Vitest package identity is invalid") from exc
    if version != EXPECTED_VITEST_VERSION:
        raise ValueError("issue-2083 Vitest version changed")
    closure = canonical_json(
        sorted(
            {"name": path.name, "sha256": _digest(path)}
            for path in native
        )
    )
    return {
        "runtime_manifest_sha256": _digest(manifest),
        "launcher_sha256": _digest(launcher),
        "entrypoint_sha256": _digest(entrypoint),
        "native_closure_sha256": hashlib.sha256(closure.encode()).hexdigest(),
        "package_json_sha256": EXPECTED_PACKAGE_JSON_SHA256,
        "package_lock_sha256": EXPECTED_PACKAGE_LOCK_SHA256,
    }


def source_identity(root: Path) -> str:
    """Return HEAD only for the exact committed, clean diagnostic source."""
    ancestry = subprocess.run(
        ["git", "merge-base", "--is-ancestor", SUBJECT_SHA, "HEAD"],
        cwd=root,
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )
    changed = subprocess.run(
        ["git", "diff", "--name-only", SUBJECT_SHA, "HEAD"],
        cwd=root,
        capture_output=True,
        text=True,
        check=True,
        timeout=30,
    ).stdout.splitlines()
    if ancestry.returncode != 0 or set(changed) != _SOURCE_PATHS:
        raise ValueError("issue-2083 subject or immutable source changed")
    dirty = subprocess.run(
        ["git", "status", "--porcelain=v1", "--untracked-files=all"],
        cwd=root,
        capture_output=True,
        text=True,
        check=True,
        timeout=30,
    ).stdout
    if dirty:
        raise ValueError("issue-2083 source tree is not clean")
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=root,
        capture_output=True,
        text=True,
        check=True,
        timeout=30,
    ).stdout.strip()
    if _SHA.fullmatch(head) is None:
        raise ValueError("issue-2083 source HEAD is invalid")
    return head


def verify_assumptions(root: Path) -> tuple[str, dict[str, str]]:
    """Fail closed unless source, Python, Node, npm, and Vitest are exact."""
    source_sha = source_identity(root)
    if sys.version_info[:2] != (3, 12):
        raise ValueError("issue-2083 Python version changed")
    _exact_version(["node", "--version"], EXPECTED_NODE_VERSION, "Node")
    _exact_version(["npm", "--version"], EXPECTED_NPM_VERSION, "npm")
    return (
        source_sha,
        {
            "node": EXPECTED_NODE_VERSION,
            "npm": EXPECTED_NPM_VERSION,
            "vitest": EXPECTED_VITEST_VERSION,
            **_runtime_identity(root),
        },
    )


def run_matrix(root: Path, output: Path) -> int:
    """Run the immutable matrix and write only canonical sanitized evidence."""
    if output.exists():
        raise ValueError("issue-2083 output already exists")
    source_sha, toolchain = verify_assumptions(root)
    schedule = build_schedule()
    results: list[ObservationResult] = []
    cursor = 0
    while cursor < len(schedule):
        first = schedule[cursor]
        if first.width == 1:
            results.append(_run_command(root, first, None))
            cursor += 1
            continue
        wave = first.wave
        members: list[Observation] = []
        while cursor < len(schedule) and schedule[cursor].wave == wave:
            members.append(schedule[cursor])
            cursor += 1
        with tempfile.TemporaryDirectory(prefix="pdd-2083-barrier-") as temporary:
            barrier = Path(temporary)
            with concurrent.futures.ThreadPoolExecutor(
                max_workers=first.width
            ) as executor:
                futures = [
                    executor.submit(_run_command, root, member, barrier)
                    for member in members
                ]
                results.extend(future.result() for future in futures)
    results.sort(key=lambda value: value.observation)
    decision = evaluate(results)
    payload = {
        "schema": RESULTS_SCHEMA,
        "subject_sha": SUBJECT_SHA,
        "source_sha": source_sha,
        "toolchain": toolchain,
        "observations": [asdict(result) for result in results],
        "decision": {
            key: value
            for key, value in asdict(decision).items()
            if key != "exit_code"
        },
    }
    output.mkdir(mode=0o700)
    (output / "results.json").write_text(
        canonical_json(payload),
        encoding="utf-8",
    )
    return decision.exit_code


def _digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _validate_source_sha(value: str) -> str:
    if _SHA.fullmatch(value) is None:
        raise ValueError("diagnostic source SHA is invalid")
    return value


def _validate_run_id(value: str) -> str:
    if _RUN_ID.fullmatch(value) is None:
        raise ValueError("diagnostic run ID is invalid")
    return value


def _validate_attempt(value: str | int) -> int:
    try:
        attempt = int(value)
    except (TypeError, ValueError) as exc:
        raise ValueError("diagnostic attempt is invalid") from exc
    if isinstance(value, bool) or attempt < 1 or str(attempt) != str(value):
        raise ValueError("diagnostic attempt is invalid")
    return attempt


def _regular_names(root: Path) -> set[str]:
    if not root.is_dir() or root.is_symlink():
        raise ValueError("diagnostic evidence directory is invalid")
    names = set()
    for path in root.iterdir():
        if path.is_symlink() or not path.is_file():
            raise ValueError("diagnostic evidence file set is invalid")
        names.add(path.name)
    return names


def _load_canonical_results(path: Path) -> dict[str, object]:
    raw = path.read_text(encoding="utf-8")
    try:
        payload = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ValueError("diagnostic results are malformed") from exc
    if canonical_json(payload) != raw:
        raise ValueError("diagnostic results are not canonical")
    expected_fields = {
        "schema", "subject_sha", "source_sha", "toolchain", "observations",
        "decision",
    }
    if not isinstance(payload, dict) or set(payload) != expected_fields:
        raise ValueError("diagnostic results fields are invalid")
    if payload["schema"] != RESULTS_SCHEMA:
        raise ValueError("diagnostic results schema is invalid")
    if payload["subject_sha"] != SUBJECT_SHA:
        raise ValueError("diagnostic results subject is invalid")
    if not isinstance(payload["source_sha"], str) or _SHA.fullmatch(
        payload["source_sha"]
    ) is None:
        raise ValueError("diagnostic results source SHA is invalid")
    toolchain = payload["toolchain"]
    toolchain_fields = {
        "node", "npm", "vitest", "runtime_manifest_sha256", "launcher_sha256",
        "entrypoint_sha256", "native_closure_sha256", "package_json_sha256",
        "package_lock_sha256",
    }
    if not isinstance(toolchain, dict) or set(toolchain) != toolchain_fields:
        raise ValueError("diagnostic results toolchain fields are invalid")
    if (
        toolchain["node"] != EXPECTED_NODE_VERSION
        or toolchain["npm"] != EXPECTED_NPM_VERSION
        or toolchain["vitest"] != EXPECTED_VITEST_VERSION
        or toolchain["package_json_sha256"] != EXPECTED_PACKAGE_JSON_SHA256
        or toolchain["package_lock_sha256"] != EXPECTED_PACKAGE_LOCK_SHA256
        or any(
            not isinstance(toolchain[field], str)
            or _HEX_DIGEST.fullmatch(toolchain[field]) is None
            for field in (
                "runtime_manifest_sha256", "launcher_sha256",
                "entrypoint_sha256", "native_closure_sha256",
            )
        )
    ):
        raise ValueError("diagnostic results toolchain identity is invalid")
    values = payload["observations"]
    if not isinstance(values, list):
        raise ValueError("diagnostic results observations are invalid")
    records: list[ObservationResult] = []
    record_fields = {
        "observation", "arm", "stratum", "status", "diagnostic_sha256"
    }
    for value in values:
        if not isinstance(value, dict) or set(value) != record_fields:
            raise ValueError("diagnostic observation fields are invalid")
        try:
            records.append(ObservationResult(**value))
        except TypeError as exc:
            raise ValueError("diagnostic observation is invalid") from exc
    schedule = build_schedule()
    if len(records) != len(schedule) or any(
        record.observation != observation.index
        or record.arm != observation.arm
        or record.stratum != observation.stratum
        or record.status not in {"pass", "sigabrt", "infrastructure"}
        or not isinstance(record.diagnostic_sha256, str)
        or _HEX_DIGEST.fullmatch(record.diagnostic_sha256) is None
        for record, observation in zip(records, schedule)
    ):
        raise ValueError("diagnostic observations do not match the matrix")
    evaluated = evaluate(records)
    decision = payload["decision"]
    expected_decision = {
        key: value
        for key, value in asdict(evaluated).items()
        if key != "exit_code"
    }
    if not isinstance(decision, dict) or decision != expected_decision:
        raise ValueError("diagnostic results decision is invalid")
    return payload


def seal(
    source: Path,
    destination: Path,
    expected_source_sha: str,
    run_id: str,
    attempt: str | int,
) -> None:
    """Seal the one canonical result file with replay-bound provenance."""
    if destination.exists():
        raise ValueError("sealed diagnostic destination already exists")
    if _regular_names(source) != {"results.json"}:
        raise ValueError("diagnostic evidence file set is invalid")
    results = _load_canonical_results(source / "results.json")
    source_sha = _validate_source_sha(expected_source_sha)
    if results["source_sha"] != source_sha:
        raise ValueError("diagnostic results source SHA does not match")
    validated_run_id = _validate_run_id(run_id)
    run_attempt = _validate_attempt(attempt)
    destination.mkdir(mode=0o700)
    target = destination / "results.json"
    linked = destination / ".results.link"
    try:
        os.link(source / "results.json", linked)
        shutil.copyfile(linked, target)
    except OSError:
        shutil.copyfile(source / "results.json", target)
    finally:
        linked.unlink(missing_ok=True)
    manifest = {
        "schema": MANIFEST_SCHEMA,
        "subject_sha": SUBJECT_SHA,
        "source_sha": source_sha,
        "run_id": validated_run_id,
        "run_attempt": run_attempt,
        "files": {
            "results.json": {
                "sha256": _digest(target),
                "size": target.stat().st_size,
            }
        },
    }
    (destination / "manifest.json").write_text(
        canonical_json(manifest),
        encoding="utf-8",
    )
    for path in destination.iterdir():
        path.chmod(0o444)
    destination.chmod(0o555)


def verify_seal(
    root: Path,
    expected_source_sha: str,
    expected_run_id: str,
    expected_attempt: str | int,
) -> None:
    """Verify exact inventory, canonical metadata, provenance, and SHA256."""
    if _regular_names(root) != {"manifest.json", "results.json"}:
        raise ValueError("diagnostic evidence file set is invalid")
    raw = (root / "manifest.json").read_text(encoding="utf-8")
    try:
        manifest = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ValueError("diagnostic manifest is malformed") from exc
    if canonical_json(manifest) != raw:
        raise ValueError("diagnostic manifest is not canonical")
    expected_keys = {
        "schema", "subject_sha", "source_sha", "run_id", "run_attempt", "files"
    }
    if not isinstance(manifest, dict) or set(manifest) != expected_keys:
        raise ValueError("diagnostic manifest fields are invalid")
    if manifest["schema"] != MANIFEST_SCHEMA or manifest["subject_sha"] != SUBJECT_SHA:
        raise ValueError("diagnostic manifest identity is invalid")
    if manifest["source_sha"] != _validate_source_sha(expected_source_sha):
        raise ValueError("diagnostic manifest source SHA is invalid")
    if manifest["run_id"] != _validate_run_id(expected_run_id):
        raise ValueError("diagnostic manifest run ID does not match")
    if manifest["run_attempt"] != _validate_attempt(expected_attempt):
        raise ValueError("diagnostic manifest attempt does not match")
    files = manifest["files"]
    if not isinstance(files, dict) or set(files) != {"results.json"}:
        raise ValueError("diagnostic manifest file set is invalid")
    record = files["results.json"]
    if (
        not isinstance(record, dict)
        or set(record) != {"sha256", "size"}
        or record["sha256"] != _digest(root / "results.json")
        or record["size"] != (root / "results.json").stat().st_size
    ):
        raise ValueError("diagnostic SHA256 manifest mismatch")
    results = _load_canonical_results(root / "results.json")
    if results["source_sha"] != manifest["source_sha"]:
        raise ValueError("diagnostic results source SHA does not match")


def main() -> int:
    """Run, seal, or verify the immutable diagnostic."""
    parser = argparse.ArgumentParser()
    operations = parser.add_subparsers(dest="operation", required=True)
    run = operations.add_parser("run")
    run.add_argument("--root", required=True, type=Path)
    run.add_argument("--output", required=True, type=Path)
    seal_parser = operations.add_parser("seal")
    seal_parser.add_argument("--source", required=True, type=Path)
    seal_parser.add_argument("--destination", required=True, type=Path)
    seal_parser.add_argument("--expected-source-sha", required=True)
    seal_parser.add_argument("--run-id", required=True)
    seal_parser.add_argument("--attempt", required=True)
    verify = operations.add_parser("verify-seal")
    verify.add_argument("--root", required=True, type=Path)
    verify.add_argument("--expected-source-sha", required=True)
    verify.add_argument("--expected-run-id", required=True)
    verify.add_argument("--expected-attempt", required=True)
    arguments = parser.parse_args()
    if arguments.operation == "run":
        return run_matrix(arguments.root.resolve(), arguments.output)
    if arguments.operation == "seal":
        seal(
            arguments.source,
            arguments.destination,
            arguments.expected_source_sha,
            arguments.run_id,
            arguments.attempt,
        )
        return 0
    verify_seal(
        arguments.root,
        arguments.expected_source_sha,
        arguments.expected_run_id,
        arguments.expected_attempt,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
