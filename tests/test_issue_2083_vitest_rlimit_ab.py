"""Contracts for the immutable issue-2083 RLIMIT_AS A/B diagnostic."""
# pylint: disable=missing-function-docstring,protected-access,duplicate-code

from __future__ import annotations

import hashlib
import importlib.util
import json
import subprocess
import sys
from dataclasses import asdict
from pathlib import Path

import pytest

from pdd.sync_core import runner as production_runner
from pdd.sync_core.supervisor import SupervisorLimits


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/ci/run_issue_2083_vitest_rlimit_ab.py"
CONTROL = ROOT / "scripts/ci/issue_2083_vitest_rlimit_2g.py"
CANDIDATE = ROOT / "scripts/ci/issue_2083_vitest_rlimit_4g.py"
BARRIER = ROOT / "scripts/ci/issue_2083_vitest_barrier.py"
SOURCE_PATHS = {
    path.relative_to(ROOT).as_posix()
    for path in (SCRIPT, CONTROL, CANDIDATE, BARRIER, Path(__file__))
}
SOURCE_SHA = "c" * 40


def _load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _runner():
    return _load(SCRIPT, "issue_2083_vitest_rlimit_ab")


def _records(
    module,
    *,
    candidate_aborts: int = 0,
    control_by_stratum: tuple[int, int, int] = (2, 2, 1),
):
    schedule = module.build_schedule()
    remaining = {
        "serial": control_by_stratum[0],
        "width-2": control_by_stratum[1],
        "width-4": control_by_stratum[2],
    }
    candidate_remaining = candidate_aborts
    records = []
    for item in schedule:
        status = "pass"
        if item.arm == "control-2g" and remaining[item.stratum]:
            status = "sigabrt"
            remaining[item.stratum] -= 1
        elif item.arm == "candidate-4g" and candidate_remaining:
            status = "sigabrt"
            candidate_remaining -= 1
        records.append(
            module.ObservationResult(
                observation=item.index,
                arm=item.arm,
                stratum=item.stratum,
                status=status,
                diagnostic_sha256="a" * 64,
            )
        )
    return records


def _live_results(path: Path, module) -> None:
    path.mkdir()
    payload = {
        "schema": module.RESULTS_SCHEMA,
        "subject_sha": module.SUBJECT_SHA,
        "source_sha": SOURCE_SHA,
        "toolchain": {
            "node": module.EXPECTED_NODE_VERSION,
            "npm": module.EXPECTED_NPM_VERSION,
            "vitest": module.EXPECTED_VITEST_VERSION,
            "runtime_manifest_sha256": "a" * 64,
            "launcher_sha256": "b" * 64,
            "entrypoint_sha256": "a" * 64,
            "native_closure_sha256": "b" * 64,
            "package_json_sha256": module.EXPECTED_PACKAGE_JSON_SHA256,
            "package_lock_sha256": module.EXPECTED_PACKAGE_LOCK_SHA256,
        },
        "observations": [asdict(record) for record in _records(module)],
        "decision": {
            "state": "accepted",
            "candidate_sigabrt": 0,
            "control_sigabrt": 5,
            "control_sigabrt_strata": 3,
            "fisher_one_sided_p": module.fisher_exact_control_greater(0, 5),
        },
    }
    (path / "results.json").write_text(module.canonical_json(payload), encoding="utf-8")


def test_source_scope_is_exact_and_has_no_workflow() -> None:
    assert all(path.exists() for path in (SCRIPT, CONTROL, CANDIDATE, BARRIER))
    assert SOURCE_PATHS == {
        "scripts/ci/run_issue_2083_vitest_rlimit_ab.py",
        "scripts/ci/issue_2083_vitest_rlimit_2g.py",
        "scripts/ci/issue_2083_vitest_rlimit_4g.py",
        "scripts/ci/issue_2083_vitest_barrier.py",
        "tests/test_issue_2083_vitest_rlimit_ab.py",
    }
    assert not (ROOT / ".github/workflows/issue-2083-vitest-rlimit-ab.yml").exists()


def test_schedule_has_exact_counts_order_and_bounds() -> None:
    module = _runner()
    schedule = module.build_schedule()

    assert len(schedule) == 60
    assert [item.index for item in schedule] == list(range(1, 61))
    assert sum(item.arm == "control-2g" for item in schedule) == 30
    assert sum(item.arm == "candidate-4g" for item in schedule) == 30
    serial = [item for item in schedule if item.width == 1]
    assert len(serial) == 24
    assert [
        tuple(item.arm for item in serial[offset : offset + 2])
        for offset in range(0, 24, 2)
    ] == [
        ("control-2g", "candidate-4g") if pair % 2 == 0
        else ("candidate-4g", "control-2g")
        for pair in range(12)
    ]
    for width in (2, 4):
        waves = {}
        for item in schedule:
            if item.width == width:
                waves.setdefault(item.wave, []).append(item)
        assert len(waves) == 6
        assert [items[0].arm for items in waves.values()] == [
            "control-2g", "candidate-4g",
            "candidate-4g", "control-2g",
            "control-2g", "candidate-4g",
        ]
        assert all(len(items) == width for items in waves.values())
        assert all(len({item.arm for item in items}) == 1 for items in waves.values())
    assert module.INVOCATION_TIMEOUT_SECONDS == 75


@pytest.mark.parametrize(
    ("path", "virtual_memory"),
    [(CONTROL, 2 * 1024**3), (CANDIDATE, 4 * 1024**3)],
)
def test_plugins_assert_every_original_field_and_change_only_rlimit_as(
    monkeypatch: pytest.MonkeyPatch,
    path: Path,
    virtual_memory: int,
) -> None:
    plugin = _load(path, f"plugin_{virtual_memory}")
    original = SupervisorLimits(
        max_output_bytes=16 * 1024**2,
        max_writable_bytes=512 * 1024**2,
        max_memory_bytes=4 * 1024**3,
        max_virtual_memory_bytes=2 * 1024**3,
        max_cpu_seconds=300,
        max_processes=128,
    )
    monkeypatch.setattr(production_runner, "_VITEST_SUPERVISOR_LIMITS", original)

    plugin.pytest_configure()

    actual = production_runner._VITEST_SUPERVISOR_LIMITS
    assert asdict(actual) == asdict(original) | {
        "max_virtual_memory_bytes": virtual_memory
    }

    monkeypatch.setattr(
        production_runner,
        "_VITEST_SUPERVISOR_LIMITS",
        SupervisorLimits(max_memory_bytes=3 * 1024**3),
    )
    with pytest.raises(RuntimeError, match="production Vitest limits changed"):
        plugin.pytest_configure()


def test_no_arm_selector_or_candidate_output_is_accepted() -> None:
    sources = "\n".join(
        path.read_text(encoding="utf-8") for path in (SCRIPT, CONTROL, CANDIDATE)
    )
    forbidden = (
        "PDD_2083_ARM",
        "--arm",
        "candidate_stdout",
        "candidate_stderr",
        "stdout_text",
        "stderr_text",
    )
    assert all(value not in sources for value in forbidden)
    assert "v22.23.1" in sources
    assert "10.9.8" in sources
    assert "4.1.10" in sources
    assert "PDD_REAL_VITEST_TOOLCHAIN_MANIFEST" in sources
    assert "test_real_vitest_runs_copied_entrypoint" in sources


@pytest.mark.parametrize(
    ("candidate", "control", "expected"),
    [
        (0, 0, 1.0),
        (0, 5, 0.026092774308652998),
        (0, 6, 0.011860351958478633),
        (1, 5, 0.09725488605952479),
        (5, 5, 0.6346788379107509),
    ],
)
def test_fisher_exact_known_vectors(
    candidate: int, control: int, expected: float
) -> None:
    assert _runner().fisher_exact_control_greater(candidate, control) == pytest.approx(
        expected, rel=1e-12
    )


def test_acceptance_requires_zero_candidate_five_control_two_strata_and_p() -> None:
    module = _runner()
    accepted = module.evaluate(_records(module))
    candidate_failure = module.evaluate(_records(module, candidate_aborts=1))
    weak_control = module.evaluate(
        _records(module, control_by_stratum=(2, 1, 1))
    )
    one_stratum = module.evaluate(
        _records(module, control_by_stratum=(5, 0, 0))
    )

    assert accepted.state == "accepted"
    assert accepted.exit_code == module.EXIT_ACCEPTED
    assert candidate_failure.state == "rejected"
    assert candidate_failure.exit_code == module.EXIT_REJECTED
    assert weak_control.state == "inconclusive"
    assert weak_control.exit_code == module.EXIT_INCONCLUSIVE
    assert one_stratum.state == "inconclusive"


def test_classification_is_exact_and_retains_only_a_hash() -> None:
    module = _runner()
    secret = "candidate-secret"
    passing = module.classify_completed(0, secret, "")
    abort = module.classify_completed(
        1,
        secret,
        "reporter=missing; kind=signal; signal=SIGABRT; signal_number=6; "
        "cgroup_memory_oom_delta=0; cgroup_memory_oom_kill_delta=0; "
        "cgroup_pids_max_delta=0; "
        "diagnostic_sha256="
        "bb513afd31fa58609832d821820622c8dbc8f357e8363c695add12000f5ad1c6",
    )
    fallback = module.classify_completed(1, secret, "ordinary pytest failure")

    assert passing.status == "pass"
    assert abort.status == "sigabrt"
    assert fallback.status == "infrastructure"
    assert passing.diagnostic_sha256 == hashlib.sha256(
        (secret + "\0").encode()
    ).hexdigest()
    assert secret not in json.dumps(asdict(passing))
    assert not hasattr(passing, "stdout")
    assert not hasattr(passing, "stderr")


@pytest.mark.parametrize(
    ("returncode", "suffix"),
    [
        (137, ""),
        (1, "; arbitrary-suffix=1"),
        (1, " cgroup_memory_oom_delta=1"),
        (1, " cgroup_memory_oom_kill_delta=1"),
        (1, " cgroup_pids_max_delta=1"),
        (1, " diagnostic_sha256=" + "c" * 64),
    ],
)
def test_sigabrt_classification_rejects_incomplete_or_forged_prior_class(
    returncode: int,
    suffix: str,
) -> None:
    module = _runner()
    trusted = (
        "reporter=missing; kind=signal; signal=SIGABRT; signal_number=6; "
        "cgroup_memory_oom_delta=0; cgroup_memory_oom_kill_delta=0; "
        "cgroup_pids_max_delta=0; "
        "diagnostic_sha256="
        "bb513afd31fa58609832d821820622c8dbc8f357e8363c695add12000f5ad1c6"
    )
    result = module.classify_completed(returncode, "", trusted + suffix)

    assert result.status == "infrastructure"


def test_source_identity_requires_exact_committed_clean_source(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    module = _runner()
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(
        ["git", "config", "user.email", "runner@example.com"],
        cwd=tmp_path,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Runner"],
        cwd=tmp_path,
        check=True,
    )
    (tmp_path / "base").write_text("base\n", encoding="utf-8")
    subprocess.run(["git", "add", "base"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "base"], cwd=tmp_path, check=True)
    base = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    source = tmp_path / "scripts/ci/diagnostic.py"
    source.parent.mkdir(parents=True)
    source.write_text("immutable = True\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "source"], cwd=tmp_path, check=True)
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    monkeypatch.setattr(module, "SUBJECT_SHA", base)
    monkeypatch.setattr(module, "_SOURCE_PATHS", {"scripts/ci/diagnostic.py"})

    assert module.source_identity(tmp_path) == head

    source.write_text("immutable = False\n", encoding="utf-8")
    with pytest.raises(ValueError, match="clean"):
        module.source_identity(tmp_path)


def test_infrastructure_result_is_distinct_from_statistical_states() -> None:
    module = _runner()
    records = _records(module)
    records[0] = module.ObservationResult(
        observation=1,
        arm=records[0].arm,
        stratum=records[0].stratum,
        status="infrastructure",
        diagnostic_sha256="b" * 64,
    )
    decision = module.evaluate(records)

    assert decision.state == "infrastructure"
    assert decision.exit_code == module.EXIT_INFRASTRUCTURE


def test_seal_verifies_and_rejects_replay_mutation_and_extra_file(
    tmp_path: Path,
) -> None:
    module = _runner()
    live = tmp_path / "live"
    sealed = tmp_path / "sealed"
    _live_results(live, module)

    module.seal(live, sealed, SOURCE_SHA, "12345", 1)
    module.verify_seal(sealed, SOURCE_SHA, "12345", 1)

    with pytest.raises(ValueError, match="source SHA"):
        module.verify_seal(sealed, "d" * 40, "12345", 1)
    with pytest.raises(ValueError, match="run ID"):
        module.verify_seal(sealed, SOURCE_SHA, "54321", 1)
    results = sealed / "results.json"
    results.chmod(0o644)
    results.write_text("{}", encoding="utf-8")
    with pytest.raises(ValueError, match="SHA256"):
        module.verify_seal(sealed, SOURCE_SHA, "12345", 1)

    results.write_text(
        (live / "results.json").read_text(encoding="utf-8"), encoding="utf-8"
    )
    sealed.chmod(0o755)
    (sealed / "extra.json").write_text("{}", encoding="utf-8")
    with pytest.raises(ValueError, match="file set"):
        module.verify_seal(sealed, SOURCE_SHA, "12345", 1)


def test_seal_rejects_noncanonical_results_and_copy_fallback_is_safe(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    module = _runner()
    live = tmp_path / "live"
    _live_results(live, module)
    with pytest.raises(ValueError, match="source SHA"):
        module.seal(live, tmp_path / "false-source", "d" * 40, "run", 1)
    payload = json.loads((live / "results.json").read_text(encoding="utf-8"))
    (live / "results.json").write_text(json.dumps(payload, indent=2), encoding="utf-8")
    with pytest.raises(ValueError, match="canonical"):
        module.seal(live, tmp_path / "bad", SOURCE_SHA, "run", 1)

    payload["candidate_output"] = "must never be sealed"
    (live / "results.json").write_text(module.canonical_json(payload), encoding="utf-8")
    with pytest.raises(ValueError, match="fields"):
        module.seal(live, tmp_path / "raw", SOURCE_SHA, "run", 1)
    payload.pop("candidate_output")
    (live / "results.json").write_text(module.canonical_json(payload), encoding="utf-8")
    monkeypatch.setattr(module.os, "link", lambda *_args: (_ for _ in ()).throw(OSError()))
    sealed = tmp_path / "fallback"
    module.seal(live, sealed, SOURCE_SHA, "run", 1)
    module.verify_seal(sealed, SOURCE_SHA, "run", 1)
