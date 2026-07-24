"""Tests for the fail-closed M0 global-sync execution contract."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
from types import SimpleNamespace

import pytest
import yaml


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "verify_global_sync_execution_contract.py"
CURRENT_PROTECTED_BASE_SHA = "d8423f5fcc1b22583f8262b994cf3f154a128b8b"
HISTORICAL_M0_BASE_SHA = "abd9726bddbdb04e9889fbf14f751cb126d7cf23"


def _module():
    spec = importlib.util.spec_from_file_location("execution_contract", SCRIPT)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _write_contract(tmp_path: Path) -> tuple[Path, Path, Path]:
    plan = tmp_path / "plan.md"
    plan.write_text(
        "# Plan\n\nM0 M1 M2 M3 M4 M5\n\n"
        "```bash\n"
        "python -m yaml\n"
        "python scripts/present.py\n"
        "python -m pytest tests/test_present.py\n"
        "```\n",
        encoding="utf-8",
    )
    (tmp_path / "docs").mkdir()
    (tmp_path / ".github" / "workflows").mkdir(parents=True)
    (tmp_path / "tests").mkdir()
    (tmp_path / "scripts").mkdir()
    (tmp_path / "tests" / "test_present.py").write_text("pass\n", encoding="utf-8")
    (tmp_path / "scripts" / "present.py").write_text("pass\n", encoding="utf-8")
    (tmp_path / ".github" / "workflows" / "present.yml").write_text("name: present\n", encoding="utf-8")
    base = "a" * 40
    state = {
        "schema_version": 1,
        "protected_base_sha": base,
        "preflight": {"protected_base_ref": "origin/main", "protected_base_sha": base, "source_checkout_clean": "pending-m0-validation"},
        "integration": {"worktree": "integration", "branch": "feat/m0", "owner": "integration", "base_sha": base},
        "tracks": [{"id": "m0-bootstrap", "owner": "integration", "worktree": "m0", "branch": "feat/m0", "write_set": ["scripts/verify_global_sync_execution_contract.py"]}],
        "command_registry": [
            {"id": "present-module", "state": "EXISTS", "argv": ["python", "-m", "yaml"], "kind": "module", "owner": "integration", "introducing_milestone": "M0", "earliest_invocable_milestone": "M0", "introducing_pr": "local", "last_source_validation_sha": base, "last_wheel_validation_sha": base},
            {"id": "present-script", "state": "EXISTS", "argv": ["python", "scripts/present.py"], "kind": "script", "owner": "integration", "introducing_milestone": "M0", "earliest_invocable_milestone": "M0", "introducing_pr": "local", "last_source_validation_sha": base, "last_wheel_validation_sha": base},
            {"id": "present-test", "state": "EXISTS", "argv": ["python", "-m", "pytest", "tests/test_present.py"], "kind": "test", "owner": "integration", "introducing_milestone": "M0", "earliest_invocable_milestone": "M0", "introducing_pr": "local", "last_source_validation_sha": base, "last_wheel_validation_sha": base},
            {"id": "present-workflow", "state": "EXISTS", "argv": [".github/workflows/present.yml"], "kind": "workflow", "owner": "integration", "introducing_milestone": "M0", "earliest_invocable_milestone": "M0", "introducing_pr": "local", "last_source_validation_sha": base, "last_wheel_validation_sha": base},
        ],
        "validation_steps": [{"id": "m0-contract", "milestone": "M0", "executable": True, "validation_commands": ["present-module", "present-script", "present-test", "present-workflow"]}],
        "active_blocker": "m0-executable-baseline",
        "milestone_order": ["M0", "M1", "M2", "M3", "M4", "M5"],
        "ledger_source": "docs/ledger_source.yaml",
        "generated_ledger": "docs/ledger.yaml",
    }
    ledger = {"execution_contract": {"protected_base_sha": base, "milestone_order": state["milestone_order"], "active_blocker": "m0-executable-baseline", "command_registry": state["command_registry"], "validation_steps": state["validation_steps"]}}
    state_path = tmp_path / "docs" / "state.yaml"
    source_path = tmp_path / "docs" / "ledger_source.yaml"
    output_path = tmp_path / "docs" / "ledger.yaml"
    state_path.write_text(yaml.safe_dump(state, sort_keys=False), encoding="utf-8")
    source_path.write_text(yaml.safe_dump(ledger, sort_keys=False), encoding="utf-8")
    output_path.write_bytes(source_path.read_bytes())
    return plan, state_path, tmp_path


def _verify(tmp_path: Path):
    plan, state, root = _write_contract(tmp_path)
    return _module().verify(plan, state, root=root, validate_cli=False), state, root


def test_execution_contract_accepts_complete_concordant_registry(tmp_path: Path) -> None:
    assert _verify(tmp_path)[0] == []


@pytest.mark.parametrize(
    ("command_id", "kind", "argv", "expected"),
    [
        ("missing-module", "module", ["python", "-m", "missing_global_sync_module"], "module"),
        ("missing-script", "script", ["python", "scripts/missing.py"], "script"),
        ("missing-test", "test", ["python", "-m", "pytest", "tests/missing.py"], "test"),
        ("missing-workflow", "workflow", [".github/workflows/missing.yml"], "workflow"),
    ],
)
def test_execution_contract_rejects_missing_declared_component(tmp_path: Path, command_id: str, kind: str, argv: list[str], expected: str) -> None:
    _, state_path, root = _verify(tmp_path)
    state = yaml.safe_load(state_path.read_text(encoding="utf-8"))
    state["command_registry"][0].update({"id": command_id, "kind": kind, "argv": argv})
    state_path.write_text(yaml.safe_dump(state, sort_keys=False), encoding="utf-8")
    errors = _module().verify(root / "plan.md", state_path, root=root, validate_cli=False)
    assert any(expected in error and command_id in error for error in errors)


def test_execution_contract_rejects_empty_executable_validation_and_to_build_invocation(tmp_path: Path) -> None:
    _, state_path, root = _verify(tmp_path)
    state = yaml.safe_load(state_path.read_text(encoding="utf-8"))
    state["validation_steps"][0]["validation_commands"] = []
    state["command_registry"][0]["state"] = "TO_BUILD"
    state["promotion_commands"] = ["present-module"]
    state_path.write_text(yaml.safe_dump(state, sort_keys=False), encoding="utf-8")
    errors = _module().verify(root / "plan.md", state_path, root=root, validate_cli=False)
    assert any("empty validation" in error for error in errors)
    assert any("TO_BUILD" in error for error in errors)


def test_execution_contract_rejects_plan_command_missing_from_registry(tmp_path: Path) -> None:
    _, state_path, root = _verify(tmp_path)
    plan = root / "plan.md"
    plan.write_text(
        plan.read_text(encoding="utf-8").replace(
            "python -m yaml", "python -m missing_global_sync_module"
        ),
        encoding="utf-8",
    )
    errors = _module().verify(plan, state_path, root=root, validate_cli=False)
    assert any("plan command is absent from registry" in error for error in errors)


def test_execution_contract_checks_every_test_target_not_only_the_first(tmp_path: Path) -> None:
    _, state_path, root = _verify(tmp_path)
    state = yaml.safe_load(state_path.read_text(encoding="utf-8"))
    state["command_registry"][2]["argv"].append("tests/missing_later.py")
    state_path.write_text(yaml.safe_dump(state, sort_keys=False), encoding="utf-8")
    errors = _module().verify(root / "plan.md", state_path, root=root, validate_cli=False)
    assert any("present-test" in error and "tests/missing_later.py" in error for error in errors)


def test_execution_contract_requires_validation_milestone_and_lifecycle_order(tmp_path: Path) -> None:
    _, state_path, root = _verify(tmp_path)
    state = yaml.safe_load(state_path.read_text(encoding="utf-8"))
    state["validation_steps"].append({"id": "missing-milestone", "executable": False})
    state["command_registry"][0]["earliest_invocable_milestone"] = "M1"
    state_path.write_text(yaml.safe_dump(state, sort_keys=False), encoding="utf-8")
    errors = _module().verify(root / "plan.md", state_path, root=root, validate_cli=False)
    assert any("validation step milestone" in error for error in errors)
    assert any("before earliest invocable milestone" in error for error in errors)


def test_execution_contract_rejects_exact_click_option_prefix_collision(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    module = _module()

    def fake_run(_: list[str], **__: object) -> SimpleNamespace:
        return SimpleNamespace(returncode=0, stdout="--base-reference TEXT\n", stderr="")

    monkeypatch.setattr(module.subprocess, "run", fake_run)
    errors = module._cli_errors(  # pylint: disable=protected-access
        {"id": "source-certify", "kind": "console", "argv": ["pdd", "certify"], "documented_options": ["--base-ref"]},
        sys.executable, "source", tmp_path,
    )
    assert any("--base-ref" in error for error in errors)


def test_execution_contract_rejects_stale_expected_protected_base(tmp_path: Path) -> None:
    _, state_path, root = _verify(tmp_path)
    errors = _module().verify(
        root / "plan.md", state_path, root=root, validate_cli=False,
        expected_protected_base="b" * 40,
    )
    assert any("expected protected base" in error for error in errors)


def test_execution_contract_rejects_installed_wheel_bound_to_another_digest(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    wheel_root = tmp_path / "wheel-environment"
    wheel_python = wheel_root / "bin" / "python"
    wheel_python.parent.mkdir(parents=True)
    wheel_python.write_text("placeholder\n", encoding="utf-8")
    wheel = tmp_path / "candidate.whl"
    wheel.write_bytes(b"candidate wheel")

    def fake_run(_: list[str], **__: object) -> SimpleNamespace:
        return SimpleNamespace(
            returncode=0,
            stdout='{"direct_url": {"archive_info": {"hash": "sha256=old"}}}\n',
            stderr="",
        )

    module = _module()
    monkeypatch.setattr(module.subprocess, "run", fake_run)
    errors = module._wheel_binding_errors(  # pylint: disable=protected-access
        str(wheel_python), wheel, "a" * 40, tmp_path / "checkout"
    )
    assert any("does not bind" in error for error in errors)


def test_execution_contract_rejects_ledger_base_and_registry_disagreement(tmp_path: Path) -> None:
    _, state_path, root = _verify(tmp_path)
    ledger = yaml.safe_load((root / "docs" / "ledger_source.yaml").read_text(encoding="utf-8"))
    ledger["execution_contract"]["protected_base_sha"] = "b" * 40
    (root / "docs" / "ledger_source.yaml").write_text(yaml.safe_dump(ledger, sort_keys=False), encoding="utf-8")
    errors = _module().verify(root / "plan.md", state_path, root=root, validate_cli=False)
    assert any("base SHA" in error for error in errors)


def test_execution_contract_rejects_wrong_click_parent_and_unsupported_option(tmp_path: Path) -> None:
    _, state_path, root = _verify(tmp_path)
    state = yaml.safe_load(state_path.read_text(encoding="utf-8"))
    state["command_registry"].append({"id": "wrong-parent", "state": "EXISTS", "argv": ["pdd", "sync", "certify"], "kind": "console", "owner": "integration", "introducing_milestone": "M0", "earliest_invocable_milestone": "M0", "introducing_pr": "local", "last_source_validation_sha": "a" * 40, "last_wheel_validation_sha": "a" * 40, "documented_options": ["--not-real"]})
    state["validation_steps"][0]["validation_commands"].append("wrong-parent")
    state_path.write_text(yaml.safe_dump(state, sort_keys=False), encoding="utf-8")
    errors = _module().verify(root / "plan.md", state_path, root=root, validate_cli=True)
    assert any("wrong Click parent" in error for error in errors)
    assert any("--not-real" in error for error in errors)


def test_execution_contract_probes_source_with_current_interpreter_not_path(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _, state_path, root = _verify(tmp_path)
    state = yaml.safe_load(state_path.read_text(encoding="utf-8"))
    state["command_registry"].append({"id": "source-certify", "state": "EXISTS", "argv": ["pdd", "certify"], "kind": "console", "owner": "integration", "introducing_milestone": "M0", "earliest_invocable_milestone": "M0", "introducing_pr": "local", "last_source_validation_sha": None, "last_wheel_validation_sha": None, "documented_options": ["--help"]})
    state["validation_steps"][0]["validation_commands"].append("source-certify")
    state_path.write_text(yaml.safe_dump(state, sort_keys=False), encoding="utf-8")
    observed: list[list[str]] = []

    def fake_run(argv: list[str], **_: object) -> SimpleNamespace:
        observed.append(argv)
        return SimpleNamespace(returncode=0, stdout="--help", stderr="")

    module = _module()
    monkeypatch.setattr(module.subprocess, "run", fake_run)
    module.verify(root / "plan.md", state_path, root=root, validate_cli=True)
    assert observed == [[sys.executable, "-m", "pdd", "certify", "--help"]]


def test_execution_contract_rejects_wheel_probe_that_imports_checkout_source(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    wheel_root = tmp_path / "wheel-environment"
    wheel_python = wheel_root / "bin" / "python"
    wheel_python.parent.mkdir(parents=True)
    wheel_python.write_text("placeholder\n", encoding="utf-8")
    checkout = tmp_path / "checkout"
    (checkout / "pdd").mkdir(parents=True)
    source_package = checkout / "pdd" / "__init__.py"
    source_package.write_text("\n", encoding="utf-8")
    observed: list[tuple[list[str], Path, dict[str, str]]] = []

    def fake_run(argv: list[str], **kwargs: object) -> SimpleNamespace:
        observed.append((argv, kwargs["cwd"], kwargs["env"]))  # type: ignore[index]
        return SimpleNamespace(
            returncode=0,
            stdout=(f'{{"prefix": "{wheel_root}", "pdd_file": "{source_package}"}}\n'),
            stderr="",
        )

    module = _module()
    monkeypatch.setattr(module.subprocess, "run", fake_run)
    errors = module._cli_errors(  # pylint: disable=protected-access
        {"id": "wheel-certify", "kind": "console", "argv": ["pdd", "certify"]},
        str(wheel_python), "built-wheel", checkout,
    )
    assert any("checkout source" in error for error in errors)
    assert observed[0][0][:3] == [str(wheel_python), "-I", "-c"]
    assert observed[0][1] == wheel_root
    assert "PYTHONPATH" not in observed[0][2]


def test_execution_contract_accepts_wheel_only_after_outside_site_packages_preflight(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    wheel_root = tmp_path / "wheel-environment"
    wheel_python = wheel_root / "bin" / "python"
    wheel_python.parent.mkdir(parents=True)
    wheel_python.write_text("placeholder\n", encoding="utf-8")
    package = wheel_root / "lib" / "python3.12" / "site-packages" / "pdd" / "__init__.py"
    package.parent.mkdir(parents=True)
    package.write_text("\n", encoding="utf-8")
    calls = 0

    def fake_run(_: list[str], **__: object) -> SimpleNamespace:
        nonlocal calls
        calls += 1
        return SimpleNamespace(
            returncode=0,
            stdout=(f'{{"prefix": "{wheel_root}", "pdd_file": "{package}"}}\n'
                    if calls == 1 else "--base-ref\n"),
            stderr="",
        )

    module = _module()
    monkeypatch.setattr(module.subprocess, "run", fake_run)
    assert module._cli_errors(  # pylint: disable=protected-access
        {"id": "wheel-certify", "kind": "console", "argv": ["pdd", "certify"], "documented_options": ["--base-ref"]},
        str(wheel_python), "built-wheel", tmp_path / "checkout",
    ) == []
    assert calls == 2


def test_execution_contract_accepts_standard_symlinked_venv_launcher(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    wheel_root = tmp_path / "wheel-environment"
    wheel_python = wheel_root / "bin" / "python"
    wheel_python.parent.mkdir(parents=True)
    wheel_python.symlink_to(Path(sys.executable))
    package = wheel_root / "lib" / "python3.12" / "site-packages" / "pdd" / "__init__.py"
    package.parent.mkdir(parents=True)
    package.write_text("\n", encoding="utf-8")
    calls: list[tuple[list[str], Path, dict[str, str]]] = []

    def fake_run(argv: list[str], **kwargs: object) -> SimpleNamespace:
        calls.append((argv, kwargs["cwd"], kwargs["env"]))  # type: ignore[index]
        stdout = (
            '{"prefix": "' + str(wheel_root) + '", "pdd_file": "' + str(package) + '"}\n'
            if len(calls) == 1 else "--base-ref\n"
        )
        return SimpleNamespace(returncode=0, stdout=stdout, stderr="")

    module = _module()
    monkeypatch.setattr(module.subprocess, "run", fake_run)
    assert module._cli_errors(  # pylint: disable=protected-access
        {"id": "wheel-certify", "kind": "console", "argv": ["pdd", "certify"], "documented_options": ["--base-ref"]},
        str(wheel_python), "built-wheel", tmp_path / "checkout",
    ) == []
    assert calls[0][0][:3] == [str(wheel_python), "-I", "-c"]
    assert calls[0][1] == wheel_root
    assert not {"PYTHONPATH", "PYTHONHOME", "PYTHONUSERBASE"} & calls[0][2].keys()


def test_execution_contract_rejects_venv_launcher_with_resolved_base_prefix(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    wheel_root = tmp_path / "wheel-environment"
    wheel_python = wheel_root / "bin" / "python"
    wheel_python.parent.mkdir(parents=True)
    wheel_python.symlink_to(Path(sys.executable))
    base_package = tmp_path / "base" / "lib" / "python3.12" / "site-packages" / "pdd" / "__init__.py"
    base_package.parent.mkdir(parents=True)
    base_package.write_text("\n", encoding="utf-8")

    def fake_run(_: list[str], **__: object) -> SimpleNamespace:
        return SimpleNamespace(
            returncode=0,
            stdout=(f'{{"prefix": "{tmp_path / "base"}", "pdd_file": "{base_package}"}}\n'),
            stderr="",
        )

    module = _module()
    monkeypatch.setattr(module.subprocess, "run", fake_run)
    errors = module._cli_errors(  # pylint: disable=protected-access
        {"id": "wheel-certify", "kind": "console", "argv": ["pdd", "certify"]},
        str(wheel_python), "built-wheel", tmp_path / "checkout",
    )
    assert any("sys.prefix" in error for error in errors)


def test_execution_contract_rejects_unarchived_legacy_steps(tmp_path: Path) -> None:
    _, state_path, root = _verify(tmp_path)
    for ledger_path in (root / "docs" / "ledger_source.yaml", root / "docs" / "ledger.yaml"):
        ledger = yaml.safe_load(ledger_path.read_text(encoding="utf-8"))
        ledger["steps"] = [{"order": 1, "validation_commands": ["pdd sync certify"]}]
        ledger_path.write_text(yaml.safe_dump(ledger, sort_keys=False), encoding="utf-8")
    errors = _module().verify(root / "plan.md", state_path, root=root, validate_cli=False)
    assert any("legacy step" in error and "ARCHIVED" in error for error in errors)


def test_execution_contract_rejects_invoked_pending_external_and_invalid_validation_sha(tmp_path: Path) -> None:
    _, state_path, root = _verify(tmp_path)
    state = yaml.safe_load(state_path.read_text(encoding="utf-8"))
    state["command_registry"].append({"id": "external", "state": "EXTERNAL_PROTECTED", "argv": ["pdd-sync-checker"], "kind": "console", "owner": "track-c", "introducing_milestone": "M3", "earliest_invocable_milestone": "M3", "introducing_pr": "pending", "artifact_digest": "pending", "control_plane_identity": "pending", "last_source_validation_sha": "not-a-sha", "last_wheel_validation_sha": None})
    state["promotion_commands"] = ["external"]
    state_path.write_text(yaml.safe_dump(state, sort_keys=False), encoding="utf-8")
    errors = _module().verify(root / "plan.md", state_path, root=root, validate_cli=False)
    assert any("EXTERNAL_PROTECTED" in error and "pending binding" in error for error in errors)
    assert any("last_source_validation_sha" in error for error in errors)


def test_execution_contract_requires_plan_named_to_build_components_and_real_state_is_complete() -> None:
    errors = _module().verify(
        ROOT / "docs" / "global_sync_resolution_plan.md",
        ROOT / "docs" / "global_sync_execution_state.yaml",
        root=ROOT,
        validate_cli=False,
    )
    assert errors == []


def test_execution_state_records_the_exact_m0_focused_suite_and_owned_m0_paths() -> None:
    state = yaml.safe_load(
        (ROOT / "docs" / "global_sync_execution_state.yaml").read_text(encoding="utf-8")
    )
    commands = {command["id"]: command for command in state["command_registry"]}
    assert commands["m0-focused-cli-test"]["argv"] == [
        "python", "-m", "pytest", "-q",
        "tests/test_sync_core_cli.py",
        "tests/test_sync_core_transaction.py",
        "tests/test_sync_core_reporting.py",
        "tests/test_sync_core_standalone_package.py",
    ]
    tracks = {track["id"]: track for track in state["tracks"]}
    assert tracks["m0-finalizer-test"]["write_set"] == ["tests/test_sync_core_reporting.py"]
    assert tracks["m0-scope-samples"]["write_set"] == [
        "scripts/verify_global_sync_m0_samples.py", "docs/global_sync_m0_scope_report.md"
    ]


def test_execution_state_and_generated_ledger_bind_the_protected_kickoff_base() -> None:
    """Keep active M0 topology and its ledger anchored to the kickoff base."""
    state = yaml.safe_load(
        (ROOT / "docs" / "global_sync_execution_state.yaml").read_text(encoding="utf-8")
    )
    source = yaml.safe_load(
        (ROOT / "docs" / "global_sync_evidence_ledger_source.yaml").read_text(
            encoding="utf-8"
        )
    )
    generated = yaml.safe_load(
        (ROOT / "docs" / "global_sync_evidence_ledger.yaml").read_text(
            encoding="utf-8"
        )
    )

    assert state["protected_base_sha"] == CURRENT_PROTECTED_BASE_SHA
    assert state["scoreboard"]["base_sha"] == CURRENT_PROTECTED_BASE_SHA
    assert state["integration"]["base_sha"] == CURRENT_PROTECTED_BASE_SHA
    assert source["execution_contract"]["protected_base_sha"] == CURRENT_PROTECTED_BASE_SHA
    assert generated["execution_contract"]["protected_base_sha"] == CURRENT_PROTECTED_BASE_SHA
    tracks = {track["id"]: track for track in state["tracks"]}
    for historical_track in (
        "m0-contract", "m0-finalizer-test", "m0-scope-samples"
    ):
        assert tracks[historical_track]["base_sha"] == HISTORICAL_M0_BASE_SHA
    for current_track in (
        "m0-reporting-remediation", "m0-rebase-state", "m0-scope-current",
        "track-a-repair", "track-b-runner", "track-c-checker", "track-d-routing",
        "track-e-consumer",
    ):
        assert tracks[current_track]["base_sha"] == CURRENT_PROTECTED_BASE_SHA
    reporting = tracks["m0-reporting-remediation"]
    assert reporting["owner"] == "m0-reporting-remediation"
    assert reporting["worktree"] == (
        "/Users/gregtanaka/.local/state/agent-worktrees/promptdriven__pdd/"
        "issue-1932-m0-reporting-selection"
    )
    assert reporting["branch"] == "fix/1932-m0-reporting-selection-20260724"
    assert reporting["base_sha"] == CURRENT_PROTECTED_BASE_SHA
    assert reporting["write_set"] == [
        "pdd/sync_core/reporting.py", "tests/test_sync_core_reporting.py"
    ]
    assert tracks["m0-rebase-state"]["write_set"] == [
        "docs/global_sync_execution_state.yaml",
        "docs/global_sync_evidence_ledger_source.yaml",
        "docs/global_sync_evidence_ledger.yaml",
        "tests/test_global_sync_execution_contract.py",
    ]
    assert tracks["m0-scope-current"]["write_set"] == []
    delivery_tracks = [
        track for track in state["tracks"] if track["id"].startswith("track-")
    ]
    claimed_paths = [
        path for track in delivery_tracks for path in track["write_set"]
    ]
    assert len(claimed_paths) == len(set(claimed_paths))
