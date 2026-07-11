"""Contract tests for the fail-closed trusted Jest adapter."""

import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

import pytest

from pdd.sync_core import (
    AttestationIssue,
    AttestationSigner,
    EvidenceOutcome,
    RunBinding,
    RunnerConfig,
    UnitId,
    VerificationObligation,
    VerificationProfile,
    run_profile,
)
from pdd.sync_core.runner import _jest_command_error, jest_validator_config_digest
from pdd.sync_core.runner import _local_javascript_imports


UNIT = UnitId("repository-1", PurePosixPath("prompts/widget_js.prompt"), "javascript")
IDENTITY = "tests/widget.test.js::widget works"


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()


def _fake_jest(tmp_path: Path) -> Path:
    runner = tmp_path / "fake_jest.py"
    runner.write_text(
        "import json, os, pathlib, time\n"
        "root = pathlib.Path.cwd()\n"
        "mode = (root / 'source.js').read_text().strip() if (root / 'source.js').exists() else 'pass'\n"
        "if mode == 'timeout': time.sleep(5)\n"
        "if mode == 'malformed': pathlib.Path(os.environ['PDD_TRUSTED_JEST_OUTPUT']).write_text('{')\n"
        "else:\n"
        "  tests = [] if mode == 'zero' else [{'identity': 'tests/widget.test.js::widget works', 'status': {'fail': 'failed', 'skip': 'pending', 'todo': 'todo'}.get(mode, 'passed')}]\n"
        "  if mode == 'mismatch': tests = [{'identity': 'tests/widget.test.js::other', 'status': 'passed'}]\n"
        "  if mode == 'candidate': tests.append({'identity': 'tests/widget.test.js::candidate only', 'status': 'passed'})\n"
        "  pathlib.Path(os.environ['PDD_TRUSTED_JEST_OUTPUT']).write_text(json.dumps({'tests': tests}))\n"
    )
    return runner


def _repository(tmp_path: Path, *, mode: str = "pass", config: str = '{"testMatch":["**/*.test.js"]}') -> tuple[Path, str]:
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "runner@example.com")
    _git(root, "config", "user.name", "Runner Test")
    (root / "tests").mkdir()
    (root / "tests/widget.test.js").write_text("test('widget works', () => expect(true).toBe(true));\n")
    (root / "jest.config.json").write_text(config)
    (root / "source.js").write_text(mode)
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "protected Jest tests")
    return root, _git(root, "rev-parse", "HEAD")


def _run(root: Path, base: str, head: str, fake_jest: Path, timeout: int = 2):
    paths = (PurePosixPath("tests/widget.test.js"),)
    try:
        config_digest = jest_validator_config_digest(root, base, paths)
    except ValueError:
        config_digest = "invalid-jest-config"
    obligation = VerificationObligation(
        "jest", "test", "jest", config_digest,
        ("REQ-1",), paths,
    )
    profile = VerificationProfile(UNIT, (obligation,), ("REQ-1",), "profile-v1")
    return run_profile(
        root, profile, RunBinding("snapshot-v1", base, head),
        AttestationIssue(AttestationSigner("trusted-ci", b"v" * 32), "id", "nonce", datetime(2026, 7, 10, tzinfo=timezone.utc)),
        config=RunnerConfig(timeout_seconds=timeout, jest_command=(sys.executable, str(fake_jest))),
    )


def _run_default_jest(root: Path, base: str, head: str, timeout: int = 2):
    paths = (PurePosixPath("tests/widget.test.js"),)
    obligation = VerificationObligation(
        "jest", "test", "jest", jest_validator_config_digest(root, base, paths),
        ("REQ-1",), paths,
    )
    profile = VerificationProfile(UNIT, (obligation,), ("REQ-1",), "profile-v1")
    return run_profile(
        root, profile, RunBinding("snapshot-v1", base, head),
        AttestationIssue(AttestationSigner("trusted-ci", b"v" * 32), "id", "nonce", datetime(2026, 7, 10, tzinfo=timezone.utc)),
        config=RunnerConfig(timeout_seconds=timeout),
    )


@pytest.mark.parametrize(
    ("mode", "outcome"),
    [("pass", EvidenceOutcome.PASS), ("fail", EvidenceOutcome.FAIL), ("skip", EvidenceOutcome.SKIP), ("todo", EvidenceOutcome.SKIP), ("zero", EvidenceOutcome.NOT_COLLECTED), ("timeout", EvidenceOutcome.TIMEOUT), ("malformed", EvidenceOutcome.COLLECTION_ERROR)],
)
def test_jest_normalizes_non_pass_outcomes(tmp_path: Path, mode: str, outcome: EvidenceOutcome) -> None:
    root, commit = _repository(tmp_path, mode=mode)
    _envelope, executions = _run(root, commit, commit, _fake_jest(tmp_path), timeout=1)
    assert executions[0].outcome is outcome


@pytest.mark.parametrize("mode", ["mismatch", "candidate"])
def test_jest_collection_identity_mismatch_cannot_pass(tmp_path: Path, mode: str) -> None:
    root, base = _repository(tmp_path)
    (root / "source.js").write_text(mode)
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change application behavior")
    _envelope, executions = _run(root, base, _git(root, "rev-parse", "HEAD"), _fake_jest(tmp_path))
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED


def test_jest_removed_protected_test_cannot_pass(tmp_path: Path) -> None:
    root, base = _repository(tmp_path)
    (root / "tests/widget.test.js").write_text("// removed\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "remove protected test")
    _envelope, executions = _run(root, base, _git(root, "rev-parse", "HEAD"), _fake_jest(tmp_path))
    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


@pytest.mark.parametrize("path", ["jest.config.json", "setup.js", "transform.js"])
def test_jest_config_and_support_mutation_cannot_pass(tmp_path: Path, path: str) -> None:
    config = '{"setupFilesAfterEnv":["<rootDir>/setup.js"],"transform":{"^.+\\\\.js$":"<rootDir>/transform.js"}}'
    root, base = _repository(tmp_path, config=config)
    (root / "setup.js").write_text("export {};\n")
    (root / "transform.js").write_text("module.exports = {};\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add protected support")
    base = _git(root, "rev-parse", "HEAD")
    (root / path).write_text("changed\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate protected Jest support")
    _envelope, executions = _run(root, base, _git(root, "rev-parse", "HEAD"), _fake_jest(tmp_path))
    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_jest_dirty_support_cannot_influence_run(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    (root / "setup.js").write_text("untracked\n")
    _envelope, executions = _run(root, commit, commit, _fake_jest(tmp_path))
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED


def test_jest_imported_test_helper_mutation_cannot_pass(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/helper.js").write_text("module.exports = { expected: true };\n")
    (root / "tests/widget.test.js").write_text(
        "const { expected } = require('./helper');\n"
        "test('widget works', () => expect(expected).toBe(true));\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add protected Jest helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "tests/helper.js").write_text("module.exports = { expected: false };\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate imported Jest helper")

    _envelope, executions = _run(root, base, _git(root, "rev-parse", "HEAD"), _fake_jest(tmp_path))

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_jest_side_effect_import_helper_mutation_cannot_pass(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/helper.js").write_text("global.expected = true;\n")
    (root / "tests/widget.test.js").write_text(
        "import './helper';\n"
        "test('widget works', () => expect(global.expected).toBe(true));\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add protected side effect helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "tests/helper.js").write_text("global.expected = false;\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate side effect helper")

    _envelope, executions = _run(root, base, _git(root, "rev-parse", "HEAD"), _fake_jest(tmp_path))

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_jest_parent_directory_import_helper_mutation_cannot_pass(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "shared").mkdir()
    (root / "shared/helper.js").write_text("module.exports = { expected: true };\n")
    (root / "tests/widget.test.js").write_text(
        "const { expected } = require('../shared/helper');\n"
        "test('widget works', () => expect(expected).toBe(true));\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add parent import helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "shared/helper.js").write_text("module.exports = { expected: false };\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate parent import helper")

    _envelope, executions = _run(root, base, _git(root, "rev-parse", "HEAD"), _fake_jest(tmp_path))

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_jest_parent_directory_side_effect_import_mutation_cannot_pass(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "shared").mkdir()
    (root / "shared/setup.js").write_text("global.expected = true;\n")
    (root / "tests/widget.test.js").write_text(
        "import '../shared/setup';\n"
        "test('widget works', () => expect(global.expected).toBe(true));\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add parent side effect helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "shared/setup.js").write_text("global.expected = false;\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate parent side effect helper")

    _envelope, executions = _run(root, base, _git(root, "rev-parse", "HEAD"), _fake_jest(tmp_path))

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_jest_parent_directory_index_import_mutation_cannot_pass(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "shared/helpers").mkdir(parents=True)
    (root / "shared/helpers/index.ts").write_text("export const expected = true;\n")
    (root / "tests/widget.test.js").write_text(
        "import { expected } from '../shared/helpers';\n"
        "test('widget works', () => expect(expected).toBe(true));\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add parent index helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "shared/helpers/index.ts").write_text("export const expected = false;\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate parent index helper")

    _envelope, executions = _run(root, base, _git(root, "rev-parse", "HEAD"), _fake_jest(tmp_path))

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_jest_parent_directory_imports_change_validator_digest(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    paths = (PurePosixPath("tests/widget.test.js"),)
    (root / "shared/helpers").mkdir(parents=True)
    (root / "shared/helpers/index.ts").write_text("export const expected = true;\n")
    (root / "shared/setup.js").write_text("global.expected = true;\n")
    (root / "tests/widget.test.js").write_text(
        "import { expected } from '../shared/helpers';\n"
        "import '../shared/setup';\n"
        "test('widget works', () => expect(expected && global.expected).toBe(true));\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add parent import helpers")
    base = _git(root, "rev-parse", "HEAD")
    base_digest = jest_validator_config_digest(root, base, paths)

    (root / "shared/helpers/index.ts").write_text("export const expected = false;\n")
    (root / "shared/setup.js").write_text("global.expected = false;\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate parent import helpers")
    head_digest = jest_validator_config_digest(root, _git(root, "rev-parse", "HEAD"), paths)

    assert head_digest != base_digest


def test_jest_config_reference_index_candidate_changes_validator_digest(tmp_path: Path) -> None:
    config = '{"setupFilesAfterEnv":["<rootDir>/support/setup"]}'
    root, _commit = _repository(tmp_path, config=config)
    paths = (PurePosixPath("tests/widget.test.js"),)
    (root / "support/setup").mkdir(parents=True)
    (root / "support/setup/index.ts").write_text("global.expected = true;\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add extensionless setup index")
    base = _git(root, "rev-parse", "HEAD")
    base_digest = jest_validator_config_digest(root, base, paths)

    (root / "support/setup/index.ts").write_text("global.expected = false;\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate extensionless setup index")
    head_digest = jest_validator_config_digest(root, _git(root, "rev-parse", "HEAD"), paths)

    assert head_digest != base_digest


def test_jest_repository_escape_import_is_not_bound(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    source = b"import '../../outside.js';\n"
    imports = _local_javascript_imports(
        root,
        commit,
        PurePosixPath("tests/widget.test.js"),
        source,
    )
    assert imports == set()


@pytest.mark.parametrize("config_key", ["globalSetup", "globalTeardown", "testEnvironment"])
def test_jest_executable_config_hook_mutation_cannot_pass(
    tmp_path: Path, config_key: str
) -> None:
    config = '{"%s":"<rootDir>/hook.js"}' % config_key
    root, _commit = _repository(tmp_path, config=config)
    (root / "hook.js").write_text("module.exports = {};\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add protected Jest hook")
    base = _git(root, "rev-parse", "HEAD")
    (root / "hook.js").write_text("module.exports = { changed: true };\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate Jest hook")

    _envelope, executions = _run(root, base, _git(root, "rev-parse", "HEAD"), _fake_jest(tmp_path))

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


@pytest.mark.parametrize(
    ("config", "path"),
    [
        ('{"snapshotSerializers":["<rootDir>/serializer.js"]}', "serializer.js"),
        ('{"testSequencer":"<rootDir>/sequencer.js"}', "sequencer.js"),
        ('{"moduleNameMapper":{"^@/(.*)$":"<rootDir>/src/$1"}}', "src/helper.js"),
    ],
)
def test_jest_additional_executable_config_mutation_cannot_pass(
    tmp_path: Path, config: str, path: str
) -> None:
    root, _commit = _repository(tmp_path, config=config)
    target = root / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text("module.exports = {};\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add protected Jest executable config")
    base = _git(root, "rev-parse", "HEAD")
    target.write_text("module.exports = { changed: true };\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate protected Jest executable config")

    _envelope, executions = _run(root, base, _git(root, "rev-parse", "HEAD"), _fake_jest(tmp_path))

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_jest_module_directories_bare_import_cannot_pass_unbound(
    tmp_path: Path,
) -> None:
    config = '{"moduleDirectories":["src","node_modules"]}'
    root, _commit = _repository(tmp_path, config=config)
    (root / "src").mkdir()
    (root / "src/helper.js").write_text("module.exports = { expected: true };\n")
    (root / "tests/widget.test.js").write_text(
        "const { expected } = require('helper');\n"
        "test('widget works', () => expect(expected).toBe(true));\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add moduleDirectories support")
    base = _git(root, "rev-parse", "HEAD")
    (root / "src/helper.js").write_text("module.exports = { expected: false };\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate moduleDirectories support")

    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_jest(tmp_path)
    )

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_default_candidate_node_modules_jest_is_not_trusted(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    binary = root / "node_modules" / "jest" / "bin" / "jest.js"
    binary.parent.mkdir(parents=True)
    binary.write_text(
        "const fs = require('fs');\n"
        "fs.writeFileSync(process.env.PDD_TRUSTED_JEST_OUTPUT, "
        "JSON.stringify({tests:[{identity:'tests/widget.test.js::widget works',status:'passed'}]}));\n"
    )
    _git(root, "add", "node_modules/jest/bin/jest.js")
    _git(root, "commit", "-q", "-m", "add local Jest toolchain")
    commit = _git(root, "rev-parse", "HEAD")

    _envelope, executions = _run_default_jest(root, commit, commit)

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "candidate node_modules" in executions[0].detail


def test_explicit_candidate_local_jest_command_is_not_trusted(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    runner = root / "tools" / "jest.py"
    runner.parent.mkdir()
    runner.write_text(_fake_jest(tmp_path).read_text())
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add candidate-local Jest command")
    commit = _git(root, "rev-parse", "HEAD")

    _envelope, executions = _run(root, commit, commit, runner)

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "candidate checkout" in executions[0].detail


def test_pathless_jest_script_operand_is_not_resolved_from_candidate(
    tmp_path: Path,
) -> None:
    root, base = _repository(tmp_path)
    (root / "fake_jest.py").write_text(_fake_jest(tmp_path).read_text())
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add pathless candidate Jest command")
    base = _git(root, "rev-parse", "HEAD")
    (root / "fake_jest.py").write_text(_fake_jest(tmp_path).read_text() + "\n# changed\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate pathless Jest command")
    paths = (PurePosixPath("tests/widget.test.js"),)
    obligation = VerificationObligation(
        "jest",
        "test",
        "jest",
        jest_validator_config_digest(root, base, paths),
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
            jest_command=(sys.executable, "fake_jest.py"),
        ),
    )

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "pathless" in executions[0].detail


@pytest.mark.parametrize(
    "command_tail",
    [("fake_jest",), ("--require=./candidate-helper", "/external/jest.js")],
)
def test_jest_prefix_rejects_pathless_entrypoints_and_code_loaders(
    tmp_path: Path, command_tail: tuple[str, ...]
) -> None:
    executable = tmp_path / "python"
    executable.write_text("#!/bin/sh\n", encoding="utf-8")
    executable.chmod(0o755)

    error = _jest_command_error(tmp_path / "candidate", (str(executable), *command_tail))

    assert error is not None


def test_jest_subprocess_cannot_read_secret(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    root, commit = _repository(tmp_path)
    fake = _fake_jest(tmp_path)
    fake.write_text(fake.read_text() + "\nassert 'PDD_ATTESTATION_SIGNING_KEY' not in os.environ\n")
    monkeypatch.setenv("PDD_ATTESTATION_SIGNING_KEY", "must-not-leak")
    _envelope, executions = _run(root, commit, commit, fake)
    assert executions[0].outcome is EvidenceOutcome.PASS


def test_jest_rejects_dynamic_config(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path, config="{}")
    (root / "jest.config.json").unlink()
    (root / "jest.config.js").write_text("module.exports = {};\n")
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", "dynamic config")
    commit = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, commit, commit, _fake_jest(tmp_path))
    assert executions[0].outcome is EvidenceOutcome.ERROR
