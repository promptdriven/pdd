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
from pdd.sync_core.runner import jest_validator_config_digest


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
