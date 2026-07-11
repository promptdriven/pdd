"""Contract tests for the fail-closed trusted Vitest adapter."""

import json
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
from pdd.sync_core.runner import vitest_validator_config_digest


UNIT = UnitId("repository-1", PurePosixPath("prompts/widget_ts.prompt"), "typescript")
IDENTITY = "tests/widget.test.ts::widget works"


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()


def _fake_vitest(tmp_path: Path) -> Path:
    runner = tmp_path / "fake_vitest.py"
    runner.write_text(
        "import json, os, pathlib, time\n"
        "root = pathlib.Path.cwd()\n"
        "mode = (root / 'source.ts').read_text().strip()\n"
        "if mode == 'timeout': time.sleep(5)\n"
        "if mode == 'malformed': pathlib.Path(os.environ['PDD_TRUSTED_VITEST_OUTPUT']).write_text('{')\n"
        "else:\n"
        "  tests = [] if mode == 'zero' else [{'identity': 'tests/widget.test.ts::widget works', 'status': {'fail': 'failed', 'skip': 'skipped', 'todo': 'todo'}.get(mode, 'passed')}]\n"
        "  if mode == 'mismatch': tests = [{'identity': 'tests/widget.test.ts::other', 'status': 'passed'}]\n"
        "  if mode == 'candidate': tests.append({'identity': 'tests/widget.test.ts::candidate only', 'status': 'passed'})\n"
        "  pathlib.Path(os.environ['PDD_TRUSTED_VITEST_OUTPUT']).write_text(json.dumps({'tests': tests}))\n",
        encoding="utf-8",
    )
    return runner


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
        config=RunnerConfig(
            timeout_seconds=timeout, vitest_command=(sys.executable, str(fake_vitest))
        ),
    )


def test_vitest_passing_collected_test_is_pass(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    _envelope, executions = _run(root, commit, commit, _fake_vitest(tmp_path))
    assert executions[0].outcome is EvidenceOutcome.PASS


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
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED


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
    ],
)
def test_vitest_rejects_unbound_execution_controls(
    tmp_path: Path, config: str
) -> None:
    root, commit = _repository(tmp_path, config=config)
    _envelope, executions = _run(root, commit, commit, _fake_vitest(tmp_path))
    assert executions[0].outcome is EvidenceOutcome.ERROR
