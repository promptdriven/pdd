"""Contract tests for the fail-closed trusted Vitest adapter."""

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
from pdd.sync_core.runner import _local_javascript_imports


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


def _run_default_vitest(root: Path, base: str, head: str, timeout: int = 2):
    paths = (PurePosixPath("tests/widget.test.ts"),)
    obligation = VerificationObligation(
        "vitest",
        "test",
        "vitest",
        vitest_validator_config_digest(root, base, paths),
        ("REQ-1",),
        paths,
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
        config=RunnerConfig(timeout_seconds=timeout),
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
    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


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


def test_vitest_imported_test_helper_mutation_cannot_pass(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/helper.ts").write_text("export const expected = true;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import { expect, test } from 'vitest';\n"
        "import { expected } from './helper';\n"
        "test('widget works', () => expect(expected).toBe(true));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add protected Vitest helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "tests/helper.ts").write_text("export const expected = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate imported Vitest helper")

    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_vitest(tmp_path)
    )

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_vitest_side_effect_import_helper_mutation_cannot_pass(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/helper.ts").write_text("globalThis.expected = true;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import { expect, test } from 'vitest';\n"
        "import './helper';\n"
        "test('widget works', () => expect(globalThis.expected).toBe(true));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add protected side effect helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "tests/helper.ts").write_text("globalThis.expected = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate side effect helper")

    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_vitest(tmp_path)
    )

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_vitest_parent_directory_import_helper_mutation_cannot_pass(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "shared").mkdir()
    (root / "shared/helper.ts").write_text("export const expected = true;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import { expect, test } from 'vitest';\n"
        "import { expected } from '../shared/helper';\n"
        "test('widget works', () => expect(expected).toBe(true));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add parent import helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "shared/helper.ts").write_text("export const expected = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate parent import helper")

    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_vitest(tmp_path)
    )

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_vitest_parent_directory_side_effect_import_mutation_cannot_pass(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "shared").mkdir()
    (root / "shared/setup.ts").write_text("globalThis.expected = true;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import { expect, test } from 'vitest';\n"
        "import '../shared/setup';\n"
        "test('widget works', () => expect(globalThis.expected).toBe(true));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add parent side effect helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "shared/setup.ts").write_text("globalThis.expected = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate parent side effect helper")

    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_vitest(tmp_path)
    )

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_vitest_parent_directory_imports_change_validator_digest(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    paths = (PurePosixPath("tests/widget.test.ts"),)
    (root / "shared/helpers").mkdir(parents=True)
    (root / "shared/helpers/index.ts").write_text(
        "export const expected = true;\n", encoding="utf-8"
    )
    (root / "shared/setup.ts").write_text("globalThis.expected = true;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import { expect, test } from 'vitest';\n"
        "import { expected } from '../shared/helpers';\n"
        "import '../shared/setup';\n"
        "test('widget works', () => expect(expected && globalThis.expected).toBe(true));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add parent import helpers")
    base = _git(root, "rev-parse", "HEAD")
    base_digest = vitest_validator_config_digest(root, base, paths)

    (root / "shared/helpers/index.ts").write_text(
        "export const expected = false;\n", encoding="utf-8"
    )
    (root / "shared/setup.ts").write_text("globalThis.expected = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate parent import helpers")
    head_digest = vitest_validator_config_digest(root, _git(root, "rev-parse", "HEAD"), paths)

    assert head_digest != base_digest


def test_vitest_config_reference_index_candidate_changes_validator_digest(tmp_path: Path) -> None:
    config = '{"test":{"setupFiles":["support/setup"]}}'
    root, _commit = _repository(tmp_path, config=config)
    paths = (PurePosixPath("tests/widget.test.ts"),)
    (root / "support/setup").mkdir(parents=True)
    (root / "support/setup/index.ts").write_text(
        "globalThis.expected = true;\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add extensionless setup index")
    base = _git(root, "rev-parse", "HEAD")
    base_digest = vitest_validator_config_digest(root, base, paths)

    (root / "support/setup/index.ts").write_text(
        "globalThis.expected = false;\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate extensionless setup index")
    head_digest = vitest_validator_config_digest(root, _git(root, "rev-parse", "HEAD"), paths)

    assert head_digest != base_digest


def test_vitest_repository_escape_import_is_not_bound(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    imports = _local_javascript_imports(
        root,
        commit,
        PurePosixPath("tests/widget.test.ts"),
        b"import '../../outside.js';\n",
    )
    assert imports == set()


def test_vitest_local_alias_config_fails_closed(tmp_path: Path) -> None:
    config = '{"resolve":{"alias":{"@":"./src"}}}'
    root, commit = _repository(tmp_path, config=config)
    (root / "src").mkdir()
    (root / "src/helper.ts").write_text("export const expected = true;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import { expect, test } from 'vitest';\n"
        "import { expected } from '@/helper';\n"
        "test('widget works', () => expect(expected).toBe(true));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add aliased protected helper")
    commit = _git(root, "rev-parse", "HEAD")

    _envelope, executions = _run(root, commit, commit, _fake_vitest(tmp_path))

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "alias" in executions[0].detail


def test_default_candidate_node_modules_vitest_is_not_trusted(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    (root / ".gitignore").write_text("node_modules/\n", encoding="utf-8")
    _git(root, "add", ".gitignore")
    _git(root, "commit", "-q", "-m", "ignore local node modules")
    commit = _git(root, "rev-parse", "HEAD")
    binary = root / "node_modules" / "vitest" / "vitest.mjs"
    binary.parent.mkdir(parents=True)
    binary.write_text(
        "import fs from 'fs';\n"
        "const output = process.argv.find((arg) => arg.startsWith('--outputFile='))"
        "?.slice('--outputFile='.length);\n"
        "fs.writeFileSync(output, JSON.stringify({tests:[{identity:"
        "'tests/widget.test.ts::widget works',status:'passed'}]}));\n",
        encoding="utf-8",
    )

    _envelope, executions = _run_default_vitest(root, commit, commit)

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "candidate node_modules" in executions[0].detail


def test_explicit_candidate_local_vitest_command_is_not_trusted(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    runner = root / "tools" / "vitest.py"
    runner.parent.mkdir()
    runner.write_text(_fake_vitest(tmp_path).read_text(encoding="utf-8"), encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add candidate-local Vitest command")
    commit = _git(root, "rev-parse", "HEAD")

    _envelope, executions = _run(root, commit, commit, runner)

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "candidate checkout" in executions[0].detail


def test_pathless_vitest_script_operand_is_not_resolved_from_candidate(
    tmp_path: Path,
) -> None:
    root, base = _repository(tmp_path)
    (root / "fake_vitest.py").write_text(
        _fake_vitest(tmp_path).read_text(encoding="utf-8"), encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add pathless candidate Vitest command")
    base = _git(root, "rev-parse", "HEAD")
    (root / "fake_vitest.py").write_text(
        _fake_vitest(tmp_path).read_text(encoding="utf-8") + "\n# changed\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate pathless Vitest command")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    obligation = VerificationObligation(
        "vitest",
        "test",
        "vitest",
        vitest_validator_config_digest(root, base, paths),
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
            vitest_command=(sys.executable, "fake_vitest.py"),
        ),
    )

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "pathless" in executions[0].detail


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
