"""Contract tests for the fail-closed trusted Playwright adapter."""

import shutil
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
from pdd.sync_core.runner import (
    _playwright_result,
    playwright_validator_config_digest,
)


UNIT = UnitId("repository-1", PurePosixPath("prompts/widget_ts.prompt"), "typescript")
IDENTITY = "chromium::tests/widget.spec.ts::widget works"


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()


def _fake_playwright(tmp_path: Path) -> Path:
    runner = tmp_path / "fake_playwright.py"
    runner.write_text(
        "import json, os, pathlib, sys, time\n"
        "root = pathlib.Path.cwd()\n"
        "mode = (root / 'source.ts').read_text().strip()\n"
        "if mode == 'timeout': time.sleep(5)\n"
        "if mode == 'malformed': print('{')\n"
        "else:\n"
        "  tests = [] if mode == 'zero' else [{'identity': 'chromium::tests/widget.spec.ts::widget works', 'status': {'fail': 'failed', 'skip': 'skipped'}.get(mode, 'passed')}]\n"
        "  if mode == 'mismatch': tests = [{'identity': 'chromium::tests/widget.spec.ts::other', 'status': 'passed'}]\n"
        "  if mode == 'candidate': tests.append({'identity': 'chromium::tests/widget.spec.ts::candidate only', 'status': 'passed'})\n"
        "  print(json.dumps({'tests': tests}))\n",
        encoding="utf-8",
    )
    return runner


def _fake_node_playwright(tmp_path: Path) -> Path:
    runner = tmp_path / "fake_node_playwright.js"
    runner.write_text(
        "const path = require('path');\n"
        "try { require.resolve('@playwright/test'); }\n"
        "catch (error) {\n"
        "  console.log(JSON.stringify({suites: [], errors: [{message: error.message}]}));\n"
        "  process.exit(1);\n"
        "}\n"
        "const file = path.resolve(process.cwd(), 'tests/widget.spec.ts');\n"
        "const collection = process.argv.includes('--list');\n"
        "const result = collection ? [] : [{status: 'passed'}];\n"
        "console.log(JSON.stringify({suites: [{title: 'tests/widget.spec.ts', file, specs: [{title: 'widget works', file, tests: [{projectName: 'chromium', results: result}]}]}]}));\n",
        encoding="utf-8",
    )
    return runner


def _fake_node_playwright_requiring_browser_path(tmp_path: Path) -> Path:
    runner = tmp_path / "fake_node_playwright_browser_path.js"
    runner.write_text(
        "const path = require('path');\n"
        "try { require.resolve('@playwright/test'); }\n"
        "catch (error) {\n"
        "  console.log(JSON.stringify({suites: [], errors: [{message: error.message}]}));\n"
        "  process.exit(1);\n"
        "}\n"
        "if (process.env.PLAYWRIGHT_BROWSERS_PATH !== '0') {\n"
        "  console.log(JSON.stringify({suites: [], errors: [{message: 'missing package-local browsers path'}]}));\n"
        "  process.exit(1);\n"
        "}\n"
        "const file = path.resolve(process.cwd(), 'tests/widget.spec.ts');\n"
        "const collection = process.argv.includes('--list');\n"
        "const result = collection ? [] : [{status: 'passed'}];\n"
        "console.log(JSON.stringify({suites: [{title: 'tests/widget.spec.ts', file, specs: [{title: 'widget works', file, tests: [{projectName: 'chromium', results: result}]}]}]}));\n",
        encoding="utf-8",
    )
    return runner


def _repository(
    tmp_path: Path, *, mode: str = "pass", config: str = "export default {};\n"
) -> tuple[Path, str]:
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "runner@example.com")
    _git(root, "config", "user.name", "Runner Test")
    (root / "tests").mkdir()
    (root / "tests/widget.spec.ts").write_text(
        "import { expect, test } from '@playwright/test';\n"
        "test('widget works', async () => expect(true).toBeTruthy());\n",
        encoding="utf-8",
    )
    (root / "playwright.config.ts").write_text(config, encoding="utf-8")
    (root / "source.ts").write_text(mode, encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "protected Playwright tests")
    return root, _git(root, "rev-parse", "HEAD")


def _run(
    root: Path,
    base: str,
    head: str,
    fake: Path | tuple[str, ...],
    timeout: int = 2,
):
    paths = (PurePosixPath("tests/widget.spec.ts"),)
    try:
        config_digest = playwright_validator_config_digest(root, base, paths)
    except ValueError:
        config_digest = "invalid-playwright-config"
    obligation = VerificationObligation(
        "playwright", "test", "playwright", config_digest, ("REQ-1",), paths
    )
    profile = VerificationProfile(UNIT, (obligation,), ("REQ-1",), "profile-v1")
    return run_profile(
        root,
        profile,
        RunBinding("snapshot-v1", base, head),
        AttestationIssue(
            AttestationSigner("trusted-ci", b"p" * 32),
            "id",
            "nonce",
            datetime(2026, 7, 10, tzinfo=timezone.utc),
        ),
        config=RunnerConfig(
            timeout_seconds=timeout,
            playwright_command=fake
            if isinstance(fake, tuple)
            else (sys.executable, str(fake)),
        ),
    )


def _run_default_playwright(root: Path, base: str, head: str, timeout: int = 2):
    paths = (PurePosixPath("tests/widget.spec.ts"),)
    obligation = VerificationObligation(
        "playwright",
        "test",
        "playwright",
        playwright_validator_config_digest(root, base, paths),
        ("REQ-1",),
        paths,
    )
    profile = VerificationProfile(UNIT, (obligation,), ("REQ-1",), "profile-v1")
    return run_profile(
        root,
        profile,
        RunBinding("snapshot-v1", base, head),
        AttestationIssue(
            AttestationSigner("trusted-ci", b"p" * 32),
            "id",
            "nonce",
            datetime(2026, 7, 10, tzinfo=timezone.utc),
        ),
        config=RunnerConfig(timeout_seconds=timeout),
    )


def test_playwright_passing_collected_test_is_pass(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    _envelope, executions = _run(root, commit, commit, _fake_playwright(tmp_path))
    assert executions[0].outcome is EvidenceOutcome.PASS


def test_playwright_candidate_node_modules_dependency_is_not_trusted(
    tmp_path: Path,
) -> None:
    root, commit = _repository(tmp_path)
    (root / ".gitignore").write_text("node_modules/\n", encoding="utf-8")
    module = root / "node_modules" / "@playwright" / "test"
    module.mkdir(parents=True)
    (module / "index.js").write_text("module.exports = {};\n", encoding="utf-8")
    _git(root, "add", ".gitignore")
    _git(root, "commit", "-q", "-m", "ignore local node modules")
    commit = _git(root, "rev-parse", "HEAD")

    node = shutil.which("node")
    assert node is not None

    _envelope, executions = _run(
        root,
        commit,
        commit,
        (node, str(_fake_node_playwright(tmp_path))),
    )

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "candidate node_modules" in executions[0].detail


def test_playwright_candidate_browser_cache_is_not_trusted(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    (root / ".gitignore").write_text("node_modules/\n", encoding="utf-8")
    module = root / "node_modules" / "@playwright" / "test"
    module.mkdir(parents=True)
    (module / "index.js").write_text("module.exports = {};\n", encoding="utf-8")
    browsers = (
        root
        / "node_modules"
        / "playwright-core"
        / ".local-browsers"
        / "chromium_headless_shell-1181"
    )
    browsers.mkdir(parents=True)
    _git(root, "add", ".gitignore")
    _git(root, "commit", "-q", "-m", "ignore package local Playwright install")
    commit = _git(root, "rev-parse", "HEAD")

    node = shutil.which("node")
    assert node is not None

    _envelope, executions = _run(
        root,
        commit,
        commit,
        (node, str(_fake_node_playwright_requiring_browser_path(tmp_path))),
    )

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "candidate node_modules" in executions[0].detail


def test_default_candidate_node_modules_playwright_is_not_trusted(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    (root / ".gitignore").write_text("node_modules/\n", encoding="utf-8")
    _git(root, "add", ".gitignore")
    _git(root, "commit", "-q", "-m", "ignore local node modules")
    commit = _git(root, "rev-parse", "HEAD")
    binary = root / "node_modules" / "@playwright" / "test" / "cli.js"
    binary.parent.mkdir(parents=True)
    binary.write_text(
        "console.log(JSON.stringify({tests:[{identity:"
        "'chromium::tests/widget.spec.ts::widget works',status:'passed'}]}));\n",
        encoding="utf-8",
    )

    _envelope, executions = _run_default_playwright(root, commit, commit)

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "candidate node_modules" in executions[0].detail


def test_playwright_result_resolves_relative_spec_file_from_runner_root(
    tmp_path: Path,
) -> None:
    root = tmp_path / "repo"
    (root / "tests").mkdir(parents=True)
    (root / "tests/widget.spec.ts").write_text("", encoding="utf-8")
    output = (
        '{"suites":[{"title":"tests/widget.spec.ts","specs":[{'
        '"title":"widget works","file":"tests/widget.spec.ts",'
        '"tests":[{"projectName":"chromium","results":[{"status":"passed"}]}]'
        '}]}]}'
    )

    outcome, detail, identities = _playwright_result(
        root,
        output,
        0,
        None,
    )

    assert outcome is EvidenceOutcome.PASS
    assert detail == "1 protected Playwright tests passed"
    assert identities == ("chromium::tests/widget.spec.ts::tests/widget.spec.ts > widget works",)


@pytest.mark.parametrize(
    ("mode", "outcome"),
    [
        ("fail", EvidenceOutcome.FAIL),
        ("skip", EvidenceOutcome.SKIP),
        ("zero", EvidenceOutcome.NOT_COLLECTED),
        ("timeout", EvidenceOutcome.TIMEOUT),
        ("malformed", EvidenceOutcome.COLLECTION_ERROR),
    ],
)
def test_playwright_normalizes_non_pass_outcomes(
    tmp_path: Path, mode: str, outcome: EvidenceOutcome
) -> None:
    root, commit = _repository(tmp_path, mode=mode)
    _envelope, executions = _run(root, commit, commit, _fake_playwright(tmp_path), 1)
    assert executions[0].outcome is outcome


@pytest.mark.parametrize("mode", ["mismatch", "candidate"])
def test_playwright_collection_identity_mismatch_cannot_pass(
    tmp_path: Path, mode: str
) -> None:
    root, base = _repository(tmp_path)
    (root / "source.ts").write_text(mode, encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change application behavior")
    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_playwright(tmp_path)
    )
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED


def test_playwright_removed_protected_test_cannot_pass(tmp_path: Path) -> None:
    root, base = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text("// removed\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "remove protected test")
    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_playwright(tmp_path)
    )
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED


@pytest.mark.parametrize("path", ["playwright.config.ts", "setup.ts", "reporter.ts"])
def test_playwright_config_and_support_mutation_cannot_pass(
    tmp_path: Path, path: str
) -> None:
    config = "import './setup';\nexport default { reporter: './reporter.ts' };\n"
    root, _commit = _repository(tmp_path, config=config)
    (root / "setup.ts").write_text("export {};\n", encoding="utf-8")
    (root / "reporter.ts").write_text("export default class Reporter {}\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add protected support")
    base = _git(root, "rev-parse", "HEAD")
    (root / path).write_text("changed\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate protected Playwright support")
    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_playwright(tmp_path)
    )
    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_playwright_side_effect_import_helper_mutation_cannot_pass(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/helper.ts").write_text("globalThis.expected = true;\n", encoding="utf-8")
    (root / "tests/widget.spec.ts").write_text(
        "import { expect, test } from '@playwright/test';\n"
        "import './helper';\n"
        "test('widget works', async () => expect(globalThis.expected).toBeTruthy());\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add protected side effect helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "tests/helper.ts").write_text("globalThis.expected = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate side effect helper")

    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_playwright(tmp_path)
    )

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_playwright_dirty_support_cannot_influence_run(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    (root / "ambient.ts").write_text("export {};\n", encoding="utf-8")
    _envelope, executions = _run(root, commit, commit, _fake_playwright(tmp_path))
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED


def test_playwright_subprocess_cannot_read_secret(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, commit = _repository(tmp_path)
    fake = _fake_playwright(tmp_path)
    fake.write_text(
        fake.read_text(encoding="utf-8")
        + "\nassert 'PDD_ATTESTATION_SIGNING_KEY' not in os.environ\n",
        encoding="utf-8",
    )
    monkeypatch.setenv("PDD_ATTESTATION_SIGNING_KEY", "must-not-leak")
    _envelope, executions = _run(root, commit, commit, fake)
    assert executions[0].outcome is EvidenceOutcome.PASS


def test_explicit_candidate_local_playwright_command_is_not_trusted(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    runner = root / "tools" / "playwright.py"
    runner.parent.mkdir()
    runner.write_text(_fake_playwright(tmp_path).read_text(encoding="utf-8"), encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add candidate-local Playwright command")
    commit = _git(root, "rev-parse", "HEAD")

    _envelope, executions = _run(root, commit, commit, runner)

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "candidate checkout" in executions[0].detail


@pytest.mark.parametrize(
    "config",
    [
        "export default process.env.PLAYWRIGHT_CONFIG;\n",
        "export default { grep: /widget/ };\n",
        "export default { retries: 1 };\n",
        "export default { webServer: { command: 'npm run dev' } };\n",
        "const globalSetup = './setup';\nexport default { globalSetup };\n",
        "const webServer = { command: 'npm run dev' };\nexport default { webServer };\n",
    ],
)
def test_playwright_rejects_unbound_execution_controls(
    tmp_path: Path, config: str
) -> None:
    root, commit = _repository(tmp_path, config=config)
    _envelope, executions = _run(root, commit, commit, _fake_playwright(tmp_path))
    assert executions[0].outcome is EvidenceOutcome.ERROR


@pytest.mark.parametrize(
    "config",
    [
        'export default { "grep": /widget/ };\n',
        "export default { 'retries': 1 };\n",
        'export default { "globalSetup": "./setup.ts" };\n',
        'export default { "webServer": { command: "npm run dev" } };\n',
    ],
)
def test_playwright_rejects_quoted_execution_control_keys(
    tmp_path: Path, config: str
) -> None:
    root, commit = _repository(tmp_path, config=config)
    (root / "setup.ts").write_text("export default async function setup() {}\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add quoted control support")
    commit = _git(root, "rev-parse", "HEAD")

    _envelope, executions = _run(root, commit, commit, _fake_playwright(tmp_path))

    assert executions[0].outcome is EvidenceOutcome.ERROR
