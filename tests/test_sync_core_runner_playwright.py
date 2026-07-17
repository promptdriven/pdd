"""Contract tests for the fail-closed trusted Playwright adapter."""

import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
from collections.abc import Iterator
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

import pytest
import pdd.sync_core.runner as runner_module
from pdd.sync_core.supervisor import (
    SupervisedCompletedProcess,
    SupervisorTermination,
    TerminationKind,
)

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
    PLAYWRIGHT_SUPERVISOR_LIMITS,
    _directory_identity,
    _local_javascript_imports,
    _playwright_environment,
    _playwright_command_error,
    _playwright_missing_result_detail,
    _playwright_reporter_source,
    _playwright_reported_failure_detail,
    _playwright_result,
    _playwright_runtime_prefix,
    _playwright_snapshot_aggregate_identity,
    _playwright_snapshot_binding_proofs,
    _playwright_host_temp_parent,
    _playwright_infrastructure_termination,
    _toolchain_manifest_roles,
    _toolchain_manifest_identity,
    _playwright_toolchain_identity,
    playwright_validator_config_digest,
)


UNIT = UnitId("repository-1", PurePosixPath("prompts/widget_ts.prompt"), "typescript")
IDENTITY = "chromium::tests/widget.spec.ts::widget works"
REPORTER_ERROR_REASONS = (
    "invalid_suite",
    "suite_all_tests_access",
    "suite_all_tests_call",
    "invalid_title_path",
    "title_path_call",
    "invalid_project_title",
    "project_access",
    "project_call",
    "invalid_location",
    "location_access",
    "path_operation",
    "duplicate_identity",
    "invalid_test_result",
    "unknown_test",
    "invalid_framework_error",
    "framework_error",
    "invalid_run_result",
    "serialization_failure",
    "write_failure",
)


def _trusted_completed(
    command, returncode: int, stdout: str = "", stderr: str = "", *,
    kind: TerminationKind = TerminationKind.EXIT,
    resource_limit: str | None = None,
) -> SupervisedCompletedProcess:
    """Construct production-shaped trusted termination evidence for adapter fakes."""
    termination = SupervisorTermination(
        kind,
        exit_code=returncode if kind in {TerminationKind.EXIT, TerminationKind.SANDBOX_ERROR} else None,
        signal_number=-returncode if kind is TerminationKind.SIGNAL else None,
        timeout_seconds=1 if kind is TerminationKind.TIMEOUT else None,
        resource_limit=resource_limit,
    )
    return SupervisedCompletedProcess(
        command, returncode, stdout, stderr, termination=termination
    )


@pytest.fixture(autouse=True)
def _simulate_framework_observation_for_synthetic_playwright(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Model the Linux-only inherited descriptor for the local fake runner.

    The production supervisor intentionally does not emulate the observation
    descriptor on macOS.  These synthetic runner tests therefore write the
    checker-owned pipe from the trusted test process, while real execution is
    reserved for the Linux/bwrap contract tests.
    """
    if sys.platform.startswith("linux"):
        return
    original = runner_module.run_supervised

    def supervised(command, **kwargs):
        entrypoint = Path(command[1]) if len(command) > 1 else Path()
        for source_root, destination_root in kwargs.get("readable_bindings", ()):
            try:
                entrypoint = source_root / entrypoint.relative_to(destination_root)
                break
            except ValueError:
                continue
        try:
            source = entrypoint.read_text(encoding="utf-8")
            synthetic = (
                "root = pathlib.Path.cwd()" in source
                or "const file = path.resolve" in source
            )
        except OSError:
            synthetic = False
        if not synthetic:
            return original(command, **kwargs)
        synthetic_command = [*command]
        synthetic_command[1] = str(entrypoint)
        result_fd = kwargs["result_fd"]
        writer = kwargs["result_write_fd"]
        try:
            saved_fd = os.dup(result_fd)
        except OSError:
            saved_fd = None
        os.dup2(writer, result_fd)
        try:
            result = subprocess.run(
                synthetic_command, cwd=kwargs["cwd"], env=kwargs["env"], text=True,
                capture_output=True, timeout=kwargs["timeout"], pass_fds=(result_fd,),
                check=False,
            )
        except subprocess.TimeoutExpired as exc:
            result = _trusted_completed(
                command, 124, exc.stdout or "", exc.stderr or "",
                kind=TerminationKind.TIMEOUT,
            )
        finally:
            if saved_fd is None:
                os.close(result_fd)
            else:
                os.dup2(saved_fd, result_fd)
                os.close(saved_fd)
        if not isinstance(result, SupervisedCompletedProcess):
            result = _trusted_completed(
                command, result.returncode, result.stdout, result.stderr
            )
        return result, False

    monkeypatch.setattr(runner_module, "run_supervised", supervised)


def _write_framework_observation(kwargs: dict, payload: dict) -> None:
    """Model the checker-owned reporter transport in supervisor fakes."""
    writer = kwargs.get("result_write_fd")
    close_writer = writer is None
    if writer is None:
        writer = os.open(kwargs["result_fifo"], os.O_WRONLY)
    try:
        os.write(writer, json.dumps({
            "pdd_playwright_reporter": 1, **payload,
        }).encode())
    finally:
        if close_writer:
            os.close(writer)


def _reporter_callback_receipt(tmp_path: Path, callbacks: str) -> dict:
    """Run generated reporter callbacks through Playwright's swallowed-error shape."""
    node = shutil.which("node")
    if node is None:
        pytest.skip("requires Node")
    read_fd, write_fd = os.pipe()
    reporter = tmp_path / "reporter.cjs"
    driver = tmp_path / "reporter-driver.cjs"
    reporter.write_text(_playwright_reporter_source(write_fd), encoding="utf-8")
    driver.write_text(
        "const path = require('path');\n"
        "const Reporter = require(process.argv[2]);\n"
        "const reporter = new Reporter();\n"
        "const valid = (title = 'widget works') => ({\n"
        "  titlePath: () => ['', 'chromium', 'widget.spec.ts', title],\n"
        "  parent: { project: () => ({ name: 'chromium' }) },\n"
        "  location: { file: path.join(process.cwd(), 'tests/widget.spec.ts') },\n"
        "});\n"
        f"{callbacks}\n",
        encoding="utf-8",
    )
    try:
        completed = subprocess.run(
            [node, str(driver), str(reporter)],
            cwd=tmp_path,
            capture_output=True,
            text=True,
            timeout=10,
            pass_fds=(write_fd,),
            check=False,
        )
    finally:
        os.close(write_fd)
    output = os.read(read_fd, 64 * 1024)
    os.close(read_fd)
    assert completed.returncode == 0, completed.stderr
    assert output, completed.stderr
    return json.loads(output)


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()


def _fake_playwright(tmp_path: Path) -> Path:
    runner = tmp_path / "fake_playwright.py"
    runner.write_text(
        "import json, os, pathlib, re, sys, time\n"
        "root = pathlib.Path.cwd()\n"
        "mode = (root / 'source.ts').read_text().strip()\n"
        "if mode == 'timeout': time.sleep(5)\n"
        "if mode == 'malformed': print('{')\n"
        "else:\n"
        "  tests = [] if mode == 'zero' else [{'identity': 'chromium::tests/widget.spec.ts::widget works', 'status': {'fail': 'failed', 'skip': 'skipped'}.get(mode, 'passed')}]\n"
        "  if mode == 'mismatch': tests = [{'identity': 'chromium::tests/widget.spec.ts::other', 'status': 'passed'}]\n"
        "  if mode == 'candidate': tests.append({'identity': 'chromium::tests/widget.spec.ts::candidate only', 'status': 'passed'})\n"
        "  reporter = next((arg.split('=', 1)[1] for arg in sys.argv if arg.startswith('--reporter=')), '')\n"
        "  fd = int(re.search(r'RESULT_FD = (\\d+)', pathlib.Path(reporter).read_text()).group(1))\n"
        "  os.write(fd, json.dumps({'pdd_playwright_reporter': 1, 'tests': tests}).encode())\n",
        encoding="utf-8",
    )
    return runner


def _fake_node_playwright(tmp_path: Path) -> Path:
    runner = tmp_path / "fake_node_playwright.js"
    runner.write_text(
        "const fs = require('fs');\n"
        "const path = require('path');\n"
        "try { require.resolve('@playwright/test'); }\n"
        "catch (error) {\n"
        "  console.log(JSON.stringify({suites: [], errors: [{message: error.message}]}));\n"
        "  process.exit(1);\n"
        "}\n"
        "const file = path.resolve(process.cwd(), 'tests/widget.spec.ts');\n"
        "const collection = process.argv.includes('--list');\n"
        "const reporter = process.argv.find((arg) => arg.startsWith('--reporter='));\n"
        "const fd = Number(/RESULT_FD = (\\d+)/.exec(fs.readFileSync(reporter.slice(11), 'utf8'))[1]);\n"
        "fs.writeSync(fd, JSON.stringify({pdd_playwright_reporter: 1, tests: [{identity: 'chromium::tests/widget.spec.ts::widget works', status: collection ? 'collected' : 'passed'}]}));\n",
        encoding="utf-8",
    )
    return runner


def _fake_node_playwright_requiring_browser_path(tmp_path: Path) -> Path:
    runner = tmp_path / "fake_node_playwright_browser_path.js"
    runner.write_text(
        "const fs = require('fs');\n"
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
        "const reporter = process.argv.find((arg) => arg.startsWith('--reporter='));\n"
        "const fd = Number(/RESULT_FD = (\\d+)/.exec(fs.readFileSync(reporter.slice(11), 'utf8'))[1]);\n"
        "fs.writeSync(fd, JSON.stringify({pdd_playwright_reporter: 1, tests: [{identity: 'chromium::tests/widget.spec.ts::widget works', status: collection ? 'collected' : 'passed'}]}));\n",
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


def _repository_with_playwright_config_suffix(
    tmp_path: Path, suffix: str, js_scope: str | None,
) -> tuple[Path, str]:
    """Create one committed config whose relative paths require its real directory."""
    root, _commit = _repository(tmp_path)
    (root / "playwright.config.ts").unlink()
    commonjs = suffix == ".cjs" or (
        suffix == ".js" and js_scope == "commonjs"
    )
    config = (
        "module.exports = { testDir: './tests' };\n"
        if commonjs else "export default { testDir: './tests' };\n"
    )
    (root / f"playwright.config{suffix}").write_text(config, encoding="utf-8")
    if suffix == ".js":
        assert js_scope is not None
        (root / "package.json").write_text(
            json.dumps({"type": js_scope}), encoding="utf-8"
        )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", f"protected Playwright {suffix} config")
    return root, _git(root, "rev-parse", "HEAD")


def _toolchain_manifest(directory: Path, launcher: Path, entrypoint: Path) -> Path:
    directory.mkdir(parents=True, exist_ok=True)
    dependencies = directory / "node_modules"
    browsers = directory / "browsers"
    dependencies.mkdir(exist_ok=True)
    browsers.mkdir(exist_ok=True)
    package = dependencies / "@playwright/test"
    package.mkdir(parents=True, exist_ok=True)
    (package / "index.js").write_text("module.exports = {};\n", encoding="utf-8")
    installed_entrypoint = package / f"cli{entrypoint.suffix}"
    if entrypoint.resolve() != installed_entrypoint.resolve():
        installed_entrypoint.write_bytes(entrypoint.read_bytes())
    lockfile = directory / "package-lock.json"
    lockfile.write_text("{}\n", encoding="utf-8")
    native = directory / "native-runtime.so"
    native.write_bytes(b"synthetic-native-runtime")
    manifest = directory / "playwright-toolchain.json"
    manifest.write_text(
        json.dumps({
            "version": 3,
            "roles": {
                "launcher": str(launcher.resolve()),
                "entrypoint": str(installed_entrypoint.resolve()),
                "dependencies": str(dependencies.resolve()),
                "browser_runtime": str(browsers.resolve()),
                "native_runtime": [str(native.resolve())],
                "lockfile": str(lockfile.resolve()),
            },
        }),
        encoding="utf-8",
    )
    return manifest


def _manifest_entrypoint(manifest: Path) -> Path:
    return Path(json.loads(manifest.read_text(encoding="utf-8"))["roles"]["entrypoint"])


@pytest.fixture
def trusted_toolchain_dir() -> Iterator[Path]:
    """Provide a deterministic synthetic toolchain outside sandbox-backed /tmp."""
    with tempfile.TemporaryDirectory(
        prefix="pdd-test-playwright-toolchain-",
        dir=_playwright_host_temp_parent(),
    ) as directory:
        yield Path(directory)


def _trusted_playwright_config(
    toolchain_dir: Path, fake: Path,
) -> RunnerConfig:
    """Build one externally declared synthetic Playwright toolchain config."""
    manifest = _toolchain_manifest(
        toolchain_dir / "trusted-toolchain", Path(sys.executable), fake
    )
    return RunnerConfig(
        timeout_seconds=2,
        playwright_command=(sys.executable, str(_manifest_entrypoint(manifest))),
        playwright_toolchain_manifest=manifest,
    )


@pytest.mark.skipif(
    not sys.platform.startswith("linux")
    or not shutil.which("bwrap")
    or not os.environ.get("PDD_RUN_REAL_PLAYWRIGHT")
    or not os.environ.get("PDD_REAL_PLAYWRIGHT_TOOLCHAIN_MANIFEST"),
    reason="requires the mandatory hosted Linux Playwright protocol lane",
)
@pytest.mark.parametrize(
    ("suffix", "js_scope"),
    [
        (".js", "commonjs"),
        (".js", "module"),
        (".cjs", None),
        (".mjs", None),
        (".ts", None),
        (".cts", None),
        (".mts", None),
    ],
)
def test_real_playwright_1_55_config_suffixes_collect_and_use_config_dir(
    tmp_path: Path, suffix: str, js_scope: str | None,
) -> None:
    """Run every admitted config syntax through Playwright and Chromium."""
    if os.environ.get("PDD_REQUIRE_INSTALLED_WHEEL"):
        module_path = Path(runner_module.__file__).resolve()
        assert "site-packages" in module_path.parts, module_path

    manifest = Path(os.environ["PDD_REAL_PLAYWRIGHT_TOOLCHAIN_MANIFEST"])
    roles = json.loads(manifest.read_text(encoding="utf-8"))["roles"]
    for role in ("dependencies", "browser_runtime"):
        role_root = Path(roles[role])
        assert stat.S_IMODE(role_root.stat().st_mode) == 0o755
    dependencies = Path(roles["dependencies"])
    recursive_bytes = sum(
        member.stat().st_size for member in dependencies.rglob("*")
        if member.is_file() and not member.is_symlink()
    )
    assert recursive_bytes > 1024 * 1024
    root = tmp_path / "real-playwright-repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "runner@example.com")
    _git(root, "config", "user.name", "Runner Test")
    (root / "tests").mkdir()
    (root / "tests/widget.spec.ts").write_text(
        "import { expect, test } from '@playwright/test';\n"
        "test('real protected browser', async ({ page }, testInfo) => {\n"
        "  await expect(testInfo.config.metadata.pddCandidateConfigLoaded).toBe(true);\n"
        "  await page.goto('data:text/html,<title>Widget</title>');\n"
        "  await expect(page).toHaveTitle('Widget');\n"
        "});\n",
        encoding="utf-8",
    )
    commonjs = suffix == ".cjs" or (
        suffix == ".js" and js_scope == "commonjs"
    )
    config = (
        "module.exports = { testDir: './tests', metadata: { pddCandidateConfigLoaded: true } };\n"
        if commonjs
        else "export default { testDir: './tests', metadata: { pddCandidateConfigLoaded: true } };\n"
    )
    (root / f"playwright.config{suffix}").write_text(config, encoding="utf-8")
    if suffix == ".js":
        assert js_scope is not None
        (root / "package.json").write_text(
            json.dumps({"type": js_scope}), encoding="utf-8"
        )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "protected real Playwright test")
    commit = _git(root, "rev-parse", "HEAD")
    paths = (PurePosixPath("tests/widget.spec.ts"),)
    obligation = VerificationObligation(
        "playwright-real", "test", "playwright",
        playwright_validator_config_digest(root, commit, paths),
        ("REQ-1",), paths,
    )
    profile = VerificationProfile(
        UnitId("repo", PurePosixPath("prompts/widget_ts.prompt"), "typescript"),
        (obligation,), ("REQ-1",), "profile-v1",
    )

    envelope, executions = run_profile(
        root,
        profile,
        RunBinding("snapshot", commit, commit),
        AttestationIssue(
            AttestationSigner("trusted-ci", b"w" * 32), "id", "nonce",
            datetime(2026, 7, 13, tzinfo=timezone.utc),
        ),
        RunnerConfig(
            timeout_seconds=60,
            playwright_command=(roles["launcher"], roles["entrypoint"]),
            playwright_toolchain_manifest=manifest,
        ),
    )

    assert executions[0].outcome is EvidenceOutcome.PASS, executions[0].detail
    assert dict(envelope.binding.adapter_identities)["playwright"]


@pytest.mark.skipif(
    not sys.platform.startswith("linux")
    or not os.environ.get("PDD_RUN_REAL_PLAYWRIGHT")
    or not os.environ.get("PDD_REAL_PLAYWRIGHT_TOOLCHAIN_MANIFEST"),
    reason="requires the mandatory hosted Linux Playwright protocol lane",
)
@pytest.mark.parametrize(
    ("suffix", "js_scope"),
    [
        (".js", "commonjs"),
        (".js", "module"),
        (".cjs", None),
        (".mjs", None),
        (".ts", None),
        (".cts", None),
        (".mts", None),
    ],
)
def test_real_playwright_1_55_list_protocol_emits_canonical_identities(
    tmp_path: Path, suffix: str, js_scope: str | None,
) -> None:
    """Use the exact reporter with every admitted config syntax and ``--list``."""
    if os.environ.get("PDD_REQUIRE_INSTALLED_WHEEL"):
        module_path = Path(runner_module.__file__).resolve()
        assert "site-packages" in module_path.parts, module_path

    manifest = Path(os.environ["PDD_REAL_PLAYWRIGHT_TOOLCHAIN_MANIFEST"])
    roles = json.loads(manifest.read_text(encoding="utf-8"))["roles"]
    root = tmp_path / "candidate"
    controller = tmp_path / "controller"
    root.mkdir()
    controller.mkdir()
    os.symlink(roles["dependencies"], root / "node_modules", target_is_directory=True)
    (root / "tests").mkdir()
    (root / "tests/widget.spec.ts").write_text(
        "import { test } from '@playwright/test';\n"
        "test.describe('widget suite', () => {\n"
        "  test('list protocol works', () => {});\n"
        "});\n",
        encoding="utf-8",
    )
    commonjs = suffix == ".cjs" or (
        suffix == ".js" and js_scope == "commonjs"
    )
    config = (
        "module.exports = { testDir: './tests', projects: [{ name: 'chromium' }, { name: 'firefox' }] };\n"
        if commonjs
        else "export default { testDir: './tests', projects: [{ name: 'chromium' }, { name: 'firefox' }] };\n"
    )
    config_path = root / f"playwright.config{suffix}"
    config_path.write_text(config, encoding="utf-8")
    if suffix == ".js":
        assert js_scope is not None
        (root / "package.json").write_text(
            json.dumps({"type": js_scope}), encoding="utf-8"
        )
    read_fd, write_fd = os.pipe()
    result_fd = 198
    reporter = controller / "reporter.cjs"
    reporter.write_text(_playwright_reporter_source(result_fd), encoding="utf-8")
    try:
        saved_fd = os.dup(result_fd)
    except OSError:
        saved_fd = None
    try:
        os.dup2(write_fd, result_fd)
        result = subprocess.run(
            [
                roles["launcher"], roles["entrypoint"], "test",
                "tests/widget.spec.ts", f"--config={config_path}",
                f"--reporter={reporter}", "--list",
            ],
            cwd=root,
            capture_output=True,
            text=True,
            env={**os.environ, "NODE_PATH": roles["dependencies"]},
            pass_fds=(result_fd,),
            check=False,
        )
    finally:
        os.close(write_fd)
        if saved_fd is None:
            os.close(result_fd)
        else:
            os.dup2(saved_fd, result_fd)
            os.close(saved_fd)
    payload = os.read(read_fd, 64 * 1024).decode("utf-8")
    os.close(read_fd)

    outcome, detail, identities = _playwright_result(
        root, payload, result.returncode, None, collection=True,
    )

    assert outcome is EvidenceOutcome.PASS, f"{detail}: {result.stderr}"
    assert identities == (
        "chromium::tests/widget.spec.ts::widget suite > list protocol works",
        "firefox::tests/widget.spec.ts::widget suite > list protocol works",
    )


@pytest.mark.skipif(
    not sys.platform.startswith("linux")
    or not os.environ.get("PDD_RUN_REAL_PLAYWRIGHT")
    or not os.environ.get("PDD_REAL_PLAYWRIGHT_TOOLCHAIN_MANIFEST"),
    reason="requires the mandatory hosted Linux Playwright protocol lane",
)
@pytest.mark.parametrize(
    ("test_source", "reason"),
    [
        ((
            "import { test } from '@playwright/test';\n"
            "test('valid identity', () => {});\n"
            "test.skip('bad::identity', () => {});\n"
        ), "invalid_project_title"),
        ((
            "import { test } from '@playwright/test';\n"
            "test('duplicate identity', () => {});\n"
            "test('duplicate identity', () => {});\n"
        ), "framework_error"),
    ],
)
def test_real_playwright_1_55_rejects_partial_list_receipts(
    tmp_path: Path, test_source: str, reason: str,
) -> None:
    """Real list callbacks latch malformed skipped and duplicate identities."""
    manifest = Path(os.environ["PDD_REAL_PLAYWRIGHT_TOOLCHAIN_MANIFEST"])
    roles = json.loads(manifest.read_text(encoding="utf-8"))["roles"]
    package = Path(roles["dependencies"]) / "@playwright/test/package.json"
    assert json.loads(package.read_text(encoding="utf-8"))["version"].startswith("1.55.")
    root = tmp_path / "candidate"
    controller = tmp_path / "controller"
    root.mkdir()
    controller.mkdir()
    os.symlink(roles["dependencies"], root / "node_modules", target_is_directory=True)
    (root / "tests").mkdir()
    (root / "tests/widget.spec.ts").write_text(test_source, encoding="utf-8")
    config = root / "playwright.config.ts"
    config.write_text(
        "export default { testDir: './tests', projects: [{ name: 'chromium' }] };\n",
        encoding="utf-8",
    )
    read_fd, write_fd = os.pipe()
    reporter = controller / "reporter.cjs"
    reporter.write_text(_playwright_reporter_source(write_fd), encoding="utf-8")
    try:
        result = subprocess.run(
            [
                roles["launcher"], roles["entrypoint"], "test",
                "tests/widget.spec.ts", f"--config={config}",
                f"--reporter={reporter}", "--list",
            ],
            cwd=root,
            capture_output=True,
            text=True,
            env={**os.environ, "NODE_PATH": roles["dependencies"]},
            pass_fds=(write_fd,),
            check=False,
        )
    finally:
        os.close(write_fd)
    output = os.read(read_fd, 64 * 1024)
    os.close(read_fd)

    assert output, result.stderr
    assert json.loads(output) == {
        "pdd_playwright_reporter": 1,
        "reporter_error": "invalid_reporter_state",
        "reason": reason,
    }
def test_playwright_binds_static_runtime_resources_and_rejects_reflection(
    tmp_path: Path,
) -> None:
    root, _commit = _repository(tmp_path)
    resource = root / "oracle.js"
    resource.write_text("window.expected = true;\n", encoding="utf-8")
    (root / "tests/widget.spec.ts").write_text(
        "import { expect, test } from '@playwright/test';\n"
        "test('widget works', async ({ page }) => {\n"
        "  await page.addInitScript({ path: './oracle.js' });\n"
        "  await expect(page).toHaveTitle('Widget');\n"
        "});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "bind runtime oracle")
    base = _git(root, "rev-parse", "HEAD")
    paths = (PurePosixPath("tests/widget.spec.ts"),)
    before = playwright_validator_config_digest(root, base, paths)
    resource.write_text("window.expected = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change runtime oracle")
    assert playwright_validator_config_digest(
        root, _git(root, "rev-parse", "HEAD"), paths
    ) != before

    (root / "tests/widget.spec.ts").write_text(
        "import { test } from '@playwright/test';\n"
        "test('reflect', () => Object.getOwnPropertyDescriptor({}, 'x'));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "attempt reflection")
    with pytest.raises(ValueError, match="capability|reflect"):
        playwright_validator_config_digest(
            root, _git(root, "rev-parse", "HEAD"), paths
        )


def test_playwright_support_snapshot_binds_owning_spec_directory(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/assertions.ts").write_text(
        "import { expect } from '@playwright/test';\n"
        "export const check = (value: string) => expect(value).toMatchSnapshot();\n",
        encoding="utf-8",
    )
    (root / "tests/widget.spec.ts").write_text(
        "import { test } from '@playwright/test';\n"
        "import { check } from './assertions';\n"
        "test('widget works', () => check('base'));\n",
        encoding="utf-8",
    )
    snapshot = root / "tests/widget.spec.ts-snapshots/oracle.txt"
    snapshot.parent.mkdir()
    snapshot.write_text("base", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "helper-owned snapshot assertion")
    base = _git(root, "rev-parse", "HEAD")
    paths = (PurePosixPath("tests/widget.spec.ts"),)
    before = playwright_validator_config_digest(root, base, paths)
    snapshot.write_text("candidate", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change owning snapshot")
    assert playwright_validator_config_digest(
        root, _git(root, "rev-parse", "HEAD"), paths
    ) != before


def test_playwright_resources_resolve_from_runner_cwd(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "oracle.js").write_text("window.expected = 'root';\n", encoding="utf-8")
    (root / "tests/oracle.js").write_text("window.expected = 'decoy';\n", encoding="utf-8")
    (root / "tests/widget.spec.ts").write_text(
        "import { test } from '@playwright/test';\n"
        "test('widget works', async ({ page }) => "
        "page.addInitScript({ path: './oracle.js' }));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "cwd resource")
    base = _git(root, "rev-parse", "HEAD")
    paths = (PurePosixPath("tests/widget.spec.ts"),)
    before = playwright_validator_config_digest(root, base, paths)
    (root / "oracle.js").write_text("window.expected = 'changed';\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change consumed resource")
    assert playwright_validator_config_digest(root, "HEAD", paths) != before


@pytest.mark.parametrize(
    "argument",
    [
        "{ path: './bound.js', path: './candidate.js' }",
        "{ path: './bound.js', ...override }",
        "{ path: './bound.js', ['path']: './candidate.js' }",
    ],
)
def test_playwright_resource_objects_require_exact_schema(
    tmp_path: Path, argument: str
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(
        "import { test } from '@playwright/test';\n"
        f"test('widget works', async ({{ page }}) => page.addInitScript({argument}));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "ambiguous resource object")
    with pytest.raises(ValueError, match="schema|property|path"):
        playwright_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
        )


@pytest.mark.parametrize(
    "target", ["oracle.js", "tests/widget.spec.ts-snapshots/oracle.txt"]
)
def test_playwright_rejects_symlinked_closure_members(
    tmp_path: Path, target: str
) -> None:
    root, _commit = _repository(tmp_path)
    actual = root / "actual.txt"
    actual.write_text("trusted", encoding="utf-8")
    link = root / target
    link.parent.mkdir(parents=True, exist_ok=True)
    link.symlink_to(
        Path("actual.txt") if link.parent == root else Path("../../actual.txt")
    )
    if target == "oracle.js":
        (root / "tests/widget.spec.ts").write_text(
            "import { test } from '@playwright/test';\n"
            "test('widget works', async ({ page }) => "
            "page.addInitScript({ path: './oracle.js' }));\n",
            encoding="utf-8",
        )
    else:
        (root / "tests/widget.spec.ts").write_text(
            "import { expect, test } from '@playwright/test';\n"
            "test('widget works', () => expect('x').toMatchSnapshot());\n",
            encoding="utf-8",
        )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "symlink closure member")
    with pytest.raises(ValueError, match="regular|symlink"):
        playwright_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
        )


def test_playwright_excludes_declared_product_edges_from_support_digest(
    tmp_path: Path,
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "src").mkdir()
    product = root / "src/widget.ts"
    product.write_text("export const value = 'base';\n", encoding="utf-8")
    (root / "tests/widget.spec.ts").write_text(
        "import { expect, test } from '@playwright/test';\n"
        "import { value } from '../src/widget';\n"
        "test('widget works', () => expect(value).toBeTruthy());\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "product import")
    paths = (PurePosixPath("tests/widget.spec.ts"),)
    products = (PurePosixPath("src/widget.ts"),)
    before = playwright_validator_config_digest(root, "HEAD", paths, products)
    product.write_text("export const value = 'candidate';\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "candidate product change")
    assert playwright_validator_config_digest(root, "HEAD", paths, products) == before


def test_playwright_receiver_schema_accepts_representative_suite(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(
        "import { expect, test } from '@playwright/test';\n"
        "test.use({ viewport: { width: 800, height: 600 } });\n"
        "test.beforeEach(async ({ page }) => page.goto('/'));\n"
        "test('widget works', async ({ page }) => test.step('action', async () => {\n"
        "  await page.waitForSelector('#ready');\n"
        "  await expect(page.locator('#ready')).toBeEnabled();\n"
        "}));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "representative suite")
    assert playwright_validator_config_digest(
        root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
    )


@pytest.mark.parametrize(
    "target", ("file:///tmp/oracle.html", "./oracle.html", "../oracle.html")
)
def test_playwright_rejects_unbound_local_navigation(
    tmp_path: Path, target: str,
) -> None:
    """Local navigation must not read a file outside the protected closure."""
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(
        "import { test } from '@playwright/test';\n"
        "test('local navigation', async ({ page }) => {\n"
        f"  await page.goto({target!r});\n"
        "});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "unbound local navigation")

    with pytest.raises(ValueError, match="navigation target"):
        playwright_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
        )


@pytest.mark.parametrize(
    "source",
    (
        "test('file', async ({ page }) => page.goto('FILE:///tmp/oracle.html'));\n",
        "test.use({ baseURL: 'file:///tmp/' }); test('absolute', async ({ page }) => page.goto('/etc/passwd'));\n",
        "test.use({ baseURL: 'file:///tmp/' }); test('bare', async ({ page }) => page.goto('oracle.html'));\n",
        "test.use({ baseURL: 'file:///tmp/' }); test('network', async ({ page }) => page.goto('//localhost/etc/passwd'));\n",
    ),
)
def test_playwright_rejects_file_url_navigation_semantics(
    tmp_path: Path, source: str,
) -> None:
    """URL resolution must not turn a static navigation into a local file read."""
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(
        "import { test } from '@playwright/test';\n" + source,
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "file navigation semantics")

    with pytest.raises(ValueError, match="baseURL|navigation target"):
        playwright_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
        )


def test_playwright_allows_relative_navigation_with_http_base_url(tmp_path: Path) -> None:
    """Normal HTTP(S) base URL navigation remains an admitted browser capability."""
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(
        "import { test } from '@playwright/test';\n"
        "test.use({ baseURL: 'https://example.test/app/' });\n"
        "test('relative', async ({ page }) => page.goto('oracle.html'));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "http base navigation")

    assert playwright_validator_config_digest(
        root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
    )
def test_playwright_toolchain_entrypoint_must_resolve_inside_declared_package(
    tmp_path: Path,
) -> None:
    root, _commit = _repository(tmp_path)
    entrypoint = _fake_node_playwright(tmp_path)
    manifest = _toolchain_manifest(
        tmp_path / "unrelated-toolchain", Path(sys.executable), entrypoint
    )
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["roles"]["entrypoint"] = str(entrypoint.resolve())
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(ValueError, match="entrypoint|dependency|package"):
        _playwright_toolchain_identity(
            root, (sys.executable, str(entrypoint)), manifest
        )


def test_playwright_execution_uses_process_group_supervisor(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, commit = _repository(tmp_path)
    calls: list[list[str]] = []
    readable_bindings = []
    snapshot_proofs = []
    scratch_bindings = []
    temp_directories = []
    phase_roots = []

    def supervised(command, **_kwargs):
        calls.append(command)
        readable_bindings.append(_kwargs["readable_bindings"])
        snapshot_proofs.append(_kwargs["snapshot_binding_proofs"])
        scratch_bindings.append(_kwargs["writable_bindings"])
        temp_directories.append(_kwargs["temp_directory"])
        phase_roots.append(_kwargs["cwd"])
        _write_framework_observation(_kwargs, {
            "tests": [{"identity": IDENTITY, "status": "passed"}],
        })
        return _trusted_completed(command, 0, "forged stdout is ignored", ""), False

    monkeypatch.setattr(runner_module, "run_supervised", supervised)
    _envelope, executions = _run(root, commit, commit, _fake_playwright(tmp_path))
    assert executions[0].outcome is EvidenceOutcome.PASS
    assert calls
    assert scratch_bindings[0][0][1] == Path("/tmp")
    assert scratch_bindings[0][0][0].name == "tmp"
    assert scratch_bindings[0][0][0].parent.name == "scratch"
    assert temp_directories[0] == Path("/tmp")
    exact_path = str(phase_roots[0] / "tests/widget.spec.ts")
    assert calls[0][1] == str(
        phase_roots[0] / "node_modules/@playwright/test/cli.py"
    )
    assert calls[0][3] == f"^{re.escape(exact_path)}$"
    dependency_source, dependency_destination = readable_bindings[0][-1]
    assert dependency_source.name == "node_modules"
    assert dependency_destination == phase_roots[0] / "node_modules"
    assert {proof.destination for proof in snapshot_proofs[0]} >= {
        dependency_destination,
        calls[0][0] and Path(calls[0][0]),
    }
    assert all("pdd-snapshot-binding-v1" in proof.attestation for proof in snapshot_proofs[0])


def test_playwright_anonymous_observation_rejects_path_and_fd_injection(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A same-UID process cannot forge PASS through the removed FIFO pathname."""
    root, commit = _repository(tmp_path)
    attempts = 0

    def supervised(command, **kwargs):
        nonlocal attempts
        attempts += 1
        assert "result_fifo" not in kwargs
        writer = kwargs["result_write_fd"]
        assert os.get_inheritable(writer) is False
        aggregate = json.loads(kwargs["playwright_snapshot_aggregate"].attestation)
        reporter = next(
            json.loads(member["attestation"])["source"]
            for member in aggregate["members"] if member["role"] == "reporter"
        )
        temporary = Path(reporter).parent.parent
        assert not tuple(temporary.rglob("result.fifo"))
        stale = temporary / "attacker-channel/result.fifo"
        stale.parent.mkdir()
        stale.write_text(json.dumps({
            "pdd_playwright_reporter": 1,
            "tests": [{"identity": IDENTITY, "status": "passed"}],
        }), encoding="utf-8")
        injected = subprocess.run(
            [
                sys.executable, "-c",
                "import os,sys;os.write(int(sys.argv[1]),b'forged')", str(writer),
            ],
            close_fds=True, capture_output=True, text=True, check=False,
        )
        assert injected.returncode != 0
        _write_framework_observation(kwargs, {
            "tests": [{"identity": IDENTITY, "status": "skipped"}],
        })
        return _trusted_completed(command, 0), False

    monkeypatch.setattr(runner_module, "run_supervised", supervised)
    _envelope, executions = _run(root, commit, commit, _fake_playwright(tmp_path))

    assert attempts == 3
    assert executions[0].outcome is EvidenceOutcome.SKIP


@pytest.mark.parametrize(
    "role", [
        "launcher", "entrypoint", "dependencies", "browser_runtime", "lockfile",
        "native_runtime",
    ]
)
def test_playwright_snapshot_aggregate_binds_every_toolchain_role(
    tmp_path: Path, role: str,
) -> None:
    """The helper snapshot identity covers every accepted external role."""
    launcher = tmp_path / "node"
    launcher.write_text("#!/bin/sh\n", encoding="utf-8")
    launcher.chmod(0o755)
    entrypoint = _fake_playwright(tmp_path)
    manifest = _toolchain_manifest(tmp_path / "toolchain", launcher, entrypoint)
    roles = _toolchain_manifest_roles(manifest)
    reporter = tmp_path / "reporter.cjs"
    reporter.write_text(_playwright_reporter_source(198), encoding="utf-8")
    dependency_destination = tmp_path / "phase" / "node_modules"
    runtime_prefix = _playwright_runtime_prefix(
        (str(roles.launcher), str(roles.entrypoint)), roles.launcher
    )
    accepted = _toolchain_manifest_identity(manifest)

    proofs = _playwright_snapshot_binding_proofs(
        reporter,
        roles,
        Path(runtime_prefix[0]),
        dependency_destination,
        roles.native_bindings,
    )
    identity, aggregate = _playwright_snapshot_aggregate_identity(
        proofs,
        reporter,
        roles,
        Path(runtime_prefix[0]),
        dependency_destination,
        roles.native_bindings,
    )
    assert identity == accepted
    assert all(proof.source != roles.entrypoint for proof in proofs)
    reporter.write_text("changed reporter", encoding="utf-8")
    reporter_proofs = _playwright_snapshot_binding_proofs(
        reporter,
        roles,
        Path(runtime_prefix[0]),
        dependency_destination,
        roles.native_bindings,
    )
    with pytest.raises(ValueError, match="reporter snapshot is not canonical"):
        _playwright_snapshot_aggregate_identity(
            reporter_proofs,
            reporter,
            roles,
            Path(runtime_prefix[0]),
            dependency_destination,
            roles.native_bindings,
        )
    reporter.write_text(_playwright_reporter_source(198), encoding="utf-8")

    if role == "launcher":
        roles.launcher.write_text("#!/bin/sh\nexit 1\n", encoding="utf-8")
    elif role == "entrypoint":
        roles.entrypoint.write_text("changed entrypoint", encoding="utf-8")
    elif role == "dependencies":
        (roles.dependencies / "changed.js").write_text("changed", encoding="utf-8")
    elif role == "browser_runtime":
        (roles.browser_runtime / "changed").write_text("changed", encoding="utf-8")
    elif role == "lockfile":
        roles.lockfile.write_text('{"changed":true}\n', encoding="utf-8")
    else:
        roles.native_runtime[0].write_bytes(b"changed-native")

    changed = _playwright_snapshot_binding_proofs(
        reporter,
        roles,
        Path(runtime_prefix[0]),
        dependency_destination,
        roles.native_bindings,
    )
    changed_identity, changed_aggregate = _playwright_snapshot_aggregate_identity(
        changed,
        reporter,
        roles,
        Path(runtime_prefix[0]),
        dependency_destination,
        roles.native_bindings,
    )
    assert changed_identity != accepted
    assert changed_aggregate.digest != aggregate.digest


def test_playwright_snapshot_aggregate_binds_external_entrypoint_role(
    tmp_path: Path,
) -> None:
    """An entrypoint outside dependencies has one independent exact snapshot."""
    launcher = tmp_path / "node"
    launcher.write_text("#!/bin/sh\n", encoding="utf-8")
    launcher.chmod(0o755)
    source_entrypoint = _fake_playwright(tmp_path)
    manifest = _toolchain_manifest(tmp_path / "toolchain", launcher, source_entrypoint)
    external_entrypoint = tmp_path / "external-cli.py"
    external_entrypoint.write_bytes(source_entrypoint.read_bytes())
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["roles"]["entrypoint"] = str(external_entrypoint.resolve())
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    roles = _toolchain_manifest_roles(manifest)
    reporter = tmp_path / "reporter.cjs"
    reporter.write_text(_playwright_reporter_source(198), encoding="utf-8")
    dependency_destination = tmp_path / "phase" / "node_modules"
    accepted = _toolchain_manifest_identity(manifest)

    proofs = _playwright_snapshot_binding_proofs(
        reporter,
        roles,
        roles.launcher,
        dependency_destination,
        roles.native_bindings,
    )
    identity, aggregate = _playwright_snapshot_aggregate_identity(
        proofs,
        reporter,
        roles,
        roles.launcher,
        dependency_destination,
        roles.native_bindings,
    )
    entrypoint_proofs = [proof for proof in proofs if proof.source == external_entrypoint]
    assert len(entrypoint_proofs) == 1
    assert entrypoint_proofs[0].destination == external_entrypoint
    assert external_entrypoint in roles.readable_roots
    assert identity == accepted

    external_entrypoint.write_text("changed entrypoint", encoding="utf-8")
    changed = _playwright_snapshot_binding_proofs(
        reporter,
        roles,
        roles.launcher,
        dependency_destination,
        roles.native_bindings,
    )
    changed_identity, changed_aggregate = _playwright_snapshot_aggregate_identity(
        changed,
        reporter,
        roles,
        roles.launcher,
        dependency_destination,
        roles.native_bindings,
    )
    assert changed_identity != accepted
    assert changed_aggregate.digest != aggregate.digest


def test_playwright_native_alias_topology_changes_stable_identity(
    tmp_path: Path,
) -> None:
    """Distinct native loader aliases cannot share an accepted identity."""
    launcher = tmp_path / "node"
    launcher.write_text("#!/bin/sh\n", encoding="utf-8")
    launcher.chmod(0o755)
    entrypoint = _fake_playwright(tmp_path)
    manifest = _toolchain_manifest(tmp_path / "toolchain", launcher, entrypoint)
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    toolchain = manifest.parent
    first_source = toolchain / "libnative-a.so"
    second_source = toolchain / "libnative-b.so"
    first_source.write_bytes(b"identical-native-runtime")
    second_source.write_bytes(first_source.read_bytes())
    first_alias = toolchain / "libnative-first.so"
    second_alias = toolchain / "libnative-second.so"
    first_alias.symlink_to(first_source.name)
    second_alias.symlink_to(second_source.name)
    reporter = tmp_path / "reporter.cjs"
    reporter.write_text(_playwright_reporter_source(198), encoding="utf-8")
    destination = tmp_path / "phase" / "node_modules"

    payload["roles"]["native_runtime"] = [str(first_alias)]
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    first_roles = _toolchain_manifest_roles(manifest)
    first_identity = _toolchain_manifest_identity(manifest)
    first_proofs = _playwright_snapshot_binding_proofs(
        reporter, first_roles, first_roles.launcher, destination,
        first_roles.native_bindings,
    )
    first_snapshot_identity, _aggregate = _playwright_snapshot_aggregate_identity(
        first_proofs, reporter, first_roles, first_roles.launcher, destination,
        first_roles.native_bindings,
    )

    payload["roles"]["native_runtime"] = [str(second_alias)]
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    second_roles = _toolchain_manifest_roles(manifest)
    second_identity = _toolchain_manifest_identity(manifest)
    second_proofs = _playwright_snapshot_binding_proofs(
        reporter, second_roles, second_roles.launcher, destination,
        second_roles.native_bindings,
    )
    second_snapshot_identity, _aggregate = _playwright_snapshot_aggregate_identity(
        second_proofs, reporter, second_roles, second_roles.launcher, destination,
        second_roles.native_bindings,
    )

    assert first_identity == first_snapshot_identity
    assert second_identity == second_snapshot_identity
    assert first_identity != second_identity


def test_playwright_intermediate_native_alias_retarget_changes_identities(
    tmp_path: Path,
) -> None:
    """Retargeting an intermediate alias cannot preserve same-bytes identity."""
    launcher = tmp_path / "node"
    launcher.write_text("#!/bin/sh\n", encoding="utf-8")
    launcher.chmod(0o755)
    entrypoint = _fake_playwright(tmp_path)
    manifest = _toolchain_manifest(tmp_path / "toolchain", launcher, entrypoint)
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    toolchain = manifest.parent
    for name in ("a", "b"):
        source = toolchain / name / "lib.so"
        source.parent.mkdir()
        source.write_bytes(b"identical-native-runtime")
    current = toolchain / "current"
    current.symlink_to("a", target_is_directory=True)
    alias = toolchain / "alias.so"
    alias.symlink_to("current/lib.so")
    payload["roles"]["native_runtime"] = [str(alias)]
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    reporter = tmp_path / "reporter.cjs"
    reporter.write_text(_playwright_reporter_source(198), encoding="utf-8")
    destination = tmp_path / "phase" / "node_modules"

    first_roles = _toolchain_manifest_roles(manifest)
    first_manifest_identity = _toolchain_manifest_identity(manifest)
    first_proofs = _playwright_snapshot_binding_proofs(
        reporter, first_roles, first_roles.launcher, destination,
        first_roles.native_bindings,
    )
    first_snapshot_identity, _aggregate = _playwright_snapshot_aggregate_identity(
        first_proofs, reporter, first_roles, first_roles.launcher, destination,
        first_roles.native_bindings,
    )
    current.unlink()
    current.symlink_to("b", target_is_directory=True)
    second_roles = _toolchain_manifest_roles(manifest)
    second_manifest_identity = _toolchain_manifest_identity(manifest)
    second_proofs = _playwright_snapshot_binding_proofs(
        reporter, second_roles, second_roles.launcher, destination,
        second_roles.native_bindings,
    )
    second_snapshot_identity, _aggregate = _playwright_snapshot_aggregate_identity(
        second_proofs, reporter, second_roles, second_roles.launcher, destination,
        second_roles.native_bindings,
    )

    assert first_manifest_identity == first_snapshot_identity
    assert second_manifest_identity == second_snapshot_identity
    assert first_manifest_identity != second_manifest_identity


def test_playwright_snapshot_rejects_native_alias_retarget_after_measurement(
    tmp_path: Path, trusted_toolchain_dir: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A same-bytes native alias retarget cannot satisfy the accepted identity."""
    root, commit = _repository(tmp_path)
    fake = _fake_playwright(tmp_path)
    manifest = _toolchain_manifest(
        trusted_toolchain_dir / "toolchain", Path(sys.executable), fake
    )
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    toolchain = manifest.parent
    first_source = toolchain / "native-first.so"
    second_source = toolchain / "native-second.so"
    first_source.write_bytes(b"identical-native-runtime")
    second_source.write_bytes(first_source.read_bytes())
    alias = toolchain / "native-alias.so"
    alias.symlink_to(first_source.name)
    payload["roles"]["native_runtime"] = [str(alias)]
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    roles = _toolchain_manifest_roles(manifest)
    config = RunnerConfig(
        timeout_seconds=2,
        playwright_command=(str(roles.launcher), str(roles.entrypoint)),
        playwright_toolchain_manifest=manifest,
        playwright_toolchain_identity=_playwright_toolchain_identity(
            root, (str(roles.launcher), str(roles.entrypoint)), manifest
        ),
    )
    original = runner_module._playwright_snapshot_binding_proofs

    def retarget_before_snapshot(*args, **kwargs):
        alias.unlink()
        alias.symlink_to(second_source.name)
        return original(*args, **kwargs)

    def must_not_supervise(*_args, **_kwargs):
        raise AssertionError("retargeted native alias must fail before supervision")

    monkeypatch.setattr(
        runner_module, "_playwright_snapshot_binding_proofs", retarget_before_snapshot
    )
    monkeypatch.setattr(runner_module, "run_supervised", must_not_supervise)
    execution, _identities = runner_module._run_playwright_in_tree(
        root, (PurePosixPath("tests/widget.spec.ts"),), 2, config,
        expected_commit=commit,
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert "snapshot" in execution.detail.lower()


@pytest.mark.parametrize("swap", ["launcher", "dependency"])
def test_playwright_rejects_swap_between_accepted_identity_and_snapshot(
    tmp_path: Path, trusted_toolchain_dir: Path, monkeypatch: pytest.MonkeyPatch,
    swap: str,
) -> None:
    """A replacement cannot self-attest after the accepted identity is measured."""
    root, commit = _repository(tmp_path)
    fake = _fake_playwright(tmp_path)
    launcher = trusted_toolchain_dir / "node"
    launcher.write_text(
        f"#!/bin/sh\nexec {sys.executable!s} \"$@\"\n", encoding="utf-8"
    )
    launcher.chmod(0o755)
    manifest = _toolchain_manifest(trusted_toolchain_dir / "toolchain", launcher, fake)
    roles = _toolchain_manifest_roles(manifest)
    config = RunnerConfig(
        timeout_seconds=2,
        playwright_command=(str(launcher), str(roles.entrypoint)),
        playwright_toolchain_manifest=manifest,
        playwright_toolchain_identity=_playwright_toolchain_identity(
            root, (str(launcher), str(roles.entrypoint)), manifest
        ),
    )
    original = runner_module._playwright_snapshot_binding_proofs
    supervised = False

    def swap_before_snapshot(*args, **kwargs):
        if swap == "launcher":
            roles.launcher.write_text("#!/bin/sh\nexit 1\n", encoding="utf-8")
        else:
            (roles.dependencies / "attacker.js").write_text(
                "module.exports = 'attacker';\n", encoding="utf-8"
            )
        return original(*args, **kwargs)

    def must_not_supervise(*_args, **_kwargs):
        nonlocal supervised
        supervised = True
        raise AssertionError("snapshot mismatch must reject before helper handoff")

    monkeypatch.setattr(
        runner_module, "_playwright_snapshot_binding_proofs", swap_before_snapshot
    )
    monkeypatch.setattr(runner_module, "run_supervised", must_not_supervise)
    execution, _identities = runner_module._run_playwright_in_tree(
        root,
        (PurePosixPath("tests/widget.spec.ts"),),
        2,
        config,
        expected_commit=commit,
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert "snapshot" in execution.detail.lower()
    assert supervised is False


def test_playwright_exact_filter_escapes_regex_metacharacters(
    tmp_path: Path, trusted_toolchain_dir: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Select one literal test path even when its name contains regex syntax."""
    root, commit = _repository(tmp_path)
    original = root / "tests/widget.spec.ts"
    selected = root / "tests/widget[1]+.spec.ts"
    original.rename(selected)
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", "regex metacharacter test path")
    commit = _git(root, "rev-parse", "HEAD")
    calls: list[list[str]] = []

    def supervised(command, **kwargs):
        calls.append(command)
        _write_framework_observation(kwargs, {
            "tests": [{"identity": IDENTITY, "status": "passed"}],
        })
        return _trusted_completed(command, 0), False

    monkeypatch.setattr(runner_module, "run_supervised", supervised)
    execution, _identities = runner_module._run_playwright_in_tree(
        root, (PurePosixPath("tests/widget[1]+.spec.ts"),), 2,
        _trusted_playwright_config(trusted_toolchain_dir, _fake_playwright(tmp_path)),
        expected_commit=commit,
    )

    assert execution.outcome is EvidenceOutcome.PASS
    assert calls[0][3] == f"^{re.escape(str(selected))}$"


def test_playwright_rejects_candidate_node_modules_directory_before_execution(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, commit = _repository(tmp_path)
    (root / "node_modules").mkdir()
    launches = 0

    def supervised(*_args, **_kwargs):
        nonlocal launches
        launches += 1
        raise AssertionError("candidate node_modules must fail before execution")

    monkeypatch.setattr(runner_module, "run_supervised", supervised)
    monkeypatch.setattr(
        runner_module,
        "_playwright_toolchain_identity",
        lambda *_args: (_ for _ in ()).throw(
            ValueError("toolchain validation must follow candidate preflight")
        ),
    )

    execution, _identities = runner_module._run_playwright_in_tree(
        root, (PurePosixPath("tests/widget.spec.ts"),), 2,
        _trusted_playwright_config(tmp_path / "trusted", _fake_playwright(tmp_path)),
        expected_commit=commit,
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert "candidate node_modules" in execution.detail
    assert launches == 0


@pytest.mark.parametrize("reserved", ["@playwright/test", "playwright", "playwright-core"])
def test_playwright_rejects_candidate_package_self_reference_before_execution(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, reserved: str,
) -> None:
    root, commit = _repository(tmp_path)
    (root / "package.json").write_text(
        json.dumps({
            "name": reserved,
            "type": "module",
            "exports": {".": "./tests/widget.spec.ts"},
        }),
        encoding="utf-8",
    )
    _git(root, "add", "package.json")
    _git(root, "commit", "-q", "-m", "candidate package self reference")
    commit = _git(root, "rev-parse", "HEAD")
    launches = 0

    def supervised(*_args, **_kwargs):
        nonlocal launches
        launches += 1
        raise AssertionError("reserved package scope must fail before execution")

    monkeypatch.setattr(runner_module, "run_supervised", supervised)

    _envelope, executions = _run(
        root, commit, commit, _fake_playwright(tmp_path)
    )

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "reserved" in executions[0].detail.lower()
    assert launches == 0


def test_playwright_rejects_candidate_node_modules_symlink_before_execution(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, commit = _repository(tmp_path)
    outside = tmp_path / "candidate-modules"
    outside.mkdir()
    (root / "node_modules").symlink_to(outside, target_is_directory=True)
    launches = 0

    def supervised(*_args, **_kwargs):
        nonlocal launches
        launches += 1
        raise AssertionError("node_modules symlink must fail before execution")

    monkeypatch.setattr(runner_module, "run_supervised", supervised)

    execution, _identities = runner_module._run_playwright_in_tree(
        root, (PurePosixPath("tests/widget.spec.ts"),), 2,
        _trusted_playwright_config(tmp_path / "trusted", _fake_playwright(tmp_path)),
        expected_commit=commit,
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert "node_modules" in execution.detail
    assert "symlink" in execution.detail
    assert launches == 0


@pytest.mark.parametrize("module_type", ["commonjs", "module"])
@pytest.mark.parametrize("reserved", ["@playwright/test", "playwright", "playwright-core"])
def test_playwright_rejects_nested_reserved_package_scopes(
    tmp_path: Path, module_type: str, reserved: str,
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/package.json").write_text(
        json.dumps({"name": reserved, "type": module_type}), encoding="utf-8"
    )
    _git(root, "add", "tests/package.json")
    _git(root, "commit", "-q", "-m", "nested package self reference")

    with pytest.raises(ValueError, match="reserved package self-reference"):
        playwright_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
        )


@pytest.mark.parametrize("module_type", ["commonjs", "module"])
@pytest.mark.parametrize("node_modules_type", ["directory", "symlink", "file"])
def test_playwright_rejects_nested_node_modules_before_execution(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    module_type: str, node_modules_type: str,
) -> None:
    root, commit = _repository(tmp_path)
    (root / "tests/package.json").write_text(
        json.dumps({"name": "candidate-tests", "type": module_type}),
        encoding="utf-8",
    )
    _git(root, "add", "tests/package.json")
    _git(root, "commit", "-q", "-m", "nested module mode")
    commit = _git(root, "rev-parse", "HEAD")
    destination = root / "tests/node_modules"
    if node_modules_type == "directory":
        destination.mkdir()
    elif node_modules_type == "symlink":
        outside = tmp_path / "outside-modules"
        outside.mkdir()
        destination.symlink_to(outside, target_is_directory=True)
    else:
        destination.write_text("shadow", encoding="utf-8")
    launches = 0

    def supervised(*_args, **_kwargs):
        nonlocal launches
        launches += 1
        raise AssertionError("nested node_modules must fail before execution")

    monkeypatch.setattr(runner_module, "run_supervised", supervised)
    monkeypatch.setattr(
        runner_module,
        "_playwright_toolchain_identity",
        lambda *_args: (_ for _ in ()).throw(
            ValueError("toolchain validation must follow candidate preflight")
        ),
    )
    execution, _identities = runner_module._run_playwright_in_tree(
        root, (PurePosixPath("tests/widget.spec.ts"),), 2,
        _trusted_playwright_config(tmp_path / "trusted", _fake_playwright(tmp_path)),
        expected_commit=commit,
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert "tests/node_modules" in execution.detail
    assert launches == 0


@pytest.mark.parametrize("module_type", ["commonjs", "module"])
def test_playwright_accepts_normal_nested_package_scope(
    tmp_path: Path, module_type: str,
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/package.json").write_text(
        json.dumps({"name": "candidate-tests", "type": module_type}),
        encoding="utf-8",
    )
    _git(root, "add", "tests/package.json")
    _git(root, "commit", "-q", "-m", "normal nested package")

    assert playwright_validator_config_digest(
        root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
    )


@pytest.mark.parametrize("member", ["support", "product"])
def test_playwright_checks_node_resolution_for_all_executable_closure_members(
    tmp_path: Path, member: str,
) -> None:
    root, _commit = _repository(tmp_path)
    if member == "support":
        source = root / "helpers/deep/support.ts"
        source.parent.mkdir(parents=True)
        source.write_text("export const value = true;\n", encoding="utf-8")
        (root / "tests/widget.spec.ts").write_text(
            "import { test } from '@playwright/test';\n"
            "import { value } from '../helpers/deep/support';\n"
            "test('widget works', () => value);\n",
            encoding="utf-8",
        )
        products: tuple[PurePosixPath, ...] = ()
    else:
        source = root / "src/deep/widget.ts"
        source.parent.mkdir(parents=True)
        source.write_text("export const value = true;\n", encoding="utf-8")
        products = (PurePosixPath("src/deep/widget.ts"),)
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "nested executable closure member")
    (source.parent / "node_modules").mkdir()

    with pytest.raises(ValueError, match="candidate node_modules"):
        playwright_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),), products
        )


@pytest.mark.parametrize("attack", ["reserved", "node_modules"])
def test_playwright_rejects_node_trust_attacks_anywhere_in_phase_tree(
    tmp_path: Path, attack: str,
) -> None:
    root, _commit = _repository(tmp_path)
    unrelated = root / "unrelated/deep"
    unrelated.mkdir(parents=True)
    if attack == "reserved":
        (unrelated / "package.json").write_text(
            json.dumps({"name": "@playwright/test"}), encoding="utf-8"
        )
        _git(root, "add", ".")
        _git(root, "commit", "-q", "-m", "unrelated reserved package")
        match = "reserved package self-reference"
    else:
        (unrelated / "node_modules").mkdir()
        match = "candidate node_modules"

    with pytest.raises(ValueError, match=match):
        playwright_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
        )


@pytest.mark.parametrize("suffix", ["", ".node", ".txt"])
def test_playwright_rejects_unsupported_executable_local_imports(
    tmp_path: Path, suffix: str,
) -> None:
    root, _commit = _repository(tmp_path)
    imported = root / f"tests/native{suffix}"
    imported.write_bytes(b"module payload")
    (root / "tests/widget.spec.ts").write_text(
        "import { test } from '@playwright/test';\n"
        f"import './native{suffix}';\n"
        "test('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "unsupported local executable")

    with pytest.raises(ValueError, match="unsupported executable|native module"):
        playwright_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
        )


def test_playwright_full_tree_policy_covers_dynamic_product_dependencies(
    tmp_path: Path,
) -> None:
    root, _commit = _repository(tmp_path)
    product = root / "src/dynamic.ts"
    product.parent.mkdir()
    product.write_text(
        "export async function load() { return import('./feature'); }\n",
        encoding="utf-8",
    )
    (root / "src/node_modules").mkdir()
    _git(root, "add", "src/dynamic.ts")
    _git(root, "commit", "-q", "-m", "dynamic product dependency")

    with pytest.raises(ValueError, match="candidate node_modules"):
        playwright_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),),
            (PurePosixPath("src/dynamic.ts"),),
        )


@pytest.mark.skipif(not shutil.which("node"), reason="requires Node module resolution")
@pytest.mark.parametrize("module_type", ["commonjs", "module"])
def test_trusted_playwright_package_resolves_for_real_node_modes(
    tmp_path: Path, module_type: str,
) -> None:
    """Exercise real CJS and ESM resolution against the identity-bound package."""
    project = tmp_path / module_type
    package = project / "node_modules/@playwright/test"
    package.mkdir(parents=True)
    (package / "package.json").write_text(
        json.dumps({"name": "@playwright/test", "main": "index.js"}),
        encoding="utf-8",
    )
    (package / "index.js").write_text(
        "module.exports = { identity: 'trusted-playwright-package' };\n",
        encoding="utf-8",
    )
    (project / "package.json").write_text(
        json.dumps({"name": "candidate", "type": module_type}), encoding="utf-8"
    )
    script = (
        "console.log(require('@playwright/test').identity);"
        if module_type == "commonjs"
        else "import('@playwright/test').then(x => console.log(x.default.identity));"
    )

    completed = subprocess.run(
        [shutil.which("node"), "-e", script], cwd=project,
        capture_output=True, text=True, check=False,
    )

    assert completed.returncode == 0, completed.stderr
    assert completed.stdout.strip() == "trusted-playwright-package"


def test_playwright_checker_temp_roots_cannot_alias_sandbox_tmp(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Keep every checker mount source outside the host path bound to /tmp."""
    root, commit = _repository(tmp_path)
    phase_roots: list[Path] = []
    scratch_roots: list[Path] = []
    result_writer_authorities: list[tuple[bool, bool]] = []
    readable_roots: list[tuple[Path, ...]] = []
    readable_bindings: list[tuple[tuple[Path, Path], ...]] = []
    tmp_sources: list[Path] = []
    tmp_destinations: list[Path] = []

    def supervised(command, *, cwd, writable_roots, writable_bindings, **kwargs):
        phase_roots.append(cwd)
        scratch_roots.append(writable_roots[0])
        readable_roots.append(kwargs["readable_roots"])
        readable_bindings.append(kwargs["readable_bindings"])
        writer = kwargs["result_write_fd"]
        result_writer_authorities.append((
            stat.S_ISFIFO(os.fstat(writer).st_mode), os.get_inheritable(writer)
        ))
        source, destination = writable_bindings[0]
        tmp_sources.append(source)
        tmp_destinations.append(destination)
        _write_framework_observation(kwargs, {
            "tests": [{"identity": IDENTITY, "status": "passed"}],
        })
        return _trusted_completed(command, 0), False

    monkeypatch.setattr(runner_module, "run_supervised", supervised)
    _envelope, executions = _run(root, commit, commit, _fake_playwright(tmp_path))

    assert executions[0].outcome is EvidenceOutcome.PASS
    assert len(phase_roots) == 3
    assert len(readable_roots) == len(phase_roots)
    assert len(readable_bindings) == len(phase_roots)
    assert all(len(roots) == 4 for roots in readable_roots)
    assert all(len(bindings) == 2 for bindings in readable_bindings)
    sandbox_tmp = Path("/tmp").resolve()
    assert result_writer_authorities == [(True, False)] * len(phase_roots)
    for path in (*phase_roots, *scratch_roots):
        assert not path.resolve().is_relative_to(sandbox_tmp)
    for roots in readable_roots:
        for path in roots:
            assert not path.resolve().is_relative_to(sandbox_tmp)
    for bindings in readable_bindings:
        for _source, destination in bindings:
            assert not destination.resolve().is_relative_to(sandbox_tmp)
    for source, destination in zip(tmp_sources, tmp_destinations, strict=True):
        assert destination == Path("/tmp")
        assert source.resolve() != sandbox_tmp
        assert not source.resolve().is_relative_to(sandbox_tmp)
        assert not sandbox_tmp.is_relative_to(source.resolve())


def test_playwright_checker_temp_parent_rejects_sandbox_tmp_alias(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Do not fall back to /tmp when the trusted parent aliases it."""
    monkeypatch.setattr(runner_module, "_PLAYWRIGHT_HOST_TEMP_PARENT", Path("/tmp"))

    with pytest.raises(RuntimeError, match="aliases sandbox /tmp"):
        _playwright_host_temp_parent()


def test_playwright_rejects_tmp_toolchain_destination_before_supervision(
    tmp_path: Path, trusted_toolchain_dir: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A manifest mount destination must not collide with bounded sandbox /tmp."""
    root, commit = _repository(tmp_path)
    fake = _fake_playwright(tmp_path)
    config = _trusted_playwright_config(trusted_toolchain_dir, fake)
    manifest = config.playwright_toolchain_manifest
    assert manifest is not None
    browser_runtime = Path("/tmp") / f"pdd-playwright-{os.urandom(16).hex()}"
    browser_runtime.mkdir()
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["roles"]["browser_runtime"] = str(browser_runtime)
    manifest.write_text(json.dumps(payload), encoding="utf-8")

    def must_not_supervise(*_args, **_kwargs):
        raise AssertionError("/tmp-rooted toolchain must fail before supervision")

    monkeypatch.setattr(runner_module, "run_supervised", must_not_supervise)
    try:
        execution, _identities = runner_module._run_playwright_in_tree(
            root,
            (PurePosixPath("tests/widget.spec.ts"),),
            2,
            config,
            expected_commit=commit,
        )
    finally:
        shutil.rmtree(browser_runtime)

    assert execution.outcome is EvidenceOutcome.COLLECTION_ERROR
    assert "sandbox /tmp" in execution.detail


def test_playwright_rejects_native_runtime_lexically_in_tmp(
    tmp_path: Path, trusted_toolchain_dir: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Reject a /tmp native destination even when its target is outside /tmp."""
    root, commit = _repository(tmp_path)
    config = _trusted_playwright_config(
        trusted_toolchain_dir, _fake_playwright(tmp_path)
    )
    manifest = config.playwright_toolchain_manifest
    assert manifest is not None
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    native = Path(payload["roles"]["native_runtime"][0])
    link = Path("/tmp") / f"pdd-playwright-{os.urandom(16).hex()}"
    link.symlink_to(os.path.relpath(native, link.parent.resolve()))
    payload["roles"]["native_runtime"] = [str(link)]
    manifest.write_text(json.dumps(payload), encoding="utf-8")

    def must_not_supervise(*_args, **_kwargs):
        raise AssertionError("/tmp-native destination must fail before supervision")

    monkeypatch.setattr(runner_module, "run_supervised", must_not_supervise)
    try:
        execution, _identities = runner_module._run_playwright_in_tree(
            root,
            (PurePosixPath("tests/widget.spec.ts"),),
            2,
            config,
            expected_commit=commit,
        )
    finally:
        link.unlink()

    assert execution.outcome is EvidenceOutcome.COLLECTION_ERROR
    assert "lexically aliases sandbox /tmp" in execution.detail


def test_playwright_allows_tmp_native_source_bound_outside_tmp(
    tmp_path: Path, trusted_toolchain_dir: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Permit an outside destination whose final native symlink targets /tmp."""
    root, commit = _repository(tmp_path)
    config = _trusted_playwright_config(
        trusted_toolchain_dir, _fake_playwright(tmp_path)
    )
    manifest = config.playwright_toolchain_manifest
    assert manifest is not None
    source = Path("/tmp") / f"pdd-playwright-{os.urandom(16).hex()}.so"
    source.write_bytes(b"synthetic-native-runtime")
    destination = trusted_toolchain_dir / "native-runtime.so"
    destination.symlink_to(os.path.relpath(source, destination.parent.resolve()))
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["roles"]["native_runtime"] = [str(destination)]
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    supervised = False

    def run_supervised(command, **kwargs):
        nonlocal supervised
        supervised = True
        assert kwargs["readable_bindings"] == (
            (source.resolve(), destination),
            (
                Path(payload["roles"]["dependencies"]).resolve(),
                root / "node_modules",
            ),
        )
        _write_framework_observation(kwargs, {
            "tests": [{"identity": IDENTITY, "status": "passed"}],
        })
        return _trusted_completed(command, 0), False

    monkeypatch.setattr(runner_module, "run_supervised", run_supervised)
    try:
        execution, _identities = runner_module._run_playwright_in_tree(
            root,
            (PurePosixPath("tests/widget.spec.ts"),),
            2,
            config,
            expected_commit=commit,
        )
    finally:
        destination.unlink()
        source.unlink()

    assert supervised
    assert execution.outcome is EvidenceOutcome.PASS


def test_playwright_uses_one_native_binding_snapshot(
    tmp_path: Path, trusted_toolchain_dir: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Use one native binding evaluation for validation and supervision."""
    root, commit = _repository(tmp_path)
    config = _trusted_playwright_config(
        trusted_toolchain_dir, _fake_playwright(tmp_path)
    )
    original = runner_module.PlaywrightToolchainRoles.native_bindings
    evaluations = 0

    def counted_native_bindings(self):
        nonlocal evaluations
        evaluations += 1
        if evaluations > 1:
            raise AssertionError("native bindings must not be recomputed")
        return original.__get__(self, type(self))

    def run_supervised(command, **kwargs):
        assert kwargs["readable_bindings"]
        _write_framework_observation(kwargs, {
            "tests": [{"identity": IDENTITY, "status": "passed"}],
        })
        return _trusted_completed(command, 0), False

    monkeypatch.setattr(
        runner_module.PlaywrightToolchainRoles,
        "native_bindings",
        property(counted_native_bindings),
    )
    monkeypatch.setattr(runner_module, "run_supervised", run_supervised)
    execution, _identities = runner_module._run_playwright_in_tree(
        root,
        (PurePosixPath("tests/widget.spec.ts"),),
        2,
        config,
        expected_commit=commit,
    )

    assert evaluations == 1
    assert execution.outcome is EvidenceOutcome.PASS


def test_playwright_rejects_native_destination_parent_aliasing_tmp(
    tmp_path: Path, trusted_toolchain_dir: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Reject an outside spelling whose native destination parent aliases /tmp."""
    root, commit = _repository(tmp_path)
    config = _trusted_playwright_config(
        trusted_toolchain_dir, _fake_playwright(tmp_path)
    )
    manifest = config.playwright_toolchain_manifest
    assert manifest is not None
    source = Path("/tmp") / f"pdd-playwright-{os.urandom(16).hex()}.so"
    source.write_bytes(b"synthetic-native-runtime")
    alias = trusted_toolchain_dir / "tmp-alias"
    alias.symlink_to("/tmp", target_is_directory=True)
    destination = alias / source.name
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["roles"]["native_runtime"] = [str(destination)]
    manifest.write_text(json.dumps(payload), encoding="utf-8")

    def must_not_supervise(*_args, **_kwargs):
        raise AssertionError("/tmp parent alias must fail before supervision")

    monkeypatch.setattr(runner_module, "run_supervised", must_not_supervise)
    try:
        execution, _identities = runner_module._run_playwright_in_tree(
            root,
            (PurePosixPath("tests/widget.spec.ts"),),
            2,
            config,
            expected_commit=commit,
        )
    finally:
        alias.unlink()
        source.unlink()

    assert execution.outcome is EvidenceOutcome.COLLECTION_ERROR
    assert "parent resolves into sandbox /tmp" in execution.detail


@pytest.mark.parametrize(
    ("kind", "expected"),
    [
        ("candidate", "candidate"),
        ("checker", "checker"),
        ("writable", "approved writable"),
        ("traversal", "lexically normalized"),
    ],
)
def test_playwright_rejects_unsafe_native_destination_topology(
    tmp_path: Path, kind: str, expected: str,
) -> None:
    """Native loader aliases need an approved, non-candidate mount topology."""
    toolchain = tmp_path / "toolchain"
    dependencies = toolchain / "node_modules"
    entrypoint = dependencies / "@playwright/test/cli.js"
    entrypoint.parent.mkdir(parents=True)
    entrypoint.write_text("cli", encoding="utf-8")
    launcher = toolchain / "node"
    launcher.write_text("#!/bin/sh\n", encoding="utf-8")
    browser = toolchain / "browser"
    browser.mkdir()
    lockfile = toolchain / "package-lock.json"
    lockfile.write_text("{}", encoding="utf-8")
    source = toolchain / "native.so"
    source.write_bytes(b"native")
    roles = runner_module.PlaywrightToolchainRoles(
        launcher, entrypoint, dependencies, browser, (source,), lockfile
    )
    candidate = tmp_path / "candidate"
    candidate.mkdir()
    checker = tmp_path / "checker-control"
    checker.mkdir()
    unapproved = tmp_path / "unapproved"
    unapproved.mkdir()
    if kind == "candidate":
        destination = candidate / "native-alias.so"
    elif kind == "checker":
        destination = checker / "native-alias.so"
    elif kind == "writable":
        destination = unapproved / "native-alias.so"
    else:
        escaped = candidate / "native-alias.so"
        destination = toolchain / ".." / candidate.name / escaped.name
    destination.symlink_to(os.path.relpath(source, destination.parent))

    error = runner_module._playwright_sandbox_destination_error(
        roles,
        ((source, destination),),
        candidate_root=candidate,
        checker_roots=(checker,),
        approved_writable_roots=(toolchain,),
    )

    assert error is not None
    assert expected in error


def test_playwright_rejects_chmod_capable_native_destination_parent(
    tmp_path: Path,
) -> None:
    """A user-owned 0555 parent remains mutable through chmod."""
    toolchain = tmp_path / "toolchain"
    dependencies = toolchain / "node_modules"
    entrypoint = dependencies / "@playwright/test/cli.js"
    entrypoint.parent.mkdir(parents=True)
    entrypoint.write_text("cli", encoding="utf-8")
    launcher = toolchain / "node"
    launcher.write_text("#!/bin/sh\n", encoding="utf-8")
    browser = toolchain / "browser"
    browser.mkdir()
    lockfile = toolchain / "package-lock.json"
    lockfile.write_text("{}", encoding="utf-8")
    source = toolchain / "native.so"
    source.write_bytes(b"native")
    roles = runner_module.PlaywrightToolchainRoles(
        launcher, entrypoint, dependencies, browser, (source,), lockfile
    )
    unapproved = tmp_path / "unapproved"
    unapproved.mkdir()
    destination = unapproved / "native-alias.so"
    destination.symlink_to(os.path.relpath(source, destination.parent))
    unapproved.chmod(0o555)
    try:
        error = runner_module._playwright_sandbox_destination_error(
            roles,
            ((source, destination),),
            approved_writable_roots=(toolchain,),
        )
    finally:
        unapproved.chmod(0o755)

    assert error is not None
    assert "owner-controlled" in error


def test_playwright_rejects_replaceable_native_destination_ancestor(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A sealed immediate parent is unsafe beneath a replaceable ancestor."""
    toolchain = tmp_path / "toolchain"
    dependencies = toolchain / "node_modules"
    entrypoint = dependencies / "@playwright/test/cli.js"
    entrypoint.parent.mkdir(parents=True)
    entrypoint.write_text("cli", encoding="utf-8")
    launcher = toolchain / "node"
    launcher.write_text("#!/bin/sh\n", encoding="utf-8")
    browser = toolchain / "browser"
    browser.mkdir()
    lockfile = toolchain / "package-lock.json"
    lockfile.write_text("{}", encoding="utf-8")
    source = toolchain / "native.so"
    source.write_bytes(b"native")
    roles = runner_module.PlaywrightToolchainRoles(
        launcher, entrypoint, dependencies, browser, (source,), lockfile
    )
    replaceable = tmp_path / "replaceable"
    sealed = replaceable / "sealed"
    sealed.mkdir(parents=True)
    destination = sealed / "native-alias.so"
    destination.symlink_to(os.path.relpath(source, destination.parent))
    sealed.chmod(0o555)
    original_stat = Path.stat
    sealed_identity = sealed.resolve()

    def stat_with_foreign_sealed_owner(
        path: Path, *, follow_symlinks: bool = True,
    ) -> os.stat_result:
        metadata = original_stat(path, follow_symlinks=follow_symlinks)
        if path == sealed_identity:
            values = list(metadata)
            values[4] = os.getuid() + 1
            return os.stat_result(values)
        return metadata

    monkeypatch.setattr(Path, "stat", stat_with_foreign_sealed_owner)
    try:
        error = runner_module._playwright_sandbox_destination_error(
            roles,
            ((source, destination),),
            approved_writable_roots=(toolchain,),
        )
    finally:
        sealed.chmod(0o755)

    assert error is not None
    assert str(replaceable) in error


@pytest.mark.parametrize(
    ("target", "expected"),
    [
        ("phase", EvidenceOutcome.COLLECTION_ERROR),
        ("trusted", EvidenceOutcome.ERROR),
    ],
)
def test_playwright_temp_creation_failure_is_normalized(
    tmp_path: Path, trusted_toolchain_dir: Path, monkeypatch: pytest.MonkeyPatch,
    target: str, expected: EvidenceOutcome,
) -> None:
    """Creation failures remain non-passing evidence in both Playwright lifecycles."""
    root, commit = _repository(tmp_path)
    config = _trusted_playwright_config(
        trusted_toolchain_dir, _fake_playwright(tmp_path)
    )

    def unavailable(*_args, **_kwargs):
        raise PermissionError("temporary directory denied")

    monkeypatch.setattr(runner_module.tempfile, "TemporaryDirectory", unavailable)
    paths = (PurePosixPath("tests/widget.spec.ts"),)
    if target == "phase":
        execution, _identities = runner_module._run_playwright(
            root, paths, 2, config
        )
    else:
        execution, _identities = runner_module._run_playwright_in_tree(
            root, paths, 2, config, expected_commit=commit
        )

    assert execution.outcome is expected
    assert "temporary directory" in execution.detail


@pytest.mark.parametrize(
    ("target", "expected"),
    [
        ("phase", EvidenceOutcome.COLLECTION_ERROR),
        ("trusted", EvidenceOutcome.ERROR),
    ],
)
def test_playwright_temp_cleanup_failure_is_normalized(
    tmp_path: Path, trusted_toolchain_dir: Path, monkeypatch: pytest.MonkeyPatch,
    target: str, expected: EvidenceOutcome,
) -> None:
    """Cleanup failures remain non-passing evidence in both Playwright lifecycles."""
    root, commit = _repository(tmp_path)
    config = _trusted_playwright_config(
        trusted_toolchain_dir, _fake_playwright(tmp_path)
    )
    original = runner_module.tempfile.TemporaryDirectory

    class CleanupFailureTemporaryDirectory:
        """Delegate setup, then model a checker temporary cleanup failure."""

        def __init__(self, *args, **kwargs):
            self._temporary = original(*args, **kwargs)

        def __enter__(self):
            return self._temporary.__enter__()

        def __exit__(self, *args):
            self._temporary.__exit__(*args)
            raise PermissionError("temporary directory cleanup denied")

    def supervised(command, **kwargs):
        _write_framework_observation(kwargs, {
            "tests": [{"identity": IDENTITY, "status": "passed"}],
        })
        return _trusted_completed(command, 0), False

    monkeypatch.setattr(
        runner_module.tempfile, "TemporaryDirectory", CleanupFailureTemporaryDirectory
    )
    monkeypatch.setattr(runner_module, "run_supervised", supervised)
    paths = (PurePosixPath("tests/widget.spec.ts"),)
    if target == "phase":
        execution, _identities = runner_module._run_playwright(
            root, paths, 2, config
        )
    else:
        execution, _identities = runner_module._run_playwright_in_tree(
            root, paths, 2, config, expected_commit=commit
        )

    assert execution.outcome is expected
    assert "temporary directory" in execution.detail


def test_playwright_temp_body_oserror_propagates_unchanged() -> None:
    """Do not normalize a body OSError when temporary cleanup succeeds."""
    with pytest.raises(FileNotFoundError, match="body failure"):
        with runner_module._playwright_temporary_directory(
            "pdd-test-playwright-", _playwright_host_temp_parent()
        ):
            raise FileNotFoundError("body failure")


@pytest.mark.parametrize(
    "config",
    [
        "export default { updateSnapshots: 'all' };\n",
        "export default { updateSourceMethod: 'overwrite' };\n",
    ],
)
def test_playwright_rejects_snapshot_update_configuration(
    tmp_path: Path, config: str
) -> None:
    root, commit = _repository(tmp_path, config=config)
    _envelope, executions = _run(root, commit, commit, _fake_playwright(tmp_path))
    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "update" in executions[0].detail.lower()


def test_playwright_forces_snapshot_updates_off_and_detects_tree_writes(
    tmp_path: Path,
) -> None:
    root, commit = _repository(tmp_path)
    fake = _fake_playwright(tmp_path)
    fake.write_text(
        fake.read_text(encoding="utf-8")
        + "\nassert '--update-snapshots=none' in sys.argv\n"
        + "\n(root / 'tests/widget.spec.ts').write_text('mutated')\n",
        encoding="utf-8",
    )
    _envelope, executions = _run(root, commit, commit, fake)
    assert executions[0].outcome in {
        EvidenceOutcome.ERROR, EvidenceOutcome.COLLECTION_ERROR,
    }


def test_playwright_manifest_roles_drive_runtime_environment(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    runner = _fake_playwright(tmp_path)
    runner.write_text(
        runner.read_text(encoding="utf-8")
        + "\nassert os.environ['NODE_PATH'].endswith('node_modules')\n"
        + "assert os.environ['PLAYWRIGHT_BROWSERS_PATH'].endswith('browsers')\n",
        encoding="utf-8",
    )
    _envelope, executions = _run(root, commit, commit, runner)
    assert executions[0].outcome is EvidenceOutcome.PASS


@pytest.mark.parametrize(
    ("suffix", "source"),
    [
        ("js", "const view = <div />; test('widget works', () => expect(view).toBeTruthy());\n"),
        ("jsx", "const view = <div />; test('widget works', () => expect(view).toBeTruthy());\n"),
        ("ts", "const value: string = 'ok'; test('widget works', () => expect(value).toBeTruthy());\n"),
        ("tsx", "const view: JSX.Element = <div />; test('widget works', () => expect(view).toBeTruthy());\n"),
    ],
)
def test_playwright_selects_parser_for_js_jsx_ts_tsx(
    tmp_path: Path, suffix: str, source: str
) -> None:
    root, _commit = _repository(
        tmp_path,
        config=(
            "import { defineConfig } from '@playwright/test';\n"
            "export default defineConfig({ timeout: 1000 });\n"
        ),
    )
    old = root / "tests/widget.spec.ts"
    spec = old.with_suffix(f".{suffix}")
    old.rename(spec)
    spec.write_text(
        "import { expect, test } from '@playwright/test';\n" + source,
        encoding="utf-8",
    )
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", "parser-specific source")
    playwright_validator_config_digest(
        root, _git(root, "rev-parse", "HEAD"),
        (PurePosixPath(f"tests/widget.spec.{suffix}"),),
    )


def test_toolchain_identity_streams_role_files_without_read_bytes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runner = _fake_playwright(tmp_path)
    manifest = _toolchain_manifest(tmp_path / "toolchain", Path(sys.executable), runner)
    dependency = tmp_path / "toolchain/node_modules/large.bin"
    dependency.write_bytes(b"x" * 1024 * 1024)
    original = Path.read_bytes

    def guarded_read_bytes(path: Path) -> bytes:
        if path == dependency:
            raise AssertionError("toolchain role files must be streamed")
        return original(path)

    monkeypatch.setattr(Path, "read_bytes", guarded_read_bytes)
    assert _toolchain_manifest_identity(manifest)


def _run(
    root: Path,
    base: str,
    head: str,
    fake: Path | tuple[str, ...],
    timeout: int = 2,
    code_under_test_paths: tuple[PurePosixPath, ...] = (),
):
    command = fake if isinstance(fake, tuple) else (sys.executable, str(fake))
    entrypoint = Path(command[1])
    with tempfile.TemporaryDirectory(
        prefix="pdd-test-playwright-toolchain-",
        dir=_playwright_host_temp_parent(),
    ) as directory:
        manifest_root = Path(directory)
        manifest_entrypoint = entrypoint
        if entrypoint.is_relative_to(root):
            manifest_entrypoint = manifest_root / "protected-playwright-tool"
            manifest_entrypoint.write_bytes(b"protected")
        manifest = _toolchain_manifest(
            manifest_root, Path(command[0]), manifest_entrypoint
        )
        if not entrypoint.is_relative_to(root):
            command = (command[0], str(_manifest_entrypoint(manifest)))
        paths = (PurePosixPath("tests/widget.spec.ts"),)
        try:
            config_digest = playwright_validator_config_digest(
                root, base, paths, code_under_test_paths
            )
        except ValueError:
            config_digest = "invalid-playwright-config"
        obligation = VerificationObligation(
            "playwright", "test", "playwright", config_digest, ("REQ-1",), paths,
            code_under_test_paths=code_under_test_paths,
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
                playwright_command=command,
                playwright_toolchain_manifest=manifest,
            ),
        )


def test_synthetic_playwright_supervisor_reads_dependency_bound_entrypoint(
    tmp_path: Path,
) -> None:
    """Use the host fake runner after production relocates it into a mount."""
    root, commit = _repository(tmp_path)
    _envelope, executions = _run(root, commit, commit, _fake_playwright(tmp_path))

    assert executions[0].outcome is EvidenceOutcome.PASS


@pytest.mark.parametrize(
    ("candidate_mode", "expected"),
    [("candidate-pass", EvidenceOutcome.PASS), ("fail", EvidenceOutcome.FAIL)],
)
def test_playwright_candidate_product_changes_execute_instead_of_quarantine(
    tmp_path: Path, candidate_mode: str, expected: EvidenceOutcome
) -> None:
    root, base = _repository(tmp_path)
    (root / "source.ts").write_text(candidate_mode, encoding="utf-8")
    _git(root, "add", "source.ts")
    _git(root, "commit", "-q", "-m", "candidate product")
    _envelope, executions = _run(
        root,
        base,
        _git(root, "rev-parse", "HEAD"),
        _fake_playwright(tmp_path),
        code_under_test_paths=(PurePosixPath("source.ts"),),
    )
    assert executions[0].outcome is expected


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


@pytest.mark.parametrize("name", ["DATABASE_URL", "SSH_AUTH_SOCK", "KUBECONFIG"])
def test_playwright_environment_drops_ambient_credentials_and_capabilities(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, name: str
) -> None:
    monkeypatch.setenv(name, "candidate-readable")
    assert name not in _playwright_environment(tmp_path, None)


@pytest.mark.parametrize(
    "payload", ["[]", "null", "1", '"value"', '{"suites":[{"specs":null}]}']
)
def test_playwright_malformed_json_shapes_fail_closed(
    tmp_path: Path, payload: str
) -> None:
    outcome, _detail, identities = _playwright_result(
        tmp_path, payload, 0, None
    )
    assert outcome is EvidenceOutcome.COLLECTION_ERROR
    assert identities == ()


@pytest.mark.parametrize(
    ("callbacks", "reason"),
    [
        ((
            "const bad = valid('bad'); bad.titlePath = () => { throw new Error('bad'); };\n"
            "try { reporter.onBegin({ allTests: () => [valid(), bad] }); } catch {}\n"
            "reporter.onEnd({ status: 'passed' });"
        ), "title_path_call"),
        ((
            "try { reporter.onBegin({ allTests: () => [valid(), valid()] }); } catch {}\n"
            "reporter.onEnd({ status: 'passed' });"
        ), "duplicate_identity"),
        ((
            "try { reporter.onBegin({ allTests: () => { throw new Error('bad'); } }); } catch {}\n"
            "reporter.onEnd({ status: 'passed' });"
        ), "suite_all_tests_call"),
        ((
            "const suite = {};\n"
            "Object.defineProperty(suite, 'allTests', { get: () => { throw new Error('bad'); } });\n"
            "reporter.onBegin(suite); reporter.onEnd({ status: 'passed' });"
        ), "suite_all_tests_access"),
        ((
            "reporter.onBegin({ allTests: () => [valid()] });\n"
            "try { reporter.onTestEnd(valid(), null); } catch {}\n"
            "reporter.onEnd({ status: 'passed' });"
        ), "invalid_test_result"),
        ((
            "const bad = valid('bad');\n"
            "Object.defineProperty(bad, 'parent', { get: () => { throw new Error('bad'); } });\n"
            "reporter.onBegin({ allTests: () => [valid(), bad] });\n"
            "reporter.onEnd({ status: 'passed' });"
        ), "project_access"),
        ((
            "const bad = valid('bad'); bad.parent.project = () => { throw new Error('bad'); };\n"
            "reporter.onBegin({ allTests: () => [valid(), bad] });\n"
            "reporter.onEnd({ status: 'passed' });"
        ), "project_call"),
        ((
            "const bad = valid('bad');\n"
            "Object.defineProperty(bad, 'location', { get: () => { throw new Error('bad'); } });\n"
            "reporter.onBegin({ allTests: () => [valid(), bad] });\n"
            "reporter.onEnd({ status: 'passed' });"
        ), "location_access"),
        ((
            "path.relative = () => { throw new Error('bad'); };\n"
            "reporter.onBegin({ allTests: () => [valid()] });\n"
            "reporter.onEnd({ status: 'passed' });"
        ), "path_operation"),
    ],
)
def test_playwright_reporter_latches_swallowed_callback_errors(
    tmp_path: Path, callbacks: str, reason: str,
) -> None:
    """A swallowed callback failure must replace every partial observation."""
    receipt = _reporter_callback_receipt(tmp_path, callbacks)

    assert receipt == {
        "pdd_playwright_reporter": 1,
        "reporter_error": "invalid_reporter_state",
        "reason": reason,
    }
    outcome, _detail, identities = _playwright_result(
        tmp_path, json.dumps(receipt), 0, None, collection=True,
    )
    assert outcome is EvidenceOutcome.COLLECTION_ERROR
    assert not identities


def test_playwright_reporter_on_end_uses_minimal_error_fallback(
    tmp_path: Path,
) -> None:
    """Serialization preparation failure emits only the fixed error receipt."""
    receipt = _reporter_callback_receipt(
        tmp_path,
        "reporter.onBegin({ allTests: () => [valid()] });\n"
        "reporter.tests = { [Symbol.iterator]: () => { throw new Error('bad'); } };\n"
        "try { reporter.onEnd({ status: 'passed' }); } catch {}",
    )

    assert receipt == {
        "pdd_playwright_reporter": 1,
        "reporter_error": "invalid_reporter_state",
        "reason": "serialization_failure",
    }


def test_playwright_reporter_defers_well_formed_framework_error_to_run_status(
    tmp_path: Path,
) -> None:
    """A normal onError callback is interpreted with Playwright's final status."""
    receipt = _reporter_callback_receipt(
        tmp_path,
        "reporter.onError({ message: 'framework detail' });\n"
        "reporter.onBegin({ allTests: () => [valid()] });\n"
        "reporter.onEnd({ status: 'passed' });",
    )

    assert receipt == {
        "pdd_playwright_reporter": 1,
        "tests": [{"identity": IDENTITY, "status": "collected"}],
    }


@pytest.mark.parametrize(
    ("error", "status", "reason"),
    [
        ("null", "passed", "invalid_framework_error"),
        ("{ message: 1 }", "passed", "invalid_framework_error"),
        ("{ message: 'failed' }", "failed", "framework_error"),
        ("{ message: 'failed' }", "candidate", "invalid_run_result"),
    ],
)
def test_playwright_reporter_framework_error_status_contract(
    tmp_path: Path, error: str, status: str, reason: str,
) -> None:
    receipt = _reporter_callback_receipt(
        tmp_path,
        f"reporter.onError({error});\n"
        "reporter.onBegin({ allTests: () => [valid()] });\n"
        f"reporter.onEnd({{ status: '{status}' }});",
    )

    assert receipt == {
        "pdd_playwright_reporter": 1,
        "reporter_error": "invalid_reporter_state",
        "reason": reason,
    }


@pytest.mark.parametrize("reason", REPORTER_ERROR_REASONS)
def test_playwright_reporter_error_reason_is_closed_and_bounded(
    tmp_path: Path, reason: str,
) -> None:
    receipt = {
        "pdd_playwright_reporter": 1,
        "reporter_error": "invalid_reporter_state",
        "reason": reason,
    }

    outcome, detail, identities = _playwright_result(
        tmp_path, json.dumps(receipt), 0, None, collection=True,
    )

    assert outcome is EvidenceOutcome.COLLECTION_ERROR
    assert detail.endswith(f" ({reason})")
    assert not identities


@pytest.mark.parametrize(
    "receipt",
    [
        {
            "pdd_playwright_reporter": 1,
            "reporter_error": "invalid_reporter_state",
            "reason": "invalid_title_path",
            "tests": [{"identity": IDENTITY, "status": "collected"}],
        },
        {
            "pdd_playwright_reporter": True,
            "reporter_error": "invalid_reporter_state",
            "reason": "invalid_title_path",
        },
        {
            "pdd_playwright_reporter": 1,
            "reporter_error": "candidate title",
            "reason": "invalid_title_path",
        },
        {
            "pdd_playwright_reporter": 1,
            "reporter_error": "invalid_reporter_state",
            "reason": "invalid_title_path",
            "extra": False,
        },
        {"reporter_error": "invalid_reporter_state"},
        {
            "pdd_playwright_reporter": 1,
            "reporter_error": "invalid_reporter_state",
        },
        {
            "pdd_playwright_reporter": 1,
            "reporter_error": "invalid_reporter_state",
            "reason": "candidate-derived-value",
        },
        {
            "pdd_playwright_reporter": 1,
            "reporter_error": "invalid_reporter_state",
            "reason": True,
        },
    ],
)
def test_playwright_reporter_error_receipt_schema_is_strict(
    tmp_path: Path, receipt: dict,
) -> None:
    outcome, _detail, identities = _playwright_result(
        tmp_path, json.dumps(receipt), 0, None, collection=True,
    )

    assert outcome is EvidenceOutcome.COLLECTION_ERROR
    assert not identities


@pytest.mark.parametrize(
    "payload",
    [
        {
            "pdd_playwright_reporter": 1,
            "tests": [{"identity": IDENTITY, "status": "collected"}],
            "extra": None,
        },
        {
            "pdd_playwright_reporter": 1,
            "tests": [{
                "identity": IDENTITY, "status": "collected", "extra": None,
            }],
        },
        {
            "pdd_playwright_reporter": 1,
            "tests": [{"identity": IDENTITY, "status": True}],
        },
    ],
)
def test_playwright_success_receipt_schema_rejects_extras_and_bool_types(
    tmp_path: Path, payload: dict,
) -> None:
    outcome, _detail, identities = _playwright_result(
        tmp_path, json.dumps(payload), 0, None, collection=True,
    )

    assert outcome is EvidenceOutcome.COLLECTION_ERROR
    assert not identities


@pytest.mark.parametrize(
    "config",
    [
        "const key='grep'; export default { [key]: /widget/ };\n",
        "const controls={ ['webServer']: {command:'./server.sh'} }; export default {...controls};\n",
    ],
)
def test_playwright_rejects_non_declarative_config_shapes(
    tmp_path: Path, config: str
) -> None:
    root, commit = _repository(tmp_path, config=config)
    with pytest.raises(ValueError, match="configuration"):
        playwright_validator_config_digest(
            root, commit, (PurePosixPath("tests/widget.spec.ts"),)
        )


def test_playwright_rejects_semantic_config_indirection(tmp_path: Path) -> None:
    root, commit = _repository(
        tmp_path,
        config="export default Object.fromEntries([['global' + 'Setup', './setup.ts']]);\n",
    )
    with pytest.raises(ValueError, match="declarative"):
        playwright_validator_config_digest(
            root, commit, (PurePosixPath("tests/widget.spec.ts"),)
        )


@pytest.mark.parametrize(
    "config",
    [
        "export default { global\\u0053etup: './setup.ts' };\n",
        "export default { ['globalSetup']: './setup.ts' };\n",
        "export default { reporter() { return './reporter.ts'; } };\n",
        "export default { timeout: (() => 1000)() };\n",
    ],
)
def test_playwright_config_uses_enumerated_static_syntax(
    tmp_path: Path, config: str
) -> None:
    root, commit = _repository(tmp_path, config=config)
    with pytest.raises(ValueError, match="configuration"):
        playwright_validator_config_digest(
            root, commit, (PurePosixPath("tests/widget.spec.ts"),)
        )


@pytest.mark.parametrize(
    "source",
    [
        "const dependency='helper'; await import(dependency);\n",
        "const load = require; load('helper');\n",
    ],
)
def test_playwright_rejects_dynamic_or_aliased_module_loading(
    tmp_path: Path, source: str
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(source, encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "dynamic loader")
    commit = _git(root, "rev-parse", "HEAD")
    with pytest.raises(ValueError, match="module loading|capability schema"):
        playwright_validator_config_digest(
            root, commit, (PurePosixPath("tests/widget.spec.ts"),)
        )


@pytest.mark.parametrize(
    "source",
    [
        "const path = './helper'; require(path);\n",
        "const path = './helper'; module.require(path);\n",
        "const load = globalThis['require']; load('./helper');\n",
    ],
)
def test_playwright_rejects_all_non_literal_module_loading(
    tmp_path: Path, source: str
) -> None:
    root, commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(source, encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "dynamic loader")
    commit = _git(root, "rev-parse", "HEAD")
    with pytest.raises(ValueError, match="module loading|capability schema"):
        playwright_validator_config_digest(
            root, commit, (PurePosixPath("tests/widget.spec.ts"),)
        )


@pytest.mark.parametrize(
    "source",
    [
        "const path = './helper'; module['require'](path);\n",
        "const path = './helper'; require /*comment*/ (path);\n",
        "const load = module.createRequire(import.meta.url); load('./helper');\n",
        "Function('return require')()('./helper');\n",
    ],
)
def test_playwright_rejects_semantic_loader_variants(
    tmp_path: Path, source: str
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(source, encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "semantic loader")
    with pytest.raises(ValueError, match="module loading|capability schema"):
        playwright_validator_config_digest(
            root,
            _git(root, "rev-parse", "HEAD"),
            (PurePosixPath("tests/widget.spec.ts"),),
        )


@pytest.mark.parametrize(
    "source",
    [
        "const matcher = 'toHave' + 'Screenshot'; expect(page)[matcher]('widget.png');\n",
        "process.getBuiltinModule('fs').readFileSync('oracle.json');\n",
        "process.getBuiltinModule('child_process').execFileSync('./helper');\n",
    ],
)
def test_playwright_rejects_reflective_runtime_resource_access(
    tmp_path: Path, source: str
) -> None:
    root, commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(source, encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "reflective resource access")
    commit = _git(root, "rev-parse", "HEAD")
    with pytest.raises(ValueError, match="runtime resource"):
        playwright_validator_config_digest(
            root, commit, (PurePosixPath("tests/widget.spec.ts"),)
        )


@pytest.mark.parametrize(
    "source",
    [
        "import { execFileSync } from 'node:child_process'; execFileSync('./oracle');\n",
        "const assertion = expect(page); const matcher = 'toHave' + 'Screenshot'; assertion[matcher]('widget.png');\n",
        "import * as filesystem from 'node:fs'; filesystem.readFileSync('oracle');\n",
    ],
)
def test_playwright_rejects_unbound_runtime_capabilities(
    tmp_path: Path, source: str
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(source, encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "runtime capability")
    with pytest.raises(ValueError, match="runtime resource"):
        playwright_validator_config_digest(
            root,
            _git(root, "rev-parse", "HEAD"),
            (PurePosixPath("tests/widget.spec.ts"),),
        )


def test_playwright_snapshot_oracle_is_bound_to_validator_digest(tmp_path: Path) -> None:
    root, base = _repository(tmp_path)
    snapshot = root / "tests/widget.spec.ts-snapshots/widget-linux.png"
    snapshot.parent.mkdir()
    snapshot.write_bytes(b"base")
    spec = root / "tests/widget.spec.ts"
    spec.write_text(
        spec.read_text(encoding="utf-8")
        + "test('visual', async ({page}) => expect(page).toHaveScreenshot('widget.png'));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "snapshot oracle")
    base = _git(root, "rev-parse", "HEAD")
    before = playwright_validator_config_digest(root, base, (PurePosixPath("tests/widget.spec.ts"),))
    snapshot.write_bytes(b"candidate")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change oracle")
    after = playwright_validator_config_digest(
        root, _git(root, "rev-parse", "HEAD"), (PurePosixPath("tests/widget.spec.ts"),)
    )
    assert after != before


def test_playwright_decoded_config_keys_bind_executable_references(tmp_path: Path) -> None:
    root, _commit = _repository(
        tmp_path,
        config='export default { "global\\u0053etup": "./setup.ts" };\n',
    )
    (root / "setup.ts").write_text("export default async () => {};\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add decoded setup")
    base = _git(root, "rev-parse", "HEAD")
    paths = (PurePosixPath("tests/widget.spec.ts"),)
    before = playwright_validator_config_digest(root, base, paths)
    (root / "setup.ts").write_text("export default async () => { throw 1 };\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change decoded setup")
    assert playwright_validator_config_digest(
        root, _git(root, "rev-parse", "HEAD"), paths
    ) != before


def test_playwright_rejects_decoded_unsupported_resource_key(tmp_path: Path) -> None:
    root, commit = _repository(
        tmp_path,
        config='export default { "storage\\u0053tate": "./auth.json" };\n',
    )
    with pytest.raises(ValueError, match="unsupported"):
        playwright_validator_config_digest(
            root, commit, (PurePosixPath("tests/widget.spec.ts"),)
        )


@pytest.mark.parametrize(
    "statement",
    [
        'export { oracle } from "./helper";\n',
        'export * from "./helper";\n',
        'export type { Oracle } from "./helper";\n',
    ],
)
def test_playwright_reexports_are_in_the_support_closure(
    tmp_path: Path, statement: str
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(
        'import "./barrel";\n', encoding="utf-8"
    )
    (root / "tests/barrel.ts").write_text(statement, encoding="utf-8")
    (root / "tests/helper.ts").write_text("export const oracle = 1;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add reexport")
    base = _git(root, "rev-parse", "HEAD")
    paths = (PurePosixPath("tests/widget.spec.ts"),)
    before = playwright_validator_config_digest(root, base, paths)
    (root / "tests/helper.ts").write_text("export const oracle = 2;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change reexport target")
    assert playwright_validator_config_digest(
        root, _git(root, "rev-parse", "HEAD"), paths
    ) != before


def test_playwright_text_snapshot_oracle_is_bound(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    snapshot = root / "tests/widget.spec.ts-snapshots/oracle.txt"
    snapshot.parent.mkdir()
    snapshot.write_text("base", encoding="utf-8")
    (root / "tests/widget.spec.ts").write_text(
        "import { expect, test } from '@playwright/test';\n"
        "test('snapshot', () => expect('value').toMatchSnapshot('oracle.txt'));\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add text snapshot")
    base = _git(root, "rev-parse", "HEAD")
    paths = (PurePosixPath("tests/widget.spec.ts"),)
    before = playwright_validator_config_digest(root, base, paths)
    snapshot.write_text("candidate", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change text snapshot")
    assert playwright_validator_config_digest(
        root, _git(root, "rev-parse", "HEAD"), paths
    ) != before


def test_playwright_ast_capability_allowlist_rejects_reflection(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(
        'Reflect.get(process, "getBuiltin" + "Module")'
        '.call(process, "no" + "de:fs");\n',
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "reflective capability")
    with pytest.raises(ValueError, match="runtime capability"):
        playwright_validator_config_digest(
            root,
            _git(root, "rev-parse", "HEAD"),
            (PurePosixPath("tests/widget.spec.ts"),),
        )


def test_playwright_accepts_cjs_config_and_ordinary_typescript(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "playwright.config.ts").unlink()
    (root / "playwright.config.cjs").write_text(
        'module.exports = { globalSetup: "./setup.ts", timeout: 1000 };\n',
        encoding="utf-8",
    )
    (root / "setup.ts").write_text("export default async () => {};\n", encoding="utf-8")
    (root / "tests/widget.spec.ts").write_text(
        "import { expect, test } from '@playwright/test';\n"
        "type Values = string[]; const [first] = ['ok'];\n"
        "test(`ordinary ${first}`, () => expect(/o[k]/.test(first)).toBeTruthy());\n",
        encoding="utf-8",
    )
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", "ordinary cjs and typescript")
    playwright_validator_config_digest(
        root,
        _git(root, "rev-parse", "HEAD"),
        (PurePosixPath("tests/widget.spec.ts"),),
    )


def test_toolchain_manifest_requires_complete_typed_external_roles(tmp_path: Path) -> None:
    toolchain = tmp_path / "toolchain"
    toolchain.mkdir()
    (toolchain / "node").write_bytes(b"node")
    manifest = toolchain / "manifest.json"
    manifest.write_text(
        '{"version":1,"files":["node","missing-cli.js"]}', encoding="utf-8"
    )
    with pytest.raises(ValueError, match="roles"):
        _toolchain_manifest_identity(manifest)


def test_toolchain_manifest_requires_nonempty_native_runtime(tmp_path: Path) -> None:
    launcher = Path(sys.executable)
    manifest = _toolchain_manifest(tmp_path / "toolchain", launcher, launcher)
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["roles"]["native_runtime"] = []
    manifest.write_text(json.dumps(payload), encoding="utf-8")

    with pytest.raises(ValueError, match="incomplete"):
        _toolchain_manifest_identity(manifest)


def test_toolchain_manifest_identity_binds_native_runtime_content(tmp_path: Path) -> None:
    launcher = Path(sys.executable)
    manifest = _toolchain_manifest(tmp_path / "toolchain", launcher, launcher)
    native = tmp_path / "toolchain/native.so"
    native.write_bytes(b"base-native")
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["roles"]["native_runtime"] = [str(native.resolve())]
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    before = _toolchain_manifest_identity(manifest)

    native.write_bytes(b"changed-native")

    assert _toolchain_manifest_identity(manifest) != before


def test_directory_identity_binds_symlink_topology(tmp_path: Path) -> None:
    target = tmp_path / "package-a"
    target.mkdir()
    (target / "index.js").write_text("module.exports = 1", encoding="utf-8")
    dependencies = tmp_path / "node_modules"
    dependencies.mkdir()
    (dependencies / "helper").symlink_to(target, target_is_directory=True)
    before = _directory_identity(dependencies)
    (dependencies / "helper").unlink()
    (dependencies / "helper").symlink_to(tmp_path / "missing", target_is_directory=True)
    assert _directory_identity(dependencies) != before


def test_toolchain_manifest_rejects_absolute_symlinks(
    tmp_path: Path,
) -> None:
    toolchain = tmp_path / "toolchain"
    target = tmp_path / "packages" / "helper"
    target.mkdir(parents=True)
    (target / "index.js").write_text("module.exports = 1", encoding="utf-8")
    toolchain.mkdir()
    (toolchain / "node").write_bytes(b"node")
    (toolchain / "cli.js").write_text("require('./modules/helper')", encoding="utf-8")
    (toolchain / "modules").mkdir()
    (toolchain / "modules/helper").symlink_to(target, target_is_directory=True)
    manifest = tmp_path / "playwright-toolchain.json"
    (toolchain / "browsers").mkdir()
    (toolchain / "package-lock.json").write_text("{}", encoding="utf-8")
    manifest.write_text(json.dumps({
        "version": 3,
        "roles": {
            "launcher": str((toolchain / "node").resolve()),
            "entrypoint": str((toolchain / "cli.js").resolve()),
            "dependencies": str((toolchain / "modules").resolve()),
            "browser_runtime": str((toolchain / "browsers").resolve()),
            "native_runtime": [str((toolchain / "node").resolve())],
            "lockfile": str((toolchain / "package-lock.json").resolve()),
        },
    }), encoding="utf-8")
    with pytest.raises(ValueError, match="absolute symlink"):
        _toolchain_manifest_identity(manifest)


def test_toolchain_manifest_identity_is_relocation_stable_with_relative_symlink(
    tmp_path: Path,
) -> None:
    first = tmp_path / "first"
    second = tmp_path / "second"
    for root in (first, second):
        toolchain = root / "toolchain"
        (toolchain / "modules" / "helper").mkdir(parents=True)
        (toolchain / "node").write_bytes(b"node")
        (toolchain / "cli.js").write_text("require('./modules/link')", encoding="utf-8")
        (toolchain / "modules" / "helper" / "index.js").write_text(
            "module.exports = 1", encoding="utf-8"
        )
        (toolchain / "modules" / "link").symlink_to("helper", target_is_directory=True)
        (toolchain / "browsers").mkdir()
        (toolchain / "package-lock.json").write_text("{}", encoding="utf-8")
        (root / "manifest.json").write_text(json.dumps({
            "version": 3,
            "roles": {
                "launcher": str((toolchain / "node").resolve()),
                "entrypoint": str((toolchain / "cli.js").resolve()),
                "dependencies": str((toolchain / "modules").resolve()),
                "browser_runtime": str((toolchain / "browsers").resolve()),
                "native_runtime": [str((toolchain / "node").resolve())],
                "lockfile": str((toolchain / "package-lock.json").resolve()),
            },
        }), encoding="utf-8")
    assert _toolchain_manifest_identity(first / "manifest.json") == _toolchain_manifest_identity(
        second / "manifest.json"
    )


def test_playwright_production_run_requires_and_rechecks_toolchain_manifest(
    tmp_path: Path, trusted_toolchain_dir: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, commit = _repository(tmp_path)
    runner = _fake_playwright(tmp_path)
    manifest = _toolchain_manifest(
        trusted_toolchain_dir / "protected-toolchain", Path(sys.executable), runner
    )
    installed = _manifest_entrypoint(manifest)
    original_supervised = runner_module.run_supervised

    def mutate_after_playwright(*args, **kwargs):
        result = original_supervised(*args, **kwargs)
        installed.write_text(installed.read_text(encoding="utf-8") + "# changed\n")
        return result

    monkeypatch.setattr(runner_module, "run_supervised", mutate_after_playwright)
    paths = (PurePosixPath("tests/widget.spec.ts"),)
    obligation = VerificationObligation(
        "playwright", "test", "playwright",
        playwright_validator_config_digest(root, commit, paths), ("REQ-1",), paths,
    )
    profile = VerificationProfile(UNIT, (obligation,), ("REQ-1",), "profile-v1")
    _envelope, executions = run_profile(
        root, profile, RunBinding("snapshot-v1", commit, commit),
        AttestationIssue(
            AttestationSigner("trusted-ci", b"p" * 32), "id", "nonce",
            datetime(2026, 7, 10, tzinfo=timezone.utc),
        ),
        config=RunnerConfig(
            timeout_seconds=2,
            playwright_command=(sys.executable, str(installed)),
            playwright_toolchain_manifest=manifest,
        ),
    )
    assert executions[0].outcome is EvidenceOutcome.COLLECTION_ERROR
    assert "toolchain" in executions[0].detail.lower()


def test_playwright_rechecks_one_identity_after_the_complete_protocol(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, commit = _repository(tmp_path)
    runner = _fake_playwright(tmp_path)
    original = __import__("pdd.sync_core.runner", fromlist=["_run_playwright"])._run_playwright
    calls = 0

    def mutate_after_final_run(*args, **kwargs):
        nonlocal calls
        result = original(*args, **kwargs)
        calls += 1
        if calls == 3:
            manifest = args[3].playwright_toolchain_manifest
            assert manifest is not None
            installed = _manifest_entrypoint(manifest)
            installed.write_text(
                installed.read_text(encoding="utf-8") + "# post-run drift\n"
            )
        return result

    monkeypatch.setattr("pdd.sync_core.runner._run_playwright", mutate_after_final_run)
    _envelope, executions = _run(root, commit, commit, runner)
    assert calls == 3
    assert executions[0].outcome is EvidenceOutcome.COLLECTION_ERROR
    assert "toolchain" in executions[0].detail.lower()


@pytest.mark.parametrize("launcher_kind", ["missing", "directory", "non_executable"])
def test_playwright_launch_failures_are_normalized(
    tmp_path: Path, launcher_kind: str
) -> None:
    root, commit = _repository(tmp_path)
    launcher = tmp_path / launcher_kind
    if launcher_kind == "directory":
        launcher.mkdir()
    elif launcher_kind == "non_executable":
        launcher.write_text("#!/bin/sh\n", encoding="utf-8")
    entrypoint = _fake_playwright(tmp_path)
    _envelope, executions = _run(
        root, commit, commit, (str(launcher), str(entrypoint))
    )
    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert any(token in executions[0].detail.lower() for token in ("executable", "does not exist", "file"))


@pytest.mark.parametrize("option", ["--require=helper", "--import=helper", "--loader=helper"])
def test_playwright_command_rejects_candidate_resolving_prefix_options(
    tmp_path: Path, option: str
) -> None:
    executable = tmp_path.parent / "node"
    entrypoint = tmp_path.parent / "playwright-cli.js"
    executable.write_bytes(b"node")
    entrypoint.write_bytes(b"cli")
    error = _playwright_command_error(
        tmp_path, (str(executable), option, str(entrypoint))
    )
    assert error is not None


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


def test_playwright_ignored_bare_package_mutation_cannot_change_evidence(
    tmp_path: Path,
) -> None:
    root, commit = _repository(tmp_path)
    (root / ".gitignore").write_text("node_modules/\n", encoding="utf-8")
    (root / "tests/widget.spec.ts").write_text(
        "import { expect, test } from '@playwright/test';\n"
        "import { expected } from 'helper';\n"
        "test('widget works', async () => expect(expected).toBeTruthy());\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "ignore bare package dependencies")
    commit = _git(root, "rev-parse", "HEAD")
    helper = root / "node_modules" / "helper" / "index.js"
    helper.parent.mkdir(parents=True)
    helper.write_text("exports.expected = true;\n", encoding="utf-8")

    _envelope, first = _run(root, commit, commit, _fake_playwright(tmp_path))
    helper.write_text("exports.expected = false;\n", encoding="utf-8")
    _envelope, second = _run(root, commit, commit, _fake_playwright(tmp_path))

    assert first[0].outcome is EvidenceOutcome.ERROR
    assert first[0].detail == second[0].detail
    assert first[0].command_digest == second[0].command_digest
    assert "bare package imports" in first[0].detail


def test_playwright_external_node_modules_environment_is_available(
    tmp_path: Path,
) -> None:
    root, commit = _repository(tmp_path)
    protected = tmp_path / "protected"
    package = protected / "node_modules" / "@playwright" / "test"
    package.mkdir(parents=True)
    (package / "index.js").write_text("module.exports = {};\n", encoding="utf-8")
    runner = package / "cli.js"
    runner.write_text(_fake_node_playwright(tmp_path).read_text(encoding="utf-8"))

    node = shutil.which("node")
    assert node is not None

    _envelope, executions = _run(root, commit, commit, (node, str(runner)))

    assert executions[0].outcome is EvidenceOutcome.PASS


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

    with pytest.raises(ValueError, match="candidate node_modules"):
        _run_default_playwright(root, commit, commit)


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
    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_playwright_removed_protected_test_cannot_pass(tmp_path: Path) -> None:
    root, base = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text("// removed\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "remove protected test")
    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_playwright(tmp_path)
    )
    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


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


def test_playwright_parent_directory_import_helper_mutation_cannot_pass(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "shared").mkdir()
    (root / "shared/helper.ts").write_text("export const expected = true;\n", encoding="utf-8")
    (root / "tests/widget.spec.ts").write_text(
        "import { expect, test } from '@playwright/test';\n"
        "import { expected } from '../shared/helper';\n"
        "test('widget works', async () => expect(expected).toBeTruthy());\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add parent import helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "shared/helper.ts").write_text("export const expected = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate parent import helper")

    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_playwright(tmp_path)
    )

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_playwright_parent_directory_side_effect_import_mutation_cannot_pass(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "shared").mkdir()
    (root / "shared/setup.ts").write_text("export const setupExpected = true;\n", encoding="utf-8")
    (root / "tests/widget.spec.ts").write_text(
        "import { expect, test } from '@playwright/test';\n"
        "import '../shared/setup';\n"
        "test('widget works', async () => expect(globalThis.expected).toBeTruthy());\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add parent side effect helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "shared/setup.ts").write_text("globalThis.expected = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate parent side effect helper")

    _envelope, executions = _run(
        root, base, _git(root, "rev-parse", "HEAD"), _fake_playwright(tmp_path)
    )

    assert executions[0].outcome in {EvidenceOutcome.ERROR, EvidenceOutcome.QUARANTINED}


def test_playwright_parent_directory_imports_change_validator_digest(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    paths = (PurePosixPath("tests/widget.spec.ts"),)
    (root / "shared/helpers").mkdir(parents=True)
    (root / "shared/helpers/index.ts").write_text(
        "export const expected = true;\n", encoding="utf-8"
    )
    (root / "shared/setup.ts").write_text("export const setupExpected = true;\n", encoding="utf-8")
    (root / "tests/widget.spec.ts").write_text(
        "import { expect, test } from '@playwright/test';\n"
        "import { expected } from '../shared/helpers';\n"
        "import '../shared/setup';\n"
        "test('widget works', async () => expect(expected).toBeTruthy());\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add parent import helpers")
    base = _git(root, "rev-parse", "HEAD")
    base_digest = playwright_validator_config_digest(root, base, paths)

    (root / "shared/helpers/index.ts").write_text(
        "export const expected = false;\n", encoding="utf-8"
    )
    (root / "shared/setup.ts").write_text("export const setupExpected = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate parent import helpers")
    head_digest = playwright_validator_config_digest(
        root, _git(root, "rev-parse", "HEAD"), paths
    )

    assert head_digest != base_digest


def test_playwright_config_reference_index_candidate_changes_validator_digest(tmp_path: Path) -> None:
    config = "import './support/setup';\nexport default {};\n"
    root, _commit = _repository(tmp_path, config=config)
    paths = (PurePosixPath("tests/widget.spec.ts"),)
    (root / "support/setup").mkdir(parents=True)
    (root / "support/setup/index.ts").write_text(
        "export const expected = true;\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add extensionless setup index")
    base = _git(root, "rev-parse", "HEAD")
    base_digest = playwright_validator_config_digest(root, base, paths)

    (root / "support/setup/index.ts").write_text(
        "export const expected = false;\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate extensionless setup index")
    head_digest = playwright_validator_config_digest(
        root, _git(root, "rev-parse", "HEAD"), paths
    )

    assert head_digest != base_digest


def test_playwright_repository_escape_import_is_not_bound(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    with pytest.raises(ValueError, match="escapes repository"):
        _local_javascript_imports(
            root,
            commit,
            PurePosixPath("tests/widget.spec.ts"),
            b"import '../../outside.js';\n",
        )


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
    assert "candidate checkout" in executions[0].detail or "entrypoint role" in executions[0].detail


def test_pathless_playwright_script_operand_is_not_resolved_from_candidate(
    tmp_path: Path,
) -> None:
    root, base = _repository(tmp_path)
    (root / "fake_playwright.py").write_text(
        _fake_playwright(tmp_path).read_text(encoding="utf-8"), encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add pathless candidate Playwright command")
    base = _git(root, "rev-parse", "HEAD")
    (root / "fake_playwright.py").write_text(
        _fake_playwright(tmp_path).read_text(encoding="utf-8") + "\n# changed\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate pathless Playwright command")
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
            playwright_command=(sys.executable, "fake_playwright.py"),
        ),
    )

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "pathless" in executions[0].detail or "manifest" in executions[0].detail


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


def test_playwright_rejects_identifier_executable_config_value(
    tmp_path: Path,
) -> None:
    root, commit = _repository(
        tmp_path,
        config="const setup = './setup.ts';\nexport default { globalSetup: setup };\n",
    )
    (root / "setup.ts").write_text(
        "export default async function setup() {}\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add aliased setup control")
    commit = _git(root, "rev-parse", "HEAD")

    _envelope, executions = _run(root, commit, commit, _fake_playwright(tmp_path))

    assert executions[0].outcome is EvidenceOutcome.ERROR


def test_playwright_each_protocol_phase_uses_fresh_immutable_materialization(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, commit = _repository(tmp_path)
    phase_roots: list[Path] = []

    def supervised(command, *, cwd, writable_roots, **_kwargs):
        phase_roots.append(cwd)
        assert cwd not in writable_roots
        assert cwd / ".git" not in writable_roots
        _write_framework_observation(_kwargs, {"tests": [{"identity": IDENTITY, "status": "passed"}]})
        return _trusted_completed(command, 0), False

    monkeypatch.setattr(runner_module, "run_supervised", supervised)
    _envelope, executions = _run(root, commit, commit, _fake_playwright(tmp_path))

    assert executions[0].outcome is EvidenceOutcome.PASS
    assert len(phase_roots) == 3
    assert len({path.resolve() for path in phase_roots}) == 3


@pytest.mark.parametrize("mutation", ["commit", "ignored"])
def test_playwright_detects_clean_status_and_ignored_phase_writes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mutation: str
) -> None:
    root, commit = _repository(tmp_path)
    if mutation == "ignored":
        (root / ".gitignore").write_text("candidate-cache/\n", encoding="utf-8")
        _git(root, "add", ".gitignore")
        _git(root, "commit", "-q", "-m", "ignore candidate cache")
        commit = _git(root, "rev-parse", "HEAD")
    calls = 0

    def supervised(command, *, cwd, **_kwargs):
        nonlocal calls
        calls += 1
        if calls == 2:
            if mutation == "commit":
                (cwd / "tests/widget.spec.ts").write_text(
                    "import { test } from '@playwright/test';\n"
                    "test('widget works', async () => {});\n",
                    encoding="utf-8",
                )
                _git(cwd, "config", "user.email", "candidate@example.com")
                _git(cwd, "config", "user.name", "Candidate")
                _git(cwd, "add", "tests/widget.spec.ts")
                _git(cwd, "commit", "-q", "-m", "replace protected test")
            else:
                (cwd / "candidate-cache").mkdir()
                (cwd / "candidate-cache/state").write_text("candidate", encoding="utf-8")
        _write_framework_observation(_kwargs, {"tests": [{"identity": IDENTITY, "status": "passed"}]})
        return _trusted_completed(command, 0), False

    monkeypatch.setattr(runner_module, "run_supervised", supervised)
    _envelope, executions = _run(root, commit, commit, _fake_playwright(tmp_path))

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "modified" in executions[0].detail.lower()


def test_playwright_receiver_capabilities_accept_documented_representative_chains(
    tmp_path: Path,
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(
        "import { expect, test } from '@playwright/test';\n"
        "test.describe.configure({ mode: 'serial' });\n"
        "test.beforeEach(async ({ page }) => {\n"
        "  await page.getByTestId('card').filter({ hasText: 'ready' }).first().hover();\n"
        "  await page.mainFrame().getByRole('button').click();\n"
        "});\n"
        "test('widget works', async ({ page }) => {\n"
        "  const card = page.locator('.card');\n"
        "  await expect(card).toHaveCount(1);\n"
        "});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "documented receiver chains")

    assert playwright_validator_config_digest(
        root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
    )


def test_playwright_rejects_suite_level_retries(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(
        "import { test } from '@playwright/test';\n"
        "test.describe.configure({ retries: 2 });\n"
        "test('widget works', async () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "suite retries")

    with pytest.raises(ValueError, match="retr"):
        playwright_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
        )


def test_playwright_reporter_preserves_failure_across_retry_attempts(
    tmp_path: Path,
) -> None:
    root, _commit = _repository(tmp_path)
    payload = {
        "suites": [{
            "title": "",
            "specs": [{
                "title": "widget works",
                "file": str(root / "tests/widget.spec.ts"),
                "tests": [{
                    "projectName": "chromium",
                    "results": [{"status": "failed"}, {"status": "passed"}],
                }],
            }],
        }],
    }

    outcome, _detail, identities = _playwright_result(
        root, json.dumps(payload), 0, None
    )

    assert outcome is EvidenceOutcome.FAIL
    assert identities == (IDENTITY,)


def test_playwright_phase_identity_excludes_imported_declared_product(
    tmp_path: Path,
) -> None:
    root, _base = _repository(tmp_path)
    (root / "source.ts").write_text(
        "import React from 'react';\n"
        "export const widget = React.createElement('div');\n",
        encoding="utf-8",
    )
    (root / "tests/widget.spec.ts").write_text(
        "import { expect, test } from '@playwright/test';\n"
        "import { widget } from '../source';\n"
        "test('widget works', async () => expect(widget).toBeTruthy());\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "import declared product")
    head = _git(root, "rev-parse", "HEAD")

    _envelope, executions = _run(
        root,
        head,
        head,
        _fake_playwright(tmp_path),
        code_under_test_paths=(PurePosixPath("source.ts"),),
    )

    assert executions[0].outcome is EvidenceOutcome.PASS


def test_playwright_rejects_symlink_config_before_subprocess_launch(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "playwright.config.ts").unlink()
    target = root / "export default {};"
    target.write_text("export default {};\n", encoding="utf-8")
    (root / "playwright.config.ts").symlink_to(target.name)
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "symlink config")
    commit = _git(root, "rev-parse", "HEAD")
    launches = 0

    def supervised(*_args, **_kwargs):
        nonlocal launches
        launches += 1
        raise AssertionError("invalid closure must fail before Playwright launch")

    monkeypatch.setattr(runner_module, "run_supervised", supervised)
    _envelope, executions = _run(root, commit, commit, _fake_playwright(tmp_path))

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert launches == 0
    assert "symlink" in executions[0].detail.lower()


def test_playwright_tracks_page_locator_and_frame_receiver_aliases(
    tmp_path: Path,
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(
        "import { test } from '@playwright/test';\n"
        "test('widget works', async ({ page: browserPage }) => {\n"
        "  const card = browserPage.locator('.card');\n"
        "  const firstCard = card.first();\n"
        "  const frame = browserPage.mainFrame();\n"
        "  await firstCard.click();\n"
        "  await frame.waitForSelector('#ready');\n"
        "});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "receiver aliases")

    assert playwright_validator_config_digest(
        root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
    )


def test_playwright_stdout_result_forgery_is_not_a_reporter_result(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    outcome, _detail, identities = _playwright_result(
        root, json.dumps({"tests": [{"identity": IDENTITY, "status": "passed"}]}), 0, None
    )
    assert outcome is EvidenceOutcome.COLLECTION_ERROR
    assert not identities


def test_playwright_missing_observation_has_bounded_diagnostics() -> None:
    result = subprocess.CompletedProcess(
        ["playwright"], 17, "", "mount failed\n" + ("x" * 600)
    )

    detail = _playwright_missing_result_detail(result)

    assert "exit 17" in detail
    assert "mount failed" in detail
    assert len(detail) < 600


@pytest.mark.parametrize(
    ("kind", "returncode", "outcome"),
    [
        (TerminationKind.TIMEOUT, 124, EvidenceOutcome.TIMEOUT),
        (TerminationKind.RESOURCE_LIMIT, 125, EvidenceOutcome.ERROR),
        (TerminationKind.SIGNAL, -9, EvidenceOutcome.ERROR),
        (TerminationKind.SANDBOX_ERROR, 125, EvidenceOutcome.ERROR),
    ],
)
def test_playwright_rejects_non_exit_termination_before_reporter(
    kind: TerminationKind, returncode: int, outcome: EvidenceOutcome,
) -> None:
    """Only authenticated ordinary EXIT evidence may reach reporter status parsing."""
    result = _trusted_completed(
        ["playwright"], returncode, kind=kind,
        resource_limit="memory" if kind is TerminationKind.RESOURCE_LIMIT else None,
    )

    observed = _playwright_infrastructure_termination(result, False)

    assert observed is not None
    assert observed[0] is outcome


def test_playwright_requires_typed_termination_evidence() -> None:
    result = subprocess.CompletedProcess(["playwright"], 0, "", "")

    observed = _playwright_infrastructure_termination(result, False)

    assert observed == (
        EvidenceOutcome.ERROR,
        "phase=execution; Playwright trusted termination evidence is missing",
    )


def test_playwright_timeout_preserves_phase_reporter_and_cgroup_diagnostics(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, commit = _repository(tmp_path)

    def supervised(command, **kwargs):
        collection = "--list" in command
        _write_framework_observation(kwargs, {
            "tests": [{
                "identity": IDENTITY,
                "status": "collected" if collection else "timedOut",
                "error": "browserType.launch exceeded 30000ms",
            }],
        })
        stderr = "cgroup pids.events max delta=7\n" + ("x" * 5000)
        return _trusted_completed(
            command, 0 if collection else 1, "", stderr
        ), False

    monkeypatch.setattr(runner_module, "run_supervised", supervised)

    _envelope, executions = _run(
        root, commit, commit, _fake_playwright(tmp_path)
    )

    assert executions[0].outcome is EvidenceOutcome.TIMEOUT
    assert "phase=execution" in executions[0].detail
    assert "browserType.launch exceeded 30000ms" in executions[0].detail
    assert "cgroup pids.events max delta=7" in executions[0].detail
    assert len(executions[0].detail) < 2500


def test_playwright_uses_two_gib_physical_and_256_gib_virtual_limits(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Chromium receives address space without relaxing aggregate physical memory."""
    root, commit = _repository(tmp_path)
    observed: list[dict] = []

    def supervised(command, **kwargs):
        observed.append(kwargs)
        _write_framework_observation(kwargs, {
            "tests": [{"identity": IDENTITY, "status": "passed"}],
        })
        return _trusted_completed(command, 0), False

    monkeypatch.setattr(runner_module, "run_supervised", supervised)
    _envelope, executions = _run(root, commit, commit, _fake_playwright(tmp_path))

    assert executions[0].outcome is EvidenceOutcome.PASS
    assert len(observed) == 3
    assert all(kwargs["limits"] == PLAYWRIGHT_SUPERVISOR_LIMITS for kwargs in observed)
    assert PLAYWRIGHT_SUPERVISOR_LIMITS.max_memory_bytes == 2 * 1024 * 1024 * 1024
    assert PLAYWRIGHT_SUPERVISOR_LIMITS.max_virtual_memory_bytes == 256 * 1024 * 1024 * 1024
    assert PLAYWRIGHT_SUPERVISOR_LIMITS.max_processes == 128
    assert all("private_overlays" not in kwargs for kwargs in observed)
    assert all("readable_data" not in kwargs for kwargs in observed)


def test_playwright_does_not_inject_browser_or_node_wasm_flags(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The checker must leave Chromium and Node flags to the trusted toolchain."""
    monkeypatch.setattr(runner_module.sys, "platform", "linux")

    prefix = _playwright_runtime_prefix(
        ("/usr/bin/node", "/opt/playwright/cli.js"), Path("/usr/bin/node")
    )

    assert prefix == ("/usr/bin/node", "/opt/playwright/cli.js")


def test_playwright_reported_failure_has_bounded_diagnostics() -> None:
    detail = _playwright_reported_failure_detail([{
        "identity": IDENTITY,
        "status": "failed",
        "error": "browser launch failed\n" + ("x" * 3000) + "\nloader tail",
    }])

    assert "browser launch failed" in detail
    assert "loader tail" in detail
    assert len(detail) < 2200


@pytest.mark.parametrize("source", [
    "const proc = globalThis.process; proc.exit(0);",
    "const { exit } = process; exit(0);",
    "const load = process.getBuiltinModule; const fs = load('node:fs'); fs.readFileSync('./x');",
    "const { write } = process.stdout; write('forged');",
])
def test_playwright_rejects_ambient_capability_aliases(tmp_path: Path, source: str) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(source, encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "ambient capability alias")
    with pytest.raises(ValueError, match="runtime|module loading"):
        playwright_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
        )


@pytest.mark.parametrize("config", [
    "export default { expect: { toHaveScreenshot: { pathTemplate: './oracle.png' } } };\n",
    "export default { expect: { toHaveScreenshot: { pathTemplate: '../oracle.png' } } };\n",
])
def test_playwright_rejects_unbound_expect_path_options(tmp_path: Path, config: str) -> None:
    root, _commit = _repository(tmp_path, config=config)
    with pytest.raises(ValueError, match="expect|unsupported"):
        playwright_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
        )


@pytest.mark.parametrize("option", [
    "storageState: './auth.json'",
    "launchOptions: { executablePath: './evil-browser' }",
    "recordHar: { path: './capture.har' }",
])
def test_playwright_rejects_unbound_test_use_paths(tmp_path: Path, option: str) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(
        "import { test } from '@playwright/test';\n"
        f"test.use({{ {option} }});\n"
        "test('widget works', async () => {});\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "path-bearing use option")
    with pytest.raises(ValueError, match="path option|executable option|unsupported"):
        playwright_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
        )


@pytest.mark.parametrize("option", [
    "channel: 'chrome'",
    "browserName: 'firefox'",
    "launchOptions: { channel: 'msedge' }",
    "connectOptions: { wsEndpoint: 'ws://host' }",
])
def test_playwright_rejects_executable_selecting_test_use_options(
    tmp_path: Path, option: str
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(
        "import { test } from '@playwright/test';\n"
        f"test.use({{ {option} }});\n"
        "test('widget works', async () => {});\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "browser selecting use option")
    with pytest.raises(ValueError, match="executable option"):
        playwright_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
        )


def test_playwright_accepts_supported_literal_test_use_option(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(
        "import { test } from '@playwright/test';\n"
        "test.use({ viewport: { width: 800, height: 600 }, locale: 'en-US' });\n"
        "test('widget works', async () => {});\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "literal use option")
    assert playwright_validator_config_digest(
        root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
    )


def test_playwright_import_aliases_are_bound_by_provenance(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(
        "import { expect as assert, test as it } from '@playwright/test';\n"
        "it('widget works', () => assert(true).toBeTruthy());\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "bound Playwright aliases")
    assert playwright_validator_config_digest(
        root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
    )


@pytest.mark.parametrize("source", [
    "import { expect, test } from '@playwright/test';\nconst expect = () => ({ toBe: () => {} });\ntest('widget works', () => expect(false).toBe(true));\n",
    "import { test } from '@playwright/test';\nfunction helper(test) { test('x', () => {}); }\nhelper(test);\n",
    "const expect = () => ({ toBe: () => {} });\nconst test = () => {};\ntest('widget works', () => expect(false).toBe(true));\n",
])
def test_playwright_rejects_unprovenanced_or_shadowed_bindings(
    tmp_path: Path, source: str
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.spec.ts").write_text(source, encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "shadowed Playwright binding")
    with pytest.raises(ValueError, match="shadowed|bound|schema"):
        playwright_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
        )


def test_playwright_reporter_collects_each_identity_before_execution() -> None:
    """Keep v2 collection on an irreversible fixed-error receipt contract."""
    source = _playwright_reporter_source(198)
    assert "version() { return 'v2'; }" in source
    assert "onBegin(suite)" in source
    assert "allTestsFunction.call(suite)" in source
    assert "this.tests = new Map()" in source
    assert "invalid_reporter_state" in source
    assert "REPORTER_ERROR_REASONS" in source
    assert '"reason"' in source
    assert "invalidate(reason)" in source
    assert "if (this.reporterError) return;" in source
    assert "this.reporterError" in source
    assert "catch" in source
    assert "throw new Error" not in source
    assert "titles.join(' > ')" in source
    assert "onTestEnd(test, result)" in source
    assert "onError(error)" in source
    assert "onEnd(result)" in source
    assert "this.frameworkError && status !== 'passed'" in source


def test_playwright_package_import_mapping_is_bound_with_nearest_manifest(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/package.json").write_text(
        json.dumps({"imports": {"#helper": "./helper.ts"}}), encoding="utf-8"
    )
    (root / "tests/helper.ts").write_text("export const ready = true;\n", encoding="utf-8")
    (root / "tests/widget.spec.ts").write_text(
        "import { test } from '@playwright/test';\n"
        "import { ready } from '#helper';\n"
        "test('widget works', async () => { check(ready); });\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mapped Playwright helper")
    before = playwright_validator_config_digest(
        root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
    )
    (root / "tests/helper.ts").write_text("export const ready = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate mapped helper")
    assert playwright_validator_config_digest(
        root, "HEAD", (PurePosixPath("tests/widget.spec.ts"),)
    ) != before
