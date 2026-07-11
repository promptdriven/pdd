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
    _directory_identity,
    _local_javascript_imports,
    _playwright_environment,
    _playwright_command_error,
    _playwright_result,
    _toolchain_manifest_identity,
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
    command = fake if isinstance(fake, tuple) else (sys.executable, str(fake))
    entrypoint = Path(command[1])
    manifest_root = root.parent if entrypoint.is_relative_to(root) else entrypoint.parent
    declared = entrypoint.name
    if entrypoint.is_relative_to(root):
        declared = "protected-playwright-tool"
        (manifest_root / declared).write_bytes(b"protected")
    manifest = manifest_root / "playwright-toolchain.json"
    manifest.write_text(
        '{"version":1,"files":[' + repr(declared).replace("'", '"') + "]}",
        encoding="utf-8",
    )
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
            playwright_command=command,
            playwright_toolchain_manifest=manifest,
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
    "config",
    [
        "const key='grep'; export default { [key]: /widget/ };\n",
        "const controls={ ['webServer']: {command:'./server.sh'} }; export default {...controls};\n",
        "export default { globalSetup /*comment*/: './setup.ts' };\n",
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
    with pytest.raises(ValueError, match="module loading"):
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
    with pytest.raises(ValueError, match="module loading"):
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
    with pytest.raises(ValueError, match="module loading"):
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


def test_toolchain_manifest_binds_transitive_and_stable_symlink_target_bytes(
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
    manifest.write_text(
        '{"version":1,"files":["toolchain/node","toolchain/cli.js",'
        '"toolchain/modules/helper"]}',
        encoding="utf-8",
    )
    before = _toolchain_manifest_identity(manifest)
    (target / "index.js").write_text("module.exports = 2", encoding="utf-8")
    assert _toolchain_manifest_identity(manifest) != before


def test_playwright_production_run_requires_and_rechecks_toolchain_manifest(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, commit = _repository(tmp_path)
    runner = _fake_playwright(tmp_path)
    manifest = tmp_path / "playwright-toolchain.json"
    manifest.write_text(
        '{"version":1,"files":["fake_playwright.py"]}', encoding="utf-8"
    )
    original_run = subprocess.run

    def mutate_after_playwright(*args, **kwargs):
        kwargs.setdefault("check", False)
        result = original_run(*args, **kwargs)
        command = args[0] if args else kwargs.get("args", ())
        if isinstance(command, (list, tuple)) and str(runner) in command:
            runner.write_text(runner.read_text(encoding="utf-8") + "# changed\n")
        return result

    monkeypatch.setattr("pdd.sync_core.runner.subprocess.run", mutate_after_playwright)
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
            playwright_command=(sys.executable, str(runner)),
            playwright_toolchain_manifest=manifest,
        ),
    )
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
    assert executions[0].outcome is EvidenceOutcome.COLLECTION_ERROR
    assert "launch" in executions[0].detail.lower()


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
    assert "exactly" in error or "options" in error


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
    (root / "shared/setup.ts").write_text("globalThis.expected = true;\n", encoding="utf-8")
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
    (root / "shared/setup.ts").write_text("globalThis.expected = true;\n", encoding="utf-8")
    (root / "tests/widget.spec.ts").write_text(
        "import { expect, test } from '@playwright/test';\n"
        "import { expected } from '../shared/helpers';\n"
        "import '../shared/setup';\n"
        "test('widget works', async () => expect(expected && globalThis.expected).toBeTruthy());\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add parent import helpers")
    base = _git(root, "rev-parse", "HEAD")
    base_digest = playwright_validator_config_digest(root, base, paths)

    (root / "shared/helpers/index.ts").write_text(
        "export const expected = false;\n", encoding="utf-8"
    )
    (root / "shared/setup.ts").write_text("globalThis.expected = false;\n", encoding="utf-8")
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
        "globalThis.expected = true;\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add extensionless setup index")
    base = _git(root, "rev-parse", "HEAD")
    base_digest = playwright_validator_config_digest(root, base, paths)

    (root / "support/setup/index.ts").write_text(
        "globalThis.expected = false;\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate extensionless setup index")
    head_digest = playwright_validator_config_digest(
        root, _git(root, "rev-parse", "HEAD"), paths
    )

    assert head_digest != base_digest


def test_playwright_repository_escape_import_is_not_bound(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    imports = _local_javascript_imports(
        root,
        commit,
        PurePosixPath("tests/widget.spec.ts"),
        b"import '../../outside.js';\n",
    )
    assert imports == set()


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
    assert "pathless" in executions[0].detail


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
