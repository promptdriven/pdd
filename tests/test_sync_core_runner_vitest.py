"""Contract tests for the fail-closed trusted Vitest adapter."""

import hashlib
import json
import os
import errno as errno_module
import signal
import shutil
import subprocess
import sys
from types import SimpleNamespace
import tomllib
from dataclasses import replace
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

import pytest

import pdd.sync_core.runner as runner_module
import pdd.sync_core.supervisor as supervisor_module
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
    _copy_vitest_dependencies,
    _local_javascript_imports,
    _collect_vitest_at_base,
    _load_vitest_toolchain_descriptor,
    _prepare_vitest_toolchain,
    _run_vitest,
    _validator_tree_identity,
    _vitest_command_error,
    _vitest_environment,
    _vitest_result,
    jest_validator_config_digest,
    runner_identity_digest,
    vitest_validator_config_digest,
)
from pdd.sync_core.evidence_store import attestation_payload, decode_attestation
from pdd.sync_core.supervisor import (
    CgroupResourceTelemetry,
    SupervisedCompletedProcess,
    SupervisorLimits,
    SupervisorTermination,
    TerminationKind,
)


def test_framework_observation_fifo_eof_waits_for_late_writer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class Completion:
        def __init__(self) -> None:
            self.checks = 0
            self.waits = []

        def is_set(self) -> bool:
            self.checks += 1
            return self.checks > 3

        def wait(self, timeout: float) -> bool:
            self.waits.append(timeout)
            return False

    completion = Completion()
    result: dict[str, object] = {}
    monkeypatch.setattr(
        runner_module.select, "select", lambda *_args: ([17], [], [])
    )
    monkeypatch.setattr(runner_module.os, "read", lambda *_args: b"")

    runner_module._drain_result_pipe(17, completion, result)

    assert completion.waits
    assert all(wait == .01 for wait in completion.waits)
    assert result["data"] == b""


UNIT = UnitId("repository-1", PurePosixPath("prompts/widget_ts.prompt"), "typescript")
IDENTITY = "tests/widget.test.ts::widget works"


@pytest.fixture(autouse=True)
def _controlled_supervisor(
    monkeypatch: pytest.MonkeyPatch, request: pytest.FixtureRequest
) -> None:
    """Exercise adapter logic portably without weakening production policy."""
    if request.node.name.startswith("test_real_vitest_runs_copied_entrypoint"):
        return

    def execute(
        command, *, cwd, timeout, env, result_fifo=None, result_fd=198, **_limits
    ):
        write_fd = os.open(result_fifo, os.O_WRONLY) if result_fifo else None
        if write_fd is not None:
            os.dup2(write_fd, result_fd)
            if write_fd != result_fd:
                os.close(write_fd)
        try:
            result = subprocess.run(
                command,
                cwd=cwd,
                timeout=timeout,
                env=env,
                pass_fds=((result_fd,) if result_fifo else ()),
                capture_output=True,
                text=True,
                check=False,
            )
        except subprocess.TimeoutExpired:
            result = subprocess.CompletedProcess(command, 124, "", "timeout")
        finally:
            if result_fifo:
                os.close(result_fd)
        return result, False

    monkeypatch.setattr("pdd.sync_core.runner.run_supervised", execute)


@pytest.mark.parametrize(
    "control",
    [
        "--testNamePattern=smoke",
        "--project=unit",
        "--shard=1/2",
        "--related=src/widget.ts",
        "--retry=3",
        "--repeat=2",
        "--update",
    ],
)
def test_vitest_command_schema_rejects_non_launcher_controls(
    tmp_path: Path, control: str
) -> None:
    launcher = tmp_path / "node"
    launcher.write_text("#!/bin/sh\n", encoding="utf-8")
    launcher.chmod(0o755)
    entrypoint = tmp_path / "vitest.mjs"
    entrypoint.write_text("", encoding="utf-8")

    assert _vitest_command_error(
        tmp_path, (str(launcher), str(entrypoint), control)
    ) is not None


def test_vitest_prior_retry_failure_cannot_normalize_to_pass(tmp_path: Path) -> None:
    output = tmp_path / "results.json"
    output.write_text(
        json.dumps(
            {
                "testResults": [
                    {
                        "name": str(tmp_path / "tests/widget.test.ts"),
                        "assertionResults": [
                            {
                                "title": "widget works",
                                "fullName": "widget works",
                                "status": "passed",
                                "failureMessages": ["first attempt failed"],
                            }
                        ],
                    }
                ]
            }
        ),
        encoding="utf-8",
    )

    outcome, _detail, _identities = _vitest_result(tmp_path, output, 0, None)
    assert outcome is not EvidenceOutcome.PASS


def test_vitest_declared_product_is_excluded_from_support_digest(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "src").mkdir()
    (root / "src/product.ts").write_text("export const value = 1;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import '../src/product';\nimport { test } from 'vitest';\ntest('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "import declared product")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    products = (PurePosixPath("src/product.ts"),)
    before = vitest_validator_config_digest(root, "HEAD", paths, products)
    (root / "src/product.ts").write_text("export const value = 2;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change product")
    assert vitest_validator_config_digest(root, "HEAD", paths, products) == before


def test_vitest_ast_binds_static_template_loader_and_rejects_runtime_config(
    tmp_path: Path,
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/resource.ts").write_text("export default 'base';\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import(`./resource`);\nimport { test } from 'vitest';\ntest('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add static template loader")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    before = vitest_validator_config_digest(root, "HEAD", paths)
    (root / "tests/resource.ts").write_text("export default 'changed';\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change loaded resource")
    assert vitest_validator_config_digest(root, "HEAD", paths) != before
    (root / "snapshot-environment.ts").write_text("export {};\n", encoding="utf-8")
    (root / "vitest.config.json").write_text(
        '{"test":{"snapshotEnvironment":"./snapshot-environment.ts"}}', encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "unsupported runtime config")
    with pytest.raises(ValueError, match="snapshotEnvironment"):
        vitest_validator_config_digest(root, "HEAD", paths)


@pytest.mark.parametrize(
    "loader",
    [
        "const p = './helper'; module.require(p);",
        "import.meta.glob('./helpers/*.ts');",
    ],
)
def test_vitest_rejects_unbound_alternate_local_loaders(
    tmp_path: Path, loader: str
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/widget.test.ts").write_text(
        f"{loader}\nimport {{ test }} from 'vitest';\ntest('widget works', () => {{}});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add alternate loader")

    with pytest.raises(ValueError, match="loader|module loading|glob|createRequire"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


def test_vitest_rejects_unbound_alternate_loader_transitively(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/helper.ts").write_text(
        "import.meta.glob('./fixtures/*.ts');\n", encoding="utf-8"
    )
    (root / "tests/widget.test.ts").write_text(
        "import './helper';\nimport { test } from 'vitest';\n"
        "test('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add transitive alternate loader")

    with pytest.raises(ValueError, match="glob|loader"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


@pytest.mark.parametrize(
    "loader",
    [
        "const req = require; req('./helper.cjs');",
        (
            "import { createRequire } from 'node:module'; "
            "const req = createRequire(import.meta.url); req('./helper.cjs');"
        ),
        (
            "import { createRequire as makeRequire } from 'node:module'; "
            "const req = makeRequire(import.meta.url); req('./helper.cjs');"
        ),
        (
            "const { createRequire: makeRequire } = require('node:module'); "
            "const req = makeRequire(import.meta.url); req('./helper.cjs');"
        ),
        "let req; req = require; req('./helper.cjs');",
    ],
)
def test_vitest_binds_statically_proven_commonjs_loader_aliases(
    tmp_path: Path, loader: str
) -> None:
    root, _commit = _repository(tmp_path)
    helper = root / "tests/helper.cjs"
    helper.write_text("module.exports = 'trusted';\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        f"{loader}\nimport {{ test }} from 'vitest';\n"
        "test('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add static CommonJS alias")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    before = vitest_validator_config_digest(root, "HEAD", paths)
    helper.write_text("module.exports = 'changed';\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change CommonJS helper")

    assert vitest_validator_config_digest(root, "HEAD", paths) != before


@pytest.mark.parametrize(
    "loader",
    [
        "let req = require; req = unknown; req('./helper.cjs');",
        "const req = enabled ? require : unknown; req('./helper.cjs');",
        (
            "import { createRequire } from 'node:module'; "
            "const req = createRequire(runtimeUrl); req('./helper.cjs');"
        ),
        "const req = require; const box = { req }; box.req('./helper.cjs');",
        "const box = getLoader(); box.load('./helper.cjs');",
        "const p = './helper.cjs'; require.apply(null, [p]);",
        "const p = './helper.cjs'; Reflect.apply(require, null, [p]);",
        "const p = './helper.cjs'; const [load = require] = []; load(p);",
        "const p = './helper.cjs'; module.constructor._load(p, module);",
    ],
)
def test_vitest_rejects_dynamic_or_ambiguous_loader_aliases(
    tmp_path: Path, loader: str
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/helper.cjs").write_text("module.exports = 1;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        f"{loader}\nimport {{ test }} from 'vitest';\n"
        "test('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add ambiguous CommonJS alias")

    with pytest.raises(ValueError, match="alias|loader|dynamic|provenance"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


@pytest.mark.parametrize(
    "loader",
    [
        (
            "const p = './helper.cjs'; "
            "function invoke(loader, arg) { return loader(arg); } "
            "invoke(require, p);"
        ),
        (
            "const p = './helper.cjs'; const { apply } = Reflect; "
            "apply(require, null, [p]);"
        ),
        (
            "const p = './helper.cjs'; const invoke = Reflect.apply; "
            "invoke(require, null, [p]);"
        ),
        (
            "const p = './helper.cjs'; const invoke = Function.prototype.call; "
            "invoke(require, null, p);"
        ),
        "const p = './helper.cjs'; (0, require)(p);",
        "const p = './helper.cjs'; (require, require)(p);",
        (
            "import Module from 'node:module'; const p = './helper.cjs'; "
            "const load = Module._load; load(p);"
        ),
        (
            "const p = './helper.cjs'; "
            "const load = module.constructor._load; load(p, module);"
        ),
        (
            "import Module from 'node:module'; const p = './helper.cjs'; "
            "const { _load: load } = Module; load(p);"
        ),
        (
            "const key = '_load'; const p = './helper.cjs'; "
            "const load = module.constructor[key]; load(p, module);"
        ),
        "const p = './helper.cjs'; const box = { load: require }; box.load(p);",
        "const p = './helper.cjs'; function pass() { return require; } pass()(p);",
        "const req = require; { const req = unknown; req('./helper.cjs'); }",
        "const req = require; function shadow(req) { req('./helper.cjs'); } shadow(req);",
        "const req = require; req = unknown; req('./helper.cjs');",
        r"requ\u0069re(process.argv[2]);",
        r"const req = requ\u0069re; req(process.argv[2]);",
        (
            r"import { create\u0052equire as make } from 'node:module'; "
            "const req = make(import.meta.url); req(process.argv[2]);"
        ),
        "eval('require')(process.argv[2]);",
        "Function('return require')()(process.argv[2]);",
        (
            "const m = module; const req = Reflect.get(m, 'require'); "
            "req(process.argv[2]);"
        ),
        (
            "const m = module; const c = m.constructor; const key = '_lo' + 'ad'; "
            "const load = c[key]; load(process.argv[2], m);"
        ),
        (
            "const m = module; const c = m.constructor; "
            "const load = Reflect.get(c, '_lo' + 'ad'); load(process.argv[2], m);"
        ),
        (
            "const key = 'requ' + 'ire'; const req = globalThis[key]; "
            "req(process.argv[2]);"
        ),
        (
            "const key = '_lo' + 'ad'; const load = process.mainModule.constructor[key]; "
            "load(process.argv[2]);"
        ),
    ],
)
def test_vitest_positive_loader_capability_rejects_unproven_uses(
    tmp_path: Path, loader: str
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/helper.cjs").write_text("module.exports = 1;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        f"{loader}\nimport {{ test }} from 'vitest';\n"
        "test('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add uncertain loader capability")

    with pytest.raises(ValueError, match="capability|loader|provenance|internal"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


def test_vitest_rejects_loader_capability_forwarding_transitively(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "tests/helper.cjs").write_text("module.exports = 1;\n", encoding="utf-8")
    (root / "tests/loader.cjs").write_text(
        "const p = './helper.cjs';\n"
        "function invoke(loader, arg) { return loader(arg); }\n"
        "module.exports = invoke(require, p);\n",
        encoding="utf-8",
    )
    (root / "tests/widget.test.ts").write_text(
        "import './loader.cjs';\nimport { test } from 'vitest';\n"
        "test('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "forward loader transitively")

    with pytest.raises(ValueError, match="capability|loader|provenance"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


def test_vitest_binds_transitive_create_require_helper_mutation(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    fixture = root / "tests/fixture.cjs"
    fixture.write_text("module.exports = 'trusted';\n", encoding="utf-8")
    (root / "tests/loader.cjs").write_text(
        "const { createRequire: makeRequire } = require('node:module');\n"
        "const req = makeRequire(import.meta.url);\n"
        "module.exports = req('./fixture.cjs');\n",
        encoding="utf-8",
    )
    (root / "tests/widget.test.ts").write_text(
        "import './loader.cjs';\nimport { test } from 'vitest';\n"
        "test('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add transitive createRequire helper")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    before = vitest_validator_config_digest(root, "HEAD", paths)
    fixture.write_text("module.exports = 'changed';\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate transitive createRequire helper")

    assert vitest_validator_config_digest(root, "HEAD", paths) != before


def test_vitest_grammar_dependencies_are_exactly_pinned() -> None:
    project = tomllib.loads(
        (Path(__file__).parents[1] / "pyproject.toml").read_text(encoding="utf-8")
    )
    dependencies = set(project["project"]["dependencies"])

    assert "tree-sitter==0.25.2" in dependencies
    assert "tree-sitter-javascript==0.25.0" in dependencies
    assert "tree-sitter-typescript==0.23.2" in dependencies
    assert not any(item.startswith("tree-sitter-language-pack") for item in dependencies)


def test_real_vitest_workflow_uses_checked_in_locked_toolchain() -> None:
    """Hosted protected Vitest must use one locked toolchain in a fresh worker."""
    root = Path(__file__).parents[1]
    toolchain = root / ".github/toolchains/vitest"
    package = json.loads((toolchain / "package.json").read_text(encoding="utf-8"))
    lock = json.loads((toolchain / "package-lock.json").read_text(encoding="utf-8"))
    workflow = (root / ".github/workflows/unit-tests.yml").read_text(encoding="utf-8")
    vitest_step = workflow[
        workflow.index("- name: Provision identity-bound Vitest toolchain"):
        workflow.index("- name: Provision identity-bound Playwright Chromium toolchain")
    ]

    assert package["private"] is True
    assert package["dependencies"] == {"vitest": "4.1.10"}
    assert lock["packages"][""]["dependencies"] == package["dependencies"]
    assert 'cp .github/toolchains/vitest/package.json "$toolchain/"' in workflow
    assert 'cp .github/toolchains/vitest/package-lock.json "$toolchain/"' in workflow
    assert 'npm ci --prefix "$toolchain" --ignore-scripts --no-audit --no-fund' in workflow
    assert 'npm install --prefix "$toolchain"' not in vitest_step
    real_vitest_test = (
        "tests/test_sync_core_runner_vitest.py::"
        "test_real_vitest_runs_copied_entrypoint_without_candidate_result_access"
    )
    sandbox_step = "- name: Provision and verify protected Linux sandbox"
    dedicated_step = "- name: Verify real Vitest sandbox isolation"
    focused_step = "- name: Run focused protected-runner tests"
    bulk_step = "- name: Run unit tests"
    sandbox_index = workflow.index(sandbox_step)
    dedicated_index = workflow.index(dedicated_step)
    focused_index = workflow.index(focused_step)
    bulk_index = workflow.index(bulk_step)
    dedicated_body = workflow[dedicated_index:focused_index]
    bulk_body = workflow[bulk_index:]
    target_deselect = f"--deselect={real_vitest_test}"

    assert workflow.count(real_vitest_test) == 2
    assert sandbox_index < dedicated_index < focused_index < bulk_index
    assert f"{real_vitest_test}\n          --timeout=60" in dedicated_body
    assert "-n" not in dedicated_body
    assert "xdist" not in dedicated_body
    assert "--deselect" not in dedicated_body
    assert "continue-on-error" not in dedicated_body
    assert target_deselect not in workflow[:bulk_index]
    assert bulk_body.count(target_deselect) == 1

def test_vitest_uses_packaged_grammars_without_language_pack(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setitem(sys.modules, "tree_sitter_language_pack", None)
    javascript = runner_module._vitest_parser("javascript")
    typescript = runner_module._vitest_parser("typescript")

    assert not javascript.parse(b"const value = 1;").root_node.has_error
    assert not typescript.parse(b"const value: number = 1;").root_node.has_error


def test_vitest_binds_commonjs_alias_in_transitive_local_helper(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    helper = root / "tests/fixture.cjs"
    helper.write_text("module.exports = 'trusted';\n", encoding="utf-8")
    (root / "tests/loader.cjs").write_text(
        "const req = require; module.exports = req('./fixture.cjs');\n",
        encoding="utf-8",
    )
    (root / "tests/widget.test.ts").write_text(
        "import './loader.cjs';\nimport { test } from 'vitest';\n"
        "test('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add transitive CommonJS alias")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    before = vitest_validator_config_digest(root, "HEAD", paths)
    helper.write_text("module.exports = 'changed';\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "change transitive CommonJS helper")

    assert vitest_validator_config_digest(root, "HEAD", paths) != before


def test_vitest_parser_initialization_failure_is_deterministic(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, _commit = _repository(tmp_path)
    monkeypatch.setattr(
        "pdd.sync_core.runner.importlib.metadata.version",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            runner_module.importlib.metadata.PackageNotFoundError("missing")
        ),
    )

    with pytest.raises(ValueError, match="parser is unavailable"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


def test_vitest_grammar_version_mismatch_is_deterministic(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, _commit = _repository(tmp_path)
    monkeypatch.setattr(
        "pdd.sync_core.runner.importlib.metadata.version", lambda _name: "unexpected"
    )

    with pytest.raises(ValueError, match="parser is unavailable"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


def test_vitest_rejects_nonregular_git_closure_members(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    target = tmp_path / "outside.ts"
    target.write_text("export {};\n", encoding="utf-8")
    (root / "setup.ts").symlink_to(target)
    (root / "vitest.config.json").write_text(
        '{"test":{"setupFiles":["./setup.ts"]}}', encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "symlink support")
    with pytest.raises(ValueError, match="regular|symlink"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


def test_vitest_environment_drops_protected_host_capabilities(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("PDD_ATTESTATION_SIGNER_COMMAND", "steal-me")
    monkeypatch.setenv("AWS_PROFILE", "production")
    environment = _vitest_environment(tmp_path)
    assert "PDD_ATTESTATION_SIGNER_COMMAND" not in environment
    assert "AWS_PROFILE" not in environment


def test_vitest_execution_uses_shared_supervisor(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, _commit = _repository(tmp_path)
    invoked = False

    def supervised(*_args, **_kwargs):
        nonlocal invoked
        invoked = True
        return subprocess.CompletedProcess([], 1, "", ""), set()

    monkeypatch.setattr("pdd.sync_core.runner.run_supervised", supervised)
    original_run = subprocess.run

    def guarded_run(command, *args, **kwargs):
        if command and command[0] == "git":
            return original_run(command, *args, **kwargs)
        pytest.fail("Vitest bypassed shared supervision")

    monkeypatch.setattr(
        "pdd.sync_core.runner.subprocess.run",
        guarded_run,
    )
    _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        1,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )
    assert invoked


def test_vitest_toolchain_descriptor_is_complete_typed_and_matches_command(
    tmp_path: Path,
) -> None:
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)

    assert descriptor.launcher.name == "node"
    assert descriptor.entrypoint == runner.resolve()
    assert descriptor.dependencies.name == "node_modules"
    assert descriptor.native_runtime[0].name == "runtime.bin"

    wrong = tmp_path / "wrong.py"
    wrong.write_text("pass\n", encoding="utf-8")
    with pytest.raises(ValueError, match="entrypoint.*command"):
        _load_vitest_toolchain_descriptor(
            tmp_path / "repo",
            replace(config, vitest_command=(config.vitest_command[0], str(wrong))),
        )


@pytest.mark.parametrize("missing_role", [
    "launcher", "entrypoint", "dependencies", "native_runtime", "lockfile"
])
def test_vitest_toolchain_descriptor_rejects_missing_roles(
    tmp_path: Path, missing_role: str
) -> None:
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    payload = json.loads(config.vitest_toolchain_manifest.read_text(encoding="utf-8"))
    del payload["roles"][missing_role]
    config.vitest_toolchain_manifest.write_text(json.dumps(payload), encoding="utf-8")

    with pytest.raises(ValueError, match="roles"):
        _load_vitest_toolchain_descriptor(tmp_path / "repo", config)


def test_vitest_toolchain_identity_binds_all_roles_modes_symlinks_and_ignores_cache(
    tmp_path: Path,
) -> None:
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    baseline = descriptor.identity

    launcher = descriptor.launcher
    launcher.write_bytes(launcher.read_bytes() + b"changed")
    assert _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity != baseline
    launcher.write_bytes(launcher.read_bytes().removesuffix(b"changed"))
    baseline = _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity

    runner.write_text(runner.read_text(encoding="utf-8") + "\n# changed\n", encoding="utf-8")
    assert _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity != baseline
    runner.write_text(runner.read_text(encoding="utf-8").removesuffix("\n# changed\n"), encoding="utf-8")
    baseline = _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity

    native = descriptor.native_runtime[0]
    native.write_bytes(b"changed-native")
    assert _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity != baseline
    native.write_bytes(b"native")
    baseline = _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity

    descriptor.lockfile.write_text('{"changed":true}\n', encoding="utf-8")
    assert _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity != baseline
    descriptor.lockfile.write_text("{}\n", encoding="utf-8")

    dependency = descriptor.dependencies / "vitest/dependency.js"
    dependency.write_text("export default 1;\n", encoding="utf-8")
    dependency.chmod(0o600)
    mode_identity = _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity
    dependency.chmod(0o644)
    assert _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity != mode_identity

    target = descriptor.dependencies / "linked-target"
    target.mkdir()
    (target / "native.bin").write_bytes(b"one")
    link = descriptor.dependencies / "linked-native"
    link.symlink_to("linked-target", target_is_directory=True)
    linked_identity = _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity
    (target / "native.bin").write_bytes(b"two")
    assert _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity != linked_identity

    cache = descriptor.dependencies / ".vite"
    cache.mkdir()
    before_cache = _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity
    (cache / "mutable.json").write_text("changed", encoding="utf-8")
    assert _load_vitest_toolchain_descriptor(tmp_path / "repo", config).identity == before_cache


def test_vitest_toolchain_identity_is_stable_after_relocation(tmp_path: Path) -> None:
    first = tmp_path / "first"
    second = tmp_path / "second"
    runner = _fake_vitest(first)
    first_config = _runner_config(first, runner)
    shutil.copytree(first / "trusted-toolchain", second / "trusted-toolchain")
    relocated_runner = second / "trusted-toolchain/node_modules/vitest/fake_vitest.py"
    second_config = _runner_config(second, relocated_runner)

    assert _load_vitest_toolchain_descriptor(
        tmp_path / "repo", first_config
    ).identity == _load_vitest_toolchain_descriptor(
        tmp_path / "repo", second_config
    ).identity


def test_validator_tree_identity_is_uniquely_mode_and_symlink_sensitive(
    tmp_path: Path,
) -> None:
    root = tmp_path / "tree"
    root.mkdir()
    file_path = root / "file"
    file_path.write_bytes(b"content")
    first = _validator_tree_identity(root)
    file_path.chmod(0o600)
    assert _validator_tree_identity(root) != first


def test_vitest_toolchain_entrypoint_is_copied_into_phase_tree(
    tmp_path: Path,
) -> None:
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    phase_root = tmp_path / "phase"
    phase_root.mkdir()

    phase = _prepare_vitest_toolchain(phase_root, descriptor)

    assert phase.entrypoint != descriptor.entrypoint
    assert phase.entrypoint.read_bytes() == descriptor.entrypoint.read_bytes()
    assert (phase_root / "node_modules/.vite-temp").is_dir()
    assert (phase_root / "node_modules/.vite").is_dir()


def test_vitest_phase_native_runtime_proof_is_bound_to_descriptor(
    tmp_path: Path,
) -> None:
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    phase_root = tmp_path / "phase"
    phase_root.mkdir()

    phase = _prepare_vitest_toolchain(phase_root, descriptor)

    member = next(
        item for item in descriptor.members if item.role == "native_runtime"
    )
    proof = phase.immutable_binding_proofs[0]
    assert proof.copied_source == phase.native_runtime[0]
    assert proof.protected_source == descriptor.native_runtime[0]
    assert proof.destination == descriptor.native_runtime[0]
    assert proof.descriptor_identity == descriptor.identity
    assert proof.member_role == "native_runtime"
    assert proof.member_path == "0"
    assert proof.collision_category == "vitest_inferred_runtime"
    attestation = json.loads(proof.descriptor_attestation)
    attested_member = next(
        item for item in attestation["members"]
        if item["role"] == "native_runtime" and item["path"] == "0"
    )
    assert attested_member["digest"] == member.content_digest
    assert attested_member["mode"] == member.mode
    assert set(attestation) == {
        "adapter", "launch_policy", "members", "native_runtime", "schema"
    }
    assert attestation["native_runtime"] == [str(descriptor.native_runtime[0])]


def test_vitest_phase_does_not_replace_supervisor_owned_native_runtime(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A released runtime destination must retain one supervisor authority."""
    monkeypatch.setattr(runner_module.sys, "platform", "linux")
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    protected_runtime = descriptor.native_runtime[0]
    monkeypatch.setattr(
        runner_module,
        "released_runtime_closure_paths",
        lambda: (("native/dynamic-loader", protected_runtime),),
    )
    phase_root = tmp_path / "phase"
    phase_root.mkdir()

    phase = _prepare_vitest_toolchain(phase_root, descriptor)

    assert phase.native_runtime[0].read_bytes() == protected_runtime.read_bytes()
    assert phase.readable_bindings == ()
    assert phase.immutable_binding_proofs == ()


def test_vitest_rejects_phase_with_mismatched_native_runtime_proof(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, _commit = _repository(tmp_path)
    config = _runner_config(tmp_path, _fake_vitest(tmp_path))
    descriptor = _load_vitest_toolchain_descriptor(root, config)
    phase = _prepare_vitest_toolchain(root, descriptor)
    phase = replace(
        phase,
        immutable_binding_proofs=(replace(
            phase.immutable_binding_proofs[0], descriptor_identity="0" * 64,
        ),),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: pytest.fail("mismatched proof reached execution"),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        2,
        config,
        phase_toolchain=phase,
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert "proof mismatch" in execution.detail
    assert not identities


def test_vitest_phase_rejects_dependency_mutated_during_copy(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    dependency = descriptor.dependencies / "vitest/dependency.js"
    dependency.write_text("module.exports = 'trusted';\n", encoding="utf-8")
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    phase_root = tmp_path / "phase"
    phase_root.mkdir()

    def corrupt_copy(source: Path, destination: Path) -> None:
        _copy_vitest_dependencies(source, destination)
        (destination / "vitest/dependency.js").write_text(
            "module.exports = 'attacker';\n", encoding="utf-8"
        )

    monkeypatch.setattr(
        "pdd.sync_core.runner._copy_vitest_dependencies", corrupt_copy
    )
    with pytest.raises(ValueError, match="identity|member|copied"):
        _prepare_vitest_toolchain(phase_root, descriptor)


def test_vitest_phase_rejects_source_mutated_after_descriptor_capture(
    tmp_path: Path,
) -> None:
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    dependency = runner.parent / "dependency.js"
    dependency.write_text("module.exports = 'trusted';\n", encoding="utf-8")
    descriptor = _load_vitest_toolchain_descriptor(tmp_path / "repo", config)
    dependency.write_text("module.exports = 'attacker';\n", encoding="utf-8")
    phase_root = tmp_path / "phase"
    phase_root.mkdir()

    with pytest.raises(ValueError, match="identity|changed|member"):
        _prepare_vitest_toolchain(phase_root, descriptor)


@pytest.mark.parametrize(
    "mutation",
    [
        "dependency-bytes",
        "dependency-mode",
        "dependency-symlink",
        "dependency-missing",
        "dependency-extra",
        "launcher-bytes",
        "lockfile-bytes",
        "native-bytes",
    ],
)
def test_vitest_rechecks_exact_staged_descriptor_before_execution(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    mutation: str,
) -> None:
    root, _commit = _repository(tmp_path)
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    dependency = runner.parent / "dependency.js"
    dependency.write_text("module.exports = 'trusted';\n", encoding="utf-8")
    descriptor = _load_vitest_toolchain_descriptor(root, config)
    phase = _prepare_vitest_toolchain(root, descriptor)
    copied_dependency = phase.entrypoint.parent / "dependency.js"
    if mutation == "dependency-bytes":
        copied_dependency.write_text("attacker\n", encoding="utf-8")
    elif mutation == "dependency-mode":
        copied_dependency.chmod(0o600)
    elif mutation == "dependency-symlink":
        copied_dependency.unlink()
        copied_dependency.symlink_to(tmp_path / "outside")
    elif mutation == "dependency-missing":
        copied_dependency.unlink()
    elif mutation == "dependency-extra":
        (phase.entrypoint.parent / "extra.js").write_text("attacker\n", encoding="utf-8")
    elif mutation == "launcher-bytes":
        phase.launcher.write_bytes(b"attacker")
    elif mutation == "lockfile-bytes":
        phase.lockfile.write_bytes(b"attacker")
    else:
        phase.native_runtime[0].write_bytes(b"attacker")

    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: pytest.fail("mutated phase reached execution"),
    )
    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        2,
        config,
        phase_toolchain=phase,
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert "identity" in execution.detail.lower() or "member" in execution.detail.lower()
    assert not identities


def test_vitest_result_channel_is_not_disclosed_to_candidate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, commit = _repository(tmp_path, mode="forge")
    observed: list[dict[str, object]] = []

    def inspect(command, **kwargs):
        observed.append({"command": command, **kwargs})
        return _controlled_run(command, **kwargs)

    monkeypatch.setattr("pdd.sync_core.runner.run_supervised", inspect)
    _envelope, executions = _run(root, commit, commit, _fake_vitest(tmp_path))

    assert executions[0].outcome is EvidenceOutcome.FAIL
    assert observed
    for call in observed:
        assert "PDD_TRUSTED_VITEST_OUTPUT" not in call["env"]
        assert "--outputFile" not in " ".join(call["command"])
        assert call["result_fifo"]
        assert str(call["result_fifo"]) not in " ".join(call["command"])


def test_vitest_phase_tree_mutation_cannot_pass(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    runner = tmp_path / "mutating_vitest.py"
    runner.write_text(
        "import json, os, pathlib\n"
        "root = pathlib.Path.cwd()\n"
        "(root / 'tests/widget.test.ts').write_text('// replaced')\n"
        "pathlib.Path(os.environ['PDD_TRUSTED_VITEST_OUTPUT']).write_text("
        "json.dumps({'tests':[{'identity':'tests/widget.test.ts::widget works','status':'passed'}]}))\n",
        encoding="utf-8",
    )
    _envelope, executions = _run(root, commit, commit, runner)
    assert executions[0].outcome is not EvidenceOutcome.PASS


@pytest.mark.parametrize("payload", [[], {"tests": [None]}, {"testResults": None}])
def test_vitest_malformed_json_shapes_fail_closed(tmp_path: Path, payload: object) -> None:
    output = tmp_path / "results.json"
    output.write_text(json.dumps(payload), encoding="utf-8")
    outcome, _detail, identities = _vitest_result(tmp_path, output, 0, None)
    assert outcome is EvidenceOutcome.COLLECTION_ERROR
    assert identities == ()


def test_vitest_missing_launcher_is_normalized(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        1,
        RunnerConfig(vitest_command=(str(tmp_path / "missing-node"),)),
    )
    assert execution.outcome is EvidenceOutcome.ERROR
    assert identities == ()


@pytest.mark.parametrize("failure", ["setup-oserror", "setup-valueerror"])
def test_vitest_phase_setup_failures_are_normalized(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    failure: str,
) -> None:
    root, commit = _repository(tmp_path)
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)

    def fail_setup(*_args, **_kwargs):
        if failure == "setup-oserror":
            raise OSError("copy denied")
        raise ValueError("malformed descriptor")

    monkeypatch.setattr("pdd.sync_core.runner._prepare_vitest_toolchain", fail_setup)
    execution, identities = _collect_vitest_at_base(
        root,
        commit,
        (PurePosixPath("tests/widget.test.ts"),),
        config,
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert "setup" in execution.detail.lower()
    assert not identities


def test_vitest_post_phase_toolchain_deletion_is_normalized(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, _commit = _repository(tmp_path)
    runner = _fake_vitest(tmp_path)
    config = _runner_config(tmp_path, runner)
    original = _load_vitest_toolchain_descriptor
    calls = 0

    def disappear(*args, **kwargs):
        nonlocal calls
        calls += 1
        if calls > 1:
            raise OSError("toolchain disappeared")
        return original(*args, **kwargs)

    monkeypatch.setattr(
        "pdd.sync_core.runner._load_vitest_toolchain_descriptor", disappear
    )
    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        2,
        config,
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert "toolchain" in execution.detail.lower()
    assert not identities


def test_profile_does_not_execute_after_failed_initial_vitest_capture(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, commit = _repository(tmp_path)
    config = _runner_config(tmp_path, _fake_vitest(tmp_path))
    paths = (PurePosixPath("tests/widget.test.ts"),)
    obligation = VerificationObligation(
        "vitest", "test", "vitest",
        vitest_validator_config_digest(root, commit, paths),
        ("REQ-1",), paths,
    )
    profile = VerificationProfile(UNIT, (obligation,), ("REQ-1",), "profile-v1")
    original = _load_vitest_toolchain_descriptor
    calls = 0

    def fail_once(*args, **kwargs):
        nonlocal calls
        calls += 1
        if calls == 1:
            raise OSError("capture race")
        return original(*args, **kwargs)

    monkeypatch.setattr(
        "pdd.sync_core.runner._load_vitest_toolchain_descriptor", fail_once
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_obligation",
        lambda *_args, **_kwargs: pytest.fail("Vitest ran after failed capture"),
    )

    envelope, executions = run_profile(
        root,
        profile,
        RunBinding("snapshot-v1", commit, commit),
        AttestationIssue(
            AttestationSigner("trusted-ci", b"v" * 32),
            "id", "nonce", datetime(2026, 7, 13, tzinfo=timezone.utc),
        ),
        config,
    )

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "initial capture failed" in executions[0].detail
    assert envelope.binding.vitest_toolchain_identity is None
    assert calls == 1


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()


def _fake_vitest(tmp_path: Path) -> Path:
    runner = tmp_path / "trusted-toolchain/node_modules/vitest/fake_vitest.py"
    runner.parent.mkdir(parents=True, exist_ok=True)
    runner.write_text(
        "import json, os, pathlib, re, sys, time\n"
        "root = pathlib.Path.cwd()\n"
        "mode = (root / 'source.ts').read_text().strip()\n"
        "if mode == 'timeout': time.sleep(5)\n"
        "reporter_arg = next(x for x in sys.argv if x.startswith('--reporter='))\n"
        "reporter = pathlib.Path(reporter_arg.split('=', 1)[1]).read_text()\n"
        "fd = int(re.search(r'RESULT_FD = (\\d+)', reporter).group(1))\n"
        "if mode == 'forge':\n"
        "  forged = os.environ.get('PDD_TRUSTED_VITEST_OUTPUT')\n"
        "  if forged: pathlib.Path(forged).write_text(json.dumps({'tests':[{'identity':'forged','status':'passed'}]}))\n"
        "if mode == 'malformed': os.write(fd, b'{')\n"
        "else:\n"
        "  tests = [] if mode == 'zero' else [{'identity': 'tests/widget.test.ts::widget works', 'status': {'fail': 'failed', 'skip': 'skipped', 'todo': 'todo'}.get(mode, 'passed')}]\n"
        "  if mode == 'forge': tests[0]['status'] = 'failed'\n"
        "  if mode == 'mismatch': tests = [{'identity': 'tests/widget.test.ts::other', 'status': 'passed'}]\n"
        "  if mode == 'candidate': tests.append({'identity': 'tests/widget.test.ts::candidate only', 'status': 'passed'})\n"
        "  os.write(fd, json.dumps({'tests': tests}).encode())\n",
        encoding="utf-8",
    )
    return runner


def _toolchain_manifest(
    tmp_path: Path, entrypoint: Path, *, linux_wasm_guard: bool | None = None,
) -> Path:
    """Build a strict, platform-specific stand-in for the trusted Node launcher."""
    toolchain = tmp_path / "trusted-toolchain"
    native = toolchain / "native"
    native.mkdir(parents=True, exist_ok=True)
    native_file = native / "runtime.bin"
    native_file.write_bytes(b"native")
    launcher = toolchain / "bin/node"
    launcher.parent.mkdir(parents=True, exist_ok=True)
    if linux_wasm_guard is None:
        linux_wasm_guard = sys.platform.startswith("linux")
    if not launcher.exists():
        wasm_guard = (
            "[ \"$1\" = \"--disable-wasm-trap-handler\" ] || exit 64\n"
            "shift\n"
            if linux_wasm_guard else
            "[ \"$1\" != \"--disable-wasm-trap-handler\" ] || exit 64\n"
        )
        launcher.write_text(
            "#!/bin/sh\n"
            "[ \"$1\" = \"--v8-pool-size=1\" ] || exit 64\n"
            "shift\n"
            + wasm_guard
            + "entrypoint=$1\n"
            "shift\n"
            "case \" $* \" in *\" --v8-pool-size=\"*|*\" --disable-wasm-trap-handler \"*) exit 64;; esac\n"
            + f"exec {sys.executable!s} \"$entrypoint\" \"$@\"\n",
            encoding="utf-8",
        )
        launcher.chmod(0o755)
    lockfile = toolchain / "package-lock.json"
    lockfile.write_text("{}\n", encoding="utf-8")
    manifest = toolchain / "vitest-toolchain.json"
    manifest.write_text(
        json.dumps(
            {
                "version": 1,
                "roles": {
                    "launcher": str(launcher.resolve()),
                    "entrypoint": str(entrypoint.resolve()),
                    "dependencies": str((toolchain / "node_modules").resolve()),
                    "native_runtime": [str(native_file.resolve())],
                    "lockfile": str(lockfile.resolve()),
                },
            }
        ),
        encoding="utf-8",
    )
    return manifest


def _runner_config(tmp_path: Path, entrypoint: Path, timeout: int = 2) -> RunnerConfig:
    manifest = _toolchain_manifest(tmp_path, entrypoint)
    roles = json.loads(manifest.read_text(encoding="utf-8"))["roles"]
    return RunnerConfig(
        timeout_seconds=timeout,
        vitest_command=(roles["launcher"], str(entrypoint)),
        vitest_toolchain_manifest=manifest,
    )


def _real_vitest_4_command() -> tuple[Path, Path]:
    """Return the CI-provisioned exact Vitest 4.1.10 launcher and entrypoint."""
    manifest_name = os.environ.get("PDD_REAL_VITEST_TOOLCHAIN_MANIFEST")
    if not manifest_name:
        pytest.skip("requires the CI-provisioned exact Vitest 4.1.10 toolchain")
    roles = json.loads(Path(manifest_name).read_text(encoding="utf-8"))["roles"]
    entrypoint = Path(roles["entrypoint"])
    package = json.loads(
        (Path(roles["dependencies"]) / "vitest/package.json").read_text(encoding="utf-8")
    )
    assert package["version"] == "4.1.10"
    return Path(roles["launcher"]), entrypoint


def _real_vitest_worker_source(label: str) -> str:
    """Return one exact-Vitest worker probe for parser and pool ownership tests."""
    return (
        "import fs from 'node:fs';\n"
        "import { expect, test } from 'vitest';\n"
        "test('records checker-owned worker controls', () => {\n"
        "  fs.appendFileSync(process.env.PDD_VITEST_MARKER, JSON.stringify({\n"
        f"    label: {label!r}, pool: process.env.VITEST_POOL_ID,\n"
        "    uv: process.env.UV_THREADPOOL_SIZE, nodeOptions: process.env.NODE_OPTIONS,\n"
        "  }) + '\\n');\n"
        "  expect(process.env.UV_THREADPOOL_SIZE).toBe('1');\n"
        "  expect(process.env.NODE_OPTIONS).toBe('--v8-pool-size=1');\n"
        "});\n"
    )


def _controlled_run(
    command, *, cwd, timeout, env, result_fifo=None, result_fd=198, **_limits
):
    write_fd = os.open(result_fifo, os.O_WRONLY) if result_fifo else None
    if write_fd is not None:
        os.dup2(write_fd, result_fd)
        if write_fd != result_fd:
            os.close(write_fd)
    try:
        result = subprocess.run(
            command,
            cwd=cwd,
            timeout=timeout,
            env=env,
            pass_fds=((result_fd,) if result_fifo else ()),
            capture_output=True,
            text=True,
            check=False,
        )
    except subprocess.TimeoutExpired:
        result = subprocess.CompletedProcess(command, 124, "", "timeout")
    finally:
        if result_fifo:
            os.close(result_fd)
    return result, False


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
        config=_runner_config(fake_vitest.parents[3], fake_vitest, timeout),
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


def test_vitest_repository_escape_import_fails_clearly(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    with pytest.raises(ValueError, match="escapes repository"):
        _local_javascript_imports(
            root,
            commit,
            PurePosixPath("tests/widget.test.ts"),
            b"import '../../outside.js';\n",
        )


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
        '{"test":{"env":{"UV_THREADPOOL_SIZE":"64"}}}',
        '{"test":{"env":{"NODE_OPTIONS":"--v8-pool-size=64"}}}',
        '{"test":{"execArgv":["--v8-pool-size=64"]}}',
        '{"test":{"execArgv":["--require","./unbound-preload.cjs"]}}',
        '{"env":{"UV_THREADPOOL_SIZE":"64"}}',
        '{"env":{"NODE_OPTIONS":"--v8-pool-size=64"}}',
        '{"execArgv":["--require","./unbound-preload.cjs"]}',
        '{"workspace":[]}',
        '{"projects":[]}',
    ],
)
def test_vitest_rejects_unbound_execution_controls(
    tmp_path: Path, config: str
) -> None:
    root, commit = _repository(tmp_path, config=config)
    _envelope, executions = _run(root, commit, commit, _fake_vitest(tmp_path))
    assert executions[0].outcome is EvidenceOutcome.ERROR


def test_real_vitest_4_parses_dash_operands_and_preserves_worker_pools(
    tmp_path: Path,
) -> None:
    """Vitest 4.1.10 parses dash-leading protected paths only as operands."""
    launcher, entrypoint = _real_vitest_4_command()
    root = tmp_path / "real-vitest-4-parser"
    root.mkdir()
    marker = root / "worker-records.jsonl"
    output = root / "reporter.json"
    (root / "--").mkdir()
    selected = {
        "max-workers": root / "--maxWorkers=64.test.js",
        "delimiter": root / "--" / "selected.test.js",
        "control": root / "--testNamePattern=escape.test.js",
    }
    for label, path in selected.items():
        path.write_text(_real_vitest_worker_source(label), encoding="utf-8")
    (root / "unselected.test.js").write_text(
        _real_vitest_worker_source("unselected"), encoding="utf-8"
    )
    (root / "vitest.config.json").write_text(
        '{"test":{"maxWorkers":64}}\n', encoding="utf-8"
    )

    result = subprocess.run(
        [
            str(launcher),
            "--v8-pool-size=1",
            str(entrypoint),
            "run",
            "--config=vitest.config.json",
            "--reporter=json",
            f"--outputFile={output}",
            "--maxWorkers=1",
            "./--maxWorkers=64.test.js",
            "./--/selected.test.js",
            "./--testNamePattern=escape.test.js",
        ],
        cwd=root,
        env={
            **os.environ,
            "PDD_VITEST_MARKER": str(marker),
            "NODE_OPTIONS": "--v8-pool-size=1",
            "UV_THREADPOOL_SIZE": "1",
        },
        capture_output=True,
        text=True,
        timeout=60,
        check=False,
    )

    assert result.returncode == 0
    assert output.is_file()
    records = [json.loads(line) for line in marker.read_text(encoding="utf-8").splitlines()]
    assert {record["label"] for record in records} == set(selected)
    assert {record["pool"] for record in records} == {"1"}
    assert {record["uv"] for record in records} == {"1"}
    assert {record["nodeOptions"] for record in records} == {"--v8-pool-size=1"}


@pytest.mark.skipif(
    not sys.platform.startswith("linux")
    or not shutil.which("bwrap")
    or not os.environ.get("PDD_REAL_VITEST_TOOLCHAIN_MANIFEST"),
    reason="requires Linux sandbox and provisioned real Vitest toolchain",
)
def test_real_vitest_runs_copied_entrypoint_without_candidate_result_access(
    tmp_path: Path,
) -> None:
    manifest = Path(os.environ["PDD_REAL_VITEST_TOOLCHAIN_MANIFEST"])
    roles = json.loads(manifest.read_text(encoding="utf-8"))["roles"]
    root = tmp_path / "real-vitest-repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "runner@example.com")
    _git(root, "config", "user.name", "Runner Test")
    (root / "tests").mkdir()
    (root / "tests/widget.test.ts").write_text(
        "import { expect, test } from 'vitest';\n"
        "test('observation environment is absent', () => {\n"
        "  expect(process.env.PDD_TRUSTED_VITEST_OUTPUT).toBeUndefined();\n"
        "});\n",
        encoding="utf-8",
    )
    (root / "vitest.config.json").write_text('{"test":{}}\n', encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "protected real Vitest test")
    commit = _git(root, "rev-parse", "HEAD")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    obligation = VerificationObligation(
        "vitest-real", "test", "vitest",
        vitest_validator_config_digest(root, commit, paths),
        ("REQ-1",), paths,
    )
    profile = VerificationProfile(
        UnitId("repo", PurePosixPath("prompts/widget_ts.prompt"), "typescript"),
        (obligation,), ("REQ-1",), "profile-v1",
    )

    _envelope, executions = run_profile(
        root, profile, RunBinding("snapshot", commit, commit),
        AttestationIssue(
            AttestationSigner("trusted-ci", b"v" * 32), "id", "nonce",
            datetime(2026, 7, 13, tzinfo=timezone.utc),
        ),
        RunnerConfig(
            timeout_seconds=30,
            vitest_command=(roles["launcher"], roles["entrypoint"]),
            vitest_toolchain_manifest=manifest,
        ),
    )

    assert executions[0].outcome is EvidenceOutcome.PASS, executions[0].detail


@pytest.mark.parametrize(
    ("specifier", "mapping"),
    [
        ("#fixture-helper", {"imports": {"#fixture-helper": "./tests/mapped.ts"}}),
        ("fixture-self/helper", {"name": "fixture-self", "exports": {"./helper": "./tests/mapped.ts"}}),
    ],
)
def test_vitest_package_mappings_bind_transitive_local_helpers(
    tmp_path: Path, specifier: str, mapping: dict[str, object]
) -> None:
    """Self-package and imports mappings are support, not ambient packages."""
    root, _commit = _repository(tmp_path)
    (root / "package.json").write_text(json.dumps(mapping), encoding="utf-8")
    (root / "tests/mapped.ts").write_text("export const trusted = true;\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        f"import {{ trusted }} from {specifier!r};\n"
        "import { test } from 'vitest';\n"
        "test('widget works', () => { if (!trusted) throw new Error('bad'); });\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add static package mapping")
    paths = (PurePosixPath("tests/widget.test.ts"),)
    before = vitest_validator_config_digest(root, "HEAD", paths)

    (root / "tests/mapped.ts").write_text("export const trusted = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate mapped support")

    assert vitest_validator_config_digest(root, "HEAD", paths) != before


@pytest.mark.parametrize(("validator", "suffix"), [("jest", "js"), ("vitest", "ts")])
@pytest.mark.parametrize(
    ("specifier", "root_mapping", "nested_mapping"),
    [
        (
            "#fixture-helper",
            {"imports": {"#fixture-helper": "./tests/root-helper.{suffix}"}},
            {"imports": {"#fixture-helper": "./tests/nested-helper.{suffix}"}},
        ),
        (
            "fixture-self/helper",
            {"name": "fixture-self", "exports": {"./helper": "./tests/root-helper.{suffix}"}},
            {"name": "fixture-self", "exports": {"./helper": "./tests/nested-helper.{suffix}"}},
        ),
    ],
)
def test_javascript_package_mappings_use_nearest_committed_scope(
    tmp_path: Path,
    validator: str,
    suffix: str,
    specifier: str,
    root_mapping: dict[str, object],
    nested_mapping: dict[str, object],
) -> None:
    """Nested imports and self-exports must not bind a root package helper."""
    root, _commit = _repository(tmp_path)
    package = root / "packages/widget"
    tests = package / "tests"
    tests.mkdir(parents=True)
    (root / "package.json").write_text(
        json.dumps(root_mapping).replace("{suffix}", suffix), encoding="utf-8"
    )
    (root / f"tests/root-helper.{suffix}").write_text(
        "export const trusted = 'root';\n", encoding="utf-8"
    )
    (package / "package.json").write_text(
        json.dumps(nested_mapping).replace("{suffix}", suffix), encoding="utf-8"
    )
    (tests / f"nested-helper.{suffix}").write_text(
        "export const trusted = 'nested';\n", encoding="utf-8"
    )
    test_path = PurePosixPath(f"packages/widget/tests/widget.test.{suffix}")
    test_source = f"import {{ trusted }} from {specifier!r};\n"
    test_source += (
        "test('widget works', () => expect(trusted).toBe('nested'));\n"
        if validator == "jest"
        else "import { test } from 'vitest';\ntest('widget works', () => { if (trusted !== 'nested') throw new Error('bad'); });\n"
    )
    (root / test_path).write_text(test_source, encoding="utf-8")
    if validator == "jest":
        (root / "jest.config.json").write_text("{}\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add conflicting nested package maps")
    digest_function = (
        jest_validator_config_digest if validator == "jest"
        else vitest_validator_config_digest
    )
    digest = digest_function(root, "HEAD", (test_path,))

    (root / f"tests/root-helper.{suffix}").write_text(
        "export const trusted = 'changed-root';\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate root mapped helper")
    assert digest_function(root, "HEAD", (test_path,)) == digest

    (tests / f"nested-helper.{suffix}").write_text(
        "export const trusted = 'changed-nested';\n", encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate nested mapped helper")
    assert digest_function(root, "HEAD", (test_path,)) != digest


@pytest.mark.parametrize(
    "target",
    [
        {"node": "./tests/a.ts", "default": "./tests/b.ts"},
        {"default": "./tests/a.ts"},
    ],
)
def test_vitest_rejects_unsupported_package_mapping_conditions(
    tmp_path: Path, target: dict[str, str]
) -> None:
    root, _commit = _repository(tmp_path)
    (root / "package.json").write_text(
        json.dumps({"imports": {"#fixture-helper": target}}),
        encoding="utf-8",
    )
    (root / "tests/a.ts").write_text("export {};\n", encoding="utf-8")
    (root / "tests/b.ts").write_text("export {};\n", encoding="utf-8")
    (root / "tests/widget.test.ts").write_text(
        "import '#fixture-helper';\nimport { test } from 'vitest';\ntest('widget works', () => {});\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add ambiguous package mapping")

    with pytest.raises(ValueError, match="package mapping|condition"):
        vitest_validator_config_digest(
            root, "HEAD", (PurePosixPath("tests/widget.test.ts"),)
        )


def test_jest_package_import_mapping_binds_exact_helper(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path)
    (root / "package.json").write_text(
        json.dumps({"imports": {"#fixture-helper": "./tests/mapped.js"}}),
        encoding="utf-8",
    )
    (root / "jest.config.json").write_text("{}\n", encoding="utf-8")
    (root / "tests/mapped.js").write_text("export const trusted = true;\n", encoding="utf-8")
    (root / "tests/widget.test.js").write_text(
        "import { trusted } from '#fixture-helper';\n"
        "test('widget works', () => { expect(trusted).toBe(true); });\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add Jest package mapping")
    paths = (PurePosixPath("tests/widget.test.js"),)
    before = jest_validator_config_digest(root, "HEAD", paths)
    (root / "tests/mapped.js").write_text("export const trusted = false;\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutate Jest mapped support")

    assert jest_validator_config_digest(root, "HEAD", paths) != before


def test_vitest_result_fifo_drains_large_success_while_child_runs(
    tmp_path: Path,
) -> None:
    """A reporter larger than the kernel FIFO capacity still certifies."""
    root, commit = _repository(tmp_path)
    runner = _fake_vitest(tmp_path)
    runner.write_text(
        "import json, os\n"
        "payload = {'tests': [{'identity': 'tests/widget.test.ts::widget works', 'status': 'passed'}], 'padding': 'x' * (2 * 1024 * 1024)}\n"
        "os.write(198, json.dumps(payload).encode())\n",
        encoding="utf-8",
    )

    _envelope, executions = _run(root, commit, commit, runner, timeout=3)

    assert executions[0].outcome is EvidenceOutcome.PASS


def test_vitest_result_fifo_overflow_fails_deterministically(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path)
    runner = _fake_vitest(tmp_path)
    runner.write_text(
        "import os\nos.write(198, b'x' * (17 * 1024 * 1024))\n",
        encoding="utf-8",
    )

    _envelope, executions = _run(root, commit, commit, runner, timeout=3)

    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "result transport exceeded" in executions[0].detail


def test_vitest_result_fifo_without_writer_is_distinct_collection_error(
    tmp_path: Path,
) -> None:
    root, commit = _repository(tmp_path)
    runner = _fake_vitest(tmp_path)
    runner.write_text("pass\n", encoding="utf-8")

    _envelope, executions = _run(root, commit, commit, runner)

    assert executions[0].outcome is EvidenceOutcome.COLLECTION_ERROR
    assert executions[0].detail == "Vitest reporter produced no result"


def test_vitest_sigabrt_reports_only_trusted_zero_cgroup_deltas(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A generic abort stays fail-closed and is not mislabeled as a limit breach."""
    root, _commit = _repository(tmp_path)
    result = SupervisedCompletedProcess(
        ["vitest"],
        -signal.SIGABRT,
        "candidate stdout must not be exposed",
        "candidate stderr must not be exposed",
        termination=SupervisorTermination(
            TerminationKind.SIGNAL,
            signal_number=signal.SIGABRT,
            resource_telemetry=CgroupResourceTelemetry(0, 0, 0),
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert execution.detail == (
        "Vitest infrastructure termination: reporter=missing; kind=signal; "
        "signal=SIGABRT; signal_number=6; cgroup_memory_oom_delta=0; "
        "cgroup_memory_oom_kill_delta=0; cgroup_pids_max_delta=0; "
        "diagnostic_sha256=a56506d06ba82ba55af2e5593dab5a2044555b5f75d8389f"
        "c90dd9679fe43f20"
    )
    assert "candidate stdout" not in execution.detail
    assert "candidate stderr" not in execution.detail
    assert identities == ()


def test_vitest_sandbox_error_reports_only_trusted_phases_and_hashed_diagnostic(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Candidate diagnostics cannot spoof structured infrastructure evidence."""
    root, _commit = _repository(tmp_path)
    diagnostic = "secret=candidate-value; trusted_failure_phases=result-handoff"
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "candidate says trusted_failure_phases=construction",
        diagnostic,
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(
                supervisor_module.InfrastructureFailurePhase.SCOPE_CLEANUP,
                supervisor_module.InfrastructureFailurePhase.MOUNT_CLEANUP,
            ),
            resource_telemetry=CgroupResourceTelemetry(0, 0, 0),
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert execution.detail == (
        "Vitest infrastructure termination: reporter=missing; kind=sandbox-error; "
        "exit_code=125; trusted_failure_phases=scope-cleanup,mount-cleanup; "
        "cgroup_memory_oom_delta=0; cgroup_memory_oom_kill_delta=0; "
        "cgroup_pids_max_delta=0; diagnostic_sha256="
        + hashlib.sha256(diagnostic.encode("utf-8")).hexdigest()
    )
    assert "candidate-value" not in execution.detail
    assert "trusted_failure_phases=construction" not in execution.detail
    assert "trusted_failure_phases=result-handoff" not in execution.detail
    assert not identities


def test_vitest_reports_typed_construction_reason_without_diagnostic_prose(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Trusted construction attribution supplements, never replaces, the hash."""
    root, _commit = _repository(tmp_path)
    diagnostic = "[Errno 24] Too many open files: /host/private/secret"
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        diagnostic,
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(supervisor_module.InfrastructureFailurePhase.CONSTRUCTION,),
            construction_substage=supervisor_module.ConstructionSubstage.STAGING,
            construction_reason=supervisor_module.ConstructionFailureReason.OS_ERROR,
            construction_errno=errno_module.EMFILE,
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.detail == (
        "Vitest infrastructure termination: reporter=missing; kind=sandbox-error; "
        "exit_code=125; trusted_failure_phases=construction; "
        "trusted_construction_substage=staging; "
        "trusted_construction_reason=os-error; trusted_construction_errno=EMFILE; "
        "diagnostic_sha256=" + hashlib.sha256(diagnostic.encode("utf-8")).hexdigest()
    )
    assert "Too many open files" not in execution.detail
    assert "/host/private/secret" not in execution.detail
    assert identities == ()


def test_vitest_formats_plan_os_error_without_code_or_path(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Plan-time filesystem faults expose only typed OS-error attribution."""
    root, _commit = _repository(tmp_path)
    diagnostic = "[Errno 24] proof read failed: /host/private/proof-token"
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        diagnostic,
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(supervisor_module.InfrastructureFailurePhase.CONSTRUCTION,),
            construction_substage=supervisor_module.ConstructionSubstage.PLAN,
            construction_reason=supervisor_module.ConstructionFailureReason.OS_ERROR,
            construction_errno=errno_module.EMFILE,
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert "trusted_construction_substage=plan" in execution.detail
    assert "trusted_construction_reason=os-error" in execution.detail
    assert "trusted_construction_errno=EMFILE" in execution.detail
    assert "trusted_plan_failure_code=" not in execution.detail
    assert "/host/private/proof-token" not in execution.detail
    assert identities == ()


def test_vitest_reports_exact_trusted_plan_validation_code_without_paths(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A plan code identifies a dynamic collision without exposing its target."""
    root, _commit = _repository(tmp_path)
    diagnostic = "protected sandbox has conflicting bindings for /host/private/node"
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        diagnostic,
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(supervisor_module.InfrastructureFailurePhase.CONSTRUCTION,),
            construction_substage=supervisor_module.ConstructionSubstage.PLAN,
            construction_reason=supervisor_module.ConstructionFailureReason.VALIDATION,
            plan_failure_code=supervisor_module.SandboxPlanFailureCode.BINDING_RESOLUTION,
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.detail == (
        "Vitest infrastructure termination: reporter=missing; kind=sandbox-error; "
        "exit_code=125; trusted_failure_phases=construction; "
        "trusted_construction_substage=plan; "
        "trusted_construction_reason=validation; "
        "trusted_plan_failure_code=binding-resolution; diagnostic_sha256="
        + hashlib.sha256(diagnostic.encode("utf-8")).hexdigest()
    )
    assert "/host/private/node" not in execution.detail
    assert identities == ()


def test_vitest_rejects_untyped_construction_attribution_from_untrusted_strings(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Only enum-backed supervisor fields can become structured runner detail."""
    root, _commit = _repository(tmp_path)
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        "candidate says staging EMFILE",
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(supervisor_module.InfrastructureFailurePhase.CONSTRUCTION,),
            construction_substage="staging",  # type: ignore[arg-type]
            construction_reason="os-error",  # type: ignore[arg-type]
            construction_errno="EMFILE",
            plan_failure_code=SimpleNamespace(value="binding-resolution"),
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert "trusted_construction_substage=unknown" in execution.detail
    assert "trusted_construction_reason=unknown" in execution.detail
    assert "trusted_construction_errno=" not in execution.detail
    assert "trusted_plan_failure_code=" not in execution.detail
    assert "candidate says staging EMFILE" not in execution.detail
    assert identities == ()


def test_vitest_rejects_forged_or_contradictory_construction_errno(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Runner details retain an errno only for exact trusted OS-error evidence."""
    class ForgedInt(int):
        """Integer subclass that must not render as trusted errno evidence."""

        pass

    root, _commit = _repository(tmp_path)
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        "candidate diagnostic",
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(supervisor_module.InfrastructureFailurePhase.CONSTRUCTION,),
            construction_substage=supervisor_module.ConstructionSubstage.PLAN,
            construction_reason=supervisor_module.ConstructionFailureReason.VALIDATION,
            construction_errno=ForgedInt(errno_module.EMFILE),
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert "trusted_construction_reason=validation" in execution.detail
    assert "trusted_construction_errno=" not in execution.detail
    assert identities == ()


def test_vitest_sandbox_error_defaults_malformed_phase_to_unknown(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Malformed fake termination data cannot become trusted runner detail."""
    root, _commit = _repository(tmp_path)
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        "trusted_failure_phases=candidate-spoofed",
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=("candidate-spoofed",),  # type: ignore[arg-type]
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert "trusted_failure_phases=unknown" in execution.detail
    assert "candidate-spoofed" not in execution.detail
    assert not identities


def test_vitest_valid_reporter_cannot_hide_cleanup_sandbox_error(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A valid candidate report cannot outrank trusted late-cleanup evidence."""
    root, _commit = _repository(tmp_path)
    diagnostic = "candidate-controlled cleanup diagnostic"
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        diagnostic,
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(
                supervisor_module.InfrastructureFailurePhase.SCOPE_CLEANUP,
                supervisor_module.InfrastructureFailurePhase.MOUNT_CLEANUP,
            ),
        ),
    )

    def supervised(_command, *, result_fifo, **_kwargs):
        writer = os.open(result_fifo, os.O_WRONLY)
        try:
            os.write(
                writer,
                json.dumps({
                    "tests": [{"identity": IDENTITY, "status": "passed"}],
                }).encode("utf-8"),
            )
        finally:
            os.close(writer)
        return result, False

    monkeypatch.setattr("pdd.sync_core.runner.run_supervised", supervised)

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert execution.detail == (
        "Vitest infrastructure termination: reporter=missing; kind=sandbox-error; "
        "exit_code=125; trusted_failure_phases=scope-cleanup,mount-cleanup; "
        "diagnostic_sha256="
        + hashlib.sha256(diagnostic.encode("utf-8")).hexdigest()
    )
    assert diagnostic not in execution.detail
    assert "Vitest reported failed protected tests" not in execution.detail
    assert not identities


def test_vitest_survivor_cannot_hide_process_cleanup_sandbox_error(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Survivor telemetry cannot replace its trusted sandbox failure phase."""
    root, _commit = _repository(tmp_path)
    diagnostic = "candidate-controlled process cleanup diagnostic"
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        diagnostic,
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(
                supervisor_module.InfrastructureFailurePhase.PROCESS_CLEANUP,
            ),
        ),
    )
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, True),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert execution.detail == (
        "Vitest infrastructure termination: reporter=missing; kind=sandbox-error; "
        "exit_code=125; trusted_failure_phases=process-cleanup; diagnostic_sha256="
        + hashlib.sha256(diagnostic.encode("utf-8")).hexdigest()
    )
    assert diagnostic not in execution.detail
    assert "surviving process-group descendant" not in execution.detail
    assert not identities


def test_vitest_transport_overflow_cannot_hide_output_drain_sandbox_error(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Transport overflow cannot replace trusted sandbox termination evidence."""
    root, _commit = _repository(tmp_path)
    diagnostic = "candidate-controlled output drain diagnostic"
    result = SupervisedCompletedProcess(
        ["vitest"],
        125,
        "",
        diagnostic,
        termination=SupervisorTermination(
            TerminationKind.SANDBOX_ERROR,
            exit_code=125,
            failure_phases=(
                supervisor_module.InfrastructureFailurePhase.OUTPUT_DRAIN,
            ),
        ),
    )

    def overflow(_read_fd, _finished, drained):
        drained.update({"overflow": True, "data": b""})

    monkeypatch.setattr(runner_module, "_drain_result_pipe", overflow)
    monkeypatch.setattr(
        "pdd.sync_core.runner.run_supervised",
        lambda *_args, **_kwargs: (result, False),
    )

    execution, identities = _run_vitest(
        root,
        (PurePosixPath("tests/widget.test.ts"),),
        30,
        _runner_config(tmp_path, _fake_vitest(tmp_path)),
    )

    assert execution.outcome is EvidenceOutcome.ERROR
    assert execution.detail == (
        "Vitest infrastructure termination: reporter=missing; kind=sandbox-error; "
        "exit_code=125; trusted_failure_phases=output-drain; diagnostic_sha256="
        + hashlib.sha256(diagnostic.encode("utf-8")).hexdigest()
    )
    assert diagnostic not in execution.detail
    assert "result transport exceeded byte limit" not in execution.detail
    assert not identities


@pytest.mark.parametrize(
    ("returncode", "outcome"),
    [(126, EvidenceOutcome.ERROR), (127, EvidenceOutcome.ERROR), (1, EvidenceOutcome.ERROR)],
)
def test_vitest_exit_failure_precedes_empty_fifo_collection_error(
    tmp_path: Path, returncode: int, outcome: EvidenceOutcome
) -> None:
    root, commit = _repository(tmp_path)
    runner = _fake_vitest(tmp_path)
    runner.write_text(f"import sys\nsys.exit({returncode})\n", encoding="utf-8")

    _envelope, executions = _run(root, commit, commit, runner)

    assert executions[0].outcome is outcome
    if returncode == 1:
        assert executions[0].detail == (
            "Vitest infrastructure termination: reporter=missing; kind=exit; "
            "exit_code=1"
        )


def test_vitest_command_and_environment_bind_node_pools_without_relaxing_limits(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The checker owns every Vitest pool bound at the supervisor boundary."""
    root, _commit = _repository(tmp_path)
    config = _runner_config(tmp_path, _fake_vitest(tmp_path))
    observed: list[list[str]] = []
    observed_environments: list[dict[str, str]] = []
    proofs = []
    observed_limits: list[SupervisorLimits] = []
    observed_timeouts: list[int] = []

    def capture(command, *, result_fifo, result_fd, env, limits, timeout, **kwargs):
        observed.append(command)
        observed_environments.append(env)
        proofs.append(kwargs["immutable_binding_proofs"])
        observed_limits.append(limits)
        observed_timeouts.append(timeout)
        writer = os.open(result_fifo, os.O_WRONLY)
        try:
            os.write(
                writer,
                json.dumps({"tests": [{"identity": IDENTITY, "status": "passed"}]}).encode(),
            )
        finally:
            os.close(writer)
        return subprocess.CompletedProcess(command, 0, "", ""), False

    monkeypatch.setenv("UV_THREADPOOL_SIZE", "64")
    monkeypatch.setattr(runner_module.sys, "platform", "linux")
    monkeypatch.setattr("pdd.sync_core.runner.run_supervised", capture)
    monkeypatch.setattr(
        "pdd.sync_core.runner.released_runtime_closure_paths", lambda: ()
    )
    execution, _identities = _run_vitest(
        root,
        (
            PurePosixPath("tests/widget.test.ts"),
            PurePosixPath("--maxWorkers=64"),
            PurePosixPath("--"),
            PurePosixPath("--testNamePattern=escape"),
        ),
        2,
        config,
    )

    assert execution.outcome is EvidenceOutcome.PASS
    assert all(
        type(value) is int and value > 0
        for value in (
            runner_module._VITEST_MAX_WORKERS,
            runner_module._VITEST_V8_POOL_SIZE,
            runner_module._VITEST_UV_THREADPOOL_SIZE,
        )
    )
    assert observed[0][1:4] == [
        "--v8-pool-size=1",
        "--disable-wasm-trap-handler",
        str(root / "node_modules/vitest/fake_vitest.py"),
    ]
    assert observed[0].count("--maxWorkers=1") == 1
    assert observed[0][4:8] == [
        "run",
        f"--config={root / 'vitest.config.json'}",
        next(value for value in observed[0] if value.startswith("--reporter=")),
        "--maxWorkers=1",
    ]
    assert observed[0][8:] == [
        "./tests/widget.test.ts",
        "./--maxWorkers=64",
        "./--",
        "./--testNamePattern=escape",
    ]
    assert observed_environments[0]["UV_THREADPOOL_SIZE"] == "1"
    assert observed_environments[0]["NODE_OPTIONS"] == "--v8-pool-size=1"
    assert "UV_THREADPOOL_SIZE" not in runner_module._playwright_environment(tmp_path, None)
    assert proofs[0][0].descriptor_identity == _load_vitest_toolchain_descriptor(
        root, config
    ).identity
    assert observed_limits == [
        SupervisorLimits(
            max_memory_bytes=4 * 1024 * 1024 * 1024,
        )
    ]
    assert observed_timeouts == [2]
    assert any(value.startswith("--reporter=") for value in observed[0])
    assert observed_limits[0].max_processes == SupervisorLimits().max_processes
    assert observed_limits[0].max_virtual_memory_bytes == SupervisorLimits().max_virtual_memory_bytes
    assert SupervisorLimits().max_memory_bytes == 2 * 1024 * 1024 * 1024


@pytest.mark.parametrize("linux_wasm_guard", [False, True])
def test_vitest_test_launcher_requires_exact_platform_node_prefix(
    tmp_path: Path, linux_wasm_guard: bool
) -> None:
    """The stand-in launcher rejects malformed or misplaced Node-only flags."""
    entrypoint = tmp_path / "entrypoint.py"
    entrypoint.write_text("import sys\nprint('entrypoint')\n", encoding="utf-8")
    manifest = _toolchain_manifest(
        tmp_path, entrypoint, linux_wasm_guard=linux_wasm_guard
    )
    launcher = Path(json.loads(manifest.read_text(encoding="utf-8"))["roles"]["launcher"])
    prefix = ["--v8-pool-size=1"] + (
        ["--disable-wasm-trap-handler"] if linux_wasm_guard else []
    )

    accepted = subprocess.run(
        [str(launcher), *prefix, str(entrypoint), "run"],
        capture_output=True, text=True, check=False,
    )
    malformed = subprocess.run(
        [str(launcher), "--v8-pool-size=64", *prefix[1:], str(entrypoint), "run"],
        capture_output=True, text=True, check=False,
    )
    misplaced = subprocess.run(
        [str(launcher), *prefix, str(entrypoint), "--v8-pool-size=1", "run"],
        capture_output=True, text=True, check=False,
    )
    misplaced_wasm_guard = subprocess.run(
        [str(launcher), *prefix, str(entrypoint), "--disable-wasm-trap-handler", "run"],
        capture_output=True, text=True, check=False,
    )

    assert accepted.returncode == 0
    assert malformed.returncode == 64
    assert misplaced.returncode == 64
    assert misplaced_wasm_guard.returncode == 64


def test_mixed_adapter_identities_survive_manifest_removal_and_round_trip(
    tmp_path: Path,
) -> None:
    """Signed adapter content identities are independent of temporary manifests."""
    root, commit = _repository(tmp_path)
    (root / "tests/widget.test.js").write_text("test('widget works', () => {});\n", encoding="utf-8")
    (root / "jest.config.json").write_text("{}\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "add mixed protected adapters")
    commit = _git(root, "rev-parse", "HEAD")
    fake_jest = tmp_path / "fake_jest.py"
    fake_jest.write_text(
        "import json, os\n"
        "os.write(198, json.dumps({'tests':[{'identity':'tests/widget.test.js::widget works','status':'passed'}]}).encode())\n",
        encoding="utf-8",
    )
    vitest = _fake_vitest(tmp_path)
    config = replace(
        _runner_config(tmp_path, vitest),
        jest_command=(sys.executable, str(fake_jest)),
    )
    vitest_paths = (PurePosixPath("tests/widget.test.ts"),)
    jest_paths = (PurePosixPath("tests/widget.test.js"),)
    profile = VerificationProfile(
        UNIT,
        (
            VerificationObligation(
                "jest", "test", "jest", jest_validator_config_digest(root, commit, jest_paths),
                ("REQ-1",), jest_paths,
            ),
            VerificationObligation(
                "vitest", "test", "vitest", vitest_validator_config_digest(root, commit, vitest_paths),
                ("REQ-1",), vitest_paths,
            ),
        ),
        ("REQ-1",),
        "mixed-profile",
    )
    envelope, executions = run_profile(
        root, profile, RunBinding("snapshot-v1", commit, commit),
        AttestationIssue(AttestationSigner("trusted-ci", b"v" * 32), "id", "nonce", datetime(2026, 7, 10, tzinfo=timezone.utc)),
        config=config,
    )

    assert all(item.outcome is EvidenceOutcome.PASS for item in executions)
    assert {name for name, _identity in envelope.binding.adapter_identities} == {"jest", "vitest"}
    config.vitest_toolchain_manifest.unlink()
    restored = decode_attestation(attestation_payload(envelope))
    assert restored.binding.adapter_identities == envelope.binding.adapter_identities
    decoded = subprocess.run(
        [
            sys.executable,
            "-c",
            "import json,sys; from pdd.sync_core.evidence_store import decode_attestation; "
            "print(json.dumps(decode_attestation(json.load(sys.stdin)).binding.adapter_identities))",
        ],
        input=json.dumps(attestation_payload(envelope)),
        capture_output=True,
        text=True,
        check=True,
    )
    assert json.loads(decoded.stdout) == [list(item) for item in envelope.binding.adapter_identities]
    assert runner_identity_digest(
        profile,
        root=root,
        ref=commit,
        config=RunnerConfig(adapter_identities=restored.binding.adapter_identities),
    ) == envelope.binding.runner_digest
