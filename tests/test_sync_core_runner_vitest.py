"""Contract tests for the fail-closed trusted Vitest adapter."""

import json
import os
import shutil
import subprocess
import sys
from dataclasses import replace
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
    vitest_validator_config_digest,
)


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

    assert descriptor.launcher.name == "python"
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


def _toolchain_manifest(tmp_path: Path, entrypoint: Path) -> Path:
    toolchain = tmp_path / "trusted-toolchain"
    native = toolchain / "native"
    native.mkdir(parents=True, exist_ok=True)
    native_file = native / "runtime.bin"
    native_file.write_bytes(b"native")
    launcher = toolchain / "bin/python"
    launcher.parent.mkdir(parents=True, exist_ok=True)
    if not launcher.exists():
        shutil.copy2(sys.executable, launcher)
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
        "test('result channel is private', () => {\n"
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
