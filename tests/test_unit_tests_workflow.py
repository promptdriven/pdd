"""Structural contracts for the Unit Tests GitHub Actions workflow."""

from __future__ import annotations

import json
import importlib.util
import math
import os
import re
import shlex
import stat
import struct
import subprocess
import sys
from collections.abc import Callable
from pathlib import Path

import pytest
import yaml


WORKFLOW_PATH = (
    Path(__file__).resolve().parents[1] / ".github" / "workflows" / "unit-tests.yml"
)
REPO_ROOT = WORKFLOW_PATH.parents[2]
WORKFLOW_HELPER_PATH = REPO_ROOT / ".github/toolchains/playwright_manifest.py"
WORKFLOW_HELPER_COMMAND = (
    'python .github/toolchains/playwright_manifest.py --toolchain "$toolchain" '
    '--browser-cache "$browser_cache" --environment-file "$GITHUB_ENV"'
)
SETUP_AND_FOCUSED_SECONDS = 16 * 60 + 37
BROAD_SUITE_SECONDS = 30 * 60
FULL_JOB_SECONDS = SETUP_AND_FOCUSED_SECONDS + BROAD_SUITE_SECONDS
HEADROOM_FRACTION = 0.50
REQUIRED_TIMEOUT_MINUTES = math.ceil(
    FULL_JOB_SECONDS * (1 + HEADROOM_FRACTION) / 60
)
LINUX_JOB_ID = "unit-tests"
APPROVED_DRAFT_GUARD = "github.event.pull_request.draft != true"
PROVISION_STEP_NAME = "Provision and verify protected Linux sandbox"
HOSTED_STEP_NAME = "Run real protected Playwright and authenticated supervisor protocols"
HELD_NAMESPACE_SMOKE_STEP_NAME = "Verify held-namespace transport and FD-only cleanup smoke"
FOCUSED_STEP_NAME = "Run focused protected-runner tests"
BROAD_SUITE_STEP_NAME = "Run unit tests"
HOSTED_SUPERVISOR_NODE = "tests/test_sync_core_supervisor.py::"
REQUIRED_HOSTED_NODES = (
    "tests/test_sync_core_runner_playwright.py::"
    "test_real_playwright_1_55_config_suffixes_collect_and_use_config_dir",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_authenticated_termination_and_cleanup",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_adapter_environment_handoff[pytest]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_adapter_environment_handoff[vitest]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_adapter_environment_handoff[playwright]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[normal-hierarchy-environment]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[parent-exit-before-start]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[parent-exit-during-execution]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[parent-exit-after-result]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[stalled-result-reader]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[missing-ack]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[duplicate-ack]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[trailing-frame]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[trailing-raw]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[reordered-extra]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[stalled-observation-reader]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[initial-scan-failure]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[initial-watched-assertion-failure]",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[fd-only-namespace-holder-cleanup]",
    "tests/test_sync_core_supervisor.py::"
    "test_simultaneous_high_volume_stdio_has_one_aggregate_bound",
)
EXPECTED_PROVISION_COMMANDS = (
    ("set", "-euo", "pipefail"),
    ("sudo", "apt-get", "update"),
    ("sudo", "apt-get", "install", "--yes", "bubblewrap"),
    ("command", "-v", "bwrap"),
    ("command", "-v", "systemd-run"),
    ("command", "-v", "unshare"),
    ("command", "-v", "nsenter"),
    ("sudo", "-n", "true"),
    ("bwrap", "--version"),
)
EXPECTED_HOSTED_COMMAND = (
    "pytest", "-q", *REQUIRED_HOSTED_NODES, "--timeout=90",
)
REQUIRED_HELD_NAMESPACE_SMOKE_NODES = (
    f"{HOSTED_SUPERVISOR_NODE}"
    "test_held_namespace_scan_memfd_is_sealed_and_only_transport_fds_inherit",
    f"{HOSTED_SUPERVISOR_NODE}"
    "test_namespace_scanner_rejects_exact_eof_trailing_oversized_and_malformed_frames",
    f"{HOSTED_SUPERVISOR_NODE}test_namespace_scanner_rejects_truncated_canonical_frame",
    f"{HOSTED_SUPERVISOR_NODE}test_real_linux_playwright_descriptor_exact_chain"
    "[fd-only-namespace-holder-cleanup]",
)
EXPECTED_HELD_NAMESPACE_SMOKE_COMMAND = (
    "timeout", "--signal=TERM", "--kill-after=10s", "290s",
    "pytest", "-vv", "-s", *REQUIRED_HELD_NAMESPACE_SMOKE_NODES,
    "--timeout=60",
)
EXPECTED_BROAD_SUITE_COMMAND = (
    "pytest", "tests/",
    "-m", "not integration and not e2e and not real and not private_prompt",
    "-q", "--tb=short", "--timeout=60", "-n", "auto",
    "--ignore=tests/commands/test_connect.py",
    "--ignore=tests/test_bug_to_unit_test.py",
    "--ignore=tests/test_context_generator.py",
    "--ignore=tests/test_crash_main.py",
    "--ignore=tests/test_generate_test.py",
    "--ignore=tests/test_fix_error_loop.py",
    "--ignore=tests/test_llm_invoke.py",
    "--deselect=tests/test_setup_tool.py::test_create_api_env_script_with_special_characters_zsh",
    (
        "--deselect=tests/test_setup_tool.py::"
        "test_create_api_env_script_with_common_problematic_characters"
    ),
)


def _workflow() -> dict:
    """Load the workflow with YAML semantics, never comment-sensitive text matching."""
    loaded = yaml.safe_load(WORKFLOW_PATH.read_text(encoding="utf-8"))
    assert isinstance(loaded, dict)
    return loaded


def test_workflow_loads_after_current_directory_changes(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The committed workflow path must not depend on a worker's current directory."""
    monkeypatch.chdir(tmp_path)

    assert _workflow()["jobs"][LINUX_JOB_ID]["runs-on"] == "ubuntu-latest"


def _named_step(job: dict, name: str) -> dict:
    """Return exactly one active, stable-named workflow step."""
    steps = job.get("steps")
    assert isinstance(steps, list)
    matches = [step for step in steps if isinstance(step, dict) and step.get("name") == name]
    assert len(matches) == 1, name
    return matches[0]


def _shell_commands(command: object) -> tuple[tuple[str, ...], ...]:
    """Parse top-level shell lines while excluding comments and heredoc bodies."""
    assert isinstance(command, str)
    commands = []
    continuation = ""
    heredoc_end = None
    for line in command.splitlines():
        if heredoc_end is not None:
            if line == heredoc_end:
                heredoc_end = None
            continue
        current = continuation + line
        if current.rstrip().endswith("\\"):
            continuation = current.rstrip()[:-1] + " "
            continue
        continuation = ""
        tokens = tuple(shlex.split(current, comments=True, posix=True))
        if not tokens:
            continue
        commands.append(tokens)
        marker = re.search(r"<<-?\s*['\"]?([A-Za-z_][A-Za-z0-9_]*)", current)
        if marker:
            heredoc_end = marker.group(1)
    assert heredoc_end is None
    assert not continuation
    return tuple(commands)


def _assert_enabled(subject: dict) -> None:
    """Require unconditional execution with ordinary failure propagation."""
    assert "if" not in subject
    assert "continue-on-error" not in subject


def _assert_approved_draft_guard(job: dict) -> None:
    """Require the reviewed job-level draft guard without equivalent rewrites."""
    assert job.get("if") == APPROVED_DRAFT_GUARD
    assert "continue-on-error" not in job


def _assert_hosted_linux_contract(workflow: dict) -> None:
    """Check the exact active hosted Linux command and prerequisites."""
    jobs = workflow.get("jobs")
    assert isinstance(jobs, dict)
    job = jobs.get(LINUX_JOB_ID)
    assert isinstance(job, dict)
    assert job.get("runs-on") == "ubuntu-latest"
    _assert_approved_draft_guard(job)

    steps = job.get("steps")
    assert isinstance(steps, list)
    provision = _named_step(job, PROVISION_STEP_NAME)
    hosted = _named_step(job, HOSTED_STEP_NAME)
    assert steps.index(provision) < steps.index(hosted)
    _assert_enabled(provision)
    _assert_enabled(hosted)

    provision_commands = _shell_commands(provision.get("run"))
    assert provision_commands[:len(EXPECTED_PROVISION_COMMANDS)] == (
        EXPECTED_PROVISION_COMMANDS
    )

    hosted_commands = _shell_commands(hosted.get("run"))
    assert hosted_commands == (EXPECTED_HOSTED_COMMAND,)
    pytest_command = hosted_commands[0]
    selectors = []
    for argument in pytest_command[1:]:
        if argument in {"-q", "--timeout=90"}:
            continue
        assert not argument.startswith("-"), argument
        selectors.append(argument)
    assert tuple(selectors) == REQUIRED_HOSTED_NODES
    assert len(selectors) == len(set(selectors))


def _hosted_command(workflow: dict) -> tuple[dict, str]:
    job = workflow["jobs"][LINUX_JOB_ID]
    hosted = _named_step(job, HOSTED_STEP_NAME)
    return hosted, hosted["run"]


def _append_hosted_argument(command: str, argument: str) -> str:
    """Append one active argument before the frozen pytest timeout argument."""
    return command.replace("--timeout=90", f"{argument} \\\n            --timeout=90")


def _remove_hosted_node_line(command: str) -> str:
    """Physically remove one complete required selector line."""
    node = REQUIRED_HOSTED_NODES[6]
    lines = command.splitlines(keepends=True)
    matches = [index for index, line in enumerate(lines) if node in line]
    assert len(matches) == 1
    del lines[matches[0]]
    mutated = "".join(lines)
    assert mutated != command and node not in mutated
    return mutated


def test_unit_tests_timeout_covers_documented_full_job_budget() -> None:
    """The broad-suite margin must account for required prior job work too."""
    workflow_text = WORKFLOW_PATH.read_text(encoding="utf-8")
    timeout_minutes = _workflow()["jobs"][LINUX_JOB_ID]["timeout-minutes"]

    assert isinstance(timeout_minutes, int)
    assert timeout_minutes > 0
    assert timeout_minutes >= REQUIRED_TIMEOUT_MINUTES, (
        "Unit Tests timeout must cover the 16m37s setup/protected/browser budget "
        "plus the ~30 minute broad suite with 50% headroom "
        f"({REQUIRED_TIMEOUT_MINUTES} minutes minimum)."
    )
    assert "16m37s" in workflow_text
    assert "~30 minutes" in workflow_text
    assert "46m37s" in workflow_text
    assert "50% headroom" in workflow_text


def test_unit_tests_requires_complete_privileged_descriptor_matrix() -> None:
    """The active hosted Linux lane has one exact frozen pytest node set."""
    _assert_hosted_linux_contract(_workflow())


def test_unit_tests_held_namespace_smoke_is_bounded_and_precedes_focused_suite() -> None:
    """The Linux transport smoke is exact, fail-fast, and runs before the broad lane."""
    workflow = _workflow()
    job = workflow["jobs"][LINUX_JOB_ID]
    steps = job["steps"]
    smoke = _named_step(job, HELD_NAMESPACE_SMOKE_STEP_NAME)
    focused = _named_step(job, FOCUSED_STEP_NAME)

    _assert_enabled(smoke)
    assert steps.index(smoke) < steps.index(focused)
    assert _shell_commands(smoke.get("run")) == (
        EXPECTED_HELD_NAMESPACE_SMOKE_COMMAND,
    )


def test_unit_tests_broad_suite_keeps_xdist_with_bounded_reporting() -> None:
    """The broad lane retains parallel coverage without per-test verbose output."""
    workflow = _workflow()
    job = workflow["jobs"][LINUX_JOB_ID]
    suite = _named_step(job, BROAD_SUITE_STEP_NAME)

    _assert_enabled(suite)
    assert _shell_commands(suite.get("run")) == (EXPECTED_BROAD_SUITE_COMMAND,)


def test_unit_tests_protected_smokes_use_credential_free_environment() -> None:
    """Hosted protected setup never forwards the runner's ambient credentials."""
    workflow_text = WORKFLOW_PATH.read_text(encoding="utf-8")

    assert "env=dict(os.environ)" not in workflow_text
    assert workflow_text.count("env=environment") == 10


def test_unit_workflow_resolves_playwright_native_runtime_paths() -> None:
    """The Unit manifest must invoke the shared canonical closure producer."""
    workflow = _workflow()
    job = workflow["jobs"][LINUX_JOB_ID]
    provision = _named_step(job, "Provision identity-bound Playwright Chromium toolchain")
    source = provision["run"]

    assert WORKFLOW_HELPER_COMMAND in source


def test_package_preprocess_resolves_playwright_native_runtime_paths() -> None:
    """The package smoke manifest must invoke the shared canonical producer."""
    workflow = _workflow()
    job = workflow["jobs"]["package-preprocess-smoke"]
    steps = [
        step for step in job["steps"]
        if step.get("name") == "Provision identity-bound Playwright Chromium toolchain"
    ]

    assert len(steps) == 1
    assert WORKFLOW_HELPER_COMMAND in steps[0]["run"]


def _load_playwright_manifest_module():
    """Load the workflow-owned helper without importing the PDD package."""
    spec = importlib.util.spec_from_file_location(
        "playwright_manifest", WORKFLOW_HELPER_PATH,
    )
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _elf_executable_bytes(
    *, bits: int = 64, byteorder: str = "little", dynamic: bool = True,
) -> bytes:
    """Build a minimal, structurally valid executable ELF fixture."""
    elf_class = {32: 1, 64: 2}[bits]
    data_encoding = {"little": 1, "big": 2}[byteorder]
    prefix = {"little": "<", "big": ">"}[byteorder]
    header_size = {32: 52, 64: 64}[bits]
    program_header_size = {32: 32, 64: 56}[bits]
    program_types = (1, 3, 2) if dynamic else (1,)
    header_format = {
        32: "HHIIIIIHHHHHH",
        64: "HHIQQQIHHHHHH",
    }[bits]
    program_format = {32: "IIIIIIII", 64: "IIQQQQQQ"}[bits]
    ident = b"\x7fELF" + bytes((elf_class, data_encoding, 1)) + b"\0" * 9
    header = struct.pack(
        prefix + header_format,
        2,
        3 if bits == 32 else 62,
        1,
        0,
        header_size,
        0,
        0,
        header_size,
        program_header_size,
        len(program_types),
        0,
        0,
        0,
    )
    programs = b"".join(
        struct.pack(prefix + program_format, program_type, *([0] * 7))
        for program_type in program_types
    )
    return ident + header + programs


def test_playwright_native_runtime_paths_canonicalizes_ldd_symlink_targets(
    tmp_path: Path,
) -> None:
    """Every manifest member is the canonical final library path."""
    toolchain_module = _load_playwright_manifest_module()
    executable = tmp_path / "browser"
    executable.write_bytes(_elf_executable_bytes())
    target = tmp_path / "libreal.dylib"
    target.write_bytes(b"library")
    alias = tmp_path / "libalias.dylib"
    alias.symlink_to(target)

    def ldd(command, **_kwargs):
        return subprocess.CompletedProcess(command, 0, f"lib => {alias}\n", "")

    assert toolchain_module.native_runtime_paths((executable,), ldd=ldd) == (
        target.resolve(),
    )


def test_playwright_native_runtime_paths_fails_closed_on_unresolvable_ldd_path(
    tmp_path: Path,
) -> None:
    """A loader path that cannot be canonicalized cannot enter the manifest."""
    toolchain_module = _load_playwright_manifest_module()
    executable = tmp_path / "browser"
    executable.write_bytes(_elf_executable_bytes())

    def ldd(command, **_kwargs):
        return subprocess.CompletedProcess(command, 0, "lib => /missing/lib.so\n", "")

    with pytest.raises(FileNotFoundError):
        toolchain_module.native_runtime_paths((executable,), ldd=ldd)


def test_playwright_native_runtime_paths_skips_non_elf_executable_scripts(
    tmp_path: Path,
) -> None:
    """Browser helper scripts are not dynamic-loader inputs."""
    toolchain_module = _load_playwright_manifest_module()
    script = tmp_path / "helper"
    script.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    script.chmod(script.stat().st_mode | stat.S_IXUSR)

    def ldd(*_args, **_kwargs):
        pytest.fail("ldd must not receive a non-ELF script")

    assert not toolchain_module.native_runtime_paths((script,), ldd=ldd)


@pytest.mark.parametrize(
    ("bits", "byteorder"),
    ((32, "little"), (64, "little"), (32, "big"), (64, "big")),
)
def test_playwright_native_runtime_paths_skips_well_formed_static_elfs(
    tmp_path: Path, bits: int, byteorder: str,
) -> None:
    """Only a structurally verified static ELF may bypass ldd."""
    toolchain_module = _load_playwright_manifest_module()
    executable = tmp_path / f"static-{bits}-{byteorder}"
    executable.write_bytes(
        _elf_executable_bytes(bits=bits, byteorder=byteorder, dynamic=False),
    )
    calls: list[list[str]] = []

    def ldd(command, **_kwargs):
        calls.append(command)
        return subprocess.CompletedProcess(
            command, 1, "", "not a dynamic executable",
        )

    assert toolchain_module.native_runtime_paths((executable,), ldd=ldd) == ()
    assert not calls


@pytest.mark.parametrize(
    "payload",
    (b"\x7fELF", _elf_executable_bytes()[:-1]),
)
def test_playwright_native_runtime_paths_rejects_malformed_elf_before_ldd(
    tmp_path: Path, payload: bytes,
) -> None:
    """Malformed ELF magic must fail closed instead of trusting ldd text."""
    toolchain_module = _load_playwright_manifest_module()
    executable = tmp_path / "malformed"
    executable.write_bytes(payload)

    def ldd(*_args, **_kwargs):
        pytest.fail("ldd must not receive malformed ELF data")

    with pytest.raises(RuntimeError, match="ELF"):
        toolchain_module.native_runtime_paths((executable,), ldd=ldd)


def test_playwright_native_runtime_paths_rejects_any_elf_ldd_failure(
    tmp_path: Path,
) -> None:
    """One failed ELF loader query cannot be hidden by another closure."""
    toolchain_module = _load_playwright_manifest_module()
    rejected = tmp_path / "rejected"
    accepted = tmp_path / "accepted"
    library = tmp_path / "libaccepted.so"
    for executable in (rejected, accepted):
        executable.write_bytes(_elf_executable_bytes())
    library.write_bytes(b"library")

    def ldd(command, **_kwargs):
        if Path(command[1]) == rejected:
            return subprocess.CompletedProcess(command, 1, "", "ldd failed")
        return subprocess.CompletedProcess(command, 0, f"lib => {library}\n", "")

    with pytest.raises(RuntimeError, match="ldd failed"):
        toolchain_module.native_runtime_paths((rejected, accepted), ldd=ldd)


def test_playwright_native_runtime_paths_rejects_unparseable_elf_closure(
    tmp_path: Path,
) -> None:
    """An ELF with no parseable runtime closure cannot be admitted."""
    toolchain_module = _load_playwright_manifest_module()
    executable = tmp_path / "browser"
    executable.write_bytes(_elf_executable_bytes())

    def ldd(command, **_kwargs):
        return subprocess.CompletedProcess(command, 0, "unparseable loader output\n", "")

    with pytest.raises(RuntimeError, match="closure"):
        toolchain_module.native_runtime_paths((executable,), ldd=ldd)


def _playwright_writer_inputs(tmp_path: Path) -> dict[str, Path]:
    """Build one complete fake Playwright toolchain for manifest tests."""
    toolchain = tmp_path / "toolchain"
    node_modules = toolchain / "node_modules"
    entrypoint = node_modules / "@playwright/test/cli.js"
    entrypoint.parent.mkdir(parents=True)
    entrypoint.write_text("module.exports = {};\n", encoding="utf-8")
    (toolchain / "package-lock.json").write_text("{}\n", encoding="utf-8")
    browser = tmp_path / "browser-cache"
    browser.mkdir()
    browser_elf = browser / "chrome"
    browser_elf.write_bytes(_elf_executable_bytes())
    browser_elf.chmod(browser_elf.stat().st_mode | stat.S_IXUSR)
    browser_script = browser / "chrome-wrapper"
    browser_script.write_text("#!/bin/sh\n", encoding="utf-8")
    browser_script.chmod(browser_script.stat().st_mode | stat.S_IXUSR)
    launcher = tmp_path / "node"
    launcher.write_bytes(_elf_executable_bytes())
    library = tmp_path / "libreal.so"
    library.write_bytes(b"library")
    alias = tmp_path / "libalias.so"
    alias.symlink_to(library)
    return {
        "toolchain": toolchain,
        "node_modules": node_modules,
        "entrypoint": entrypoint,
        "browser": browser,
        "browser_elf": browser_elf,
        "launcher": launcher,
        "library": library,
        "alias": alias,
        "environment": tmp_path / "github-env",
    }


def test_write_playwright_toolchain_manifest_writes_canonical_roles_and_environment(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The single producer emits the protected manifest and publishes it."""
    toolchain_module = _load_playwright_manifest_module()
    paths = _playwright_writer_inputs(tmp_path)
    monkeypatch.setattr(
        toolchain_module.shutil, "which", lambda _name: str(paths["launcher"]),
    )

    calls: list[Path] = []

    def ldd(command, **_kwargs):
        executable = Path(command[1])
        calls.append(executable)
        return subprocess.CompletedProcess(command, 0, f"lib => {paths['alias']}\n", "")

    manifest = toolchain_module.write_playwright_toolchain_manifest(
        paths["toolchain"], paths["browser"], paths["environment"], ldd=ldd,
    )

    payload = json.loads(manifest.read_text(encoding="utf-8"))
    roles = payload["roles"]
    assert payload["version"] == 3
    assert roles == {
        "launcher": str(paths["launcher"].resolve()),
        "entrypoint": str(paths["entrypoint"].resolve()),
        "dependencies": str(paths["node_modules"].resolve()),
        "browser_runtime": str(paths["browser"].resolve()),
        "native_runtime": [str(paths["library"].resolve())],
        "lockfile": str((paths["toolchain"] / "package-lock.json").resolve()),
    }
    assert calls == [paths["launcher"], paths["browser_elf"]]
    assert paths["environment"].read_text(encoding="utf-8") == (
        f"PDD_REAL_PLAYWRIGHT_TOOLCHAIN_MANIFEST={manifest}\n"
    )


@pytest.mark.parametrize(
    "case",
    [
        (1, "", "ldd failed", RuntimeError),
        (0, "lib => /missing/lib.so\n", "", FileNotFoundError),
    ],
)
def test_write_playwright_toolchain_manifest_fails_closed_for_invalid_elf_closure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    case: tuple[int, str, str, type[Exception]],
) -> None:
    """The full producer cannot publish a partial or unresolved ELF closure."""
    toolchain_module = _load_playwright_manifest_module()
    returncode, stdout, stderr, error = case
    paths = _playwright_writer_inputs(tmp_path)
    monkeypatch.setattr(
        toolchain_module.shutil, "which", lambda _name: str(paths["launcher"]),
    )

    def ldd(command, **_kwargs):
        return subprocess.CompletedProcess(command, returncode, stdout, stderr)

    with pytest.raises(error):
        toolchain_module.write_playwright_toolchain_manifest(
            paths["toolchain"], paths["browser"], paths["environment"], ldd=ldd,
        )
    assert not paths["environment"].exists()


def test_hosted_jobs_share_the_behaviorally_tested_manifest_producer() -> None:
    """Both hosted jobs must invoke the same producer after browser provisioning."""
    workflow = _workflow()
    for job_name in ("unit-tests", "package-preprocess-smoke"):
        steps = workflow["jobs"][job_name]["steps"]
        source = next(
            step["run"] for step in steps
            if step.get("name") == "Provision identity-bound Playwright Chromium toolchain"
        )
        assert source.count(WORKFLOW_HELPER_COMMAND) == 1
        assert "manifest.write_text" not in source
        assert "python - <<'PY'" not in source


def test_playwright_manifest_cli_runs_without_site_packages(tmp_path: Path) -> None:
    """The pre-install workflow command writes the full manifest with stdlib only."""
    paths = _playwright_writer_inputs(tmp_path)
    binary_dir = tmp_path / "bin"
    binary_dir.mkdir()
    node = binary_dir / "node"
    node.write_bytes(_elf_executable_bytes())
    node.chmod(node.stat().st_mode | stat.S_IXUSR)
    ldd = binary_dir / "ldd"
    ldd.write_text(
        f"#!/bin/sh\nprintf '%s\\n' 'lib => {paths['library'].resolve()}'\n",
        encoding="utf-8",
    )
    ldd.chmod(ldd.stat().st_mode | stat.S_IXUSR)
    environment = os.environ | {"PATH": f"{binary_dir}{os.pathsep}{os.environ['PATH']}"}

    result = subprocess.run(
        [
            sys.executable,
            "-I",
            "-S",
            str(WORKFLOW_HELPER_PATH.relative_to(REPO_ROOT)),
            "--toolchain",
            str(paths["toolchain"]),
            "--browser-cache",
            str(paths["browser"]),
            "--environment-file",
            str(paths["environment"]),
        ],
        cwd=REPO_ROOT,
        env=environment,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr
    manifest = paths["toolchain"] / "playwright-toolchain.json"
    assert json.loads(manifest.read_text(encoding="utf-8"))["roles"] == {
        "launcher": str(node.resolve()),
        "entrypoint": str(paths["entrypoint"].resolve()),
        "dependencies": str(paths["node_modules"].resolve()),
        "browser_runtime": str(paths["browser"].resolve()),
        "native_runtime": [str(paths["library"].resolve())],
        "lockfile": str((paths["toolchain"] / "package-lock.json").resolve()),
    }
    assert paths["environment"].read_text(encoding="utf-8") == (
        f"PDD_REAL_PLAYWRIGHT_TOOLCHAIN_MANIFEST={manifest}\n"
    )


@pytest.mark.parametrize(
    "detector",
    (
        REPO_ROOT / "scripts/ci_detect_changed_modules.py",
        REPO_ROOT / "pdd/ci_detect_changed_modules.py",
    ),
)
def test_playwright_workflow_diff_has_no_unmapped_auto_heal_modules(
    detector: Path,
) -> None:
    """The real branch diff must be accepted by both hosted detector entrypoints."""
    result = subprocess.run(
        [sys.executable, str(detector), "--diff-base", "origin/main...HEAD"],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr


@pytest.mark.parametrize(
    "mutate",
    (
        lambda command: command.replace(
            REQUIRED_HOSTED_NODES[6], "# " + REQUIRED_HOSTED_NODES[6]
        ),
        lambda command: _append_hosted_argument(command, REQUIRED_HOSTED_NODES[10]),
        lambda command: _append_hosted_argument(
            command, "tests/test_sync_core_supervisor.py::unexpected_hosted_case"
        ),
        _remove_hosted_node_line,
        lambda command: _append_hosted_argument(command, "-k parent-exit"),
        lambda command: _append_hosted_argument(
            command, "tests/test_sync_core_supervisor.py"
        ),
    ),
    ids=("commented", "duplicated", "unexpected", "removed", "k", "file-selector"),
)
def test_unit_tests_hosted_contract_rejects_selector_mutations(
    mutate: Callable[[str], str],
) -> None:
    """Every selection change must invalidate the exact hosted command."""
    workflow = _workflow()
    hosted, command = _hosted_command(workflow)
    mutated = mutate(command)
    assert mutated != command
    hosted["run"] = mutated

    with pytest.raises(AssertionError):
        _assert_hosted_linux_contract(workflow)


@pytest.mark.parametrize(
    "mutated_guard",
    (None, False, "github.event.pull_request.draft == false"),
    ids=("removed", "false", "altered"),
)
def test_unit_tests_hosted_contract_rejects_draft_guard_mutations(
    mutated_guard: object,
) -> None:
    """The reviewed draft guard must remain exactly attached to the unit-test job."""
    workflow = _workflow()
    job = workflow["jobs"][LINUX_JOB_ID]
    if mutated_guard is None:
        del job["if"]
    else:
        job["if"] = mutated_guard

    with pytest.raises(AssertionError):
        _assert_hosted_linux_contract(workflow)


@pytest.mark.parametrize(
    ("subject", "field", "value"),
    (
        ("provision", "if", False),
        ("hosted", "if", False),
        ("provision", "continue-on-error", True),
        ("hosted", "continue-on-error", True),
    ),
)
def test_unit_tests_hosted_contract_rejects_disabling_semantics(
    subject: str, field: str, value: object,
) -> None:
    """Critical steps must stay unconditional and failure-propagating."""
    workflow = _workflow()
    job = workflow["jobs"][LINUX_JOB_ID]
    targets = {
        "job": job,
        "provision": _named_step(job, PROVISION_STEP_NAME),
        "hosted": _named_step(job, HOSTED_STEP_NAME),
    }
    targets[subject][field] = value

    with pytest.raises(AssertionError):
        _assert_hosted_linux_contract(workflow)


def test_unit_tests_hosted_contract_rejects_reordered_steps() -> None:
    """Provisioning must execute before the hosted privileged test command."""
    workflow = _workflow()
    steps = workflow["jobs"][LINUX_JOB_ID]["steps"]
    provision = _named_step(workflow["jobs"][LINUX_JOB_ID], PROVISION_STEP_NAME)
    hosted = _named_step(workflow["jobs"][LINUX_JOB_ID], HOSTED_STEP_NAME)
    first, second = steps.index(provision), steps.index(hosted)
    steps[first], steps[second] = steps[second], steps[first]

    with pytest.raises(AssertionError):
        _assert_hosted_linux_contract(workflow)


def test_unit_tests_hosted_contract_rejects_dead_branch_prerequisite() -> None:
    """A prerequisite hidden in a dead shell branch is not top-level active setup."""
    workflow = _workflow()
    provision = _named_step(workflow["jobs"][LINUX_JOB_ID], PROVISION_STEP_NAME)
    active = "sudo apt-get install --yes bubblewrap"
    dead = f"if false; then\n          {active}\n          fi"
    provision["run"] = provision["run"].replace(active, dead)

    with pytest.raises(AssertionError):
        _assert_hosted_linux_contract(workflow)


def test_unit_tests_hosted_contract_rejects_commented_prerequisite() -> None:
    """A provisioning comment cannot satisfy the active Linux prerequisite contract."""
    workflow = _workflow()
    provision = _named_step(workflow["jobs"][LINUX_JOB_ID], PROVISION_STEP_NAME)
    provision["run"] = provision["run"].replace("sudo -n true", "# sudo -n true")

    with pytest.raises(AssertionError):
        _assert_hosted_linux_contract(workflow)
