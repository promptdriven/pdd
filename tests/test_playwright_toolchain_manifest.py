"""Behavioral contracts for the hosted Playwright toolchain manifest producer."""

from __future__ import annotations

import json
import importlib.util
import stat
import subprocess
import sys
from pathlib import Path

import pytest
import yaml

WORKFLOW_PATH = Path(__file__).resolve().parents[1] / ".github/workflows/unit-tests.yml"
WORKFLOW_HELPER_PATH = (
    Path(__file__).resolve().parents[1] / ".github/toolchains/playwright_manifest.py"
)
WORKFLOW_HELPER_COMMAND = (
    'python .github/toolchains/playwright_manifest.py --toolchain "$toolchain" '
    '--browser-cache "$browser_cache" --environment-file "$GITHUB_ENV"'
)


def _load_toolchain_module():
    """Load the workflow-owned helper without importing the PDD package."""
    spec = importlib.util.spec_from_file_location(
        "playwright_manifest", WORKFLOW_HELPER_PATH,
    )
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_native_runtime_paths_canonicalizes_ldd_symlink_targets(tmp_path: Path) -> None:
    """Every manifest member is the canonical final library path."""
    toolchain_module = _load_toolchain_module()
    executable = tmp_path / "browser"
    executable.write_bytes(b"\x7fELFbrowser")
    target = tmp_path / "libreal.dylib"
    target.write_bytes(b"library")
    alias = tmp_path / "libalias.dylib"
    alias.symlink_to(target)

    def ldd(command, **_kwargs):
        return subprocess.CompletedProcess(command, 0, f"lib => {alias}\n", "")

    assert toolchain_module.native_runtime_paths((executable,), ldd=ldd) == (
        target.resolve(),
    )


def test_native_runtime_paths_fails_closed_on_unresolvable_ldd_path(tmp_path: Path) -> None:
    """A loader path that cannot be canonicalized cannot enter the manifest."""
    toolchain_module = _load_toolchain_module()
    executable = tmp_path / "browser"
    executable.write_bytes(b"\x7fELFbrowser")

    def ldd(command, **_kwargs):
        return subprocess.CompletedProcess(command, 0, "lib => /missing/lib.so\n", "")

    with pytest.raises(FileNotFoundError):
        toolchain_module.native_runtime_paths((executable,), ldd=ldd)


def test_native_runtime_paths_skips_non_elf_executable_scripts(tmp_path: Path) -> None:
    """Browser helper scripts are not dynamic-loader inputs."""
    toolchain_module = _load_toolchain_module()
    script = tmp_path / "helper"
    script.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    script.chmod(script.stat().st_mode | stat.S_IXUSR)

    def ldd(*_args, **_kwargs):
        pytest.fail("ldd must not receive a non-ELF script")

    assert not toolchain_module.native_runtime_paths((script,), ldd=ldd)


def test_native_runtime_paths_rejects_any_elf_ldd_failure(tmp_path: Path) -> None:
    """One failed ELF loader query cannot be hidden by another closure."""
    toolchain_module = _load_toolchain_module()
    rejected = tmp_path / "rejected"
    accepted = tmp_path / "accepted"
    library = tmp_path / "libaccepted.so"
    for executable in (rejected, accepted):
        executable.write_bytes(b"\x7fELFbrowser")
    library.write_bytes(b"library")

    def ldd(command, **_kwargs):
        if Path(command[1]) == rejected:
            return subprocess.CompletedProcess(command, 1, "", "ldd failed")
        return subprocess.CompletedProcess(command, 0, f"lib => {library}\n", "")

    with pytest.raises(RuntimeError, match="ldd failed"):
        toolchain_module.native_runtime_paths((rejected, accepted), ldd=ldd)


def test_native_runtime_paths_rejects_unparseable_elf_closure(tmp_path: Path) -> None:
    """An ELF with no parseable runtime closure cannot be admitted."""
    toolchain_module = _load_toolchain_module()
    executable = tmp_path / "browser"
    executable.write_bytes(b"\x7fELFbrowser")

    def ldd(command, **_kwargs):
        return subprocess.CompletedProcess(command, 0, "unparseable loader output\n", "")

    with pytest.raises(RuntimeError, match="closure"):
        toolchain_module.native_runtime_paths((executable,), ldd=ldd)


def _writer_inputs(tmp_path: Path) -> dict[str, Path]:
    toolchain = tmp_path / "toolchain"
    node_modules = toolchain / "node_modules"
    entrypoint = node_modules / "@playwright/test/cli.js"
    entrypoint.parent.mkdir(parents=True)
    entrypoint.write_text("module.exports = {};\n", encoding="utf-8")
    (toolchain / "package-lock.json").write_text("{}\n", encoding="utf-8")
    browser = tmp_path / "browser-cache"
    browser.mkdir()
    browser_elf = browser / "chrome"
    browser_elf.write_bytes(b"\x7fELFbrowser")
    browser_elf.chmod(browser_elf.stat().st_mode | stat.S_IXUSR)
    browser_script = browser / "chrome-wrapper"
    browser_script.write_text("#!/bin/sh\n", encoding="utf-8")
    browser_script.chmod(browser_script.stat().st_mode | stat.S_IXUSR)
    launcher = tmp_path / "node"
    launcher.write_bytes(b"\x7fELFnode")
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
    toolchain_module = _load_toolchain_module()
    paths = _writer_inputs(tmp_path)
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
    toolchain_module = _load_toolchain_module()
    returncode, stdout, stderr, error = case
    paths = _writer_inputs(tmp_path)
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
    workflow = yaml.safe_load(WORKFLOW_PATH.read_text(encoding="utf-8"))
    for job_name in ("unit-tests", "package-preprocess-smoke"):
        steps = workflow["jobs"][job_name]["steps"]
        source = next(
            step["run"] for step in steps
            if step.get("name") == "Provision identity-bound Playwright Chromium toolchain"
        )
        assert source.count(WORKFLOW_HELPER_COMMAND) == 1
        assert "manifest.write_text" not in source
        assert "python - <<'PY'" not in source


def test_workflow_helper_loads_in_isolated_python_without_pdd() -> None:
    """The pre-install helper must load without the package or third-party deps."""
    result = subprocess.run(
        [
            sys.executable,
            "-I",
            "-c",
            (
                "import runpy, sys; "
                "runpy.run_path(sys.argv[1], run_name='workflow_helper'); "
                "assert 'pdd' not in sys.modules"
            ),
            str(WORKFLOW_HELPER_PATH),
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr
