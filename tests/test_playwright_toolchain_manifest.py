"""Behavioral contracts for the hosted Playwright toolchain manifest producer."""

from __future__ import annotations

import json
import os
import stat
import subprocess
from pathlib import Path

import pytest
import yaml

import pdd.sync_core.playwright_toolchain as toolchain_module
from pdd.sync_core.playwright_toolchain import (
    native_runtime_paths,
    write_playwright_toolchain_manifest,
)


WORKFLOW_PATH = Path(__file__).resolve().parents[1] / ".github/workflows/unit-tests.yml"


def test_native_runtime_paths_canonicalizes_ldd_symlink_targets(tmp_path: Path) -> None:
    """Every manifest member is the canonical final library path."""
    executable = tmp_path / "browser"
    executable.write_bytes(b"\x7fELFbrowser")
    target = tmp_path / "libreal.dylib"
    target.write_bytes(b"library")
    alias = tmp_path / "libalias.dylib"
    alias.symlink_to(target)

    def ldd(command, **_kwargs):
        return subprocess.CompletedProcess(command, 0, f"lib => {alias}\n", "")

    assert native_runtime_paths((executable,), ldd=ldd) == (target.resolve(),)


def test_native_runtime_paths_fails_closed_on_unresolvable_ldd_path(tmp_path: Path) -> None:
    """A loader path that cannot be canonicalized cannot enter the manifest."""
    executable = tmp_path / "browser"
    executable.write_bytes(b"\x7fELFbrowser")

    def ldd(command, **_kwargs):
        return subprocess.CompletedProcess(command, 0, "lib => /missing/lib.so\n", "")

    with pytest.raises(FileNotFoundError):
        native_runtime_paths((executable,), ldd=ldd)


def test_native_runtime_paths_skips_non_elf_executable_scripts(tmp_path: Path) -> None:
    """Browser helper scripts are not dynamic-loader inputs."""
    script = tmp_path / "helper"
    script.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    script.chmod(script.stat().st_mode | stat.S_IXUSR)

    def ldd(*_args, **_kwargs):
        pytest.fail("ldd must not receive a non-ELF script")

    assert native_runtime_paths((script,), ldd=ldd) == ()


def test_native_runtime_paths_rejects_any_elf_ldd_failure(tmp_path: Path) -> None:
    """One failed ELF loader query cannot be hidden by another closure."""
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
        native_runtime_paths((rejected, accepted), ldd=ldd)


def test_native_runtime_paths_rejects_unparseable_elf_closure(tmp_path: Path) -> None:
    """An ELF with no parseable runtime closure cannot be admitted."""
    executable = tmp_path / "browser"
    executable.write_bytes(b"\x7fELFbrowser")

    def ldd(command, **_kwargs):
        return subprocess.CompletedProcess(command, 0, "unparseable loader output\n", "")

    with pytest.raises(RuntimeError, match="closure"):
        native_runtime_paths((executable,), ldd=ldd)


def test_write_playwright_toolchain_manifest_writes_canonical_roles_and_environment(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The single producer emits the protected manifest and publishes it."""
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
    browser_script = browser / "chrome-wrapper"
    browser_script.write_text("#!/bin/sh\n", encoding="utf-8")
    browser_script.chmod(browser_script.stat().st_mode | stat.S_IXUSR)
    launcher = tmp_path / "node"
    launcher.write_bytes(b"\x7fELFnode")
    library = tmp_path / "libreal.so"
    library.write_bytes(b"library")
    alias = tmp_path / "libalias.so"
    alias.symlink_to(library)
    environment = tmp_path / "github-env"
    monkeypatch.setattr(toolchain_module.shutil, "which", lambda _name: str(launcher))

    calls: list[Path] = []

    def ldd(command, **_kwargs):
        executable = Path(command[1])
        calls.append(executable)
        return subprocess.CompletedProcess(command, 0, f"lib => {alias}\n", "")

    manifest = write_playwright_toolchain_manifest(
        toolchain, browser, environment, ldd=ldd,
    )

    payload = json.loads(manifest.read_text(encoding="utf-8"))
    roles = payload["roles"]
    assert payload["version"] == 3
    assert roles == {
        "launcher": str(launcher.resolve()),
        "entrypoint": str(entrypoint.resolve()),
        "dependencies": str(node_modules.resolve()),
        "browser_runtime": str(browser.resolve()),
        "native_runtime": [str(library.resolve())],
        "lockfile": str((toolchain / "package-lock.json").resolve()),
    }
    assert calls == [launcher, browser_elf]
    assert environment.read_text(encoding="utf-8") == (
        f"PDD_REAL_PLAYWRIGHT_TOOLCHAIN_MANIFEST={manifest}\n"
    )


def test_hosted_jobs_share_the_behaviorally_tested_manifest_producer() -> None:
    """Both hosted jobs must invoke the same producer after browser provisioning."""
    workflow = yaml.safe_load(WORKFLOW_PATH.read_text(encoding="utf-8"))
    for job_name in ("unit-tests", "package-preprocess-smoke"):
        steps = workflow["jobs"][job_name]["steps"]
        source = next(
            step["run"] for step in steps
            if step.get("name") == "Provision identity-bound Playwright Chromium toolchain"
        )
        assert source.count("python -m pdd.sync_core.playwright_toolchain") == 1
        assert "manifest.write_text" not in source
        assert "python - <<'PY'" not in source
