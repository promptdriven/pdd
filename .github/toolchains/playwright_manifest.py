"""Canonical hosted Playwright toolchain manifest production."""

from __future__ import annotations

import argparse
import json
import re
import shutil
import stat
import subprocess
from collections.abc import Callable, Iterable
from pathlib import Path


_LDD_PATH = re.compile(r"(?:=>\s+)?(/[^ ]+)")


def _is_elf_executable(path: Path) -> bool:
    """Return whether one browser runtime candidate is an ELF executable."""
    try:
        with path.open("rb") as handle:
            return handle.read(4) == b"\x7fELF"
    except OSError as error:
        raise RuntimeError(f"cannot identify Playwright executable {path}") from error


def native_runtime_paths(
    executables: Iterable[Path], *,
    ldd: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
) -> tuple[Path, ...]:
    """Resolve every ELF loader closure to canonical regular dependency paths."""
    native: set[Path] = set()
    for executable in executables:
        executable = Path(executable).resolve(strict=True)
        if not _is_elf_executable(executable):
            continue
        completed = ldd(
            ["ldd", str(executable)], capture_output=True, text=True, check=False,
        )
        if completed.returncode != 0:
            raise RuntimeError(
                f"ldd failed for {executable}: {completed.stderr.strip()}"
            )
        executable_native: set[Path] = set()
        for line in completed.stdout.splitlines():
            if not line.strip() or line.lstrip().startswith("linux-vdso"):
                continue
            if "not found" in line:
                raise RuntimeError(f"ldd reported unresolved dependency for {executable}")
            match = _LDD_PATH.search(line)
            if match is None:
                raise RuntimeError(f"ldd reported unparseable closure for {executable}")
            path = Path(match.group(1)).resolve(strict=True)
            if not path.is_file():
                raise RuntimeError(f"ldd dependency is not a regular file: {path}")
            executable_native.add(path)
        if not executable_native:
            raise RuntimeError(f"ldd reported empty closure for {executable}")
        native.update(executable_native)
    return tuple(sorted(native))


def write_playwright_toolchain_manifest(
    toolchain: Path, browser_cache: Path, environment_file: Path,
    *, ldd: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
) -> Path:
    """Write one identity-bound manifest and publish its path for the workflow."""
    root = toolchain.resolve(strict=True)
    launcher = Path(shutil.which("node") or "").resolve(strict=True)
    entrypoint = (root / "node_modules/@playwright/test/cli.js").resolve(strict=True)
    browser = browser_cache.resolve(strict=True)
    executables = [launcher, *(path for path in browser.rglob("*")
                               if path.is_file() and stat.S_IMODE(path.stat().st_mode) & 0o111)]
    native = native_runtime_paths(executables, ldd=ldd)
    if not native:
        raise RuntimeError("Playwright native runtime closure is empty")
    manifest = root / "playwright-toolchain.json"
    manifest.write_text(json.dumps({"version": 3, "roles": {
        "launcher": str(launcher), "entrypoint": str(entrypoint),
        "dependencies": str((root / "node_modules").resolve()),
        "browser_runtime": str(browser), "native_runtime": [str(path) for path in native],
        "lockfile": str((root / "package-lock.json").resolve(strict=True)),
    }}), encoding="utf-8")
    with environment_file.open("a", encoding="utf-8") as handle:
        handle.write(f"PDD_REAL_PLAYWRIGHT_TOOLCHAIN_MANIFEST={manifest}\n")
    return manifest


def main() -> None:
    """Produce the hosted manifest from explicit, workflow-owned paths."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--toolchain", required=True, type=Path)
    parser.add_argument("--browser-cache", required=True, type=Path)
    parser.add_argument("--environment-file", required=True, type=Path)
    arguments = parser.parse_args()
    write_playwright_toolchain_manifest(
        arguments.toolchain, arguments.browser_cache, arguments.environment_file,
    )


if __name__ == "__main__":
    main()
