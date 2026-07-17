"""Canonical hosted Playwright toolchain manifest production."""

from __future__ import annotations

import argparse
import json
import re
import shutil
import stat
import struct
import subprocess
from collections.abc import Callable, Iterable
from pathlib import Path


_LDD_PATH = re.compile(r"(?:=>\s+)?(/[^ ]+)")
_ELF_MAGIC = b"\x7fELF"
_ELF32 = 1
_ELF64 = 2
_ELFDATA2LSB = 1
_ELFDATA2MSB = 2
_ET_EXEC = 2
_ET_DYN = 3
_PN_XNUM = 0xFFFF
_PT_DYNAMIC = 2
_PT_INTERP = 3
_ELF_LAYOUTS = {
    _ELF32: (52, 32, "HHIIIIIHHHHHH"),
    _ELF64: (64, 56, "HHIQQQIHHHHHH"),
}


def _elf_layout(path: Path, payload: bytes) -> tuple[str, int, int, str]:
    """Return byte order and header layout after validating ELF identification."""
    if len(payload) < 16:
        raise RuntimeError(f"malformed ELF executable {path}: truncated identification")
    elf_class = payload[4]
    data_encoding = payload[5]
    if elf_class not in _ELF_LAYOUTS:
        raise RuntimeError(f"malformed ELF executable {path}: unsupported class")
    if data_encoding not in (_ELFDATA2LSB, _ELFDATA2MSB):
        raise RuntimeError(f"malformed ELF executable {path}: unsupported endianness")
    if payload[6] != 1:
        raise RuntimeError(f"malformed ELF executable {path}: unsupported version")
    header_size, program_header_size, header_format = _ELF_LAYOUTS[elf_class]
    byte_order = "<" if data_encoding == _ELFDATA2LSB else ">"
    return byte_order, header_size, program_header_size, header_format


def _program_header_bounds(
    path: Path, payload: bytes, layout: tuple[str, int, int, str],
) -> tuple[int, int]:
    """Return validated ELF program-header offset and count."""
    byte_order, header_size, program_header_size, header_format = layout
    if len(payload) < header_size:
        raise RuntimeError(f"malformed ELF executable {path}: truncated header")
    header = struct.unpack_from(byte_order + header_format, payload, 16)
    if header[0] not in (_ET_EXEC, _ET_DYN):
        raise RuntimeError(f"malformed ELF executable {path}: unsupported type")
    if header[2] != 1 or header[7] != header_size:
        raise RuntimeError(f"malformed ELF executable {path}: invalid header")
    program_header_offset = header[4]
    program_header_count = header[9]
    if program_header_count == _PN_XNUM:
        raise RuntimeError(f"malformed ELF executable {path}: extended program headers")
    if program_header_count == 0:
        if program_header_offset != 0:
            raise RuntimeError(f"malformed ELF executable {path}: invalid program headers")
        return 0, 0
    program_table_size = program_header_size * program_header_count
    if (
        header[8] != program_header_size
        or program_header_offset < header_size
        or program_header_offset > len(payload) - program_table_size
    ):
        raise RuntimeError(f"malformed ELF executable {path}: invalid program headers")
    return program_header_offset, program_header_count


def _elf_requires_dynamic_closure(path: Path) -> bool | None:
    """Return dynamic-runtime status for a valid ELF, or None for non-ELF files."""
    try:
        with path.open("rb") as handle:
            payload = handle.read()
    except OSError as error:
        raise RuntimeError(f"cannot identify Playwright executable {path}") from error

    if payload[:4] != _ELF_MAGIC:
        return None
    layout = _elf_layout(path, payload)
    byte_order, _header_size, program_header_size, _header_format = layout
    program_header_offset, program_header_count = _program_header_bounds(
        path, payload, layout,
    )

    dynamic_program_types = {_PT_DYNAMIC, _PT_INTERP}
    for index in range(program_header_count):
        offset = program_header_offset + index * program_header_size
        program_type = struct.unpack_from(byte_order + "I", payload, offset)[0]
        if program_type in dynamic_program_types:
            return True
    return False


def native_runtime_paths(
    executables: Iterable[Path], *,
    ldd: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
) -> tuple[Path, ...]:
    """Resolve every ELF loader closure to canonical regular dependency paths."""
    native: set[Path] = set()
    for executable in executables:
        executable = Path(executable).resolve(strict=True)
        if _elf_requires_dynamic_closure(executable) is not True:
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
