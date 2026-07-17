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
from typing import NamedTuple


_LDD_MAPPED_PATH = re.compile(
    r"^[ \t]*\S+[ \t]+=>[ \t]+(?P<path>/\S+)[ \t]+"
    r"\(0x[0-9A-Fa-f]+\)[ \t]*$"
)
_LDD_DIRECT_PATH = re.compile(
    r"^[ \t]*(?P<path>/\S+)[ \t]+\(0x[0-9A-Fa-f]+\)[ \t]*$"
)
_LDD_VDSO = re.compile(
    r"^[ \t]*linux-vdso\.so\.1[ \t]+\(0x[0-9A-Fa-f]+\)[ \t]*$"
)
_ELF_MAGIC = b"\x7fELF"
_ELF32 = 1
_ELF64 = 2
_ELFDATA2LSB = 1
_ELFDATA2MSB = 2
_ET_EXEC = 2
_ET_DYN = 3
_PN_XNUM = 0xFFFF
SHN_LORESERVE = 0xFF00
_PT_LOAD = 1
_PT_DYNAMIC = 2
_PT_INTERP = 3


class _ElfLayout(NamedTuple):
    """Class-specific ELF structure metadata."""

    header_size: int
    program_header_size: int
    section_header_size: int
    header_format: str
    program_header_format: str
    section_header_format: str


class _ProgramHeader(NamedTuple):
    """Program-header fields relevant to executable-loader validation."""

    kind: int
    offset: int
    virtual_address: int
    file_size: int
    memory_size: int
    alignment: int


class _ElfSource(NamedTuple):
    """Bounded reader context for one ELF executable."""

    path: Path
    handle: object
    file_size: int
    byte_order: str
    layout: _ElfLayout


_ELF_LAYOUTS = {
    _ELF32: _ElfLayout(
        52, 32, 40, "HHIIIIIHHHHHH", "IIIIIIII", "IIIIIIIIII",
    ),
    _ELF64: _ElfLayout(
        64, 56, 64, "HHIQQQIHHHHHH", "IIQQQQQQ", "IIQQQQIIQQ",
    ),
}


def _elf_layout(path: Path, identification: bytes) -> tuple[str, _ElfLayout]:
    """Return byte order and header layout after validating ELF identification."""
    if len(identification) < 16:
        raise RuntimeError(f"malformed ELF executable {path}: truncated identification")
    elf_class = identification[4]
    data_encoding = identification[5]
    if elf_class not in _ELF_LAYOUTS:
        raise RuntimeError(f"malformed ELF executable {path}: unsupported class")
    if data_encoding not in (_ELFDATA2LSB, _ELFDATA2MSB):
        raise RuntimeError(f"malformed ELF executable {path}: unsupported endianness")
    if identification[6] != 1:
        raise RuntimeError(f"malformed ELF executable {path}: unsupported version")
    byte_order = "<" if data_encoding == _ELFDATA2LSB else ">"
    return byte_order, _ELF_LAYOUTS[elf_class]


def _read_exact(handle, size: int, path: Path, description: str) -> bytes:
    """Read exactly one bounded ELF structure or fail closed."""
    payload = handle.read(size)
    if len(payload) != size:
        raise RuntimeError(f"malformed ELF executable {path}: truncated {description}")
    return payload


def _range_is_file_backed(offset: int, size: int, file_size: int) -> bool:
    """Return whether a non-negative range lies within the executable file."""
    return offset <= file_size and size <= file_size - offset


def _extended_program_header_count(
    source: _ElfSource, header: tuple[int, ...],
) -> int:
    """Resolve PN_XNUM from the first bounded section header."""
    section_header_offset = header[5]
    if (
        header[10] != source.layout.section_header_size
        or section_header_offset == 0
        or not _range_is_file_backed(
            section_header_offset, source.layout.section_header_size, source.file_size,
        )
    ):
        raise RuntimeError(
            f"malformed ELF executable {source.path}: invalid section headers",
        )
    source.handle.seek(section_header_offset)
    section = struct.unpack(
        source.byte_order + source.layout.section_header_format,
        _read_exact(
            source.handle, source.layout.section_header_size, source.path,
            "section header",
        ),
    )
    if section[1] != 0 or section[7] < _PN_XNUM:
        raise RuntimeError(f"malformed ELF executable {source.path}: invalid section zero")
    section_count = header[11]
    if section_count:
        if section_count >= SHN_LORESERVE:
            raise RuntimeError(f"malformed ELF executable {source.path}: invalid section count")
    else:
        section_count = section[5]
        if section_count < SHN_LORESERVE:
            raise RuntimeError(f"malformed ELF executable {source.path}: invalid section count")
    if (
        not _range_is_file_backed(
            section_header_offset,
            source.layout.section_header_size * section_count,
            source.file_size,
        )
    ):
        raise RuntimeError(f"malformed ELF executable {source.path}: invalid section table")
    return section[7]


def _program_header_bounds(
    source: _ElfSource, header: tuple[int, ...],
) -> tuple[int, int]:
    """Return validated ELF program-header offset and count."""
    if header[0] not in (_ET_EXEC, _ET_DYN):
        raise RuntimeError(f"malformed ELF executable {source.path}: unsupported type")
    if header[2] != 1 or header[7] != source.layout.header_size:
        raise RuntimeError(f"malformed ELF executable {source.path}: invalid header")
    program_header_offset = header[4]
    program_header_count = header[9]
    if program_header_count == _PN_XNUM:
        program_header_count = _extended_program_header_count(source, header)
    if header[8] != source.layout.program_header_size:
        raise RuntimeError(f"malformed ELF executable {source.path}: invalid program headers")
    if program_header_count == 0:
        if program_header_offset != 0:
            raise RuntimeError(
                f"malformed ELF executable {source.path}: invalid program headers",
            )
        return 0, 0
    program_table_size = source.layout.program_header_size * program_header_count
    if (
        program_header_offset < source.layout.header_size
        or not _range_is_file_backed(
            program_header_offset, program_table_size, source.file_size,
        )
    ):
        raise RuntimeError(f"malformed ELF executable {source.path}: invalid program headers")
    return program_header_offset, program_header_count


def _unpack_program_header(
    byte_order: str, layout: _ElfLayout, payload: bytes,
) -> _ProgramHeader:
    """Fully unpack one class-specific ELF program header."""
    fields = struct.unpack(byte_order + layout.program_header_format, payload)
    if layout.header_size == _ELF_LAYOUTS[_ELF32].header_size:
        return _ProgramHeader(fields[0], fields[1], fields[2], fields[4], fields[5], fields[7])
    return _ProgramHeader(fields[0], fields[2], fields[3], fields[5], fields[6], fields[7])


def _validate_program_header(
    path: Path, program: _ProgramHeader, executable_size: int,
) -> None:
    """Reject malformed file-backed segments and invalid load alignment."""
    if (
        program.file_size > program.memory_size
        or not _range_is_file_backed(
            program.offset, program.file_size, executable_size,
        )
    ):
        raise RuntimeError(f"malformed ELF executable {path}: invalid program range")
    if program.alignment not in (0, 1):
        if program.alignment & (program.alignment - 1):
            raise RuntimeError(f"malformed ELF executable {path}: invalid program alignment")
        if (
            program.kind == _PT_LOAD
            and program.offset % program.alignment
            != program.virtual_address % program.alignment
        ):
            raise RuntimeError(f"malformed ELF executable {path}: invalid load alignment")


def _elf_requires_dynamic_closure(path: Path) -> bool | None:
    """Return dynamic-runtime status for a valid ELF, or None for non-ELF files."""
    try:
        executable_size = path.stat().st_size
        with path.open("rb") as handle:
            identification = handle.read(16)
            if identification[:4] != _ELF_MAGIC:
                return None
            byte_order, layout = _elf_layout(path, identification)
            if executable_size < layout.header_size:
                raise RuntimeError(f"malformed ELF executable {path}: truncated header")
            header = struct.unpack(
                byte_order + layout.header_format,
                _read_exact(
                    handle, layout.header_size - len(identification), path, "header",
                ),
            )
            source = _ElfSource(path, handle, executable_size, byte_order, layout)
            program_header_offset, program_header_count = _program_header_bounds(source, header)
            needs_dynamic_closure = False
            for index in range(program_header_count):
                source.handle.seek(
                    program_header_offset + index * source.layout.program_header_size,
                )
                program = _unpack_program_header(
                    source.byte_order,
                    source.layout,
                    _read_exact(
                        source.handle, source.layout.program_header_size, path,
                        "program header",
                    ),
                )
                _validate_program_header(path, program, executable_size)
                if program.kind in (_PT_DYNAMIC, _PT_INTERP):
                    needs_dynamic_closure = True
    except OSError as error:
        raise RuntimeError(f"cannot identify Playwright executable {path}") from error
    return needs_dynamic_closure


def native_runtime_paths(
    executables: Iterable[Path], *,
    ldd: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
) -> tuple[Path, ...]:
    """Resolve every ELF closure while retaining mapped loader destinations."""
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
            if _LDD_VDSO.fullmatch(line):
                continue
            mapped = _LDD_MAPPED_PATH.fullmatch(line)
            match = mapped or _LDD_DIRECT_PATH.fullmatch(line)
            if match is None:
                raise RuntimeError(f"ldd reported unparseable closure for {executable}")
            declared = Path(match.group(1))
            canonical = declared.resolve(strict=True)
            if not canonical.is_file():
                raise RuntimeError(f"ldd dependency is not a regular file: {declared}")
            # Mapped entries name the SONAME path the loader will open.  Keep
            # that spelling as the bind destination after validating its
            # canonical source.  Direct entries name the interpreter itself;
            # retain its canonical regular-file identity as before.
            executable_native.add(declared if mapped is not None else canonical)
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
