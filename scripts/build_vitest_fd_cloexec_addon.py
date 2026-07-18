#!/usr/bin/env python3
"""Build a test-only Vitest FD authority addon outside the source package."""

from __future__ import annotations

import argparse
import os
import shutil
import stat
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "pdd/sync_core/native/vitest_fd_cloexec.c"


def _test_headers(headers: Path) -> Path:
    """Validate explicit non-production regression headers without link walks."""
    headers = headers.absolute()
    required = (
        "node_api.h", "node_api_types.h", "js_native_api.h",
        "js_native_api_types.h",
    )
    if headers.is_symlink() or not headers.is_dir():
        raise RuntimeError("test Node headers must be a regular directory")
    current = headers
    while True:
        metadata = current.lstat()
        if current.is_symlink() or not stat.S_ISDIR(metadata.st_mode):
            raise RuntimeError("test Node header ancestor must be a regular directory")
        if current == current.parent:
            break
        current = current.parent
    for path in (headers, *headers.rglob("*")):
        metadata = path.lstat()
        if path.is_symlink() or not (
            stat.S_ISREG(metadata.st_mode) or stat.S_ISDIR(metadata.st_mode)
        ):
            raise RuntimeError("test Node headers must be regular files")
    if any((headers / name).is_symlink() or not (headers / name).is_file() for name in required):
        raise RuntimeError("test Node headers omit required N-API declarations")
    return headers


def main() -> None:
    """Compile one test-only `.node` module without npm or network use."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--headers", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--force-fcntl-error", action="store_true")
    parser.add_argument("--force-prctl-error", action="store_true")
    parser.add_argument("--exec-probe", action="store_true")
    args = parser.parse_args()
    if not SOURCE.is_file():
        raise SystemExit(f"trusted Vitest authority source is missing: {SOURCE}")
    if not sys.platform.startswith("linux"):
        raise SystemExit("the trusted Vitest authority addon supports Linux only")
    compiler = shutil.which("cc")
    if not compiler:
        raise SystemExit("a C compiler is required to build the trusted Vitest authority addon")
    include = _test_headers(args.headers)
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    command = [compiler, "-std=c11", "-Wall", "-Wextra", "-Werror", "-I", str(include)]
    command.extend(("-shared", "-fPIC"))
    if args.force_fcntl_error:
        command.append("-DPDD_TEST_FORCE_FCNTL_ERROR=1")
    if args.force_prctl_error:
        command.append("-DPDD_TEST_FORCE_PRCTL_ERROR=1")
    if args.exec_probe:
        command.append("-DPDD_TEST_EXEC_PROBE=1")
    temporary = output.with_suffix(output.suffix + ".tmp")
    command.extend((str(SOURCE), "-o", str(temporary)))
    subprocess.run(command, cwd=ROOT, check=True, env={"PATH": os.environ["PATH"]})
    temporary.chmod(0o555)
    temporary.replace(output)


if __name__ == "__main__":
    main()
