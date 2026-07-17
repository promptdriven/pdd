#!/usr/bin/env python3
"""Build a test-only Vitest FD authority addon outside the source package."""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "pdd/sync_core/native/vitest_fd_cloexec.c"
def _node_include(node: Path) -> Path:
    """Return only the header directory belonging to the selected Node binary."""
    resolved = node.resolve(strict=True)
    include = resolved.parents[1] / "include/node"
    if not (include / "node_api.h").is_file():
        raise RuntimeError(
            "selected Node runtime does not provide N-API headers at "
            f"{include}; install a full Node 22 distribution before building"
        )
    return include


def main() -> None:
    """Compile one test-only `.node` module without npm or network use."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--node", default=shutil.which("node"))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--force-fcntl-error", action="store_true")
    parser.add_argument("--exec-probe", action="store_true")
    args = parser.parse_args()
    if not args.node:
        raise SystemExit("Node is required to build the trusted Vitest authority addon")
    if not SOURCE.is_file():
        raise SystemExit(f"trusted Vitest authority source is missing: {SOURCE}")
    if not sys.platform.startswith("linux"):
        raise SystemExit("the trusted Vitest authority addon supports Linux only")
    compiler = shutil.which("cc")
    if not compiler:
        raise SystemExit("a C compiler is required to build the trusted Vitest authority addon")
    node = Path(args.node)
    include = _node_include(node)
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    command = [compiler, "-std=c11", "-Wall", "-Wextra", "-Werror", "-I", str(include)]
    command.extend(("-shared", "-fPIC"))
    if args.force_fcntl_error:
        command.append("-DPDD_TEST_FORCE_FCNTL_ERROR=1")
    if args.exec_probe:
        command.append("-DPDD_TEST_EXEC_PROBE=1")
    temporary = output.with_suffix(output.suffix + ".tmp")
    command.extend((str(SOURCE), "-o", str(temporary)))
    subprocess.run(command, cwd=ROOT, check=True, env={"PATH": os.environ["PATH"]})
    temporary.chmod(0o555)
    temporary.replace(output)


if __name__ == "__main__":
    main()
